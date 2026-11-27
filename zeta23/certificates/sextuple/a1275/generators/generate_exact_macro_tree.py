#!/usr/bin/env python3
"""Generate an exact rational 5D macro B&B certificate for configurable A and B.

Floating-point coordinate descent proposes an anchor. Every terminal decision,
model coefficient, scalar interval minimum, margin, and stream field is checked
with fractions.Fraction. The stored relative anchors have denominator 16384.
"""
from __future__ import annotations

import argparse
import bisect
import hashlib
import json
import math
import os
import struct
import sys
import time
from collections import Counter
from dataclasses import asdict, dataclass
from fractions import Fraction as F
from pathlib import Path

PARTIALS = tuple((i, j) for i in range(5) for j in range(i, 5))
VECTORS = tuple(
    tuple(F(1) if i <= k <= j else F(0) for k in range(5))
    for i, j in PARTIALS
)
WEIGHTS = (5, 8, 9, 8, 5)
ANCHOR_DENOMINATOR = 16384
PROPOSAL_DENOMINATOR = 1 << 34


@dataclass(frozen=True)
class Piece:
    lo: F
    hi: F
    q: F
    a: F
    c: F
    kind: str


def q(text: str) -> F:
    return F(text)


def qs(value: F) -> str:
    if value.denominator == 1:
        return str(value.numerator)
    return f"{value.numerator}/{value.denominator}"


def box_json(box: tuple[tuple[F, F], ...]) -> list[list[str]]:
    return [[qs(lo), qs(hi)] for lo, hi in box]


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def atomic_bytes(path: Path, data: bytes) -> None:
    temporary = path.with_suffix(path.suffix + ".new")
    temporary.write_bytes(data)
    os.replace(temporary, path)


def atomic_json(path: Path, value: object) -> None:
    temporary = path.with_suffix(path.suffix + ".new")
    temporary.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n")
    os.replace(temporary, path)


def read_pieces(path: Path) -> list[Piece]:
    raw = json.loads(path.read_text())
    pieces: list[Piece] = []
    for item in raw["pieces"]:
        lo, hi, kind = q(item["lo"]), q(item["hi"]), item["kind"]
        if kind == "low":
            piece = Piece(lo, hi, F(0), F(1, 4), F(0), kind)
        elif kind == "zero":
            piece = Piece(lo, hi, F(0), F(0), F(0), kind)
        elif kind == "barrier":
            piece = Piece(lo, hi, F(0), q(item["a"]), F(0), kind)
        elif kind == "well":
            m, v, endpoint = q(item["m"]), q(item["v"]), q(item["q"])
            center = endpoint + v / m if item["side"] == "left" else endpoint - v / m
            piece = Piece(lo, hi, center, F(0), 2 * m * m, kind)
        else:
            raise ValueError(f"unknown piece kind: {kind}")
        pieces.append(piece)
    assert len(pieces) == 56
    assert pieces[0].lo == 0 and pieces[-1].hi == 59
    assert all(left.hi == right.lo for left, right in zip(pieces, pieces[1:]))
    assert all(piece.lo < piece.hi and piece.c >= 0 and piece.a >= 0 for piece in pieces)
    return pieces


def model_min(piece: Piece, lo: F, hi: F) -> F:
    assert piece.lo <= lo <= hi <= piece.hi
    point = piece.q if lo <= piece.q <= hi else lo if piece.q < lo else hi
    return piece.a + piece.c * (point - piece.q) ** 2


class ExactChecker:
    def __init__(self, pieces: list[Piece], A: F, B: F) -> None:
        assert 0 < A < 6 and B > 0
        self.pieces = pieces
        self.highs = [piece.hi for piece in pieces]
        self.A = A
        self.B = B
        self.cutoff = A / B
        self.scalar_values: dict[tuple[F, F], F] = {}
        self.scalar_ids: dict[tuple[F, F], int] = {}
        self.scalar_certificates: list[dict[str, object]] = []

    def containing(self, lo: F, hi: F) -> tuple[int, Piece] | None:
        if hi < lo:
            return None
        index = bisect.bisect_left(self.highs, lo)
        for candidate in (index, index + 1):
            if 0 <= candidate < len(self.pieces):
                piece = self.pieces[candidate]
                if piece.lo <= lo and hi <= piece.hi:
                    return candidate, piece
        return None

    def scalar_segments(self, lo: F, hi: F) -> list[dict[str, object]]:
        assert lo <= hi
        segments: list[dict[str, object]] = []
        first = bisect.bisect_left(self.highs, lo)
        index = max(0, first)
        while index < len(self.pieces) and self.pieces[index].lo <= hi:
            piece = self.pieces[index]
            left, right = max(lo, piece.lo), min(hi, piece.hi)
            if left <= right:
                segments.append(
                    {
                        "lo": qs(left),
                        "hi": qs(right),
                        "piece_index": index,
                        "model_min": qs(model_min(piece, left, right)),
                    }
                )
            index += 1
        assert segments
        assert q(segments[0]["lo"]) == lo and q(segments[-1]["hi"]) == hi
        assert all(q(left["hi"]) == q(right["lo"]) for left, right in zip(segments, segments[1:]))
        return segments

    def scalar_min(self, lo: F, hi: F) -> F:
        hi = min(hi, self.cutoff)
        if hi < lo:
            return F(0)
        key = (lo, hi)
        cached = self.scalar_values.get(key)
        if cached is not None:
            return cached
        segments = self.scalar_segments(lo, hi)
        value = min(q(segment["model_min"]) for segment in segments)
        self.scalar_values[key] = value
        return value

    def scalar_id(self, lo: F, hi: F) -> tuple[int, F]:
        hi = min(hi, self.cutoff)
        if hi < lo:
            return 65535, F(0)
        value = self.scalar_min(lo, hi)
        if value == 0:
            return 65535, value
        key = (lo, hi)
        if key not in self.scalar_ids:
            certificate_id = len(self.scalar_certificates)
            assert certificate_id < 32767
            self.scalar_ids[key] = certificate_id
            segments = self.scalar_segments(lo, hi)
            assert value == min(q(segment["model_min"]) for segment in segments)
            self.scalar_certificates.append(
                {"lo": qs(lo), "hi": qs(hi), "a": qs(value), "segments": segments}
            )
        return 32768 + self.scalar_ids[key], value

    def quadratic_data(self, box: tuple[tuple[F, F], ...]):
        matrix = [[F(0) for _ in range(5)] for _ in range(5)]
        linear = [self.B for _ in range(5)]
        constant = F(0)
        term_codes: list[int] = []
        for vector, (left_index, right_index) in zip(VECTORS, PARTIALS):
            lo = sum((box[k][0] for k in range(left_index, right_index + 1)), F(0))
            hi = sum((box[k][1] for k in range(left_index, right_index + 1)), F(0))
            clipped_hi = min(hi, self.cutoff)
            selected = self.containing(lo, clipped_hi)
            if selected is None:
                code, value = self.scalar_id(lo, clipped_hi)
                term_codes.append(code)
                constant += value
                continue
            piece_index, piece = selected
            term_codes.append(piece_index)
            constant += piece.a + piece.c * piece.q * piece.q
            if piece.c:
                for row in range(5):
                    if not vector[row]:
                        continue
                    linear[row] -= 2 * piece.c * piece.q
                    for column in range(5):
                        if vector[column]:
                            matrix[row][column] += piece.c
        assert len(term_codes) == 15
        return matrix, linear, constant, term_codes

    @staticmethod
    def float_coordinate_descent(matrix, linear, box, sweeps: int = 12) -> list[float]:
        mf = [[float(value) for value in row] for row in matrix]
        lf = [float(value) for value in linear]
        lo = [float(bounds[0]) for bounds in box]
        hi = [float(bounds[1]) for bounds in box]
        point = [(left + right) / 2 for left, right in zip(lo, hi)]
        for _ in range(sweeps):
            for row in range(5):
                diagonal = mf[row][row]
                if diagonal > 0:
                    off_diagonal = sum(
                        mf[row][column] * point[column]
                        for column in range(5)
                        if column != row
                    )
                    value = -(lf[row] + 2 * off_diagonal) / (2 * diagonal)
                    point[row] = min(max(value, lo[row]), hi[row])
                else:
                    point[row] = lo[row] if lf[row] >= 0 else hi[row]
        return point

    @staticmethod
    def rationalize_proposal(point: list[float], box) -> list[F]:
        result: list[F] = []
        for value, (lo, hi) in zip(point, box):
            candidate = F(round(value * PROPOSAL_DENOMINATOR), PROPOSAL_DENOMINATOR)
            result.append(min(max(candidate, lo), hi))
        return result


def polynomial(matrix, linear, constant, point: list[F]) -> F:
    return constant + sum(linear[i] * point[i] for i in range(5)) + sum(
        matrix[i][j] * point[i] * point[j]
        for i in range(5)
        for j in range(5)
    )


def tangent_lower(matrix, linear, constant, box, point: list[F]) -> F:
    value = polynomial(matrix, linear, constant, point)
    gradient = [
        linear[i] + 2 * sum(matrix[i][j] * point[j] for j in range(5))
        for i in range(5)
    ]
    return value + sum(
        min(gradient[i] * (box[i][0] - point[i]), gradient[i] * (box[i][1] - point[i]))
        for i in range(5)
    )


def nearest_integer(value: F) -> int:
    if value < 0:
        return -nearest_integer(-value)
    return (2 * value.numerator + value.denominator) // (2 * value.denominator)


def relative_anchor(proposal: list[F], box) -> tuple[list[int], list[F]]:
    codes: list[int] = []
    point: list[F] = []
    for value, (lo, hi) in zip(proposal, box):
        if lo == hi:
            code = 0
        else:
            code = min(max(nearest_integer((value - lo) / (hi - lo) * ANCHOR_DENOMINATOR), 0), ANCHOR_DENOMINATOR)
        codes.append(code)
        point.append(lo + F(code, ANCHOR_DENOMINATOR) * (hi - lo))
    return codes, point


def pack_topology(tokens: list[int]) -> tuple[bytes, list[int]]:
    words: list[int] = []
    for start in range(0, len(tokens), 20):
        word = sum(token << (3 * offset) for offset, token in enumerate(tokens[start : start + 20]))
        assert word < 1 << 60
        words.append(word)
    return b"".join(struct.pack("<Q", word) for word in words), words


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--data", type=Path, required=True)
    parser.add_argument("--output-dir", type=Path, required=True)
    parser.add_argument("--a", default="1/80")
    parser.add_argument("--b", default="1094977/5000000000")
    parser.add_argument("--max-nodes", type=int, default=2_000_000)
    parser.add_argument("--progress", type=int, default=25000)
    args = parser.parse_args()

    A, B = q(args.a), q(args.b)
    assert 0 < A < 6 and B > 0
    pieces = read_pieces(args.data)
    checker = ExactChecker(pieces, A, B)
    root = tuple((F(0), F(59)) for _ in range(5))
    stack = [(root, 0)]
    tokens: list[int] = []
    kinds = bytearray()
    anchors = bytearray()
    terms = bytearray()
    visited = leaves = tail_leaves = quadratic_leaves = maximum_depth = 0
    smallest_quadratic_margin: F | None = None
    smallest_tail_margin: F | None = None
    tightest_quadratic: dict[str, object] | None = None
    tightest_tail: dict[str, object] | None = None
    term_histogram: Counter[int] = Counter()
    started = time.monotonic()

    while stack:
        box, depth = stack.pop()
        visited += 1
        maximum_depth = max(maximum_depth, depth)
        if visited > args.max_nodes:
            raise ArithmeticError(f"node limit exceeded with {len(stack)} pending")
        span_lower = sum((bounds[0] for bounds in box), F(0))
        tail_margin = B * span_lower - A
        if tail_margin >= 0:
            tokens.append(0)
            kinds.append(0)
            leaves += 1
            tail_leaves += 1
            if smallest_tail_margin is None or tail_margin < smallest_tail_margin:
                smallest_tail_margin = tail_margin
                tightest_tail = {"depth": depth, "box": box_json(box), "margin": qs(tail_margin)}
            continue

        matrix, linear, constant, term_codes = checker.quadratic_data(box)
        float_proposal = checker.float_coordinate_descent(matrix, linear, box)
        exact_proposal = checker.rationalize_proposal(float_proposal, box)
        anchor_codes, point = relative_anchor(exact_proposal, box)
        lower = tangent_lower(matrix, linear, constant, box, point)
        margin = lower - A
        if margin >= 0:
            tokens.append(0)
            kinds.append(1)
            leaves += 1
            quadratic_leaves += 1
            if smallest_quadratic_margin is None or margin < smallest_quadratic_margin:
                smallest_quadratic_margin = margin
                tightest_quadratic = {
                    "depth": depth,
                    "box": box_json(box),
                    "anchor_codes": anchor_codes,
                    "anchor": [qs(value) for value in point],
                    "term_codes": term_codes,
                    "lower": qs(lower),
                    "margin": qs(margin),
                }
            for code in anchor_codes:
                anchors.extend(struct.pack("<H", code))
            for code in term_codes:
                terms.extend(struct.pack("<H", code))
                term_histogram[code] += 1
            continue

        weighted_widths = [
            (hi - lo) * WEIGHTS[index]
            for index, (lo, hi) in enumerate(box)
        ]
        axis = max(range(5), key=weighted_widths.__getitem__)
        tokens.append(axis + 1)
        lo, hi = box[axis]
        midpoint = (lo + hi) / 2
        left, right = list(box), list(box)
        left[axis] = (lo, midpoint)
        right[axis] = (midpoint, hi)
        stack.append((tuple(right), depth + 1))
        stack.append((tuple(left), depth + 1))

        if args.progress and visited % args.progress == 0:
            print(
                f"progress visited={visited} pending={len(stack)} depth={maximum_depth} "
                f"seconds={time.monotonic() - started:.1f}",
                flush=True,
            )

    assert smallest_quadratic_margin is not None and smallest_tail_margin is not None
    packed_topology, topology_words = pack_topology(tokens)
    args.output_dir.mkdir(parents=True, exist_ok=True)
    stream_data = {
        "topology": packed_topology,
        "kinds": bytes(kinds),
        "anchors": bytes(anchors),
        "terms": bytes(terms),
    }
    stream_names = {
        "topology": "topology-u64le.bin",
        "kinds": "terminal-kinds-u8.bin",
        "anchors": "anchors-u16le.bin",
        "terms": "term-codes-u16le.bin",
    }
    for key, data in stream_data.items():
        atomic_bytes(args.output_dir / stream_names[key], data)

    scalar_path = args.output_dir / "scalar-certificates.json"
    scalar_payload = {
        "schema": 1,
        "data_sha256": sha256(args.data),
        "A": qs(A),
        "B": qs(B),
        "cutoff": qs(checker.cutoff),
        "certificates": checker.scalar_certificates,
    }
    atomic_json(scalar_path, scalar_payload)

    manifest = {
        "schema": 1,
        "generator_sha256": sha256(Path(__file__)),
        "python": {"executable": sys.executable, "realpath": os.path.realpath(sys.executable)},
        "A": qs(A),
        "B": qs(B),
        "cutoff": qs(checker.cutoff),
        "data": str(args.data.resolve()),
        "data_sha256": sha256(args.data),
        "format": {
            "topology": "20 3-bit tokens per u64le word; unused high bits zero",
            "kinds": "u8: 0 tail, 1 quadratic",
            "anchors": "5 u16le codes per quadratic leaf; relative denominator 16384",
            "terms": "15 u16le codes per quadratic leaf: 0..55 piece, 32768+n scalar cert, 65535 zero",
        },
        "token_count": len(tokens),
        "topology_word_count": len(topology_words),
        "visited_nodes": visited,
        "leaves": leaves,
        "tail_leaves": tail_leaves,
        "quadratic_leaves": quadratic_leaves,
        "maximum_depth": maximum_depth,
        "fuel": maximum_depth + 1,
        "full_stack_exhaustion": not stack,
        "scalar_certificate_count": len(checker.scalar_certificates),
        "scalar_certificate_segment_count": sum(len(cert["segments"]) for cert in checker.scalar_certificates),
        "scalar_certificates_sha256": sha256(scalar_path),
        "smallest_quadratic_margin": qs(smallest_quadratic_margin),
        "smallest_quadratic_margin_float": float(smallest_quadratic_margin),
        "smallest_tail_margin": qs(smallest_tail_margin),
        "smallest_tail_margin_float": float(smallest_tail_margin),
        "tightest_quadratic_leaf": tightest_quadratic,
        "tightest_tail_leaf": tightest_tail,
        "zero_term_count": term_histogram[65535],
        "scalar_term_count": sum(count for code, count in term_histogram.items() if 32768 <= code < 65535),
        "stream_bytes": {key: len(data) for key, data in stream_data.items()},
        "stream_sha256": {
            key: hashlib.sha256(data).hexdigest() for key, data in stream_data.items()
        },
        "elapsed_seconds": time.monotonic() - started,
        "trust_note": "Float coordinate descent only proposes anchors. All stored terminal checks and margins use exact Fraction arithmetic.",
    }
    atomic_json(args.output_dir / "manifest.json", manifest)
    print(json.dumps(manifest, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
