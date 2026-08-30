#!/usr/bin/env python3
"""Serialized-only exact verifier for refined seam-cache 5D certificates."""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import struct
import time
from dataclasses import dataclass
from fractions import Fraction as F
from pathlib import Path
import os
LIMIT = int(os.environ.get("SEXTUPLE_LIMIT", "59"))

PARTIALS = tuple((i, j) for i in range(5) for j in range(i, 5))
VECTORS = tuple(
    tuple(F(1) if i <= k <= j else F(0) for k in range(5))
    for i, j in PARTIALS
)
ANCHOR_DENOMINATOR = 16384


@dataclass(frozen=True)
class Piece:
    lo: F
    hi: F
    q: F
    a: F
    c: F


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
            piece = Piece(lo, hi, F(0), F(1, 4), F(0))
        elif kind == "zero":
            piece = Piece(lo, hi, F(0), F(0), F(0))
        elif kind == "barrier":
            piece = Piece(lo, hi, F(0), q(item["a"]), F(0))
        elif kind == "well":
            m, v, endpoint = q(item["m"]), q(item["v"]), q(item["q"])
            center = endpoint + v / m if item["side"] == "left" else endpoint - v / m
            piece = Piece(lo, hi, center, F(0), 2 * m * m)
        else:
            raise ValueError(f"unknown piece kind: {kind}")
        pieces.append(piece)
    assert len(pieces) == 56
    assert pieces[0].lo == 0 and pieces[-1].hi == 59
    assert all(left.hi == right.lo for left, right in zip(pieces, pieces[1:]))
    assert all(piece.lo < piece.hi and piece.a >= 0 and piece.c >= 0 for piece in pieces)
    return pieces


def read_refinements(path: Path) -> list[Piece]:
    raw = json.loads(path.read_text())
    pieces: list[Piece] = []
    for item in raw["pieces"]:
        lo, hi = q(item["lo"]), q(item["hi"])
        m, v, endpoint = q(item["m"]), q(item["v"]), q(item["q"])
        center = endpoint + v / m if item["side"] == "left" else endpoint - v / m
        pieces.append(Piece(lo, hi, center, F(0), 2 * m * m))
    assert len(pieces) == 216
    assert all(piece.lo < piece.hi and piece.c > 0 for piece in pieces)
    return pieces


def model_min(piece: Piece, lo: F, hi: F) -> F:
    assert piece.lo <= lo <= hi <= piece.hi
    point = piece.q if lo <= piece.q <= hi else lo if piece.q < lo else hi
    return piece.a + piece.c * (point - piece.q) ** 2


def tangent_lower(matrix, linear, constant, box, point: list[F]) -> F:
    value = constant + sum(linear[i] * point[i] for i in range(5)) + sum(
        matrix[i][j] * point[i] * point[j]
        for i in range(5)
        for j in range(5)
    )
    gradient = [
        linear[i] + 2 * sum(matrix[i][j] * point[j] for j in range(5))
        for i in range(5)
    ]
    return value + sum(
        min(gradient[i] * (box[i][0] - point[i]), gradient[i] * (box[i][1] - point[i]))
        for i in range(5)
    )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--data", type=Path, required=True)
    parser.add_argument("--refinements", type=Path, required=True)
    parser.add_argument("--tree-dir", type=Path, required=True)
    parser.add_argument("--report", type=Path, required=True)
    args = parser.parse_args()

    started = time.monotonic()
    manifest_path = args.tree_dir / "manifest.json"
    manifest = json.loads(manifest_path.read_text())
    assert manifest["schema"] == 2
    A, B, cutoff = q(manifest["A"]), q(manifest["B"]), q(manifest["cutoff"])
    assert 0 < A < 6 and B > 0 and cutoff == A / B
    assert sha256(args.data) == manifest["data_sha256"]
    assert sha256(args.refinements) == manifest["refinements_sha256"]
    pieces = read_pieces(args.data)
    refinements = read_refinements(args.refinements)
    catalog = pieces + refinements
    assert len(pieces) == manifest["stable_piece_count"]
    assert len(refinements) == manifest["refinement_piece_count"]
    assert len(catalog) == manifest["catalog_piece_count"]

    scalar_path = args.tree_dir / "scalar-certificates.json"
    assert sha256(scalar_path) == manifest["scalar_certificates_sha256"]
    scalar_payload = json.loads(scalar_path.read_text())
    assert scalar_payload["schema"] == 1
    assert scalar_payload["data_sha256"] == manifest["data_sha256"]
    assert scalar_payload["refinements_sha256"] == manifest["refinements_sha256"]
    assert q(scalar_payload["A"]) == A
    assert q(scalar_payload["B"]) == B
    assert q(scalar_payload["cutoff"]) == cutoff
    certificates = scalar_payload["certificates"]
    assert len(certificates) == manifest["scalar_certificate_count"]
    segment_count = 0
    for certificate in certificates:
        lo, hi, value = q(certificate["lo"]), q(certificate["hi"]), q(certificate["a"])
        segments = certificate["segments"]
        assert lo <= hi <= cutoff and value > 0 and segments
        cursor = lo
        exact_values: list[F] = []
        for segment in segments:
            left, right = q(segment["lo"]), q(segment["hi"])
            piece_index = segment["piece_index"]
            assert left == cursor and left <= right and 0 <= piece_index < len(catalog)
            piece = catalog[piece_index]
            assert piece.lo <= left and right <= piece.hi
            exact_value = model_min(piece, left, right)
            assert q(segment["model_min"]) == exact_value
            exact_values.append(exact_value)
            cursor = right
            segment_count += 1
        assert cursor == hi
        assert value == min(exact_values)
    assert segment_count == manifest["scalar_certificate_segment_count"]

    stream_names = {
        "topology": "topology-u64le.bin",
        "kinds": "terminal-kinds-u8.bin",
        "anchors": "anchors-u16le.bin",
        "terms": "term-codes-u16le.bin",
    }
    streams: dict[str, bytes] = {}
    for key, name in stream_names.items():
        path = args.tree_dir / name
        data = path.read_bytes()
        assert len(data) == manifest["stream_bytes"][key]
        assert hashlib.sha256(data).hexdigest() == manifest["stream_sha256"][key]
        streams[key] = data

    token_count = manifest["token_count"]
    word_count = (token_count + 19) // 20
    assert word_count == manifest["topology_word_count"]
    assert len(streams["topology"]) == 8 * word_count
    words = list(struct.unpack("<" + "Q" * word_count, streams["topology"]))
    assert all(word < 1 << 60 for word in words)
    remainder = token_count % 20
    if remainder:
        assert words[-1] < 1 << (3 * remainder)
    tokens = [
        (words[index // 20] >> (3 * (index % 20))) & 7
        for index in range(token_count)
    ]
    assert all(token <= 5 for token in tokens)

    kinds = streams["kinds"]
    assert len(kinds) == manifest["leaves"]
    assert all(kind <= 1 for kind in kinds)
    assert len(streams["anchors"]) == manifest["quadratic_leaves"] * 5 * 2
    assert len(streams["terms"]) == manifest["quadratic_leaves"] * 15 * 2
    anchor_codes = list(
        struct.unpack("<" + "H" * (len(streams["anchors"]) // 2), streams["anchors"])
    )
    term_codes = list(
        struct.unpack("<" + "H" * (len(streams["terms"]) // 2), streams["terms"])
    )
    assert all(code <= ANCHOR_DENOMINATOR for code in anchor_codes)

    root = tuple((F(0), F(LIMIT)) for _ in range(5))
    stack = [(root, 0)]
    token_cursor = kind_cursor = quadratic_cursor = 0
    tail_leaves = quadratic_leaves = maximum_depth = 0
    smallest_tail_margin: F | None = None
    smallest_quadratic_margin: F | None = None
    tightest_tail: dict[str, object] | None = None
    tightest_quadratic: dict[str, object] | None = None

    while stack:
        box, depth = stack.pop()
        maximum_depth = max(maximum_depth, depth)
        assert token_cursor < token_count
        token = tokens[token_cursor]
        token_cursor += 1
        if token:
            axis = token - 1
            lo, hi = box[axis]
            midpoint = (lo + hi) / 2
            left, right = list(box), list(box)
            left[axis] = (lo, midpoint)
            right[axis] = (midpoint, hi)
            stack.append((tuple(right), depth + 1))
            stack.append((tuple(left), depth + 1))
            continue

        assert kind_cursor < len(kinds)
        kind = kinds[kind_cursor]
        kind_cursor += 1
        if kind == 0:
            margin = B * sum((bounds[0] for bounds in box), F(0)) - A
            assert margin >= 0
            if smallest_tail_margin is None or margin < smallest_tail_margin:
                smallest_tail_margin = margin
                tightest_tail = {"depth": depth, "box": box_json(box), "margin": qs(margin)}
            tail_leaves += 1
            continue

        assert quadratic_cursor < manifest["quadratic_leaves"]
        local_anchor_codes = anchor_codes[5 * quadratic_cursor : 5 * quadratic_cursor + 5]
        local_term_codes = term_codes[15 * quadratic_cursor : 15 * quadratic_cursor + 15]
        quadratic_cursor += 1
        point = [
            lo + F(code, ANCHOR_DENOMINATOR) * (hi - lo)
            for code, (lo, hi) in zip(local_anchor_codes, box)
        ]
        matrix = [[F(0) for _ in range(5)] for _ in range(5)]
        linear = [B for _ in range(5)]
        constant = F(0)
        for vector, (left_index, right_index), code in zip(VECTORS, PARTIALS, local_term_codes):
            distance_lo = sum(
                (box[k][0] for k in range(left_index, right_index + 1)), F(0)
            )
            distance_hi = min(
                sum((box[k][1] for k in range(left_index, right_index + 1)), F(0)),
                cutoff,
            )
            if code == 65535:
                continue
            assert distance_lo <= distance_hi
            if code < len(catalog):
                piece = catalog[code]
                assert piece.lo <= distance_lo and distance_hi <= piece.hi
                constant += piece.a + piece.c * piece.q * piece.q
            elif 32768 <= code < 32768 + len(certificates):
                certificate = certificates[code - 32768]
                assert q(certificate["lo"]) <= distance_lo
                assert distance_hi <= q(certificate["hi"])
                constant += q(certificate["a"])
                continue
            else:
                raise AssertionError(("invalid term code", code))
            if piece.c:
                for row in range(5):
                    if not vector[row]:
                        continue
                    linear[row] -= 2 * piece.c * piece.q
                    for column in range(5):
                        if vector[column]:
                            matrix[row][column] += piece.c

        lower = tangent_lower(matrix, linear, constant, box, point)
        margin = lower - A
        assert margin >= 0
        if smallest_quadratic_margin is None or margin < smallest_quadratic_margin:
            smallest_quadratic_margin = margin
            tightest_quadratic = {
                "depth": depth,
                "box": box_json(box),
                "anchor_codes": local_anchor_codes,
                "anchor": [qs(value) for value in point],
                "term_codes": local_term_codes,
                "lower": qs(lower),
                "margin": qs(margin),
            }
        quadratic_leaves += 1

    assert not stack
    assert token_cursor == token_count
    assert kind_cursor == len(kinds)
    assert quadratic_cursor == manifest["quadratic_leaves"]
    assert tail_leaves == manifest["tail_leaves"]
    assert quadratic_leaves == manifest["quadratic_leaves"]
    assert maximum_depth == manifest["maximum_depth"]
    assert tail_leaves + quadratic_leaves == manifest["leaves"]
    assert token_count == 2 * manifest["leaves"] - 1
    assert smallest_tail_margin is not None and smallest_quadratic_margin is not None
    assert qs(smallest_tail_margin) == manifest["smallest_tail_margin"]
    assert qs(smallest_quadratic_margin) == manifest["smallest_quadratic_margin"]

    report = {
        "status": "PASS",
        "verifier_sha256": sha256(Path(__file__)),
        "manifest_sha256": sha256(manifest_path),
        "scalar_certificates_sha256": sha256(scalar_path),
        "data_sha256": sha256(args.data),
        "refinements_sha256": sha256(args.refinements),
        "stable_piece_count": len(pieces),
        "refinement_piece_count": len(refinements),
        "catalog_piece_count": len(catalog),
        "A": qs(A),
        "B": qs(B),
        "cutoff": qs(cutoff),
        "token_count": token_cursor,
        "kind_cursor": kind_cursor,
        "quadratic_cursor": quadratic_cursor,
        "full_topology_exhaustion": token_cursor == token_count,
        "full_kind_exhaustion": kind_cursor == len(kinds),
        "full_quadratic_exhaustion": quadratic_cursor == manifest["quadratic_leaves"],
        "empty_stack": not stack,
        "maximum_depth": maximum_depth,
        "leaves": tail_leaves + quadratic_leaves,
        "tail_leaves": tail_leaves,
        "quadratic_leaves": quadratic_leaves,
        "scalar_certificate_count": len(certificates),
        "scalar_certificate_segment_count": segment_count,
        "smallest_tail_margin": qs(smallest_tail_margin),
        "smallest_tail_margin_float": float(smallest_tail_margin),
        "smallest_quadratic_margin": qs(smallest_quadratic_margin),
        "smallest_quadratic_margin_float": float(smallest_quadratic_margin),
        "tightest_tail_leaf": tightest_tail,
        "tightest_quadratic_leaf": tightest_quadratic,
        "elapsed_seconds": time.monotonic() - started,
        "trust_note": "Serialized streams and refined scalar certificates were replayed using exact Fraction arithmetic; floats appear only in decimal summaries.",
    }
    args.report.parent.mkdir(parents=True, exist_ok=True)
    atomic_json(args.report, report)
    print(json.dumps(report, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
