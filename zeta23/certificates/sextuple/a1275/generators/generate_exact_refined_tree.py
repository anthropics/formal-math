#!/usr/bin/env python3
"""Generate an exact 5D B&B tree using stable plus Lean-checked narrow wells."""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import struct
import sys
import time
from collections import Counter
from fractions import Fraction as F
from pathlib import Path

from generate_exact_macro_tree import (
    PARTIALS,
    VECTORS,
    WEIGHTS,
    ExactChecker,
    Piece,
    atomic_bytes,
    atomic_json,
    box_json,
    pack_topology,
    q,
    qs,
    read_pieces,
    relative_anchor,
    sha256,
    tangent_lower,
    model_min,
)


def read_refinements(path: Path) -> list[Piece]:
    raw = json.loads(path.read_text())
    pieces = []
    for item in raw["pieces"]:
        lo, hi = q(item["lo"]), q(item["hi"])
        m, v, endpoint = q(item["m"]), q(item["v"]), q(item["q"])
        center = endpoint + v / m if item["side"] == "left" else endpoint - v / m
        pieces.append(Piece(lo, hi, center, F(0), 2 * m * m, "refinement"))
    assert len(pieces) == 216
    assert all(piece.lo < piece.hi and piece.c > 0 for piece in pieces)
    return pieces


class RefinedChecker(ExactChecker):
    SELECTED_STABLE = (3, 9, 17, 23, 24, 27, 29, 35, 42)

    def __init__(self, stable: list[Piece], refinements: list[Piece], A: F, B: F) -> None:
        super().__init__(stable, A, B)
        self.refinements = refinements
        self.catalog = stable + refinements
        self.refinements_by_stable = {
            stable_index: [
                (56 + group * 24 + offset, refinements[group * 24 + offset])
                for offset in range(24)
            ]
            for group, stable_index in enumerate(self.SELECTED_STABLE)
        }

    def containing_best(self, lo: F, hi: F):
        if hi < lo:
            return None
        stable_selection = self.containing(lo, hi)
        if stable_selection is None:
            return None
        stable_index, stable_piece = stable_selection
        candidates = [(model_min(stable_piece, lo, hi), stable_index, stable_piece)]
        for index, piece in self.refinements_by_stable.get(stable_index, []):
            if piece.lo <= lo and hi <= piece.hi:
                candidates.append((model_min(piece, lo, hi), index, piece))
        _value, index, piece = max(candidates, key=lambda row: (row[0], -row[1]))
        return index, piece

    def quadratic_data(self, box):
        matrix = [[F(0) for _ in range(5)] for _ in range(5)]
        linear = [self.B for _ in range(5)]
        constant = F(0)
        term_codes = []
        for vector, (left_index, right_index) in zip(VECTORS, PARTIALS):
            lo = sum((box[k][0] for k in range(left_index, right_index + 1)), F(0))
            hi = sum((box[k][1] for k in range(left_index, right_index + 1)), F(0))
            clipped_hi = min(hi, self.cutoff)
            selected = self.containing_best(lo, clipped_hi)
            if selected is None:
                code, value = self.scalar_id(lo, clipped_hi)
                term_codes.append(code)
                constant += value
                continue
            piece_index, piece = selected
            assert piece_index < 32768
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


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--data", type=Path, required=True)
    parser.add_argument("--refinements", type=Path, required=True)
    parser.add_argument("--output-dir", type=Path, required=True)
    parser.add_argument("--a", required=True)
    parser.add_argument("--b", default="1094977/5000000000")
    parser.add_argument("--max-nodes", type=int, default=2_000_000)
    parser.add_argument("--max-depth", type=int, default=512)
    parser.add_argument("--progress", type=int, default=25000)
    args = parser.parse_args()

    A, B = q(args.a), q(args.b)
    stable = read_pieces(args.data)
    refinements = read_refinements(args.refinements)
    checker = RefinedChecker(stable, refinements, A, B)
    root = tuple((F(0), F(59)) for _ in range(5))
    stack = [(root, 0)]
    tokens = []
    kinds = bytearray()
    anchors = bytearray()
    terms = bytearray()
    visited = leaves = tail_leaves = quadratic_leaves = maximum_depth = 0
    smallest_quadratic_margin = None
    smallest_tail_margin = None
    tightest_quadratic = tightest_tail = None
    term_histogram = Counter()
    started = time.monotonic()

    while stack:
        box, depth = stack.pop()
        visited += 1
        maximum_depth = max(maximum_depth, depth)
        if visited > args.max_nodes:
            raise ArithmeticError(f"node limit exceeded with {len(stack)} pending")
        if depth > args.max_depth:
            raise ArithmeticError(f"depth limit exceeded at node {visited}")
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
            (hi - lo) * WEIGHTS[index] for index, (lo, hi) in enumerate(box)
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
    atomic_json(
        scalar_path,
        {
            "schema": 1,
            "data_sha256": sha256(args.data),
            "refinements_sha256": sha256(args.refinements),
            "A": qs(A),
            "B": qs(B),
            "cutoff": qs(checker.cutoff),
            "certificates": checker.scalar_certificates,
        },
    )
    manifest = {
        "schema": 2,
        "generator_sha256": sha256(Path(__file__)),
        "python": {"executable": sys.executable, "realpath": os.path.realpath(sys.executable)},
        "A": qs(A),
        "B": qs(B),
        "cutoff": qs(checker.cutoff),
        "data_sha256": sha256(args.data),
        "refinements_sha256": sha256(args.refinements),
        "stable_piece_count": len(stable),
        "refinement_piece_count": len(refinements),
        "catalog_piece_count": len(checker.catalog),
        "format": {
            "topology": "20 3-bit tokens per u64le word; unused high bits zero",
            "kinds": "u8: 0 tail, 1 quadratic",
            "anchors": "5 u16le codes per quadratic leaf; relative denominator 16384",
            "terms": "15 u16le codes: 0..271 catalog, 32768+n stable scalar cert, 65535 zero",
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
        "refinement_term_count": sum(count for code, count in term_histogram.items() if 56 <= code < 272),
        "scalar_term_count": sum(count for code, count in term_histogram.items() if 32768 <= code < 65535),
        "zero_term_count": term_histogram[65535],
        "stream_bytes": {key: len(data) for key, data in stream_data.items()},
        "stream_sha256": {key: hashlib.sha256(data).hexdigest() for key, data in stream_data.items()},
        "elapsed_seconds": time.monotonic() - started,
        "trust_note": "Float proposals only; every stored terminal comparison uses exact Fraction arithmetic. Refinement soundness is a separate Lean WellCert replay.",
    }
    atomic_json(args.output_dir / "manifest.json", manifest)
    print(json.dumps(manifest, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
