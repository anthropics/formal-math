#!/usr/bin/env python3
"""Independently replay the compact 5D branch-and-bound with exact leaf checks.

The existing rational LowerPiece table supplies one-dimensional models. Float
coordinate descent only proposes a rational tangent point. Every accepted
leaf is authorized by a final `fractions.Fraction` comparison. No float result
can close a leaf.
"""
from __future__ import annotations

import argparse
import bisect
import hashlib
import json
import math
import os
import re
import time
from dataclasses import dataclass
from fractions import Fraction as F
from pathlib import Path

A = F(1, 80)
B = F(1_094_977, 5_000_000_000)
CUTOFF = A / B
WEIGHTS = (5, 8, 9, 8, 5)
PARTIALS = tuple((i, j) for i in range(5) for j in range(i, 5))
VECTORS = tuple(tuple(F(1) if i <= k <= j else F(0) for k in range(5)) for i, j in PARTIALS)
HEADER = re.compile(r"^    ⟨⟨(.+?), (.+?)⟩, (.+?), (.+?), (.+?),\s*$")
CELL = re.compile(r"^        ⟨⟨.*⟩, \d+⟩")

@dataclass(frozen=True)
class Piece:
    lo: F
    hi: F
    q: F
    a: F
    c: F
    kind: str


def q(text: str) -> F:
    text = text.strip()
    while text.startswith("(") and text.endswith(")"):
        text = text[1:-1].strip()
    if "/" in text:
        numerator, denominator = text.split("/")
        return F(int(numerator), int(denominator))
    return F(int(text))


def read_pieces(path: Path) -> tuple[list[Piece], int]:
    lines = path.read_text().splitlines()
    pieces: list[Piece] = []
    cells = sum(bool(CELL.match(line)) for line in lines)
    for index, line in enumerate(lines):
        match = HEADER.match(line)
        if match is None:
            continue
        lo, hi, center, intercept, curvature = map(q, match.groups())
        kind_line = lines[index + 1].strip()
        if kind_line.startswith(".low"):
            kind = "low"
        elif kind_line.startswith(".zero"):
            kind = "zero"
        elif kind_line.startswith(".numeric"):
            kind = "numeric"
        else:
            raise ValueError((index + 2, kind_line))
        pieces.append(Piece(lo, hi, center, intercept, curvature, kind))
    if not pieces:
        raise ValueError("no LowerPiece headers found")
    if pieces[0].lo != 0 or pieces[-1].hi != 59:
        raise ValueError("piece endpoints do not cover exactly [0,59]")
    for left, right in zip(pieces, pieces[1:]):
        if left.hi != right.lo:
            raise ValueError(f"piece seam mismatch: {left.hi} != {right.lo}")
    if pieces[0] != Piece(F(0), F(2), F(0), F(1, 4), F(0), "low"):
        raise ValueError("the [0,2] low piece is not exact")
    zero_pieces = [piece for piece in pieces if piece.kind == "zero"]
    if len(zero_pieces) != 9 or any(piece.a != 0 or piece.c != 0 for piece in zero_pieces):
        raise ValueError("expected nine exact zero wells")
    return pieces, cells


def model_min(piece: Piece, lo: F, hi: F) -> F:
    point = piece.q if lo <= piece.q <= hi else (lo if piece.q < lo else hi)
    return piece.a + piece.c * (point - piece.q) ** 2


class Checker:
    def __init__(self, pieces: list[Piece], witness_denominator: int) -> None:
        self.pieces = pieces
        self.highs = [piece.hi for piece in pieces]
        self.witness_denominator = witness_denominator
        self.scalar_cache: dict[tuple[F, F], F] = {}

    def containing(self, lo: F, hi: F) -> Piece | None:
        # Closed seams can belong to either neighbor. Prefer the left piece.
        index = bisect.bisect_left(self.highs, lo)
        for candidate in (index, index + 1):
            if 0 <= candidate < len(self.pieces):
                piece = self.pieces[candidate]
                if piece.lo <= lo and hi <= piece.hi:
                    return piece
        return None

    def scalar_min(self, lo: F, hi: F) -> F:
        # In the energy branch span < A/B, so every distance is below CUTOFF.
        hi = min(hi, CUTOFF)
        if hi < lo:
            # The box portion is entirely in the affine-tail branch.
            return F(0)
        key = (lo, hi)
        cached = self.scalar_cache.get(key)
        if cached is not None:
            return cached
        first = bisect.bisect_left(self.highs, lo)
        values: list[F] = []
        index = max(0, first)
        while index < len(self.pieces) and self.pieces[index].lo <= hi:
            piece = self.pieces[index]
            left = max(lo, piece.lo)
            right = min(hi, piece.hi)
            if left <= right:
                values.append(model_min(piece, left, right))
            index += 1
        if not values:
            result = F(0)
        else:
            result = min(values)
        self.scalar_cache[key] = result
        return result

    def quadratic_data(self, box: tuple[tuple[F, F], ...]):
        matrix = [[F(0) for _ in range(5)] for _ in range(5)]
        linear = [B for _ in range(5)]
        constant = F(0)
        assigned = 0
        for vector, (left_index, right_index) in zip(VECTORS, PARTIALS):
            lo = sum((box[k][0] for k in range(left_index, right_index + 1)), F(0))
            hi = sum((box[k][1] for k in range(left_index, right_index + 1)), F(0))
            clipped_hi = min(hi, CUTOFF)
            piece = self.containing(lo, clipped_hi) if lo <= clipped_hi else None
            if piece is None:
                constant += self.scalar_min(lo, hi)
                continue
            assigned += 1
            constant += piece.a + piece.c * piece.q * piece.q
            if piece.c:
                for row in range(5):
                    if not vector[row]:
                        continue
                    linear[row] -= 2 * piece.c * piece.q
                    for column in range(5):
                        if vector[column]:
                            matrix[row][column] += piece.c
        return matrix, linear, constant, assigned

    @staticmethod
    def float_coordinate_descent(matrix, linear, box, sweeps: int) -> list[float]:
        mf = [[float(value) for value in row] for row in matrix]
        lf = [float(value) for value in linear]
        lo = [float(bounds[0]) for bounds in box]
        hi = [float(bounds[1]) for bounds in box]
        point = [(left + right) / 2 for left, right in zip(lo, hi)]
        for _ in range(sweeps):
            for row in range(5):
                diagonal = mf[row][row]
                if diagonal > 0:
                    off_diagonal = sum(mf[row][column] * point[column] for column in range(5) if column != row)
                    value = -(lf[row] + 2 * off_diagonal) / (2 * diagonal)
                    point[row] = min(max(value, lo[row]), hi[row])
                else:
                    point[row] = lo[row] if lf[row] >= 0 else hi[row]
        return point

    def rationalize(self, point: list[float], box: tuple[tuple[F, F], ...]) -> list[F]:
        denominator = self.witness_denominator
        result: list[F] = []
        for value, (lo, hi) in zip(point, box):
            candidate = F(round(value * denominator), denominator)
            result.append(min(max(candidate, lo), hi))
        return result

    @staticmethod
    def polynomial(matrix, linear, constant, point: list[F]) -> F:
        return constant + sum(linear[i] * point[i] for i in range(5)) + sum(
            matrix[i][j] * point[i] * point[j] for i in range(5) for j in range(5)
        )

    def lower(self, box: tuple[tuple[F, F], ...], sweeps: int):
        matrix, linear, constant, assigned = self.quadratic_data(box)
        proposal = self.float_coordinate_descent(matrix, linear, box, sweeps)
        point = self.rationalize(proposal, box)
        value = self.polynomial(matrix, linear, constant, point)
        gradient = [linear[i] + 2 * sum(matrix[i][j] * point[j] for j in range(5)) for i in range(5)]
        tangent = value
        for i, (lo, hi) in enumerate(box):
            tangent += min(gradient[i] * (lo - point[i]), gradient[i] * (hi - point[i]))
        return tangent, point, assigned


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--data", type=Path, required=True)
    parser.add_argument("--report", type=Path, required=True)
    parser.add_argument("--sweeps", type=int, default=12)
    parser.add_argument("--witness-denominator", type=int, default=1 << 34)
    parser.add_argument("--max-nodes", type=int, default=1_000_000)
    parser.add_argument("--progress", type=int, default=25_000)
    args = parser.parse_args()
    pieces, cells = read_pieces(args.data)
    checker = Checker(pieces, args.witness_denominator)
    root = tuple((F(0), F(59)) for _ in range(5))
    stack: list[tuple[tuple[tuple[F, F], ...], int]] = [(root, 0)]
    visited = leaves = tail_leaves = quadratic_leaves = 0
    maximum_depth = 0
    smallest_margin: F | None = None
    started = time.monotonic()
    while stack:
        box, depth = stack.pop()
        visited += 1
        maximum_depth = max(maximum_depth, depth)
        if visited > args.max_nodes:
            raise ArithmeticError(f"node limit exceeded with {len(stack)} pending")
        span_lower = sum((bounds[0] for bounds in box), F(0))
        if B * span_lower >= A:
            leaves += 1
            tail_leaves += 1
            continue
        lower, _point, _assigned = checker.lower(box, args.sweeps)
        if lower >= A:
            leaves += 1
            quadratic_leaves += 1
            margin = lower - A
            smallest_margin = margin if smallest_margin is None else min(smallest_margin, margin)
            continue
        weighted_widths = [(hi - lo) * WEIGHTS[index] for index, (lo, hi) in enumerate(box)]
        split_index = max(range(5), key=weighted_widths.__getitem__)
        lo, hi = box[split_index]
        midpoint = (lo + hi) / 2
        first = list(box)
        second = list(box)
        first[split_index] = (lo, midpoint)
        second[split_index] = (midpoint, hi)
        stack.append((tuple(second), depth + 1))
        stack.append((tuple(first), depth + 1))
        if args.progress and visited % args.progress == 0:
            print(f"progress visited={visited} stack={len(stack)} depth={maximum_depth} seconds={time.monotonic()-started:.1f}", flush=True)
    elapsed = time.monotonic() - started
    report = {
        "data": str(args.data),
        "data_sha256": hashlib.sha256(args.data.read_bytes()).hexdigest(),
        "piece_count": len(pieces),
        "numeric_cell_count": cells,
        "A": f"{A.numerator}/{A.denominator}",
        "B": f"{B.numerator}/{B.denominator}",
        "cutoff": f"{CUTOFF.numerator}/{CUTOFF.denominator}",
        "visited_nodes": visited,
        "certified_leaves": leaves,
        "tail_leaves": tail_leaves,
        "quadratic_leaves": quadratic_leaves,
        "maximum_depth": maximum_depth,
        "empty_stack": not stack,
        "smallest_quadratic_margin": None if smallest_margin is None else f"{smallest_margin.numerator}/{smallest_margin.denominator}",
        "smallest_quadratic_margin_float": None if smallest_margin is None else float(smallest_margin),
        "scalar_cache_entries": len(checker.scalar_cache),
        "sweeps": args.sweeps,
        "witness_denominator": args.witness_denominator,
        "elapsed_seconds": elapsed,
        "trust_note": "Float coordinate descent proposes witnesses only; every leaf comparison is exact Fraction arithmetic.",
    }
    args.report.parent.mkdir(parents=True, exist_ok=True)
    temporary = args.report.with_suffix(args.report.suffix + ".new")
    temporary.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    os.replace(temporary, args.report)
    print(json.dumps(report, indent=2, sort_keys=True))

if __name__ == "__main__":
    main()
