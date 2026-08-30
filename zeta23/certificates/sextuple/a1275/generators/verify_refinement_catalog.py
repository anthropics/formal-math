#!/usr/bin/env python3
"""Independent exact structural replay of the narrow-well refinement catalog."""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from dataclasses import dataclass
from fractions import Fraction as F
from pathlib import Path


@dataclass(frozen=True)
class Piece:
    lo: F
    hi: F
    q: F
    a: F
    c: F
    code: int


def q(text: str) -> F:
    return F(text)


def qs(value: F) -> str:
    if value.denominator == 1:
        return str(value.numerator)
    return f"{value.numerator}/{value.denominator}"


def load_stable(path: Path) -> list[Piece]:
    raw = json.loads(path.read_text())
    out = []
    for index, item in enumerate(raw["pieces"]):
        lo, hi, kind = q(item["lo"]), q(item["hi"]), item["kind"]
        if kind == "low":
            out.append(Piece(lo, hi, F(0), F(1, 4), F(0), index))
        elif kind == "zero":
            out.append(Piece(lo, hi, F(0), F(0), F(0), index))
        elif kind == "barrier":
            out.append(Piece(lo, hi, F(0), q(item["a"]), F(0), index))
        else:
            m, v, endpoint = q(item["m"]), q(item["v"]), q(item["q"])
            center = endpoint + v / m if item["side"] == "left" else endpoint - v / m
            out.append(Piece(lo, hi, center, F(0), 2 * m * m, index))
    assert len(out) == 56
    return out


def load_refinements(path: Path, stable_raw: dict) -> list[Piece]:
    raw = json.loads(path.read_text())
    pieces = raw["pieces"]
    selected = raw["selected_stable_piece_indices"]
    subdivisions = raw["subdivisions_per_piece"]
    assert len(pieces) == len(selected) * subdivisions == 216
    out = []
    for index, item in enumerate(pieces):
        stable_index = selected[index // subdivisions]
        assert item["stable_piece_index"] == stable_index
        assert item["subdivision"] == index % subdivisions
        source = stable_raw["pieces"][stable_index]
        source_lo, source_hi = q(source["lo"]), q(source["hi"])
        expected_lo = source_lo + (source_hi - source_lo) * F(index % subdivisions, subdivisions)
        expected_hi = source_lo + (source_hi - source_lo) * F(index % subdivisions + 1, subdivisions)
        lo, hi = q(item["lo"]), q(item["hi"])
        assert lo == expected_lo and hi == expected_hi and hi - lo == F(1, 64)
        assert item["side"] == source["side"] and item["positive"] == source["positive"]
        endpoint = hi if item["side"] == "left" else lo
        assert q(item["q"]) == endpoint and item["turn"] == source["turn"]
        m, v = q(item["m"]), q(item["v"])
        assert m > 0 and v >= 0
        center = endpoint + v / m if item["side"] == "left" else endpoint - v / m
        out.append(Piece(lo, hi, center, F(0), 2 * m * m, 56 + index))
    for group in range(len(selected)):
        group_pieces = pieces[group * subdivisions : (group + 1) * subdivisions]
        source = stable_raw["pieces"][selected[group]]
        assert q(group_pieces[0]["lo"]) == q(source["lo"])
        assert q(group_pieces[-1]["hi"]) == q(source["hi"])
        assert all(q(left["hi"]) == q(right["lo"]) for left, right in zip(group_pieces, group_pieces[1:]))
    return out


def model(piece: Piece, distance: F) -> F:
    assert piece.lo <= distance <= piece.hi
    return piece.a + piece.c * (distance - piece.q) ** 2


def strongest_value(catalog: list[Piece], gaps: list[F], B: F):
    positions = [F(0)]
    for gap in gaps:
        positions.append(positions[-1] + gap)
    value = B * sum(gaps, F(0))
    terms = []
    for right in range(1, 6):
        for left in range(right):
            distance = positions[right] - positions[left]
            options = [(model(piece, distance), piece.code) for piece in catalog if piece.lo <= distance <= piece.hi]
            assert options
            term_value, code = max(options)
            value += term_value
            terms.append({"left": left, "right": right, "distance": qs(distance), "code": code, "value": qs(term_value)})
    return value, terms


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--data", type=Path, required=True)
    parser.add_argument("--refinements", type=Path, required=True)
    parser.add_argument("--obstruction-report", type=Path, required=True)
    parser.add_argument("--report", type=Path, required=True)
    args = parser.parse_args()

    stable_raw = json.loads(args.data.read_text())
    stable = load_stable(args.data)
    refinements = load_refinements(args.refinements, stable_raw)
    catalog = stable + refinements
    B = F(1094977, 5000000000)
    obstruction_raw = json.loads(args.obstruction_report.read_text())
    obstruction_gaps = [q(value) for value in obstruction_raw["obstruction"]["point"]]
    diagnostic_gaps = [
        F(131848903, 20000000),
        F(1247825733, 100000000),
        F(656134691, 100000000),
        F(1247825733, 100000000),
        F(164811129, 25000000),
    ]
    obstruction_value, obstruction_terms = strongest_value(catalog, obstruction_gaps, B)
    diagnostic_value, diagnostic_terms = strongest_value(catalog, diagnostic_gaps, B)
    report = {
        "status": "PASS",
        "verifier_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "stable_data_sha256": hashlib.sha256(args.data.read_bytes()).hexdigest(),
        "refinements_sha256": hashlib.sha256(args.refinements.read_bytes()).hexdigest(),
        "stable_piece_count": len(stable),
        "refinement_piece_count": len(refinements),
        "catalog_piece_count": len(catalog),
        "exact_partition_groups": 9,
        "subdivisions_per_group": 24,
        "subcell_width": "1/64",
        "old_obstruction_point": {
            "gaps": [qs(value) for value in obstruction_gaps],
            "refined_value": qs(obstruction_value),
            "margin_over_0p01275": qs(obstruction_value - F(51, 4000)),
            "terms": obstruction_terms,
        },
        "true_objective_diagnostic_point": {
            "gaps": [qs(value) for value in diagnostic_gaps],
            "refined_value": qs(diagnostic_value),
            "margin_over_0p0129": qs(diagnostic_value - F(129, 10000)),
            "terms": diagnostic_terms,
        },
        "scope_note": "This exact replay checks catalog structure and rational model values. Lean WellCert.check supplies analytic soundness.",
    }
    temporary = args.report.with_suffix(args.report.suffix + ".new")
    temporary.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    os.replace(temporary, args.report)
    print(json.dumps(report, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
