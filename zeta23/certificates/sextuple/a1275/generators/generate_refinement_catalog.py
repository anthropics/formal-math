#!/usr/bin/env python3
"""Generate a separately checked narrow-well refinement catalog.

mpmath proposes conservative v/m coefficients. Lean's exact WellCert.check is
the authority for every emitted rational entry.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from fractions import Fraction as F
from pathlib import Path

import mpmath as mp

SELECTED_STABLE_PIECES = (3, 9, 17, 23, 24, 27, 29, 35, 42)
SUBDIVISIONS = 24
QUANTIZATION = 10**15
SAFETY_NUMERATOR = 995
SAFETY_DENOMINATOR = 1000


def q(text: str) -> F:
    return F(text)


def qs(value: F) -> str:
    if value.denominator == 1:
        return str(value.numerator)
    return f"{value.numerator}/{value.denominator}"


def lean_q(value: F) -> str:
    if value.denominator == 1:
        return str(value.numerator)
    return f"({value.numerator}/{value.denominator})"


def mpf(value: F):
    return mp.mpf(value.numerator) / value.denominator


def mt_kernel(x):
    root_two = mp.sqrt(2)
    theta = root_two / 2
    return (
        root_two * x * mp.cos(theta) * mp.sin(x / 2)
        - 2 * mp.sin(theta) * mp.cos(x / 2)
    ) / ((x * x - 2) * mp.sin(theta))


def floor_quantized(value) -> F:
    numerator = int(mp.floor(value * QUANTIZATION))
    return F(numerator, QUANTIZATION)


def atomic_text(path: Path, text: str) -> None:
    temporary = path.with_suffix(path.suffix + ".new")
    temporary.write_text(text)
    os.replace(temporary, path)


def propose_piece(stable_index: int, source: dict, subdivision: int) -> dict:
    lo0, hi0 = q(source["lo"]), q(source["hi"])
    assert source["kind"] == "well" and hi0 - lo0 == F(3, 8)
    lo = lo0 + (hi0 - lo0) * F(subdivision, SUBDIVISIONS)
    hi = lo0 + (hi0 - lo0) * F(subdivision + 1, SUBDIVISIONS)
    side = source["side"]
    endpoint = hi if side == "left" else lo
    endpoint_value = abs(mt_kernel(mpf(endpoint)))
    derivative = lambda x: mp.diff(mt_kernel, x)
    sample_values = [
        abs(derivative(mpf(lo) + (mpf(hi) - mpf(lo)) * sample / 32))
        for sample in range(33)
    ]
    safety = mp.mpf(SAFETY_NUMERATOR) / SAFETY_DENOMINATOR
    v = floor_quantized(endpoint_value * safety)
    m = floor_quantized(min(sample_values) * safety)
    assert v >= 0 and m > 0
    return {
        "stable_piece_index": stable_index,
        "subdivision": subdivision,
        "lo": qs(lo),
        "hi": qs(hi),
        "side": side,
        "positive": source["positive"],
        "q": qs(endpoint),
        "v": qs(v),
        "m": qs(m),
        "turn": source["turn"],
    }


SIMP = """MacroPiece.check, WellCert.check, WellCert.analyticPrereq, WellCert.midpoint, WellCert.radius,
    WellCert.point, WellCert.derivativePositive, orientedLower, absUpper,
    mtClosedDerivRange, mtClosedSecondRange, mtNumRange, mtNumDerivRange,
    mtNumSecondRange, mtDenDerivRange, mtDenSecondRange, kernelRange, kernelDenRange, rootTwoInterval, thetaTrig, thetaInterval,
    trigRange, trigPoint, reducedMid, reducedRadius, quarterTurn, piInterval,
    widen, sinPoint, cosPoint, sinPoly, cosPoly, trigError,
    RatInterval.divPos, RatInterval.invPos, RatInterval.sq, RatInterval.mul,
    RatInterval.scale, RatInterval.sub, RatInterval.neg, RatInterval.add, List.cons_ne_nil"""


def render_lean(pieces: list[dict]) -> str:
    lines = [
        "import MacroEnvelopeData",
        "",
        "namespace Zeta23.ThmD.Sextuple.MacroPrototype",
        "",
        "open RatInterval",
        "",
        "/-! Generated narrow-well additions. The stable 56-piece table is unchanged. -/",
        "",
    ]
    for index, piece in enumerate(pieces):
        positive = "true" if piece["positive"] else "false"
        lines.append(
            f"def refinementPiece{index} : MacroPiece := .well {{ box := "
            f"⟨{lean_q(q(piece['lo']))}, {lean_q(q(piece['hi']))}⟩, "
            f"side := .{piece['side']}, positive := {positive}, q := {lean_q(q(piece['q']))}, "
            f"v := {lean_q(q(piece['v']))}, m := {lean_q(q(piece['m']))}, turn := {piece['turn']} }}"
        )
    lines.append("")
    names = ", ".join(f"refinementPiece{index}" for index in range(len(pieces)))
    lines.append(f"def refinementCatalog : List MacroPiece := [{names}]")
    lines.append("")
    for index in range(len(pieces)):
        lines.extend(
            [
                f"lemma refinementPiece{index}_check : refinementPiece{index}.check = true := by",
                f"  norm_num [refinementPiece{index}, {SIMP}]",
            ]
        )
    lines.append("")
    checks = ", ".join(f"refinementPiece{index}_check" for index in range(len(pieces)))
    lines.extend(
        [
            "set_option maxRecDepth 100000 in",
            "lemma refinementCatalog_all : refinementCatalog.all MacroPiece.check = true := by",
            f"  simp [refinementCatalog, {checks}]",
            "",
            "#print axioms refinementCatalog_all",
            "",
            "end Zeta23.ThmD.Sextuple.MacroPrototype",
            "",
        ]
    )
    return "\n".join(lines)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--data", type=Path, required=True)
    parser.add_argument("--output-json", type=Path, required=True)
    parser.add_argument("--output-lean", type=Path, required=True)
    args = parser.parse_args()

    mp.mp.dps = 100
    raw = json.loads(args.data.read_text())
    source_pieces = raw["pieces"]
    pieces = [
        propose_piece(stable_index, source_pieces[stable_index], subdivision)
        for stable_index in SELECTED_STABLE_PIECES
        for subdivision in range(SUBDIVISIONS)
    ]
    assert len(pieces) == len(SELECTED_STABLE_PIECES) * SUBDIVISIONS
    payload = {
        "schema": 1,
        "generator_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "source_data_sha256": hashlib.sha256(args.data.read_bytes()).hexdigest(),
        "selected_stable_piece_indices": list(SELECTED_STABLE_PIECES),
        "subdivisions_per_piece": SUBDIVISIONS,
        "subcell_width": "1/64",
        "quantization_denominator": QUANTIZATION,
        "proposal_safety": f"{SAFETY_NUMERATOR}/{SAFETY_DENOMINATOR}",
        "authority_note": "mpmath only proposes coefficients; each emitted WellCert.check must be replayed by Lean.",
        "pieces": pieces,
    }
    atomic_text(args.output_json, json.dumps(payload, indent=2, sort_keys=True) + "\n")
    atomic_text(args.output_lean, render_lean(pieces))
    print(json.dumps({
        "piece_count": len(pieces),
        "json_sha256": hashlib.sha256(args.output_json.read_bytes()).hexdigest(),
        "lean_sha256": hashlib.sha256(args.output_lean.read_bytes()).hexdigest(),
        "generator_sha256": payload["generator_sha256"],
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
