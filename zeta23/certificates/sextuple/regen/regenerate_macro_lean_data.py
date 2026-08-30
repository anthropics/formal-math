#!/usr/bin/env python3
"""Regenerate the macro Lean data files byte-for-byte from their JSON sources.

Targets (relative to the prototype directory, i.e. the grandparent of this file):

  MacroEnvelopeData.lean      <- macro-data-exact.json
  MacroScalarData.lean        <- macro-scalar-tree/scalar-certificates.json   (all 871 certs)
  MacroScalarDataPrefix.lean  <- macro-scalar-tree/scalar-certificates.json   (first 16 certs,
                                 no scalarCertTable / no #print axioms trailer)

Standard library only; deterministic; never touches the original .lean files.

    python regenerate_macro_lean_data.py --check
        regenerates into bench/regen/out/ and prints a JSON report
        (expected SHA-256, regenerated SHA-256, byte length, PASS/FAIL per file);
        exit status 0 iff every file PASSes.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from fractions import Fraction
from pathlib import Path

# --------------------------------------------------------------------------- #
# Expected digests of the committed originals.
# --------------------------------------------------------------------------- #

EXPECTED_SHA256 = {
    "MacroEnvelopeData.lean": "632d72144a0a62258b68e94a9da93b889a6b67c8f242e6fce1eaaa8ce26690b5",
    "MacroScalarData.lean": "532dc8f4a8abd2bebc99d0de968dea271bbcf74ee7d5e012829215e36e42e359",
    "MacroScalarDataPrefix.lean": "9c22df713526d13512c988fd64e9dbafa630f42615bf08eea3e91da7b1492604",
}

ENVELOPE_JSON = "macro-data-exact.json"
SCALAR_JSON = "macro-scalar-tree/scalar-certificates.json"
PREFIX_CERT_COUNT = 16

NAMESPACE = "Zeta23.ThmD.Sextuple.MacroPrototype"
LANGLE, RANGLE, CDOT = "⟨", "⟩", "·"

# --------------------------------------------------------------------------- #
# Rational formatting: integers bare, proper fractions as (num/den).
# --------------------------------------------------------------------------- #


def rat(s: str) -> str:
    q = Fraction(s)
    if q.denominator == 1:
        return str(q.numerator)
    return f"({q.numerator}/{q.denominator})"


def box(lo: str, hi: str) -> str:
    return f"{LANGLE}{rat(lo)}, {rat(hi)}{RANGLE}"


# --------------------------------------------------------------------------- #
# MacroEnvelopeData.lean
# --------------------------------------------------------------------------- #

# norm_num simp list for `low` / `zero` base pieces (no cells to unfold).
ENV_SIMP_BASE = "MacroPiece.check, LowerPiece.check]"

# norm_num simp list for `barrier` (Lean kind `.numeric [cells]`) pieces.
ENV_SIMP_NUMERIC = (
    "MacroPiece.check, LowerPiece.check, LowerPiece.coverFrom, LowerPiece.cellCheck,\n"
    "    LowerPiece.cellModelUpper, LowerPiece.absLower, kernelRange, kernelDenRange, rootTwoInterval, thetaTrig, thetaInterval,\n"
    "    trigRange, trigPoint, reducedMid, reducedRadius, quarterTurn, piInterval,\n"
    "    widen, sinPoint, cosPoint, sinPoly, cosPoly, trigError,\n"
    "    RatInterval.divPos, RatInterval.invPos, RatInterval.sq, RatInterval.mul,\n"
    "    RatInterval.scale, RatInterval.sub, RatInterval.neg, RatInterval.add, List.cons_ne_nil]"
)

# norm_num simp list for `well` pieces.
ENV_SIMP_WELL = (
    "MacroPiece.check, WellCert.check, WellCert.analyticPrereq, WellCert.midpoint, WellCert.radius,\n"
    "    WellCert.point, WellCert.derivativePositive, orientedLower, absUpper,\n"
    "    mtClosedDerivRange, mtClosedSecondRange, mtNumRange, mtNumDerivRange,\n"
    "    mtNumSecondRange, mtDenDerivRange, mtDenSecondRange, kernelRange, kernelDenRange, rootTwoInterval, thetaTrig, thetaInterval,\n"
    "    trigRange, trigPoint, reducedMid, reducedRadius, quarterTurn, piInterval,\n"
    "    widen, sinPoint, cosPoint, sinPoly, cosPoly, trigError,\n"
    "    RatInterval.divPos, RatInterval.invPos, RatInterval.sq, RatInterval.mul,\n"
    "    RatInterval.scale, RatInterval.sub, RatInterval.neg, RatInterval.add, List.cons_ne_nil]"
)


def envelope_piece_def(i: int, p: dict) -> str:
    kind = p["kind"]
    b = box(p["lo"], p["hi"])
    if kind in ("low", "zero"):
        return (
            f"def macroPiece{i} : MacroPiece := .base {{ box := {b}, q := 0, "
            f"a := {rat(p['a'])}, c := 0, kind := .{kind} }}\n"
        )
    if kind == "barrier":
        cells = ",\n".join(
            f"      {{ box := {box(c['lo'], c['hi'])}, turn := {c['turn']} }}"
            for c in p["cells"]
        )
        return (
            f"def macroPiece{i} : MacroPiece := .base {{ box := {b}, q := 0, "
            f"a := {rat(p['a'])}, c := 0, kind := .numeric [\n{cells}\n    ] }}\n"
        )
    if kind == "well":
        positive = "true" if p["positive"] else "false"
        return (
            f"def macroPiece{i} : MacroPiece := .well {{ box := {b}, side := .{p['side']}, "
            f"positive := {positive}, q := {rat(p['q'])}, v := {rat(p['v'])}, "
            f"m := {rat(p['m'])}, turn := {p['turn']} }}\n"
        )
    raise ValueError(f"unknown piece kind {kind!r} at index {i}")


def envelope_piece_check(i: int, p: dict) -> str:
    kind = p["kind"]
    simp = {"low": ENV_SIMP_BASE, "zero": ENV_SIMP_BASE,
            "barrier": ENV_SIMP_NUMERIC, "well": ENV_SIMP_WELL}[kind]
    return (
        f"lemma macroPiece{i}_check : macroPiece{i}.check = true := by\n"
        f"  norm_num [macroPiece{i}, {simp}\n"
    )


def render_envelope(data: dict) -> str:
    pieces = data["pieces"]
    n = len(pieces)
    lo = rat(pieces[0]["lo"])
    hi = rat(pieces[-1]["hi"])
    names = ", ".join(f"macroPiece{i}" for i in range(n))
    checks = ", ".join(f"macroPiece{i}_check" for i in range(n))

    out = []
    out.append("import MacroAnalytic\n\n")
    out.append(f"namespace {NAMESPACE}\n\n")
    out.append("open RatInterval\n\n")
    for i, p in enumerate(pieces):
        out.append(envelope_piece_def(i, p))
    out.append("\n")
    out.append(f"def macroPieces : List MacroPiece := [{names}]\n\n")
    for i, p in enumerate(pieces):
        out.append(envelope_piece_check(i, p))
    out.append("\n")
    out.append(
        f"lemma macroPieces_cover : macroCoverFrom {lo} {hi} macroPieces = true := by\n"
        f"  norm_num [macroPieces, macroCoverFrom, MacroPiece.box, {names}]\n\n"
    )
    out.append(
        "lemma macroPieces_all : macroPieces.all MacroPiece.check = true := by\n"
        f"  simp [macroPieces, {checks}]\n\n"
    )
    out.append(
        "set_option maxHeartbeats 0 in\n"
        "set_option maxRecDepth 1000000 in\n"
        f"theorem macroPieces_check : checkMacroPieces {lo} {hi} macroPieces = true := by\n"
        "  unfold checkMacroPieces\n"
        "  rw [macroPieces_cover, macroPieces_all]\n"
        "  have hne : macroPieces ≠ [] := by\n"
        "    unfold macroPieces\n"
        "    exact List.cons_ne_nil _ _\n"
        "  have hdec : decide (macroPieces ≠ []) = true := decide_eq_true hne\n"
        "  simp [hdec]\n\n"
    )
    out.append(
        f"theorem macroEnvelope_sound {{x : ℝ}} (hx0 : {lo} ≤ x) (hx{hi} : x ≤ {hi}) :\n"
        "    ∃ p ∈ macroPieces, Holds p.box x ∧ p.model x ≤ 2 * mtKernel x ^ 2 := by\n"
        "  apply checkMacroPieces_sound macroPieces_check\n"
        f"  {CDOT} simpa using hx0\n"
        f"  {CDOT} norm_num\n"
        f"    exact hx{hi}\n\n"
    )
    out.append("#print axioms macroEnvelope_sound\n\n")
    # The original spot-checks the first piece and piece 3 (a well piece).
    out.append("#print axioms macroPiece0_check\n")
    out.append("#print axioms macroPiece3_check\n")
    out.append("#print axioms macroPieces_check\n\n")
    out.append(f"end {NAMESPACE}\n")
    return "".join(out)


# --------------------------------------------------------------------------- #
# MacroScalarData.lean / MacroScalarDataPrefix.lean
# --------------------------------------------------------------------------- #

SCALAR_SIMP_HEAD = (
    "MacroScalarCert.check, MacroScalarSegment.check,\n"
    "    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,\n"
    "    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,\n"
    "    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable"
)


def cert_piece_names(cert: dict) -> list[str]:
    """macroPiece names referenced by a certificate: the segments' piece_index
    values in segment order, keeping only the first occurrence of each."""
    seen: list[int] = []
    for seg in cert["segments"]:
        k = seg["piece_index"]
        if k not in seen:
            seen.append(k)
    return [f"macroPiece{k}" for k in seen]


def scalar_cert_def(i: int, c: dict, n_pieces: int) -> str:
    segs = ",\n".join(
        f"    {{ box := {box(s['lo'], s['hi'])}, pieceIndex := {s['piece_index']} }}"
        for s in c["segments"]
    )
    return (
        f"def scalarCert{i} : MacroScalarCert {n_pieces} := {{\n"
        f"  box := {box(c['lo'], c['hi'])}\n"
        f"  a := {rat(c['a'])}\n"
        f"  segments := [\n{segs}\n  ]\n}}\n"
    )


def scalar_cert_check(i: int, c: dict) -> str:
    names = ", ".join(cert_piece_names(c))
    return (
        f"lemma scalarCert{i}_check : scalarCert{i}.check stableMacroTable = true := by\n"
        f"  norm_num [scalarCert{i}, {SCALAR_SIMP_HEAD}, {names}]\n"
    )


def match_table(name: str, ty: str, count: int, elem: str) -> str:
    lines = [f"def {name} (i : Fin {count}) : {ty} :=\n", "  match i.val with\n"]
    for k in range(count - 1):
        lines.append(f"  | {k} => {elem}{k}\n")
    lines.append(f"  | _ => {elem}{count - 1}\n")
    return "".join(lines)


def render_scalar(certs: list[dict], n_pieces: int, *, with_table: bool) -> str:
    n = len(certs)
    out = []
    out.append("import MacroEnvelopeData\nimport MacroScalarAdapter\n\n")
    out.append(f"namespace {NAMESPACE}\n\n")
    out.append("open Zeta23.ThmD.Sextuple\nopen RatInterval\n\n")
    out.append(f"/-- The immutable stable {n_pieces}-piece envelope as a bounded table. -/\n")
    out.append(match_table("stableMacroTable", "MacroPiece", n_pieces, "macroPiece"))
    out.append("\n")
    out.append(
        "set_option maxHeartbeats 0 in\n"
        f"theorem stableMacroTable_check (i : Fin {n_pieces}) : (stableMacroTable i).check = true := by\n"
        "  fin_cases i\n"
    )
    for k in range(n_pieces):
        out.append(f"  {CDOT} exact macroPiece{k}_check\n")
    out.append("\n")
    for i, c in enumerate(certs):
        out.append(scalar_cert_def(i, c, n_pieces))
        out.append("\n")
    for i, c in enumerate(certs):
        out.append(scalar_cert_check(i, c))
    if with_table:
        out.append("\n")
        out.append("/-- Deduplicated positive seam bounds, addressed by the serialized UInt16 term stream. -/\n")
        out.append(match_table("scalarCertTable", f"MacroScalarCert {n_pieces}", n, "scalarCert"))
        out.append("\n")
        out.append(
            "set_option maxHeartbeats 0 in\n"
            "set_option maxRecDepth 100000 in\n"
            f"theorem scalarCertTable_check (i : Fin {n}) :\n"
            "    (scalarCertTable i).check stableMacroTable = true := by\n"
            "  fin_cases i\n"
        )
        for i in range(n):
            out.append(f"  {CDOT} exact scalarCert{i}_check\n")
        out.append("\n")
        out.append("#print axioms stableMacroTable_check\n")
        out.append("#print axioms scalarCertTable_check\n")
    out.append("\n")
    out.append(f"end {NAMESPACE}\n")
    return "".join(out)


# --------------------------------------------------------------------------- #
# Driver
# --------------------------------------------------------------------------- #


def sha256_bytes(b: bytes) -> str:
    return hashlib.sha256(b).hexdigest()


def generate_all(root: Path) -> dict[str, bytes]:
    env = json.loads((root / ENVELOPE_JSON).read_text(encoding="utf-8"))
    certs = json.loads((root / SCALAR_JSON).read_text(encoding="utf-8"))["certificates"]
    n_pieces = len(env["pieces"])
    return {
        "MacroEnvelopeData.lean": render_envelope(env).encode("utf-8"),
        "MacroScalarData.lean": render_scalar(certs, n_pieces, with_table=True).encode("utf-8"),
        "MacroScalarDataPrefix.lean": render_scalar(
            certs[:PREFIX_CERT_COUNT], n_pieces, with_table=False
        ).encode("utf-8"),
    }


def main(argv: list[str] | None = None) -> int:
    here = Path(__file__).resolve().parent
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--root", type=Path, default=here.parent.parent,
                    help="prototype directory holding the JSON sources and original .lean files")
    ap.add_argument("--out", type=Path, default=here / "out",
                    help="output directory for regenerated files (default: bench/regen/out)")
    ap.add_argument("--check", action="store_true",
                    help="regenerate into --out, print a JSON report, exit 0 iff all SHA-256 match")
    args = ap.parse_args(argv)

    root: Path = args.root.resolve()
    out_dir: Path = args.out.resolve()
    for name in EXPECTED_SHA256:
        if out_dir / name == (root / name).resolve():
            print(f"refusing to overwrite original {root / name}", file=sys.stderr)
            return 2
    out_dir.mkdir(parents=True, exist_ok=True)

    generated = generate_all(root)
    report = {}
    all_ok = True
    for name, blob in generated.items():
        (out_dir / name).write_bytes(blob)
        got = sha256_bytes(blob)
        exp = EXPECTED_SHA256[name]
        ok = got == exp
        entry = {
            "expected_sha256": exp,
            "regenerated_sha256": got,
            "bytes": len(blob),
            "status": "PASS" if ok else "FAIL",
            "output": str(out_dir / name),
        }
        orig = root / name
        if orig.is_file():
            entry["original_sha256"] = sha256_bytes(orig.read_bytes())
        report[name] = entry
        all_ok &= ok

    print(json.dumps({"root": str(root), "all_pass": all_ok, "files": report}, indent=2))
    if args.check:
        return 0 if all_ok else 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
