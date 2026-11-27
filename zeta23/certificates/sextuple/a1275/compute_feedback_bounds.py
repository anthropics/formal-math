#!/usr/bin/env python3
"""Compute exact rational feedback lower bounds and high-precision diagnostics."""
from __future__ import annotations

import hashlib
import json
import os
from fractions import Fraction as F
from pathlib import Path

import mpmath as mp

BMT_LOWER = F(672500703679, 10**12)
PI_UPPER = F(314159265358979323847, 10**20)
A_BASE = F(1, 80)
B_BASE = F(1094977, 5000000000)

CANDIDATES = [
    ("baseline", A_BASE, B_BASE, F(672755620655, 10**12)),
    ("slack_plus_5e-9", F(2500001, 200000000), B_BASE, F(672755621, 10**9)),
    ("refined_0p0126", F(63, 5000), B_BASE, F(6727668568, 10**10)),
    (
        "scaled_both_strict_999_over_1000",
        F(999, 1000) * F(63, 5000),
        F(999, 1000) * B_BASE,
        F(6727665901, 10**10),
    ),
    ("frontier_probe_0p0127", F(127, 10000), B_BASE, F(6727780933, 10**10)),
    ("refined_0p01275", F(51, 4000), B_BASE, F(6727837118, 10**10)),
    ("refined_0p0129", F(129, 10000), B_BASE, F(6728005676, 10**10)),
]


def qs(value: F) -> str:
    if value.denominator == 1:
        return str(value.numerator)
    return f"{value.numerator}/{value.denominator}"


def rational_lower(A: F, B: F) -> F:
    return (6 * BMT_LOWER - 10 * PI_UPPER * B) / (6 - A)


def mpf(value: F):
    return mp.mpf(value.numerator) / value.denominator


def actual_feedback(A: F, B: F):
    theta = mp.mpf(1) / mp.sqrt(2)
    cstar = mp.sqrt(2) * mp.sin(theta) / (mp.cos(theta) + theta * mp.sin(theta))
    bmt = 2 - 1 / cstar
    return (6 * bmt - 10 * mp.pi * mpf(B)) / (6 - mpf(A))


def main() -> None:
    mp.mp.dps = 100
    numerator_lower = 6 * BMT_LOWER - 10 * PI_UPPER * B_BASE
    assert numerator_lower > 0
    baseline_lower = rational_lower(A_BASE, B_BASE)
    rows = []
    for name, A, B, comparator in CANDIDATES:
        lower = rational_lower(A, B)
        comparator_margin = lower - comparator
        delta_A, delta_B = A - A_BASE, B - B_BASE
        if delta_A >= 0 and delta_B <= 0:
            improvement_lower = (
                numerator_lower * delta_A - 10 * F(3) * (6 - A_BASE) * delta_B
            ) / ((6 - A_BASE) * (6 - A))
        else:
            raise ValueError("the scripted strict-gain bound expects delta_A >= 0 and delta_B <= 0")
        rows.append(
            {
                "name": name,
                "A": qs(A),
                "B": qs(B),
                "delta_A_from_baseline": qs(delta_A),
                "delta_B_from_baseline": qs(delta_B),
                "certified_rational_lower": qs(lower),
                "certified_rational_lower_decimal": mp.nstr(mpf(lower), 70),
                "public_comparator": qs(comparator),
                "public_comparator_margin": qs(comparator_margin),
                "public_comparator_margin_decimal": mp.nstr(mpf(comparator_margin), 40),
                "strict_improvement_over_actual_baseline_lower_bound": qs(improvement_lower),
                "strict_improvement_over_actual_baseline_lower_bound_decimal": mp.nstr(mpf(improvement_lower), 40),
                "actual_formula_diagnostic": mp.nstr(actual_feedback(A, B), 70),
            }
        )
    report = {
        "schema": 1,
        "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "directed_inputs": {
            "BMT_lower": qs(BMT_LOWER),
            "pi_upper": qs(PI_UPPER),
            "pi_lower_for_gain": "3",
            "source": "Zeta23.ThmD.HD_one_decimal.1, Real.pi_lt_d20, and Real.pi_gt_three",
        },
        "certified_numerator_lower": qs(numerator_lower),
        "certified_numerator_positive": numerator_lower > 0,
        "feasibility_scaling": {
            "statement": "If A <= E+B*S with E,S>=0 and 0<=t<=1, then t*A <= E+(t*B)*S.",
            "certified_ray_source": "A=63/5000, B=1094977/5000000000",
            "strict_both_candidate_t": "999/1000",
        },
        "monotonicity": {
            "definition": "R(A,B)=(6*M-10*pi*B)/(6-A)",
            "dR_dA": "(6*M-10*pi*B)/(6-A)^2 > 0",
            "dR_dB": "-10*pi/(6-A) < 0",
            "finite_difference": "R(A+dA,B+dB)-R(A,B)=((6*M-10*pi*B)*dA-10*pi*(6-A)*dB)/((6-A)*(6-A-dA))",
            "strict_improvement_condition": "(6*M-10*pi*B)*dA > 10*pi*(6-A)*dB, assuming A,A+dA<6",
            "baseline_diagnostics": {
                "dR_dA": mp.nstr(actual_feedback(A_BASE, B_BASE) / (6 - mpf(A_BASE)), 50),
                "dR_dB": mp.nstr(-10 * mp.pi / (6 - mpf(A_BASE)), 50),
                "neutral_dB_per_dA": mp.nstr(actual_feedback(A_BASE, B_BASE) / (10 * mp.pi), 50),
            },
        },
        "candidates": rows,
        "diagnostic_note": "mpmath decimals are diagnostic only. Every certified bound and margin is a Fraction derived from directed Lean inputs.",
    }
    output = Path(__file__).with_name("feedback-bounds.json")
    temporary = output.with_suffix(".json.new")
    temporary.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    os.replace(temporary, output)
    print(json.dumps(report, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
