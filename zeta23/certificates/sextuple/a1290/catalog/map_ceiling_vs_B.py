#!/usr/bin/env python3
"""Map the 272-model catalog ceiling A*(B) = inf_p [E_cat(p) + B*S(p)] and the feedback bound R(A*(B),B).

E_cat(p) uses, for every pair distance, the strongest catalog model covering it (exactly the
`direct_point_value` surrogate of diagnose_refined_scalar_frontier.py).  Float multi-start local
search proposes minimisers; the best point per B is re-evaluated exactly (Fraction) and gives an
UPPER bound on A*(B) (the catalog cannot certify any A above it).  R uses the directed bounds
HD(1) > 672500703679/10^12 and pi < 314159265358979323847/10^20."""
from __future__ import annotations
import json, math, random, sys
from fractions import Fraction as F
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from generate_exact_macro_tree import read_pieces, q
from generate_exact_refined_scalar_tree import read_refinements
from diagnose_refined_scalar_frontier import direct_point_value

HERE = Path(__file__).resolve().parent
DATA = HERE.parents[1] / "lean-sextuple-certificate-prototype/macro-data-exact.json"
REF = HERE.parent / "refinement-catalog-exact.json"
B6 = F(1094977, 5000000000)
HD1 = F(672500703679, 10**12); PI = F(314159265358979323847, 10**20)

stable = read_pieces(DATA); refs = read_refinements(REF); pieces = stable + refs
fp = [(float(p.lo), float(p.hi), float(p.q), float(p.a), float(p.c)) for p in pieces]
# per-distance strongest model, float
def model(d: float) -> float:
    best = -1.0
    for lo, hi, qq, a, c in fp:
        if lo <= d <= hi:
            v = a + c * (d - qq) ** 2
            if v > best: best = v
    return best
def E(p):
    pos = [0.0]
    for g in p: pos.append(pos[-1] + g)
    return sum(model(pos[r] - pos[l]) for r in range(1, 6) for l in range(r))
def obj(p, B):
    if any(x < 0 or x > 59 for x in p) or sum(p) > 59: return 1e9
    return E(p) + B * sum(p)
def nelder_mead(f, x0, step=0.05, iters=4000, tol=1e-13):
    n = len(x0); pts = [list(x0)]
    for i in range(n):
        y = list(x0); y[i] += step; pts.append(y)
    vals = [f(p) for p in pts]
    for _ in range(iters):
        order = sorted(range(n + 1), key=lambda i: vals[i]); pts = [pts[i] for i in order]; vals = [vals[i] for i in order]
        if vals[-1] - vals[0] < tol: break
        c = [sum(p[i] for p in pts[:-1]) / n for i in range(n)]
        xr = [c[i] + (c[i] - pts[-1][i]) for i in range(n)]; fr = f(xr)
        if fr < vals[0]:
            xe = [c[i] + 2 * (c[i] - pts[-1][i]) for i in range(n)]; fe = f(xe)
            if fe < fr: pts[-1], vals[-1] = xe, fe
            else: pts[-1], vals[-1] = xr, fr
        elif fr < vals[-2]: pts[-1], vals[-1] = xr, fr
        else:
            xc = [c[i] + 0.5 * (pts[-1][i] - c[i]) for i in range(n)]; fc = f(xc)
            if fc < vals[-1]: pts[-1], vals[-1] = xc, fc
            else:
                for j in range(1, n + 1):
                    pts[j] = [pts[0][i] + 0.5 * (pts[j][i] - pts[0][i]) for i in range(n)]; vals[j] = f(pts[j])
    i = min(range(n + 1), key=lambda i: vals[i]); return pts[i], vals[i]
seeds = [[6.575, 12.49, 6.575, 12.44, 6.55], [6.63, 12.47, 6.58, 12.49, 6.63], [6.58, 12.47, 6.56, 12.43, 6.59],
         [12.5, 6.6, 12.5, 6.6, 12.5], [6.6, 6.6, 12.5, 6.6, 6.6], [12.5, 12.5, 6.6, 12.5, 12.5], [19, 6.6, 6.6, 6.6, 19]]
rng = random.Random(1)
def best_for(B: float):
    cands = list(seeds) + [[rng.uniform(0, 20) for _ in range(5)] for _ in range(40)]
    best = (None, 1e9)
    for s in cands:
        x, v = nelder_mead(lambda p: obj(p, B), s, step=0.3); x, v = nelder_mead(lambda p: obj(p, B), x, step=0.01)
        if v < best[1]: best = (x, v)
    return best
results = []
for t in [0.5, 0.6, 0.7, 0.8, 0.9, 0.95, 1.0, 1.05, 1.1, 1.2, 1.35, 1.5, 1.75, 2.0]:
    B = B6 * F(t).limit_denominator(1000)
    x, v = best_for(float(B))
    # exact re-evaluation at the rationalised point (denominator 2^20)
    xe = [F(round(c * 2**20), 2**20) for c in x]
    ve, _ = direct_point_value(pieces, B, xe)
    A_up = min(ve, 59 * B)
    R = (6 * HD1 - 10 * PI * B) / (6 - A_up)
    R6 = (6 * HD1 - 10 * PI * B6) / (6 - F(257, 20000))
    results.append({"t": t, "B": str(B), "B_float": float(B), "A_ceiling_float": float(A_up), "A_ceiling": str(A_up),
                    "point": [str(c) for c in xe], "R_at_ceiling": float(R), "R_minus_current_A1285": float(R - R6),
                    "tail_ok(A<=59B)": bool(A_up <= 59 * B)})
    print(f"t={t:<5} B={float(B):.7g} A*<= {float(A_up):.7f} R(A*,B)={float(R):.10f} dR vs A1285={float(R-R6):+.3e} point={[round(c,4) for c in x]}", flush=True)
json.dump(results, open(HERE / "ceiling-vs-B.json", "w"), indent=1)
