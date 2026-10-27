#!/usr/bin/env python3
"""True-kernel ceiling: minimise F(p) = sum_pairs 2*K(d)^2 + B*S(p) over [0,59]^5, S<=59, K = Montgomery-Taylor kernel.
Compare with the 272-model catalog surrogate at the same points. Float search (multi-start Nelder-Mead), mpmath check."""
from __future__ import annotations
import math, random, sys, json
from fractions import Fraction as F
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import mpmath as mp
from generate_exact_macro_tree import read_pieces
from generate_exact_refined_scalar_tree import read_refinements
from map_ceiling_vs_B import nelder_mead, E as E_cat, seeds  # noqa
HERE = Path(__file__).resolve().parent
B6 = 1094977 / 5000000000
HD1 = 672500703679 / 10**12; PI = math.pi
r2 = math.sqrt(2); th = r2 / 2
def K(x):
    if abs(x * x - 2) < 1e-9: x += 1e-6
    return (r2 * x * math.cos(th) * math.sin(x / 2) - 2 * math.sin(th) * math.cos(x / 2)) / ((x * x - 2) * math.sin(th))
def E_true(p):
    pos = [0.0]
    for g in p: pos.append(pos[-1] + g)
    return sum(2 * K(pos[r] - pos[l]) ** 2 for r in range(1, 6) for l in range(r))
def obj(p, B, E):
    if any(x < 0 or x > 59 for x in p) or sum(p) > 59: return 1e9
    return E(p) + B * sum(p)
rng = random.Random(7)
def search(B, E, extra):
    cands = list(seeds) + extra + [[rng.uniform(0, 25) for _ in range(5)] for _ in range(300)]
    best = (None, 1e9)
    for s in cands:
        x, v = nelder_mead(lambda p: obj(p, B, E), s, step=0.4, iters=3000); x, v = nelder_mead(lambda p: obj(p, B, E), x, step=0.01, iters=3000)
        if v < best[1]: best = (x, v)
    return best
pstar = [6.6049, 12.5057, 6.5663, 12.5054, 6.6049]
print("catalog surrogate at p*: E_cat =", E_cat(pstar), " true E:", E_true(pstar), " gap:", E_true(pstar) - E_cat(pstar))
xt, vt = search(B6, E_true, [pstar])
xc, vc = search(B6, E_cat, [pstar])
def R(A, B): return (6 * HD1 - 10 * PI * B) / (6 - A)
print(f"catalog ceiling  A*_cat  <= {vc:.7f} at {[round(c,4) for c in xc]}   R = {R(vc,B6):.10f}")
print(f"true-kernel ceiling A*_true <= {vt:.7f} at {[round(c,4) for c in xt]}   R = {R(vt,B6):.10f}")
print(f"true E at catalog minimiser: {E_true(xc)+B6*sum(xc):.7f}; catalog E at true minimiser: {E_cat(xt)+B6*sum(xt):.7f}")
print("pair distances at true minimiser:", sorted(round(sum(xt[l:r]),3) for r in range(1,6) for l in range(r)))
print("pair distances at catalog minimiser:", sorted(round(sum(xc[l:r]),3) for r in range(1,6) for l in range(r)))
# per-pair contributions at p* (true vs catalog)
from map_ceiling_vs_B import model
pos=[0.0]
for g in pstar: pos.append(pos[-1]+g)
rows=[]
for r in range(1,6):
    for l in range(r):
        d=pos[r]-pos[l]; rows.append((round(d,4), round(2*K(d)**2,6), round(model(d),6), round(2*K(d)**2-model(d),6)))
rows.sort()
print("d, true 2K^2, catalog, gap:"); [print(" ",row) for row in rows]
# scan B for the true ceiling
for t in (0.8, 0.9, 1.0, 1.1, 1.2, 1.4):
    B = B6 * t; x, v = search(B, E_true, [pstar, xt]); v = min(v, 59 * B)
    print(f"t={t}: true ceiling {v:.7f}  R={R(v,B):.10f}  dR vs A1285={R(v,B)-R(257/20000,B6):+.3e}")
