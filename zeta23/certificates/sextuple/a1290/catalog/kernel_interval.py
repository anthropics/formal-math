#!/usr/bin/env python3
"""Exact (Fraction) replica of Zeta23.ThmD.Sextuple's RatInterval / TrigInterval / KernelInterval evaluators."""
from __future__ import annotations
from fractions import Fraction as F
from math import factorial
I = tuple  # (lo, hi)
def add(i, j): return (i[0] + j[0], i[1] + j[1])
def neg(i): return (-i[1], -i[0])
def sub(i, j): return add(i, neg(j))
def scale(q, i): return (q * i[0], q * i[1]) if q >= 0 else (q * i[1], q * i[0])
def mul(i, j):
    ps = (i[0] * j[0], i[0] * j[1], i[1] * j[0], i[1] * j[1]); return (min(ps), max(ps))
def sq(i): return mul(i, i)
def invPos(i): return (1 / i[1], 1 / i[0])
def divPos(i, j): return mul(i, invPos(j))
def sinPoly(x): return x - x**3/6 + x**5/120 - x**7/5040 + x**9/362880 - x**11/39916800 + x**13/6227020800
def cosPoly(x): return 1 - x**2/2 + x**4/24 - x**6/720 + x**8/40320 - x**10/3628800 + x**12/479001600
def trigError(x): return abs(x)**14 * F(15, factorial(14) * 14)
def sinPoint(x): return (sinPoly(x) - trigError(x), sinPoly(x) + trigError(x))
def cosPoint(x): return (cosPoly(x) - trigError(x), cosPoly(x) + trigError(x))
def widen(i, r): return (i[0] - r, i[1] + r)
PI = (F(314159265358979323846, 10**20), F(314159265358979323847, 10**20))
def quarterTurn(n, z):
    for _ in range(n): z = (z[1], neg(z[0]))
    return z
def reducedMid(x, n): return x - n * (PI[0] + PI[1]) / 4
def reducedRadius(n): return n * (PI[1] - PI[0]) / 4
def trigPoint(x, n):
    r = reducedMid(x, n); e = reducedRadius(n)
    return quarterTurn(n, (widen(sinPoint(r), e), widen(cosPoint(r), e)))
def trigRange(i, n):
    m = (i[0] + i[1]) / 2; r = (i[1] - i[0]) / 2
    s, c = trigPoint(m, n); return (widen(s, r), widen(c, r))
ROOT2 = (F(1414213562373095, 10**15), F(1414213562373096, 10**15))
THETA = scale(F(1, 2), ROOT2)
THETA_TRIG = trigRange(THETA, 0)
def kernelRange(i, turn):
    xt = trigRange(scale(F(1, 2), i), turn); st, ct = THETA_TRIG
    num = sub(mul(mul(mul(ROOT2, i), ct), xt[0]), mul(scale(F(2), st), xt[1]))
    den = mul(sub(sq(i), (F(2), F(2))), st)
    return divPos(num, den)
def kernelDenRange(i): return mul(sub(sq(i), (F(2), F(2))), THETA_TRIG[0])
def absLower(i): return i[0] if 0 <= i[0] else (-i[1] if i[1] <= 0 else F(0))
def cellCheck_ok(lo, hi, turn, a):
    """Replicates LowerPiece.cellCheck for a constant model (c = 0)."""
    i = (lo, hi)
    if not (2 <= lo <= hi): return False
    if abs(reducedMid((scale(F(1, 2), i)[0] + scale(F(1, 2), i)[1]) / 2, turn)) > 1: return False
    if not kernelDenRange(i)[0] > 0: return False
    return a <= 2 * absLower(kernelRange(i, turn)) ** 2
def best_turn(lo, hi):
    """The quarter-turn index that keeps |reducedMid| <= 1 for x/2 at the cell midpoint."""
    m = (lo + hi) / 4
    for n in range(0, 200):
        if abs(reducedMid(m, n)) <= 1: return n
    raise ValueError("no turn")
def barrier_bound(lo, hi):
    n = best_turn(lo, hi); return n, 2 * absLower(kernelRange((lo, hi), n)) ** 2
