/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Tasks

/-!
# The two tasks between Negative Triangle and the (min,+)-product

[VW18, Theorem 4.2], one of the reductions behind Theorem 21(b), goes from
deciding Negative Triangle to the (min,+)-product in three steps: finding a negative triangle
([VW18, Lemma 4.1]), finding for all pairs `(i, j)` at once whether some `k` has `X[i,k] + Y[k,j] <
V[i,j]`, and a search for all entries of the product at once.  Each step is a host over an arbitrary
solver of the task below it (isHost_find, isHost_pairs, isHost_mp).  This file fixes the two tasks
in the middle, findTask and pairsTask.
-/

@[expose] public section

open ThreeSumApsp

namespace Light.Sec3

open ThreeSumApsp.Spec

/-- Three matrices of weights, and the place for the three vertices of a triangle. -/
structure FindInst : Type extends TriInst where
  res : ℕ

/-- The place for the answer lies below the free pointer and does not meet the three matrices. -/
structure FindInst.Pre (x : FindInst) (μ : ℕ → ℤ) (fr : ℕ) : Prop
    extends TriInst.Pre x.toTriInst μ fr where
  belowRes : x.res + 3 ≤ fr
  apartAB : Apart x.ab (x.n * x.n) x.res 3
  apartBC : Apart x.bc (x.n * x.n) x.res 3
  apartAC : Apart x.ac (x.n * x.n) x.res 3

/-- Three matrices one after the other, with a place for an answer below them and the free pointer
behind them, are an instance. -/
theorem findPre_of_arrays {n U base res : ℕ} {AB BC AC : List ℤ} {μ : ℕ → ℤ} (hn : 1 ≤ n)
    (hU : 1 ≤ U) (hAB : ArrayAt μ base AB (n * n) U (base + 3 * (n * n)))
    (hBC : ArrayAt μ (base + n * n) BC (n * n) U (base + 3 * (n * n)))
    (hAC : ArrayAt μ (base + 2 * (n * n)) AC (n * n) U (base + 3 * (n * n)))
    (hres : res + 3 ≤ base) :
    (⟨⟨n, U, base, base + n * n, base + 2 * (n * n), AB, BC, AC⟩, res⟩ : FindInst).Pre μ
      (base + 3 * (n * n)) :=
  ⟨triPre_of_arrays hn hU hAB hBC hAC, by change res + 3 ≤ _; omega, .inr hres,
    .inr (by change res + 3 ≤ base + n * n; omega),
    .inr (by change res + 3 ≤ base + 2 * (n * n); omega)⟩

/-- **Finding a negative triangle**: find(n, U, ab, bc, ac, res, fr) returns 1 if there is a
negative triangle, and then the cells res, res + 1, res + 2 hold the vertices `a`, `b`, `c` of one;
it returns 0 if there is none. -/
noncomputable def findTask : Task where
  Inst := FindInst
  size x := x.n
  bound x := x.U
  args x := [x.n, x.U, x.ab, x.bc, x.ac, x.res]
  Pre := FindInst.Pre
  Post x μ fr r μ' :=
    r = flag (triOf x.n x.AB x.BC x.AC).HasNegativeTriangle ∧
    (r = 1 → ∃ a b c : Fin x.n, μ' x.res = a.val ∧ μ' (x.res + 1) = b.val ∧ μ' (x.res + 2) = c.val ∧
      (triOf x.n x.AB x.BC x.AC).S a b c < 0) ∧
    KeptBut μ μ' fr x.res 3

/-- Three `n × n` matrices, and the place for `n²` flags. -/
structure PairsInst : Type where
  n : ℕ
  U : ℕ
  x : ℕ
  y : ℕ
  v : ℕ
  out : ℕ
  X : List ℤ
  Y : List ℤ
  V : List ℤ

/-- The three matrices and the place for the flags lie below the free pointer; the place for the
flags does not meet the matrices. -/
structure PairsInst.Pre (q : PairsInst) (μ : ℕ → ℤ) (fr : ℕ) : Prop where
  n_pos : 1 ≤ q.n
  U_pos : 1 ≤ q.U
  lenX : q.X.length = q.n * q.n
  lenY : q.Y.length = q.n * q.n
  lenV : q.V.length = q.n * q.n
  segX : Seg μ q.x q.X
  segY : Seg μ q.y q.Y
  segV : Seg μ q.v q.V
  leX : AbsLe q.X q.U
  leY : AbsLe q.Y q.U
  leV : AbsLe q.V q.U
  belowX : q.x + q.n * q.n ≤ fr
  belowY : q.y + q.n * q.n ≤ fr
  belowV : q.v + q.n * q.n ≤ fr
  belowOut : q.out + q.n * q.n ≤ fr
  apartX : Apart q.x (q.n * q.n) q.out (q.n * q.n)
  apartY : Apart q.y (q.n * q.n) q.out (q.n * q.n)
  apartV : Apart q.v (q.n * q.n) q.out (q.n * q.n)

/-- An instance stays where it is if no cell below the free pointer changes, except the flags. -/
theorem PairsInst.Pre.keep {q : PairsInst} {μ μ' : ℕ → ℤ} {fr : ℕ} (h : q.Pre μ fr)
    (hs : KeptBut μ μ' fr q.out (q.n * q.n) := by light_keep) : q.Pre μ' fr := by
  light_facts h
  exact { h with segX := h.segX.keep, segY := h.segY.keep, segV := h.segV.keep }

/-- The flags: cell `i n + j` holds 1 if `X[i,k] + Y[k,j] < V[i,j]` for some `k < n`, and 0 if
not. -/
noncomputable def pairFlags (n : ℕ) (X Y V : List ℤ) : List ℤ :=
  (List.range (n * n)).map fun q =>
    flag (∃ k < n, X.getD (q / n * n + k) 0 + Y.getD (k * n + q % n) 0 < V.getD q 0)

/-- **All pairs**: allPairs(n, U, x, y, v, out, fr) writes the `n²` flags to out. -/
noncomputable def pairsTask : Task where
  Inst := PairsInst
  size q := q.n
  bound q := q.U
  args q := [q.n, q.U, q.x, q.y, q.v, q.out]
  Pre := PairsInst.Pre
  Post q μ fr _ μ' := Seg μ' q.out (pairFlags q.n q.X q.Y q.V) ∧ KeptBut μ μ' fr q.out (q.n * q.n)

end Light.Sec3
