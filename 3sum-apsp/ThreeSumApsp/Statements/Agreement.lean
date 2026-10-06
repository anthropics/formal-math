/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Lang.RowMajor
public import ThreeSumApsp.Machine.Solving
public import ThreeSumApsp.Sec3.Theorem21b.PathsAndWalks
public import ThreeSumApsp.Statements.Exponents

/-!
# The notions that are defined twice agree

The end statement defines Exact Triangle, the (min,+)-product, APSP, a matrix written row by row,
the weight of a `k`-clique, "a program solves a problem", `O(n^r)` and "solved in time" with Lean's
core library.  The statements on the reductions and the statements about programs use definitions of
their own, with Mathlib.  This file proves that the two definitions of each notion agree.

* Exact Triangle and the (min,+)-product: the two texts unfold to the same proposition.
* APSP: a path is a walk of finite weight (`exists_walk_of_path`, `path_of_walk`).  So the least
  weight of a path is the least weight of a walk (`isLeast_walkWeight_of_path`), and where there is
  no path every walk has weight `⊤` (`isLeast_walkWeight_of_no_path`).
* The weight of a clique: the two sums run over the same pairs of parts, in another order.
* "A program solves a problem": the two forms name the same word sizes and the same output cells
  (`output_cons`).
* `O(n^r)`: from `T(n)^q ≤ K n^p` follows `T(n) ≤ (K + 1) n^{p/q}` (`le_mul_rpow_of_pow_le`), and a
  bound for all large `n` is a bound from `n = 2` on, with a larger constant.
* "Solved in time": one direction is `SolvedInTime.endStatement`.  For the other, a step bound with
  `T(n)^q ≤ K n^p` from `n = 2` on is at most `(K + 1 + T(0) + T(1)) (n^{p/q} + 1)` at every `n`
  (`le_stepBound_of_bigO`).  The program and the slope of the word size stay the same.
-/

public section

open ThreeSumApsp.WordRam

namespace ThreeSumApsp

open EndStatement (Path)

/-! ## Exact Triangle and the (min,+)-product -/

/-- Exact Triangle: `EndStatement.ExactTriangle`, on the three matrices of weights of `T`, asks
whether `T` has a zero triangle. -/
theorem agreement_exactTriangle {n : ℕ} (T : TriangleInstance ℤ n) :
    EndStatement.ExactTriangle.yes (T.wAB, T.wBC, T.wAC) ↔ T.HasZeroTriangle :=
  Iff.rfl

/-- The (min,+)-product: the output cells are right for `EndStatement.MinPlusProduct` exactly if,
read row by row as a matrix, they are the (min,+)-product in the sense of `IsMinPlusProduct`. -/
theorem agreement_minPlusProduct {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℤ) (out : ℕ → ℤ) :
    EndStatement.MinPlusProduct.output (A, B) out ↔
      IsMinPlusProduct A B (Matrix.of fun i j => out (i.val * n + j.val)) :=
  Iff.rfl

/-! ## APSP -/

/-- A missing edge as `⊤`, written with `Option.elim` and with `toTop`. -/
private theorem elim_eq_toTop {n : ℕ} (w : Fin n → Fin n → Option ℤ) :
    (fun i j => (w i j).elim ⊤ fun z => (z : WithTop ℤ)) = fun i j => toTop (w i j) := by
  funext i j
  cases w i j <;> rfl

/-- APSP, the promise.  A missing edge is `none` in `EndStatement.APSP` and `⊤` in
`NoNegativeCycle`.  No closed `EndStatement.Path` has negative weight exactly if `NoNegativeCycle`
holds. -/
theorem agreement_apsp_noNegativeCycle {n : ℕ} (w : Fin n → Fin n → Option ℤ) :
    (∀ i d, EndStatement.Path w i i d → 0 ≤ d) ↔
      NoNegativeCycle fun i j => (w i j).elim ⊤ fun z => (z : WithTop ℤ) := by
  rw [elim_eq_toTop]
  refine ⟨noNegativeCycle_toTop, fun h i d hp => ?_⟩
  obtain ⟨rest, hend, hw⟩ := exists_walk_of_path hp
  have hnonneg := h i rest hend
  rw [hw] at hnonneg
  exact_mod_cast hnonneg

/-- The weight of a lightest path is the least weight of a walk. -/
private theorem isLeast_walkWeight_of_path {n : ℕ} {w : Fin n → Fin n → Option ℤ} {i j : Fin n}
    {d : ℤ} (hp : Path w i j d) (hmin : ∀ e, Path w i j e → d ≤ e) :
    IsLeast {y | ∃ rest, walkEnd i rest = j ∧ walkWeight (fun a b => toTop (w a b)) i rest = y}
      (d : WithTop ℤ) := by
  refine ⟨exists_walk_of_path hp, ?_⟩
  rintro y ⟨rest, rfl, hw⟩
  cases y with
  | top => exact le_top
  | coe z => exact_mod_cast hmin z (path_of_walk rest i z hw)

/-- Where there is no path, the walk along the missing edge has weight `⊤`, and so has every other
walk. -/
private theorem isLeast_walkWeight_of_no_path {n : ℕ} {w : Fin n → Fin n → Option ℤ} {i j : Fin n}
    (hno : ∀ e, ¬ Path w i j e) :
    IsLeast {y | ∃ rest, walkEnd i rest = j ∧ walkWeight (fun a b => toTop (w a b)) i rest = y}
      ⊤ := by
  refine ⟨⟨[j], rfl, ?_⟩, ?_⟩
  · cases hw : w i j with
    | none => simp [walkWeight, hw, toTop]
    | some a => exact absurd (Path.cons hw (Path.nil j)) (hno _)
  · rintro y ⟨rest, rfl, hw⟩
    cases y with
    | top => exact le_rfl
    | coe z => exact absurd (path_of_walk rest i z hw) (hno z)

/-- The output condition of `EndStatement.APSP`, for every pair of vertices. -/
private theorem output_apsp_iff {n : ℕ} (x : EndStatement.APSP.Instance n) (out : ℕ → ℤ) :
    EndStatement.APSP.output x out ↔ ∀ i j : Fin n,
      (out (2 * (i.val * n + j.val)) = 1 ∧ Path x.1 i j (out (2 * (i.val * n + j.val) + 1)) ∧
          ∀ e, Path x.1 i j e → out (2 * (i.val * n + j.val) + 1) ≤ e) ∨
        (out (2 * (i.val * n + j.val)) = 0 ∧ ∀ e, ¬ Path x.1 i j e) :=
  Iff.rfl

/-- APSP, the output.  The output cells are right for `EndStatement.APSP` exactly if the first cell
of every pair of vertices holds 0 or 1, and the matrix that has the second cell where the first
holds 1, and `⊤` elsewhere, is the distance matrix in the sense of `IsDistanceMatrix`. -/
theorem agreement_apsp_output {n : ℕ} (x : EndStatement.APSP.Instance n) (out : ℕ → ℤ) :
    EndStatement.APSP.output x out ↔
      (∀ i j : Fin n, out (2 * (i.val * n + j.val)) = 0 ∨ out (2 * (i.val * n + j.val)) = 1) ∧
      IsDistanceMatrix (fun i j => (x.1 i j).elim ⊤ fun z => (z : WithTop ℤ)) fun i j =>
        if out (2 * (i.val * n + j.val)) = 1 then (out (2 * (i.val * n + j.val) + 1) : WithTop ℤ)
        else ⊤ := by
  rw [elim_eq_toTop, output_apsp_iff]
  constructor
  · intro h
    refine ⟨fun i j => (h i j).elim (fun h1 => Or.inr h1.1) fun h0 => Or.inl h0.1, fun i j => ?_⟩
    rcases h i j with ⟨hflag, hp, hmin⟩ | ⟨hflag, hno⟩
    · simpa only [if_pos hflag] using isLeast_walkWeight_of_path hp hmin
    · simpa only [hflag, zero_ne_one, if_false] using isLeast_walkWeight_of_no_path hno
  · rintro ⟨hflags, hdist⟩ i j
    refine reachable_or_not hdist (fun htop => ?_) fun z hz => ?_
    · refine (hflags i j).resolve_right fun h1 => ?_
      simp [h1] at htop
    · by_cases h1 : out (2 * (i.val * n + j.val)) = 1
      · simp only [h1, if_true] at hz
        exact ⟨h1, by exact_mod_cast hz⟩
      · simp [h1] at hz

/-! ## A matrix row by row, and the weight of a clique -/

/-- A square matrix written row by row: `EndStatement.rowByRow` and `rowMajor` give the same
list. -/
theorem agreement_rowByRow {n : ℕ} (w : Fin n → Fin n → ℤ) :
    EndStatement.rowByRow w = rowMajor w :=
  Light.rowByRow_eq w

/-- The weight of a `k`-clique: the sum in `EndStatement.ZeroWeightKClique` is `cliqueWeight`, for
every choice `v` of one vertex in each part.  So that problem asks whether some clique has
`cliqueWeight` 0. -/
theorem agreement_cliqueWeight {k n : ℕ} (w : Fin k → Fin k → Fin n → Fin n → ℤ) :
    (∀ v : Fin k → Fin n,
      (List.ofFn fun j => (List.ofFn fun i => if i < j then w i j (v i) (v j) else 0).sum).sum =
        cliqueWeight w v) ∧
    ((EndStatement.ZeroWeightKClique k).yes w ↔ ∃ v, cliqueWeight w v = 0) := by
  have hsum : ∀ v : Fin k → Fin n,
      (List.ofFn fun j => (List.ofFn fun i => if i < j then w i j (v i) (v j) else 0).sum).sum =
        cliqueWeight w v := fun v => by
    rw [List.sum_ofFn, cliqueWeight]
    simp only [List.sum_ofFn]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun p _ => (Finset.sum_filter _ _).symm
  exact ⟨hsum, exists_congr fun v => Eq.congr_left (hsum v)⟩

/-! ## `O(n^r)`, solving a problem, and solved in time -/

/-- From `t^q ≤ K n^p` follows `t ≤ (K + 1) n^{p/q}`. -/
private theorem le_mul_rpow_of_pow_le {r : ℚ} (hr : 0 ≤ r) {t K n : ℕ}
    (h : t ^ r.den ≤ K * n ^ r.num.toNat) : (t : ℝ) ≤ ((K : ℝ) + 1) * (n : ℝ) ^ (r : ℝ) := by
  have hK : (K : ℝ) ≤ ((K : ℝ) + 1) ^ r.den :=
    (le_add_of_nonneg_right zero_le_one).trans
      (le_self_pow₀ (le_add_of_nonneg_left (Nat.cast_nonneg K)) r.den_nz)
  refine (pow_le_pow_iff_left₀ (Nat.cast_nonneg t) (by positivity) r.den_nz).1 ?_
  calc (t : ℝ) ^ r.den ≤ (K : ℝ) * (n : ℝ) ^ r.num.toNat := by exact_mod_cast h
    _ ≤ ((K : ℝ) + 1) ^ r.den * (n : ℝ) ^ r.num.toNat :=
        mul_le_mul_of_nonneg_right hK (by positivity)
    _ = (((K : ℝ) + 1) * (n : ℝ) ^ (r : ℝ)) ^ r.den := by rw [mul_pow, rpow_pow_den hr]

/-- `T(n) = O(n^r)`, for a rational exponent `r ≥ 0`: `EndStatement.BigO` says the same as
`IsBigOPow`. -/
theorem agreement_bigO (T : ℕ → ℕ) (r : ℚ) (hr : 0 ≤ r) :
    EndStatement.BigO T r ↔ IsBigOPow (fun n => (T n : ℝ)) (r : ℝ) := by
  have hnorm : ∀ n : ℕ, ‖(n : ℝ) ^ (r : ℝ)‖ = (n : ℝ) ^ (r : ℝ) := fun n =>
    Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  constructor
  · rintro ⟨K, hK⟩
    refine Asymptotics.IsBigO.of_bound ((K : ℝ) + 1)
      ((Filter.eventually_ge_atTop 2).mono fun n hn => ?_)
    rw [hnorm, Real.norm_natCast]
    exact le_mul_rpow_of_pow_le hr (hK n hn)
  · intro h
    obtain ⟨C, hC⟩ := h.bound
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hC
    -- the constant also covers the finitely many sizes below `N`, because `n^r ≥ 1`
    refine bigO_of_le_rpow (C := max C 0 + ∑ i ∈ Finset.range N, (T i : ℝ)) hr fun n hn => ?_
    have hone : (1 : ℝ) ≤ (n : ℝ) ^ (r : ℝ) :=
      Real.one_le_rpow (by exact_mod_cast (by omega : 1 ≤ n)) (by exact_mod_cast hr)
    have hsum : (0 : ℝ) ≤ ∑ i ∈ Finset.range N, (T i : ℝ) :=
      Finset.sum_nonneg fun i _ => Nat.cast_nonneg _
    rcases Nat.lt_or_ge n N with hlt | hge
    · have hT : (T n : ℝ) ≤ ∑ i ∈ Finset.range N, (T i : ℝ) :=
        Finset.single_le_sum (f := fun i => (T i : ℝ)) (fun i _ => Nat.cast_nonneg _)
          (Finset.mem_range.2 hlt)
      nlinarith [le_max_right C 0, mul_nonneg hsum (sub_nonneg.2 hone),
        mul_nonneg (le_max_right C 0) (zero_le_one.trans hone)]
    · have hb := hN n hge
      rw [hnorm, Real.norm_natCast] at hb
      nlinarith [mul_le_mul_of_nonneg_right (le_max_left C 0) (zero_le_one.trans hone),
        mul_nonneg hsum (zero_le_one.trans hone)]

/-- A step bound that is `O(n^r)` in the sense of the end statement is at most a constant times
`n^r + 1` at every size, in the form that `SolvedInTimeAt` has for `e = 0`. -/
private theorem le_stepBound_of_bigO {r : ℚ} (hr : 0 ≤ r) {T : ℕ → ℕ} {K : ℕ}
    (hK : ∀ n ≥ 2, T n ^ r.den ≤ K * n ^ r.num.toNat) (n : ℕ) :
    (T n : ℝ) ≤ ((K : ℝ) + 1 + T 0 + T 1) * ((n : ℝ) ^ (r : ℝ) * Real.log n ^ 0 + 1) := by
  have hX : (0 : ℝ) ≤ (n : ℝ) ^ (r : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have h0 : (0 : ℝ) ≤ T 0 := Nat.cast_nonneg _
  have h1 : (0 : ℝ) ≤ T 1 := Nat.cast_nonneg _
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg _
  rw [pow_zero, mul_one]
  rcases Nat.lt_or_ge n 2 with hn | hn
  · -- `T n` is `T 0` or `T 1`, and the constant is at least their sum
    have hT : (T n : ℝ) ≤ T 0 + T 1 := by
      obtain rfl | rfl : n = 0 ∨ n = 1 := by omega
      · linarith
      · linarith
    nlinarith [mul_nonneg (add_nonneg (add_nonneg (add_nonneg hK0 zero_le_one) h0) h1) hX]
  · have hT := le_mul_rpow_of_pow_le hr (hK n hn)
    nlinarith [mul_nonneg (add_nonneg h0 h1) hX]

/-- "A program solves a problem".  `Problem`, `Admissible`, `output` and `Solves` are the form for
problems with several sizes.  Write a problem `Q` of `EndStatement.lean` in this form: the instances
are those whose numbers have absolute value at most `n^κ`, the size is the one parameter of the word
size and stands in front of the input, and a right answer is a right verdict and a right output.
Then `Solves` says the same as `SolvesWithin`, which is stated through
`EndStatement.Problem.SolvedBy`. -/
theorem agreement_solves (Q : EndStatement.Problem) (κ : ℕ) (P : List EndStatement.Instr) (b : ℕ)
    (T : ℕ → ℝ) :
    SolvesWithin Q κ P b T ↔
      Solves
        ⟨Σ n, {x : Q.Instance n // ∀ a ∈ Q.input x, a.natAbs ≤ n ^ κ},
          fun ⟨n, _⟩ => [n],
          fun ⟨n, x, _⟩ => (n : ℤ) :: Q.input x,
          fun ⟨_, x, _⟩ verdict out => (verdict = true ↔ Q.yes x) ∧ Q.output x out⟩
        P b (fun _ => True) fun ⟨n, _⟩ => T n := by
  constructor
  · rintro h ⟨n, x, hx⟩ - bits hbits
    obtain ⟨t, ht, verdict, m, hexec, hyes, hout⟩ :=
      h n x hx bits (by simpa [Admissible] using hbits)
    exact ⟨t, verdict, m, ht, hexec, hyes, output_cons m n (Q.input x) ▸ hout⟩
  · intro h n x hx W hW
    obtain ⟨t, verdict, c, ht, hrun, hyes, hout⟩ :=
      h ⟨n, x, hx⟩ trivial W (by simpa [Admissible] using hW)
    exact ⟨t, ht, verdict, c, hrun, hyes, (output_cons c n (Q.input x)).symm ▸ hout⟩

/-- "Solved in time `O(n^r)`", for a rational exponent `r ≥ 0`: `EndStatement.Problem.SolvedInTime`
says the same as `SolvedInTime` with the real exponent `r` and no logarithmic factor. -/
theorem agreement_solvedInTime (Q : EndStatement.Problem) (r : ℚ) (hr : 0 ≤ r) :
    Q.SolvedInTime r ↔ SolvedInTime Q (r : ℝ) 0 := by
  refine ⟨fun h κ => ?_, fun h => h.endStatement rfl hr⟩
  obtain ⟨P, b, T, ⟨K, hK⟩, hrun⟩ := h κ
  exact ⟨P, b, (K : ℝ) + 1 + T 0 + T 1, fun n x hx W hW =>
    ⟨T n, le_stepBound_of_bigO hr hK n, hrun n x hx W hW⟩⟩

end ThreeSumApsp
