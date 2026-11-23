/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Paper.States
import Nc.Cross.Ident

/-!
# The paper, section "Two crossing wires": the identity

The polynomials B(r,n) and C(r,n) are Nc.Cross.mB and mC (with y an element of a ring), the matrix M is Nc.Cross.matM and
Ψ = det M is Nc.Cross.psi. A state enters them as the pair of the increasing enumerations of its two sets (Nc.Cross.word).
-/

set_option linter.unusedSimpArgs false

namespace Paper

open Finset Matrix Nc.Cross

/-- "Fix sizes μ, ν and energies e₁, e₂, and let Σ₁, Σ₂ be the sets of states with size and energy (μ, e₁), respectively (ν, e₂)":
the set Nc.Cross.states μ e. -/
theorem mem_stateClass {μ e : ℕ} (s : Finset ℕ × Finset ℕ) :
    s ∈ states μ e ↔ s.1.card = μ ∧ s.2.card = μ ∧ ∑ i ∈ s.1, (2 * i + 1) + ∑ j ∈ s.2, (2 * j + 1) = e := by
  rw [states, mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨mem_pairs.2 ⟨h.1.trans h.2.1.symm, h.2.2.le⟩, h⟩⟩

section Orth

variable {A : Type*} [CommRing A]

/-- The coefficients of a power series times 1 + at. -/
private theorem coeff_mk_mul_zero (f : ℕ → A) (a : A) :
    PowerSeries.coeff 0 (PowerSeries.mk f * (1 + PowerSeries.C a * PowerSeries.X)) = f 0 := by
  simp [mul_add, ← mul_assoc]

private theorem coeff_mk_mul_succ (f : ℕ → A) (a : A) (n : ℕ) :
    PowerSeries.coeff (n + 1) (PowerSeries.mk f * (1 + PowerSeries.C a * PowerSeries.X)) = f (n + 1) + f n * a := by
  simp [mul_add, ← mul_assoc, PowerSeries.coeff_succ_mul_X]

/-- "Let B(r,n) and C(r,n) be the coefficients of tⁿ in (1+t)^r/(1+yt)^(r+1) and (1+yt)^r/(1+t)^(r+1)." For B: the recursion
that defines Nc.Cross.mB gives the coefficients of the first series. -/
theorem meixner_B (y : A) (r : ℕ) :
    PowerSeries.mk (mB y r) * (1 + PowerSeries.C y * PowerSeries.X) ^ (r + 1) = (1 + PowerSeries.X) ^ r := by
  induction r with
  | zero =>
    rw [zero_add, pow_one, pow_zero]
    ext n
    cases n with
    | zero => rw [coeff_mk_mul_zero, mB_zero]; simp
    | succ n => rw [coeff_mk_mul_succ, mB_zero, mB_zero, PowerSeries.coeff_one, if_neg (Nat.succ_ne_zero n)]; ring
  | succ r ih =>
    have step : PowerSeries.mk (mB y (r + 1)) * (1 + PowerSeries.C y * PowerSeries.X) =
        PowerSeries.mk (mB y r) * (1 + PowerSeries.C 1 * PowerSeries.X) := by
      ext n
      cases n with
      | zero => rw [coeff_mk_mul_zero, coeff_mk_mul_zero, mB_zero_right, mB_zero_right]
      | succ n => rw [coeff_mk_mul_succ, coeff_mk_mul_succ, mB_succ]; ring
    rw [map_one, one_mul] at step
    rw [pow_succ' _ (r + 1), ← mul_assoc, step, mul_right_comm, ih, pow_succ]

/-- The same sentence for C: the recursion that defines Nc.Cross.mC gives the coefficients of (1+yt)^r/(1+t)^(r+1). -/
theorem meixner_C (y : A) (r : ℕ) :
    PowerSeries.mk (mC y r) * (1 + PowerSeries.X) ^ (r + 1) = (1 + PowerSeries.C y * PowerSeries.X) ^ r := by
  have one : (1 + PowerSeries.X : PowerSeries A) = 1 + PowerSeries.C 1 * PowerSeries.X := by rw [map_one, one_mul]
  induction r with
  | zero =>
    rw [zero_add, pow_one, pow_zero, one]
    ext n
    cases n with
    | zero => rw [coeff_mk_mul_zero, mC_zero]; simp
    | succ n => rw [coeff_mk_mul_succ, mC_zero, mC_zero, PowerSeries.coeff_one, if_neg (Nat.succ_ne_zero n)]; ring
  | succ r ih =>
    have step : PowerSeries.mk (mC y (r + 1)) * (1 + PowerSeries.X) =
        PowerSeries.mk (mC y r) * (1 + PowerSeries.C y * PowerSeries.X) := by
      rw [one]
      ext n
      cases n with
      | zero => rw [coeff_mk_mul_zero, coeff_mk_mul_zero, mC_zero_right, mC_zero_right]
      | succ n => rw [coeff_mk_mul_succ, coeff_mk_mul_succ, mC_succ]; ring
    rw [pow_succ' _ (r + 1), ← mul_assoc, step, mul_right_comm, ih, pow_succ]

/-- "They are polynomials in y, and yⁿ B(r,n)|_{1/y} = C(r,n)." Here z is an inverse of y. -/
theorem meixner_reciprocal {y z : A} (h : y * z = 1) (r n : ℕ) : y ^ n * mB z r n = mC y r n := by
  induction r generalizing n with
  | zero =>
    rw [mB_zero, mC_zero, ← mul_pow, mul_neg, h]
  | succ r ih =>
    induction n with
    | zero => simp [mB_zero_right, mC_zero_right]
    | succ n ih' =>
      rw [mB_succ, mC_succ, ← ih, ← ih, ← ih']
      linear_combination (-(y ^ n * mB z (r + 1) n)) * h

/-- The same relation read backwards: yⁿ C(r,n)|_{1/y} = B(r,n). -/
theorem meixner_reciprocal' {y z : A} (h : y * z = 1) (r n : ℕ) : y ^ n * mC z r n = mB y r n := by
  have h' : z * y = 1 := by rw [mul_comm, h]
  rw [← meixner_reciprocal h', ← mul_assoc, ← mul_pow, h, one_pow, one_mul]

/-- The telescoping sum. -/
private theorem tele (y : A) (u v : ℕ → A) (R : ℕ) (h : ∀ r, v (r + 1) = u r) :
    ∑ r ∈ Finset.range R, y ^ r * (v r - y * u r) = v 0 - y ^ R * v R := by
  induction R with
  | zero => simp
  | succ R ih =>
    rw [Finset.sum_range_succ, ih, h]
    ring

/-- **Paper: display eq:orth.** "(1−y) ∑_{r<R} y^r B(r,i) B(r,j) ≡ [i=j] y^i (mod y^R)." Here y is any element of any
commutative ring; the paper's case is the variable y of ℤ[y]. -/
theorem eq_orth (y : A) (R i j : ℕ) :
    y ^ R ∣ (1 - y) * ∑ r ∈ Finset.range R, y ^ r * (mB y r i * mB y r j)
      - (if i = j then y ^ i else 0) := by
  induction i generalizing j with
  | zero =>
    cases j with
    | zero =>
      have := tele y (fun _ => (1 : A)) (fun _ => 1) R (fun _ => rfl)
      refine ⟨-1, ?_⟩
      simp only [mB_zero_right, mul_one, if_true, pow_zero]
      simp only [mul_one] at this
      rw [← Finset.sum_mul] at this
      linear_combination this
    | succ j =>
      have := tele y (fun r => mB y r (j + 1) + mB y r j) (fun r => mB y r (j + 1) + y * mB y r j) R
        (fun r => by rw [mB_succ]; ring)
      refine ⟨-(mB y R (j + 1) + y * mB y R j), ?_⟩
      simp only [mB_zero_right, one_mul, (Nat.succ_ne_zero j).symm, if_false, mB_zero] at this ⊢
      rw [Finset.mul_sum]
      have e : ∑ r ∈ Finset.range R, (1 - y) * (y ^ r * mB y r (j + 1)) =
          ∑ r ∈ Finset.range R, y ^ r * (mB y r (j + 1) + y * mB y r j
            - y * (mB y r (j + 1) + mB y r j)) :=
        Finset.sum_congr rfl fun r _ => by ring
      rw [e, this]
      ring
  | succ i ih =>
    cases j with
    | zero =>
      have := tele y (fun r => mB y r (i + 1) + mB y r i) (fun r => mB y r (i + 1) + y * mB y r i) R
        (fun r => by rw [mB_succ]; ring)
      refine ⟨-(mB y R (i + 1) + y * mB y R i), ?_⟩
      simp only [mB_zero_right, mul_one, Nat.succ_ne_zero i, if_false, mB_zero] at this ⊢
      rw [Finset.mul_sum]
      have e : ∑ r ∈ Finset.range R, (1 - y) * (y ^ r * mB y r (i + 1)) =
          ∑ r ∈ Finset.range R, y ^ r * (mB y r (i + 1) + y * mB y r i
            - y * (mB y r (i + 1) + mB y r i)) :=
        Finset.sum_congr rfl fun r _ => by ring
      rw [e, this]
      ring
    | succ j =>
      have := tele y
        (fun r => (mB y r (i + 1) + mB y r i) * (mB y r (j + 1) + mB y r j))
        (fun r => (mB y r (i + 1) + y * mB y r i) * (mB y r (j + 1) + y * mB y r j)) R
        (fun r => by rw [mB_succ, mB_succ]; ring)
      obtain ⟨w, hw⟩ := ih j
      refine ⟨y * w - (mB y R (i + 1) + y * mB y R i) * (mB y R (j + 1) + y * mB y R j), ?_⟩
      have e : ∑ r ∈ Finset.range R, y ^ r * ((mB y r (i + 1) + y * mB y r i) *
            (mB y r (j + 1) + y * mB y r j)
            - y * ((mB y r (i + 1) + mB y r i) * (mB y r (j + 1) + mB y r j))) =
          (1 - y) * ∑ r ∈ Finset.range R, y ^ r * (mB y r (i + 1) * mB y r (j + 1))
          - y * ((1 - y) * ∑ r ∈ Finset.range R, y ^ r * (mB y r i * mB y r j)) := by
        simp only [Finset.mul_sum]
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun r _ => by ring
      rw [e] at this
      have z0 : (mB y 0 (i + 1) + y * mB y 0 i) = 0 := by simp only [mB_zero]; ring
      have z1 : (if i + 1 = j + 1 then y ^ (i + 1) else 0) = y * (if i = j then y ^ i else 0) := by
        by_cases hmn : i = j
        · simp [hmn, pow_succ, mul_comm]
        · simp [hmn]
      rw [z0, zero_mul, zero_sub] at this
      rw [z1]
      linear_combination this + y * hw

end Orth

section Blocks

variable {R : Type*} [CommRing R] {μ ν : ℕ}

/-- Proof of Proposition prop:identity, the coefficients: "So the block of rows a, d and columns c, b is congruent modulo X^(2R)
to FDG". Here F = facA, G = facB, K is the paper's R, and the block is Nc.Cross.blU; its part at (d,b) is treated by (eq:orth).
The other half, "and in the same way that of rows c, b and columns a, d to −G′DF′", is this theorem for the states with I and J
exchanged, transposed. -/
theorem prop_identity_blocks (K : ℕ) (x : R) (sa : Wd μ) (sd : Wd ν) (sc : Wd μ) (sb : Wd ν)
    (i j : Fin μ ⊕ Fin ν) :
    x ^ (2 * K) ∣ blU x sa sd sc sb i j -
      (facA K x sa sd * diagonal (fun r : Fin K => x ^ (2 * (r : ℕ) + 1)) * facB K x sc sb) i j := by
  have hdvd : ∀ n, ¬ n < K → x ^ (2 * K) ∣ x ^ (2 * n + 1) := fun n hn =>
    pow_dvd_pow x (by omega)
  rw [Matrix.mul_assoc, Matrix.mul_apply]
  simp only [Matrix.diagonal_mul]
  rcases i with i | i <;> rcases j with j | j
  · simp only [facA, facB, blU, of_apply, Sum.elim_inl, fromBlocks_apply₁₁, ite_mul, one_mul, zero_mul]
    rw [sum_ite_val K (sa.1 i) (fun r => x ^ (2 * r + 1) * if r = sc.2 j then 1 else 0)]
    by_cases h1 : sa.1 i < K
    · simp [h1]
    · by_cases h2 : sa.1 i = sc.2 j
      · rw [if_neg h1, if_pos h2, sub_zero]
        exact hdvd _ h1
      · simp [h1, h2]
  · simp only [facA, facB, blU, of_apply, Sum.elim_inl, Sum.elim_inr, fromBlocks_apply₁₂, ite_mul, one_mul,
      zero_mul]
    rw [sum_ite_val K (sa.1 i) (fun r => x ^ (2 * r + 1) * ((x ^ 2 - 1) * mB (x ^ 2) r (sb.2 j)))]
    by_cases h1 : sa.1 i < K
    · rw [if_pos h1]
      exact ⟨0, by ring⟩
    · rw [if_neg h1, sub_zero]
      exact Dvd.dvd.mul_left (Dvd.dvd.mul_right (hdvd _ h1) _) _
  · simp only [facA, facB, blU, of_apply, Sum.elim_inl, Sum.elim_inr, fromBlocks_apply₂₁]
    have e : ∀ r : Fin K, mB (x ^ 2) r (sd.1 i) * (x ^ (2 * (r : ℕ) + 1) *
        if (r : ℕ) = sc.2 j then 1 else 0) =
        if sc.2 j = (r : ℕ) then (fun r => mB (x ^ 2) r (sd.1 i) * x ^ (2 * r + 1)) r else 0 := by
      intro r
      by_cases h : (r : ℕ) = sc.2 j
      · simp [h]
      · simp [h, Ne.symm h]
    rw [Finset.sum_congr rfl fun r _ => e r,
      sum_ite_val K (sc.2 j) (fun r => mB (x ^ 2) r (sd.1 i) * x ^ (2 * r + 1))]
    by_cases h1 : sc.2 j < K
    · rw [if_pos h1]
      exact ⟨0, by ring⟩
    · rw [if_neg h1, sub_zero]
      exact Dvd.dvd.mul_right (hdvd _ h1) _
  · simp only [facA, facB, blU, of_apply, Sum.elim_inr, fromBlocks_apply₂₂]
    obtain ⟨w, hw⟩ := eq_orth (x ^ 2) K (sd.1 i) (sb.2 j)
    refine ⟨x * w, ?_⟩
    have e : ∑ r : Fin K, mB (x ^ 2) r (sd.1 i) * (x ^ (2 * (r : ℕ) + 1) *
        ((x ^ 2 - 1) * mB (x ^ 2) r (sb.2 j))) =
        -(x * ((1 - x ^ 2) * ∑ r ∈ Finset.range K, (x ^ 2) ^ r * (mB (x ^ 2) r (sd.1 i) *
          mB (x ^ 2) r (sb.2 j)))) := by
      rw [Finset.sum_range, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [← pow_mul, pow_succ]
      ring
    have z : (if sd.1 i = sb.2 j then x ^ (2 * sd.1 i + 1) else 0) =
        x * (if sd.1 i = sb.2 j then (x ^ 2) ^ sd.1 i else 0) := by
      split_ifs
      · rw [← pow_mul, pow_succ, mul_comm]
      · simp
    rw [e, z, pow_mul]
    linear_combination x * hw

/-- Unfolds an entry of the matrices M and of the multipliers. -/
local macro "entries" : tactic => `(tactic| simp only [matM, blX, blY, blU, scal, scal', exch, Equiv.coe_fn_mk, submatrix_apply, Sum.elim_inl,
      Sum.elim_inr, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂,
      of_apply, Matrix.neg_apply, transpose_apply, Matrix.zero_apply, mul_zero, Prod.fst_swap, Prod.snd_swap])

/-- Proof of Proposition prop:identity, reflection: "Substitute 1/X for X and multiply the rows and the columns of a, c by
X^(2i+1), those of d by (y−1)y^i and those of b by y^(i+1). The relation between B and C shows that one obtains the matrix M in
which the sites b and d are exchanged (the new site d holds s_b), with the rows and columns of the new d multiplied by 1−y."
Entry by entry; z is the inverse of x, the multipliers are Nc.Cross.scal and scal', and exch exchanges the sites. -/
theorem prop_identity_exchange {x z : R} (h : x * z = 1) (sa : Wd μ) (sb : Wd ν) (sc : Wd μ) (sd : Wd ν)
    (i j : (Fin μ ⊕ Fin ν) ⊕ (Fin μ ⊕ Fin ν)) :
    scal x sa.1 sb.1 sc.1 sd.1 i * (scal x sa.2 sb.2 sc.2 sd.2 j * matM z sa sb sc sd i j) =
      scal' x i * (scal' x j * (matM x sa sd sc sb).submatrix (exch μ ν) (exch μ ν) i j) := by
  have h2 : x ^ 2 * z ^ 2 = 1 := by rw [← mul_pow, h, one_pow]
  have hxz : ∀ n, x ^ n * z ^ n = 1 := fun n => by rw [← mul_pow, h, one_pow]
  have hB : ∀ r n, (x ^ 2) ^ n * mB (z ^ 2) r n = mC (x ^ 2) r n := meixner_reciprocal h2
  have hC : ∀ r n, (x ^ 2) ^ n * mC (z ^ 2) r n = mB (x ^ 2) r n := meixner_reciprocal' h2
  have hz : ∀ m : ℕ, x ^ (2 * m + 1) * z ^ (2 * m + 1) = 1 := fun m => hxz _
  rcases i with (i | i) | (i | i)
  · rcases j with (j | j) | (j | j)
    · entries
    · entries
      linear_combination (x ^ (2 * sa.1 i + 1) * (x ^ 2 - 1)) * hC (sa.1 i) (sd.2 j)
    · entries
      by_cases h1 : sa.1 i = sc.2 j
      · rw [if_pos h1, if_pos h1, ← h1]
        linear_combination x ^ (2 * sa.1 i + 1) * hz (sa.1 i)
      · simp [h1]
    · entries
      linear_combination (x ^ 2 * (z ^ 2 - 1) * ((x ^ 2) ^ sb.2 j * mB (z ^ 2) (sa.1 i) (sb.2 j))) *
        hz (sa.1 i) + (x ^ 2 * (z ^ 2 - 1)) * hB (sa.1 i) (sb.2 j) + mC (x ^ 2) (sa.1 i) (sb.2 j) * h2
  · rcases j with (j | j) | (j | j)
    · entries
      linear_combination (-(x ^ (2 * sa.2 j + 1) * (x ^ 2 - 1))) * hC (sa.2 j) (sd.1 i)
    · entries
    · entries
      linear_combination ((x ^ 2 - 1) * ((x ^ 2) ^ sd.1 i * mB (z ^ 2) (sc.2 j) (sd.1 i))) * hz (sc.2 j) +
        (x ^ 2 - 1) * hB (sc.2 j) (sd.1 i)
    · entries
      by_cases h1 : sd.1 i = sb.2 j
      · rw [if_pos h1, if_pos h1.symm, ← h1]
        linear_combination (x ^ (2 * sd.1 i + 1) * (1 - x ^ 2)) * hz (sd.1 i)
      · simp [h1, Ne.symm h1]
  · rcases j with (j | j) | (j | j)
    · entries
      by_cases h1 : sa.2 j = sc.1 i
      · rw [if_pos h1, if_pos h1, ← h1]
        linear_combination (-x ^ (2 * sa.2 j + 1)) * hz (sa.2 j)
      · simp [h1]
    · entries
      linear_combination (-(x ^ 2 - 1) * ((x ^ 2) ^ sd.2 j * mB (z ^ 2) (sc.1 i) (sd.2 j))) * hz (sc.1 i) -
        (x ^ 2 - 1) * hB (sc.1 i) (sd.2 j)
    · entries
    · entries
      linear_combination (-(x ^ (2 * sc.1 i + 1) * (1 - x ^ 2))) * hC (sc.1 i) (sb.2 j) -
        (x ^ (2 * sc.1 i + 1) * (x ^ 2) ^ sb.2 j * mC (z ^ 2) (sc.1 i) (sb.2 j)) * h2
  · rcases j with (j | j) | (j | j)
    · entries
      linear_combination (-(x ^ 2 * (z ^ 2 - 1) * ((x ^ 2) ^ sb.1 i * mB (z ^ 2) (sa.2 j) (sb.1 i)))) *
        hz (sa.2 j) - (x ^ 2 * (z ^ 2 - 1)) * hB (sa.2 j) (sb.1 i) - mC (x ^ 2) (sa.2 j) (sb.1 i) * h2
    · entries
      by_cases h1 : sd.2 j = sb.1 i
      · rw [if_pos h1, if_pos h1.symm, ← h1]
        linear_combination (x ^ (2 * sd.2 j + 1) * (x ^ 2 - 1)) * hz (sd.2 j)
      · simp [h1, Ne.symm h1]
    · entries
      linear_combination (x ^ (2 * sc.2 j + 1) * (1 - x ^ 2)) * hC (sc.2 j) (sb.1 i) +
        (x ^ (2 * sc.2 j + 1) * (x ^ 2) ^ sb.1 i * mC (z ^ 2) (sc.2 j) (sb.1 i)) * h2
    · entries

/-- Proof of Proposition prop:identity, reflection: "Rows and columns are permuted alike, so there is no sign." So the product of
all multipliers times Ψ(1/X; s_a, s_b, s_c, s_d) is (1−y)^(2ν) Ψ(X; s_a, s_d, s_c, s_b). -/
theorem prop_identity_exchange_det {x z : R} (h : x * z = 1) (sa : Wd μ) (sb : Wd ν) (sc : Wd μ) (sd : Wd ν) :
    (∏ i, scal x sa.1 sb.1 sc.1 sd.1 i) * ((∏ i, scal x sa.2 sb.2 sc.2 sd.2 i) * psi z sa sb sc sd) =
      (∏ i, (scal' x : (Fin μ ⊕ Fin ν) ⊕ (Fin μ ⊕ Fin ν) → R) i) *
      ((∏ i, (scal' x : (Fin μ ⊕ Fin ν) ⊕ (Fin μ ⊕ Fin ν) → R) i) * psi x sa sd sc sb) := by
  rw [psi, psi, ← det_submatrix_equiv_self (exch μ ν) (matM x sa sd sc sb),
    ← det_mul_row (scal x sa.2 sb.2 sc.2 sd.2) (matM z sa sb sc sd),
    ← det_mul_column (scal x sa.1 sb.1 sc.1 sd.1) (of fun i j => scal x sa.2 sb.2 sc.2 sd.2 j *
      matM z sa sb sc sd i j),
    ← det_mul_row (scal' x) ((matM x sa sd sc sb).submatrix (exch μ ν) (exch μ ν)),
    ← det_mul_column (scal' x) (of fun i j => scal' x j *
      (matM x sa sd sc sb).submatrix (exch μ ν) (exch μ ν) i j)]
  congr 1
  ext i j
  exact prop_identity_exchange h sa sb sc sd i j

/-- Proof of Proposition prop:identity, reflection: "The multipliers at a, c, d, b contain X to the powers e₁, e₁, e₂−2ν, e₂+2ν, in
all Θ, and the factors (y−1)^(2ν) and (1−y)^(2ν) on the two sides cancel in ℤ[X]. So
X^Θ Ψ(1/X; s_a, s_b, s_c, s_d) = Ψ(X; s_a, s_d, s_c, s_b)", Θ = 2(e₁+e₂).
Here x is an element of a domain with inverse z and x² ≠ 1; the paper's case is x = X in the field of fractions of ℤ[X]. -/
theorem prop_identity_reflection [IsDomain R] {x z : R} (h : x * z = 1) (h1 : x ^ 2 ≠ 1) (sa : Wd μ) (sb : Wd ν) (sc : Wd μ)
    (sd : Wd ν) {e₁ e₂ : ℕ} (ha : enW sa = e₁) (hb : enW sb = e₂) (hc : enW sc = e₁) (hd : enW sd = e₂) :
    x ^ (2 * (e₁ + e₂)) * psi z sa sb sc sd = psi x sa sd sc sb := by
  have key := prop_identity_exchange_det h sa sb sc sd
  rw [prod_scal, prod_scal, prod_scal'] at key
  have hne : (1 - x ^ 2) ^ ν * (1 - x ^ 2) ^ ν ≠ 0 := by
    have : (1 - x ^ 2) ≠ 0 := sub_ne_zero.2 (Ne.symm h1)
    exact mul_ne_zero (pow_ne_zero _ this) (pow_ne_zero _ this)
  refine mul_left_cancel₀ hne ?_
  have hs : (x ^ 2 - 1) ^ ν * (x ^ 2 - 1) ^ ν = (1 - x ^ 2) ^ ν * (1 - x ^ 2) ^ ν := by
    rw [← mul_pow, ← mul_pow]
    congr 1
    ring
  have hν1 : ∀ f : Fin ν → ℕ, ∑ i, 2 * f i + ν = ∑ i, (2 * f i + 1) := fun f => by
    simp [Finset.sum_add_distrib]
  have hν2 : ∀ f : Fin ν → ℕ, ∑ i, (2 * f i + 2) = ∑ i, (2 * f i + 1) + ν := fun f => by
    simp [Finset.sum_add_distrib]
    ring
  have hexp : (∑ i, (2 * sa.1 i + 1)) + (∑ i, (2 * sc.1 i + 1)) + (∑ i, 2 * sd.1 i) +
      (∑ i, (2 * sb.1 i + 2)) + ((∑ i, (2 * sa.2 i + 1)) + (∑ i, (2 * sc.2 i + 1)) + (∑ i, 2 * sd.2 i) +
      ∑ i, (2 * sb.2 i + 2)) = 2 * (e₁ + e₂) := by
    unfold enW at ha hb hc hd
    have := hν1 sd.1
    have := hν1 sd.2
    have := hν2 sb.1
    have := hν2 sb.2
    omega
  generalize (∑ i, (2 * sa.1 i + 1)) + (∑ i, (2 * sc.1 i + 1)) + (∑ i, 2 * sd.1 i) +
    (∑ i, (2 * sb.1 i + 2)) = a at key hexp
  generalize (∑ i, (2 * sa.2 i + 1)) + (∑ i, (2 * sc.2 i + 1)) + (∑ i, 2 * sd.2 i) +
    (∑ i, (2 * sb.2 i + 2)) = b at key hexp
  rw [← hexp, pow_add]
  linear_combination key - (x ^ a * x ^ b * psi z sa sb sc sd) * hs

end Blocks

/-- Proof of Proposition prop:identity, X = 1: "for states in the given classes, Ψ|_{X=1} is a sign, depending on μ, ν only,
times [J_c = I_a, I_c = J_a, J_b = I_d, I_b = J_d]." -/
theorem prop_identity_one (μ ν : ℕ) : ∃ ε : ℤˣ, ∀ (sa : Wd μ) (sb : Wd ν) (sc : Wd μ) (sd : Wd ν),
    StrictMono sa.1 → StrictMono sa.2 → StrictMono sb.1 → StrictMono sb.2 →
    StrictMono sc.1 → StrictMono sc.2 → StrictMono sd.1 → StrictMono sd.2 →
    psi (1 : ℤ) sa sb sc sd = ε * if sa = sc.swap ∧ sb = sd.swap then 1 else 0 := by
  let e : Equiv.Perm ((Fin μ ⊕ Fin ν) ⊕ (Fin μ ⊕ Fin ν)) := Equiv.sumComm _ _
  refine ⟨Equiv.Perm.sign e * (-1) ^ (μ + ν), fun sa sb sc sd ha1 ha2 hb1 hb2 hc1 hc2 hd1 hd2 => ?_⟩
  have h1 := det_permute' e (matM (1 : ℤ) sa sb sc sd)
  have h2 : (matM (1 : ℤ) sa sb sc sd).submatrix id e =
      fromBlocks (blU (1 : ℤ) sa sd sc sb) (blX (1 : ℤ) sa sd) (blY (1 : ℤ) sc sb)
        (-(blU (1 : ℤ) sa.swap sd.swap sc.swap sb.swap)ᵀ) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> simp [matM, e]
  have hY : blY (1 : ℤ) sc sb = 0 := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> simp [blY]
  have hU : ∀ (sa : Wd μ) (sd : Wd ν) (sc : Wd μ) (sb : Wd ν), StrictMono sa.1 → StrictMono sd.1 →
      StrictMono sc.2 → StrictMono sb.2 →
      (blU (1 : ℤ) sa sd sc sb).det = (-1) ^ ν * ((if sa.1 = sc.2 then 1 else 0) *
        (if sd.1 = sb.2 then 1 else 0)) := by
    intro sa sd sc sb k1 k2 k3 k4
    have e1 : blU (1 : ℤ) sa sd sc sb = fromBlocks (of fun i j => if sa.1 i = sc.2 j then 1 else 0) 0
        (of fun i j => mB 1 (sc.2 j) (sd.1 i)) (-(of fun i j => if sd.1 i = sb.2 j then 1 else 0)) := by
      ext i j
      rcases i with i | i <;> rcases j with j | j <;> simp [blU]
    rw [e1, det_fromBlocks_zero₁₂, det_neg, Fintype.card_fin, det_coinc _ _ k1 k3, det_coinc _ _ k2 k4]
    ring
  rw [h2, hY, det_fromBlocks_zero₂₁, det_neg, det_transpose, hU _ _ _ _ ha1 hd1 hc2 hb2,
    hU _ _ _ _ ha2 hd2 hc1 hb1] at h1
  simp only [Prod.fst_swap, Prod.snd_swap, Fintype.card_sum, Fintype.card_fin] at h1
  have hs : ((Equiv.Perm.sign e : ℤˣ) : ℤ) * ((Equiv.Perm.sign e : ℤˣ) : ℤ) = 1 := Int.units_coe_mul_self _
  have hν : ((-1 : ℤ) ^ ν) * (-1) ^ ν = 1 := by rw [← mul_pow]; simp
  have hind : (if sa = sc.swap ∧ sb = sd.swap then (1 : ℤ) else 0) =
      ((if sa.1 = sc.2 then 1 else 0) * (if sd.1 = sb.2 then 1 else 0)) *
      ((if sa.2 = sc.1 then 1 else 0) * (if sd.2 = sb.1 then 1 else 0)) := by
    have : (sa = sc.swap ∧ sb = sd.swap) ↔
        ((sa.1 = sc.2 ∧ sd.1 = sb.2) ∧ (sa.2 = sc.1 ∧ sd.2 = sb.1)) := by
      rw [Prod.ext_iff, Prod.ext_iff]
      simp only [Prod.fst_swap, Prod.snd_swap]
      constructor
      · rintro ⟨⟨a, b⟩, c, d⟩
        exact ⟨⟨a, d.symm⟩, b, c.symm⟩
      · rintro ⟨⟨a, d⟩, b, c⟩
        exact ⟨⟨a, b⟩, c.symm, d.symm⟩
    simp only [this]
    by_cases a : sa.1 = sc.2 <;> by_cases b : sd.1 = sb.2 <;> by_cases c : sa.2 = sc.1 <;>
      by_cases d : sd.2 = sb.1 <;> simp [a, b, c, d]
  rw [psi, hind]
  push_cast
  linear_combination (-(matM (1 : ℤ) sa sb sc sd).det) * hs - ((Equiv.Perm.sign e : ℤˣ) : ℤ) * h1
    + ((Equiv.Perm.sign e : ℤˣ) : ℤ) * (-1) ^ (μ + ν) * (((if sa.1 = sc.2 then 1 else 0) * (if sd.1 = sb.2 then 1 else 0)) *
      ((if sa.2 = sc.1 then 1 else 0) * (if sd.2 = sb.1 then 1 else 0))) * hν

/-- A sum of products over a finite index set is a sum of r products, if r is at least the size of the index set. -/
private theorem exists_products {β γ κ : Type} [Fintype κ] {f : β → γ → ℤ} (g : κ → β → ℤ) (h : κ → γ → ℤ)
    (hf : ∀ b c, f b c = ∑ t, g t b * h t c) {r : ℕ} (hr : Fintype.card κ ≤ r) :
    ∃ (g' : Fin r → β → ℤ) (h' : Fin r → γ → ℤ), ∀ b c, f b c = ∑ t, g' t b * h' t c := by
  classical
  let e := Fintype.equivFin κ
  refine ⟨fun t b => if ht : t.1 < Fintype.card κ then g (e.symm ⟨t.1, ht⟩) b else 0,
    fun t c => if ht : t.1 < Fintype.card κ then h (e.symm ⟨t.1, ht⟩) c else 0, fun b c => ?_⟩
  rw [hf]
  refine Finset.sum_of_injOn (fun t => Fin.castLE hr (e t))
    (fun _ _ _ _ he => e.injective (Fin.castLE_injective hr he)) (fun _ _ => by simp) (fun t _ ht => ?_) (fun t _ => ?_)
  · have hlt : ¬ t.1 < Fintype.card κ := fun hlt => ht ⟨e.symm ⟨t.1, hlt⟩, by simp, by simp [Fin.castLE]⟩
    simp [hlt]
  · have hlt : (Fin.castLE hr (e t)).1 < Fintype.card κ := (e t).2
    simp only [dif_pos hlt]
    simp

section Expansion

/-! ### The coefficients: the expansion

In this section X = M₁, Y = M₂, A = F, A' = F′, B = G, B' = −G′, and l is the diagonal of D. -/

variable {p q ρ : Type*} [Fintype p] [DecidableEq p] [Fintype q] [DecidableEq q] [Fintype ρ] [DecidableEq ρ]
variable {R : Type*} [CommRing R]

/-- Proof of Proposition prop:identity, the coefficients: "Up to a sign that depends on R only, the determinant of such a matrix
equals that of" the matrix with the block rows (M₁, 0, F, 0), (0, M₂, 0, G′), (0, DG, −1, 0), (DF′, 0, 0, 1) "(a Schur
complement)". Here the last two block rows are (0, −DB, 1, 0) and (−DA', 0, 0, 1), and there is no sign. -/
theorem prop_identity_schur (l : ρ → R) (X : Matrix p p R) (A : Matrix p ρ R) (A' : Matrix ρ p R)
    (Y : Matrix q q R) (B : Matrix ρ q R) (B' : Matrix q ρ R) :
    (fromBlocks X (A * diagonal l * B) (B' * diagonal l * A') Y).det =
      (fromBlocks (fromBlocks X 0 0 Y) (fromBlocks A 0 0 B')
        (-(fromBlocks 0 (diagonal l * B) (diagonal l * A') 0)) 1).det := by
  rw [det_fromBlocks_one₂₂]
  congr 1
  rw [Matrix.mul_neg, sub_neg_eq_add, fromBlocks_multiply, fromBlocks_add]
  simp [Matrix.mul_assoc]

/-- Proof of Proposition prop:identity, the coefficients: "Each of the last 2R rows is the sum of its part in DG, respectively
DF′, and its entry ±1. Expand by multilinearity, and let T₁, T₂ be the sets of rows of the third and of the fourth block row for
which the first part is taken." The term of T = (T₁, T₂) is the product of the entries of D in T, which is X^E(T) in the paper,
times the determinant of the matrix Nc.Cross.termMat T, in which the rows outside T have only their entry 1. -/
theorem prop_identity_expand (l : ρ → R) (X : Matrix p p R) (A : Matrix p ρ R) (A' : Matrix ρ p R)
    (Y : Matrix q q R) (B : Matrix ρ q R) (B' : Matrix q ρ R) :
    (fromBlocks X (A * diagonal l * B) (B' * diagonal l * A') Y).det =
      ∑ T : Finset (ρ ⊕ ρ), (∏ r ∈ T, Sum.elim l l r) * (termMat T X A A' Y B B').det := by
  have h1 : (of (Sum.elim (topRows X A Y B') fun r => Sum.elim l l r • lowRows A' B r + unitRows r) :
      Matrix ((p ⊕ q) ⊕ (ρ ⊕ ρ)) ((p ⊕ q) ⊕ (ρ ⊕ ρ)) R) =
      fromBlocks (fromBlocks X 0 0 Y) (fromBlocks A 0 0 B')
        (-(fromBlocks 0 (diagonal l * B) (diagonal l * A') 0)) 1 := by
    ext i j
    rcases i with (i | i) | (i | i) <;> rcases j with (j | j) | (j | j) <;>
      simp [topRows, lowRows, unitRows, Matrix.diagonal_mul]
  rw [prop_identity_schur, ← h1]
  exact det_expand (topRows X A Y B') (Sum.elim l l) (lowRows A' B) unitRows

/-- Proof of Proposition prop:identity, the coefficients: "This vanishes if |T₁| ≠ |T₂|, as the blocks are then not square". (In
Lean the rows outside T are kept, with their entry 1; the form with two blocks is Nc.Cross.termMat_eq_glue.) -/
theorem prop_identity_term_zero (T : Finset (ρ ⊕ ρ)) (hT : T.toLeft.card ≠ T.toRight.card)
    (X : Matrix p p R) (A : Matrix p ρ R) (A' : Matrix ρ p R)
    (Y : Matrix q q R) (B : Matrix ρ q R) (B' : Matrix q ρ R) :
    (termMat T X A A' Y B B').det = 0 := by
  rw [termMat_eq_glue]
  refine det_glue_zero _ _ _ _ ?_
  rw [card_cgrp]
  have := card_rgrp (p := p) (q := q) T
  omega

/-- Proof of Proposition prop:identity, the coefficients: "otherwise it is a polynomial in X depending on (s_a, s_d) times one
depending on (s_b, s_c)". For every T the determinant of the term is a function of (X, A, A') times a function of (Y, B, B'). -/
theorem prop_identity_term_product (T : Finset (ρ ⊕ ρ)) :
    ∃ (α : Matrix p p R → Matrix p ρ R → Matrix ρ p R → R)
      (β : Matrix q q R → Matrix ρ q R → Matrix q ρ R → R),
      ∀ X A A' Y B B', (termMat T X A A' Y B B').det = α X A A' * β Y B B' := by
  obtain ⟨a, b, h⟩ := det_glue (R := R) (rgrp T : (p ⊕ q) ⊕ (ρ ⊕ ρ) → Prop) cgrp
  exact ⟨fun X A A' => a (termMat T X A A' 0 0 0), fun Y B B' => b (termMat T 0 0 0 Y B B'),
    fun X A A' Y B B' => by rw [termMat_eq_glue, h]⟩

/-- Proof of Proposition prop:identity, the coefficients: "The T with |T₁| = |T₂| and E(T) ≤ N are at most P(N) states". -/
theorem prop_identity_term_count (K N : ℕ) : (goodT K N).card ≤ stateCount N := by
  show (goodT K N).card ≤ (pairs N).card
  refine Finset.card_le_card_of_injOn
    (fun T => (T.toLeft.map Fin.valEmbedding, T.toRight.map Fin.valEmbedding)) ?_ ?_
  · intro T hT
    have hT' := (mem_filter.1 hT).2
    have e1 : enT T = en (T.toLeft.map Fin.valEmbedding) + en (T.toRight.map Fin.valEmbedding) := by
      conv_lhs => rw [← T.toLeft_disjSum_toRight]
      unfold enT en
      rw [Finset.sum_disjSum, Finset.sum_map, Finset.sum_map]
      rfl
    refine mem_coe.2 (mem_pairs.2 ⟨?_, ?_⟩)
    · simpa using hT'.1
    · rw [← e1]
      exact hT'.2
  · intro T _ T' _ h
    have h1 := Finset.map_injective _ (Prod.ext_iff.1 h).1
    have h2 := Finset.map_injective _ (Prod.ext_iff.1 h).2
    rw [← T.toLeft_disjSum_toRight, ← T'.toLeft_disjSum_toRight, h1, h2]

open Polynomial in
/-- Proof of Proposition prop:identity, the coefficients: "… and the degree N − E(T) can be split between the two factors in at
most N+1 ways." So the coefficient of X^N of the determinant of a matrix with the diagonal blocks X, Y and the other blocks ADB,
B'DA', D = diag(X^(2r+1)), is a sum, over the T with |T₁| = |T₂| and E(T) ≤ N and over N+1 degrees, of products of a function of
(X, A, A') and one of (Y, B, B'). -/
theorem prop_identity_near (K N : ℕ) {S T : Type*}
    (X : S → Matrix p p ℤ[X]) (A : S → Matrix p (Fin K) ℤ[X]) (A' : S → Matrix (Fin K) p ℤ[X])
    (Y : T → Matrix q q ℤ[X]) (B : T → Matrix (Fin K) q ℤ[X]) (B' : T → Matrix q (Fin K) ℤ[X]) :
    ∃ (g : ↥(goodT K N) × Fin (N + 1) → S → ℤ) (h : ↥(goodT K N) × Fin (N + 1) → T → ℤ), ∀ s t,
      (fromBlocks (X s) (A s * diagonal (fun r : Fin K => (Polynomial.X : ℤ[X]) ^ (2 * (r : ℕ) + 1)) * B t)
        (B' t * diagonal (fun r : Fin K => (Polynomial.X : ℤ[X]) ^ (2 * (r : ℕ) + 1)) * A' s) (Y t)).det.coeff N =
      ∑ k, g k s * h k t := by
  choose α β hαβ using fun T : Finset (Fin K ⊕ Fin K) => prop_identity_term_product (p := p) (q := q) (R := ℤ[X]) T
  refine ⟨fun k s => (α k.1 (X s) (A s) (A' s)).coeff k.2,
    fun k t => ((Polynomial.X : ℤ[X]) ^ (enT (k.1 : Finset (Fin K ⊕ Fin K))) *
      β k.1 (Y t) (B t) (B' t)).coeff (N - k.2), fun s t => ?_⟩
  rw [prop_identity_expand, Polynomial.finsetSum_coeff, Fintype.sum_prod_type]
  have hw : ∀ T : Finset (Fin K ⊕ Fin K),
      ∏ r ∈ T, Sum.elim (fun r : Fin K => (Polynomial.X : ℤ[X]) ^ (2 * (r : ℕ) + 1))
        (fun r : Fin K => (Polynomial.X : ℤ[X]) ^ (2 * (r : ℕ) + 1)) r = Polynomial.X ^ enT T := by
    intro T
    rw [enT, ← Finset.prod_pow_eq_pow_sum]
    refine Finset.prod_congr rfl fun r _ => ?_
    rcases r with r | r <;> rfl
  rw [← Finset.sum_subset (Finset.subset_univ (goodT K N)), ← Finset.sum_coe_sort]
  · refine Finset.sum_congr rfl fun T _ => ?_
    rw [hw, hαβ, mul_left_comm, Polynomial.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range]
  · intro T _ hT
    rw [hw]
    by_cases hb : T.toLeft.card = T.toRight.card
    · have : N < enT T := by
        by_contra hcon
        exact hT (mem_filter.2 ⟨mem_univ _, hb, not_lt.1 hcon⟩)
      rw [Polynomial.coeff_X_pow_mul', if_neg (not_le.2 this)]
    · rw [prop_identity_term_zero T hb, mul_zero, Polynomial.coeff_zero]

end Expansion

open Polynomial in
/-- Proof of Proposition prop:identity, the coefficients: "This proves (b)": the coefficient of X^N in Ψ is a sum of at most
(N+1)P(N) products of a function of (s_a, s_d) and one of (s_b, s_c). "This is used only for the coefficients of degree at most
N < 2R", with R = N + 1. -/
theorem prop_identity_coefficients (μ ν N : ℕ) :
    ∃ (g : Fin ((N + 1) * stateCount N) → Wd μ × Wd ν → ℤ) (h : Fin ((N + 1) * stateCount N) → Wd ν × Wd μ → ℤ),
      ∀ (sa : Wd μ) (sb : Wd ν) (sc : Wd μ) (sd : Wd ν),
        (psi (Polynomial.X : ℤ[X]) sa sb sc sd).coeff N = ∑ k, g k (sa, sd) * h k (sb, sc) := by
  obtain ⟨g, h, hgh⟩ := prop_identity_near (p := Fin μ ⊕ Fin ν) (q := Fin μ ⊕ Fin ν) (N + 1) N
    (S := Wd μ × Wd ν) (T := Wd ν × Wd μ)
    (fun s => blX X s.1 s.2) (fun s => facA (N + 1) X s.1 s.2)
    (fun s => (facA (N + 1) X s.1.swap s.2.swap)ᵀ)
    (fun t => blY X t.2 t.1) (fun t => facB (N + 1) X t.2 t.1)
    (fun t => -(facB (N + 1) X t.2.swap t.1.swap)ᵀ)
  have key : ∀ (sa : Wd μ) (sb : Wd ν) (sc : Wd μ) (sd : Wd ν),
      (psi (Polynomial.X : ℤ[X]) sa sb sc sd).coeff N = ∑ k, g k (sa, sd) * h k (sb, sc) := by
    intro sa sb sc sd
    rw [← hgh, ← sub_eq_zero, ← Polynomial.coeff_sub]
    refine (Polynomial.X_pow_dvd_iff (n := 2 * (N + 1))).1 ?_ N (by omega)
    refine dvd_det_sub _ _ _ fun i j => ?_
    rcases i with i | i <;> rcases j with j | j
    · simp [matM]
    · simpa only [matM, fromBlocks_apply₁₂] using prop_identity_blocks (N + 1) X sa sd sc sb i j
    · have := prop_identity_blocks (N + 1) (X : ℤ[X]) sa.swap sd.swap sc.swap sb.swap j i
      simp only [matM, fromBlocks_apply₂₁]
      rw [← dvd_neg] at this
      convert this using 1
      have e : ∀ (A : Matrix (Fin μ ⊕ Fin ν) (Fin (N + 1)) ℤ[X]) (l : Fin (N + 1) → ℤ[X])
          (B : Matrix (Fin (N + 1)) (Fin μ ⊕ Fin ν) ℤ[X]),
          -Bᵀ * diagonal l * Aᵀ = -(A * diagonal l * B)ᵀ := by
        intro A l B
        rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.diagonal_transpose, Matrix.neg_mul,
          Matrix.neg_mul, Matrix.mul_assoc]
      rw [e]
      simp only [Matrix.neg_apply, Matrix.transpose_apply]
      ring
    · simp [matM]
  have hcard : Fintype.card (↥(goodT (N + 1) N) × Fin (N + 1)) ≤ (N + 1) * stateCount N := by
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_coe, Nat.mul_comm]
    exact Nat.mul_le_mul_left _ (prop_identity_term_count _ _)
  obtain ⟨g', h', e⟩ := exists_products (f := fun (p : Wd μ × Wd ν) (q : Wd ν × Wd μ) =>
    (psi (Polynomial.X : ℤ[X]) p.1 q.1 q.2 p.2).coeff N) g h (fun p q => key p.1 q.1 q.2 p.2) hcard
  exact ⟨g', h', fun sa sb sc sd => e (sa, sd) (sb, sc)⟩

section reflect

open Polynomial

variable {μ ν : ℕ}

/-- The reflection identity for polynomials: the reverse of Ψ(X; s_a, s_b, s_c, s_d) is Ψ(X; s_a, s_d, s_c, s_b), up to powers
of X. -/
theorem prop_identity_reverse (sa : Wd μ) (sb : Wd ν) (sc : Wd μ) (sd : Wd ν) {e₁ e₂ : ℕ} (ha : enW sa = e₁)
    (hb : enW sb = e₂) (hc : enW sc = e₁) (hd : enW sd = e₂) :
    (psi (X : ℤ[X]) sa sb sc sd).reverse * X ^ (2 * (e₁ + e₂)) =
      psi (X : ℤ[X]) sa sd sc sb * X ^ (psi (X : ℤ[X]) sa sb sc sd).natDegree := by
  set P := psi (X : ℤ[X]) sa sb sc sd with hP
  set Q := psi (X : ℤ[X]) sa sd sc sb with hQ
  let F := FractionRing ℤ[X]
  let ι : ℤ[X] →+* F := algebraMap ℤ[X] F
  have hι : Function.Injective ι := IsFractionRing.injective ℤ[X] F
  let x : F := ι X
  have hx : x ≠ 0 := by
    intro h
    have : (X : ℤ[X]) = 0 := hι (by rw [map_zero]; exact h)
    exact X_ne_zero this
  have hxz : x * x⁻¹ = 1 := mul_inv_cancel₀ hx
  have hx1 : x ^ 2 ≠ 1 := by
    intro h
    have h1 : (X : ℤ[X]) ^ 2 = 1 := hι (by rw [map_pow, map_one]; exact h)
    have h2 := congrArg (fun p : ℤ[X] => p.coeff 2) h1
    simp [coeff_one] at h2
  have hi : ι = eval₂RingHom (Int.castRingHom F) x := by
    refine Polynomial.ringHom_ext (fun n => by simp) ?_
    simp [x]
  let φ : ℤ[X] →+* F := eval₂RingHom (Int.castRingHom F) x⁻¹
  have hφX : φ X = x⁻¹ := by simp [φ]
  let _ : Invertible (x⁻¹ : F) := ⟨x, hxz, by rw [mul_comm]; exact hxz⟩
  have hrev : ι P.reverse * (x⁻¹) ^ P.natDegree = φ P := by
    have := eval₂_reverse_mul_pow (Int.castRingHom F) (x⁻¹ : F) P
    rw [hi]
    simp only [φ, coe_eval₂RingHom]
    exact this
  have hz : psi (x⁻¹ : F) sa sb sc sd = φ P := by
    rw [hP, map_psi, hφX]
  have hxQ : psi x sa sd sc sb = ι Q := by
    rw [hQ, map_psi]
  have key := prop_identity_reflection hxz hx1 sa sb sc sd ha hb hc hd
  rw [hz, hxQ, ← hrev] at key
  apply hι
  rw [map_mul, map_mul, map_pow, map_pow, ← key]
  show ι P.reverse * x ^ _ = _ * x ^ _
  have : (x⁻¹) ^ P.natDegree * x ^ P.natDegree = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ hx, one_pow]
  linear_combination (-(ι P.reverse * x ^ (2 * (e₁ + e₂)))) * this

/-- Proof of Proposition prop:identity, reflection: "Hence deg Ψ ≤ Θ, and the coefficient of X^N at (s_a, s_b, s_c, s_d) is that
of X^(Θ−N) at (s_a, s_d, s_c, s_b)." -/
theorem prop_identity_reflection_coeff (sa : Wd μ) (sb : Wd ν) (sc : Wd μ) (sd : Wd ν) {e₁ e₂ : ℕ} (ha : enW sa = e₁)
    (hb : enW sb = e₂) (hc : enW sc = e₁) (hd : enW sd = e₂) :
    (psi (X : ℤ[X]) sa sb sc sd).natDegree ≤ 2 * (e₁ + e₂) ∧
    ∀ N M, N + M = 2 * (e₁ + e₂) →
      (psi (X : ℤ[X]) sa sb sc sd).coeff N = (psi (X : ℤ[X]) sa sd sc sb).coeff M := by
  have key := prop_identity_reverse sa sb sc sd ha hb hc hd
  set P := psi (X : ℤ[X]) sa sb sc sd with hP
  set Q := psi (X : ℤ[X]) sa sd sc sb with hQ
  set H := 2 * (e₁ + e₂) with hH
  have hdeg : P.natDegree ≤ H := by
    by_contra hcon
    have h1 := congrArg (fun p : ℤ[X] => p.coeff H) key
    simp only [coeff_mul_X_pow', le_refl, if_true, Nat.sub_self, hcon, if_false, coeff_zero_reverse,
      leadingCoeff_eq_zero] at h1
    rw [h1] at hcon
    simp at hcon
  refine ⟨hdeg, fun N M hNM => ?_⟩
  rcases le_or_gt N P.natDegree with hN | hN
  · have h1 := congrArg (fun p : ℤ[X] => p.coeff (H + (P.natDegree - N))) key
    simp only [coeff_mul_X_pow', Nat.le_add_right, if_true, Nat.add_sub_cancel_left] at h1
    rw [if_pos (by omega), coeff_reverse, revAt_le (Nat.sub_le _ _), Nat.sub_sub_self hN] at h1
    rw [h1]
    congr 1
    omega
  · rw [coeff_eq_zero_of_natDegree_lt hN]
    have h1 := congrArg (fun p : ℤ[X] => p.coeff (M + P.natDegree)) key
    simp only [coeff_mul_X_pow', Nat.le_add_left, if_true, Nat.add_sub_cancel] at h1
    rw [if_neg (by omega)] at h1
    exact h1

end reflect

/-- **Paper: Proposition prop:identity.** "Let Θ = 2(e₁+e₂). There are integral tensors Ψ_0, …, Ψ_Θ such that, all functions
below being integer valued, (a) ∑_N Ψ_N is ⟨|Σ₁|⟩_ac ⟨|Σ₂|⟩_bd; (b) Ψ_N is a sum of at most (N+1)P(N) products of a function of
(s_a, s_d) and one of (s_b, s_c); (c) Ψ_N is a sum of at most (N′+1)P(N′) products of a function of (s_a, s_b) and one of
(s_c, s_d), where N′ = Θ − N." -/
theorem prop_identity (μ ν e₁ e₂ : ℕ) :
    ∃ Ψ : Fin (2 * (e₁ + e₂) + 1) → ↥(states μ e₁) → ↥(states ν e₂) → ↥(states μ e₁) → ↥(states ν e₂) → ℤ,
      (∀ a b c d, ∑ N, Ψ N a b c d = (if a = c then 1 else 0) * (if b = d then 1 else 0)) ∧
      (∀ N : Fin (2 * (e₁ + e₂) + 1), ∃ (g : Fin ((N.1 + 1) * stateCount N) → ↥(states μ e₁) × ↥(states ν e₂) → ℤ)
        (h : Fin ((N.1 + 1) * stateCount N) → ↥(states ν e₂) × ↥(states μ e₁) → ℤ),
        ∀ a b c d, Ψ N a b c d = ∑ k, g k (a, d) * h k (b, c)) ∧
      (∀ N : Fin (2 * (e₁ + e₂) + 1), ∀ N', N' = 2 * (e₁ + e₂) - N.1 →
        ∃ (g : Fin ((N' + 1) * stateCount N') → ↥(states μ e₁) × ↥(states ν e₂) → ℤ)
        (h : Fin ((N' + 1) * stateCount N') → ↥(states μ e₁) × ↥(states ν e₂) → ℤ),
        ∀ a b c d, Ψ N a b c d = ∑ k, g k (a, b) * h k (c, d)) := by
  obtain ⟨ε, hε⟩ := prop_identity_one μ ν
  have hεε : ((ε : ℤˣ) : ℤ) * ε = 1 := Int.units_coe_mul_self ε
  have hrefl := fun (a : ↥(states μ e₁)) (b : ↥(states ν e₂)) (c : ↥(states μ e₁)) (d : ↥(states ν e₂)) =>
    prop_identity_reflection_coeff (word a) (word b) (word c).swap (word d).swap (enW_word a) (enW_word b)
      ((enW_swap _).trans (enW_word c)) ((enW_swap _).trans (enW_word d))
  refine ⟨fun N a b c d => ε * (psi (Polynomial.X : Polynomial ℤ) (word a) (word b) (word c).swap
    (word d).swap).coeff N, fun a b c d => ?_, fun N => ?_, fun N N' hN' => ?_⟩
  · rw [← Finset.mul_sum, Fin.sum_univ_eq_sum_range (fun N => (psi (Polynomial.X : Polynomial ℤ) (word a)
      (word b) (word c).swap (word d).swap).coeff N)]
    have h1 := Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le (hrefl a b c d).1) 1
    simp only [one_pow, mul_one] at h1
    rw [← Nat.succ_eq_add_one, ← h1, ← Polynomial.coe_evalRingHom, map_psi, Polynomial.coe_evalRingHom,
      Polynomial.eval_X, hε _ _ _ _ (word_strictMono a).1 (word_strictMono a).2 (word_strictMono b).1
      (word_strictMono b).2 (word_strictMono c).2 (word_strictMono c).1 (word_strictMono d).2
      (word_strictMono d).1, ← mul_assoc, hεε, one_mul, Prod.swap_swap, Prod.swap_swap]
    simp only [word_injective.eq_iff]
    rw [ite_and]
    split_ifs <;> simp only [mul_one, mul_zero]
  · obtain ⟨g, h, hgh⟩ := prop_identity_coefficients μ ν N
    refine ⟨fun k p => ε * g k (word p.1, (word p.2).swap), fun k p => h k (word p.1, (word p.2).swap),
      fun a b c d => ?_⟩
    simp only
    rw [hgh, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  · subst hN'
    obtain ⟨g, h, hgh⟩ := prop_identity_coefficients μ ν (2 * (e₁ + e₂) - N)
    refine ⟨fun k p => ε * g k (word p.1, word p.2), fun k p => h k ((word p.2).swap, (word p.1).swap),
      fun a b c d => ?_⟩
    simp only
    rw [(hrefl a b c d).2 N (2 * (e₁ + e₂) - N) (by omega), hgh, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring

end Paper
