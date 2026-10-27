/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import GeneralPieces.Series.OneLaurent
public import Mathlib.Data.Nat.Choose.Sum

/-! # Lemma 9 (Appendix B), on the operators Q_s: paragraph "Reading off" of its proof

For monomials a, b (lists of parts), `qP a b s π σ` is the entry ⟨Q_s(a,b)⟩ = Σ_i
(−1)^i·C(H,i)·⟨a[s−h+i]∘b[h−s−i]⟩, and `qM` is the same with the two factors exchanged.
Multiplying f₊ and f₋ by (ω₁ − ω₂)^H = Σ_i (−1)^i·C(H,i)·ω₁^{H−i}·ω₂^i (`dW_pow`) shows that the
coefficient of ω₁^s·ω₂^{−s} in F is both (`coeff_F_P`, `coeff_F_M`), and that F has no other
monomials (`coeff_F_of_ne`). This gives the three claims for monomials: `qP_eq_qM`, `qP_eq_zero`,
and `sum_qP` with the constant G of the expansion. -/

@[expose] public section

namespace GeneralPieces.Series

open ClauseBound.Boson Finset

theorem W_mul_W (x y x' y' : ℤ) : W x y * W x' y' = W (x + x') (y + y') := by
  rw [W, W, W, AddMonoidAlgebra.single_mul_single, one_mul, Prod.mk_add_mk]

theorem W_pow (x y : ℤ) (n : ℕ) : W x y ^ n = W (n * x) (n * y) := by
  rw [W, W, AddMonoidAlgebra.single_pow, one_pow]
  simp

/-- (ω₁ − ω₂)^H = Σ_i (−1)^i·C(H,i)·ω₁^{H−i}·ω₂^i. -/
theorem dW_pow (H : ℕ) : dW ^ H = ∑ i ∈ range (H + 1), ((-1) ^ i * (H.choose i : ℚ)) • W (H - i) i := by
  rw [dW, sub_eq_neg_add, add_pow]
  refine sum_congr rfl fun i hi => ?_
  have hi' : i ≤ H := Nat.lt_succ_iff.1 (mem_range.1 hi)
  rw [neg_pow, W_pow, W_pow, mul_assoc ((-1 : L) ^ i), W_mul_W, Algebra.smul_def, map_mul, map_pow, map_neg, map_one, map_natCast, Nat.cast_sub hi']
  simp only [mul_zero, mul_one, zero_add, add_zero]
  ring

/-- The coefficients of (ω₁ − ω₂)^H·f in 𝓛₊. -/
theorem cfP_dW_pow_mul (H : ℕ) (f : Lp) (x y : ℤ) :
    cfP (toP dW ^ H * f) x y = ∑ i ∈ range (H + 1), ((-1) ^ i * (H.choose i : ℚ)) * cfP f (x - (H - i)) (y - i) := by
  rw [← map_pow, dW_pow, map_sum, sum_mul, cfP, cf_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [map_smul, toP_W, smul_mul_assoc, cf_smul, cf_mo_mul, cfP]

/-- The coefficients of (ω₁ − ω₂)^H·f in 𝓛₋. -/
theorem cfM_dW_pow_mul (H : ℕ) (f : Lm) (x y : ℤ) :
    cfM (toM dW ^ H * f) x y = ∑ i ∈ range (H + 1), ((-1) ^ i * (H.choose i : ℚ)) * cfM f (x - (H - i)) (y - i) := by
  rw [← map_pow, dW_pow, map_sum, sum_mul, cfM, cf_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [map_smul, toM_W, smul_mul_assoc, cf_smul, cf_mo_mul, cfM]

/-- ⟨Q_s(a,b)⟩ for monomials a, b: Σ_{i ≤ H} (−1)^i·C(H,i)·⟨a[s−h+i]∘b[h−s−i]⟩. -/
def qP (a b : List ℕ) (s : ℤ) (π σ : Multiset ℕ) : ℤ :=
  ∑ i ∈ range (a.sum + b.sum + 1), (-1) ^ i * ((a.sum + b.sum).choose i : ℤ) * mul2 a (s - b.sum + i) b (b.sum - s - i) π σ

/-- The same with the two factors of every product exchanged. -/
def qM (a b : List ℕ) (s : ℤ) (π σ : Multiset ℕ) : ℤ :=
  ∑ i ∈ range (a.sum + b.sum + 1), (-1) ^ i * ((a.sum + b.sum).choose i : ℤ) * mul2 b (b.sum - s - i) a (s - b.sum + i) π σ

variable {a b : List ℕ} {G : ℚ} {π σ : Multiset ℕ}

/-- F_s = ⟨Q_s(a,b)⟩, from (ω₁ − ω₂)^H·f₊ = F. -/
theorem Expansion.coeff_F_P (X : Expansion a b G π σ) (s : ℤ) : X.F.coeff (s, -s) = qP a b s π σ := by
  rw [← cfP_toP, ← X.dW_pow_mul_fP, cfP_dW_pow_mul, qP, Int.cast_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [cfP_fP, if_pos (by push_cast; ring), show s - (((a.sum + b.sum : ℕ) : ℤ) - i) + a.sum = s - b.sum + i by push_cast; ring,
    show -s - (i : ℤ) + b.sum = b.sum - s - i by ring]
  push_cast
  ring

/-- F_s is also the sum with the factors exchanged, from (ω₁ − ω₂)^H·f₋ = F. -/
theorem Expansion.coeff_F_M (X : Expansion a b G π σ) (s : ℤ) : X.F.coeff (s, -s) = qM a b s π σ := by
  rw [← cfM_toM, ← X.dW_pow_mul_fM, cfM_dW_pow_mul, qM, Int.cast_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [cfM_fM, if_pos (by push_cast; ring), show s - (((a.sum + b.sum : ℕ) : ℤ) - i) + a.sum = s - b.sum + i by push_cast; ring,
    show -s - (i : ℤ) + b.sum = b.sum - s - i by ring]
  push_cast
  ring

/-- F has only monomials ω₁^s·ω₂^{−s}. -/
theorem Expansion.coeff_F_of_ne (X : Expansion a b G π σ) {x y : ℤ} (h : x + y ≠ 0) : X.F.coeff (x, y) = 0 := by
  rw [← cfP_toP, ← X.dW_pow_mul_fP, cfP_dW_pow_mul]
  refine sum_eq_zero fun i _ => ?_
  rw [cfP_fP, if_neg (fun g => h (by push_cast at g; linarith)), mul_zero]

/-- Claim (a) for monomials: Q_s(a,b) does not change if the two factors are exchanged in all
products at once. -/
theorem Expansion.qP_eq_qM (X : Expansion a b G π σ) (s : ℤ) : qP a b s π σ = qM a b s π σ :=
  Int.cast_injective (α := ℚ) (by rw [← X.coeff_F_P, X.coeff_F_M])

/-- For s > E + h all terms of the first sum vanish. -/
theorem qP_eq_zero_of_lt (a b : List ℕ) (π : Multiset ℕ) {σ : Multiset ℕ} {s : ℤ} (h : (σ.sum : ℤ) + b.sum < s) : qP a b s π σ = 0 :=
  sum_eq_zero fun i _ => by rw [mul2_eq_zero a b _ π (by omega), mul_zero]

/-- For s < −E − h all terms of the second sum vanish; here h' ≤ h is used. -/
theorem qM_eq_zero_of_lt {a b : List ℕ} (hab : a.sum ≤ b.sum) (π : Multiset ℕ) {σ : Multiset ℕ} {s : ℤ} (h : s < -(σ.sum : ℤ) - b.sum) : qM a b s π σ = 0 :=
  sum_eq_zero fun i hi => by
    have := mem_range.1 hi
    rw [mul2_eq_zero b a _ π (by omega), mul_zero]

/-- Claim (b) for monomials: Q_s(a,b) = 0 for |s| > E + h. -/
theorem Expansion.qP_eq_zero (X : Expansion a b G π σ) (hab : a.sum ≤ b.sum) {s : ℤ} (hs : (σ.sum : ℤ) + b.sum < |s|) : qP a b s π σ = 0 := by
  rcases lt_abs.1 hs with h | h
  · exact qP_eq_zero_of_lt a b π h
  · rw [X.qP_eq_qM, qM_eq_zero_of_lt hab π (by omega)]

/-- F = Σ_s F_s·ω₁^s·ω₂^{−s}, with F_s = ⟨Q_s(a,b)⟩. -/
theorem Expansion.F_eq (X : Expansion a b G π σ) (hab : a.sum ≤ b.sum) :
    X.F = ∑ s ∈ Icc (-((σ.sum : ℤ) + b.sum)) ((σ.sum : ℤ) + b.sum), (qP a b s π σ : ℚ) • W s (-s) := by
  ext ⟨x, y⟩
  rw [AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  simp only [W, AddMonoidAlgebra.coeff_smul, AddMonoidAlgebra.coeff_single, Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul, Prod.mk.injEq]
  by_cases h : x + y = 0
  · obtain rfl : y = -x := by omega
    rw [X.coeff_F_P, sum_eq_single x]
    · simp
    · intro s _ hs
      rw [if_neg (fun g => hs g.1), mul_zero]
    · intro hx
      rw [X.qP_eq_zero hab (by rw [mem_Icc, not_and_or] at hx; rcases hx with g | g; exacts [lt_abs.2 (Or.inr (by omega)), lt_abs.2 (Or.inl (by omega))])]
      simp
  · rw [X.coeff_F_of_ne h]
    exact (sum_eq_zero fun s _ => by rw [if_neg (fun g => h (by omega)), mul_zero]).symm

/-- Claim (c) for monomials, with the constant of the expansion: Σ_s ⟨Q_s(a,b)⟩ = F(1,1) = G·[π =
σ]. -/
theorem Expansion.sum_qP (X : Expansion a b G π σ) (hab : a.sum ≤ b.sum) :
    ∑ s ∈ Icc (-((σ.sum : ℤ) + b.sum)) ((σ.sum : ℤ) + b.sum), (qP a b s π σ : ℚ) = if π = σ then G else 0 := by
  rw [← X.ev_F, X.F_eq hab, map_sum]
  exact sum_congr rfl fun s _ => by rw [map_smul, ev_W, smul_eq_mul, mul_one]

end GeneralPieces.Series
