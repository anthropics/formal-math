/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import GeneralPieces.Rec.Chain
public import GeneralPieces.Num.PartAUse
public import ClauseBound.Gen.Rate
import all ClauseBound.Gen.Rate

/-! # Theorem A, part (b) (Appendix A): the arithmetic, for every x₀ ≥ 18 with 2^x₀ ≥ c + 5

This file follows the proof of part (b) of Theorem A in Appendix A, in its order, for pieces whose
numbers of bits are at most 2λ (`P.m = 1`). The sentences from "so again P = g³λ" to the display for
K²L, and that case (ii) of Lemma 8
applies at every level, are in `proof/rates/GeneralPieces/Rec/Chain.lean`; the display for K²L is
used here. Part (a) enters as e_ℓ ≥ 0, e_ℓ ≤ 1 and e_ℓ·K_ℓ ≥ 1
(`proof/rates/GeneralPieces/Num/PartAUse.lean`).
Notation of the paper: K = K_ℓ, g = g_ℓ, N = g⁴λ, Ξ = g²(λ + B), P = g³λ, B₁ = gB + g²(2λ)^c. L and
B' are the program's numbers `lamNextG` and `bNextG`: L is the lemma's L computed from the program's
upper
bound for U (see Chain.lean), and B' = P·q + (gB + g²·bits)·(q + q²)·K with q = ⌊2g/K⌋, which is not
the lemma's ⌈2gP/K⌉ + g²B₁ but obeys the same crude bound B' ≤ N + g²B₁ (`B'_le`), the only one
used.

What differs. The paper counts operations; here the algorithm is a program that runs in time
polynomial in the length of a pad, and `needG` is the exponent of a pad that is long enough.
So a product of costs in the paper is a sum of exponents here where the program really multiplies
(the number of instances, the recursion) and a maximum where it only needs room
(the groupings K^g, the states 2^{2N/K}, the time 2^{cλ} of the pieces). All instances of a level
are expanded before the next level starts, so their number `cnt` and the bit length `z` of
the sum so far are carried along: by induction on ℓ, for all λ ≥ 1 and all B, cnt, z,
  needG ≤ size cnt + size (z + size cnt) + e_ℓ·K_ℓ²·λ + (6c + 14)·K_ℓ²·log(K_ℓ(λ + B)).
The constant is C₀ = 6c + 17 in place of 2(c + C₄ + 1) + C₅. -/

public section

namespace GeneralPieces.Rate

open Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.Gen ClauseBound.Gen.Rate Levels.Gen

variable {P : PiecesF} {ρ : ℝ} {c x₀ : ℕ}

/-! ### Level 0 -/

/-- "For ℓ = 0, brute force sums 2^{λK₀(K₀−1)/2} ≤ 2^{e₀K₀²λ} terms". -/
theorem brute_le (ρ : ℝ) (x₀ lam : ℕ) : ((K x₀ 0 * (K x₀ 0 - 1) / 2 * lam : ℕ) : ℝ) ≤ e ρ x₀ 0 * (K x₀ 0 : ℝ) ^ 2 * lam := by
  have h1 : 2 * (K x₀ 0 * (K x₀ 0 - 1) / 2 * lam) ≤ K x₀ 0 ^ 2 * lam := by
    calc 2 * (K x₀ 0 * (K x₀ 0 - 1) / 2 * lam) = 2 * (K x₀ 0 * (K x₀ 0 - 1) / 2) * lam := by ring
      _ ≤ K x₀ 0 * (K x₀ 0 - 1) * lam := Nat.mul_le_mul_right _ (Nat.mul_div_le _ _)
      _ ≤ K x₀ 0 * K x₀ 0 * lam := by gcongr; exact Nat.sub_le _ _
      _ = K x₀ 0 ^ 2 * lam := by ring
  have h2 : 2 * ((K x₀ 0 * (K x₀ 0 - 1) / 2 * lam : ℕ) : ℝ) ≤ (K x₀ 0 : ℝ) ^ 2 * lam := by exact_mod_cast h1
  rw [show e ρ x₀ 0 = 1 / 2 from rfl]
  linarith

/-- The first budget (room for the instances of the level) is within the bound. The inequality
e_ℓ·K_ℓ ≥ 1 is taken from part (a). -/
theorem first_le (hρ : 1 / 2 ≤ ρ) (hρ1 : ρ < 1) (hx : 18 ≤ x₀) (l lam B cnt z : ℕ) (hlam : 1 ≤ lam) :
    ((max (Nat.size (cnt * instLen (K x₀ l) lam B + 8 * z + 4 * lam + 40)) (max lam (max (Nat.size B) (Nat.size (K x₀ l)))) : ℕ) : ℝ) ≤
      Nat.size cnt + Nat.size (z + Nat.size cnt) + Bd ρ c x₀ l lam B := by
  have hK := big_le_K hx l
  have hL1 := one_le_log hx l lam B hlam
  have hX : ((K x₀ l * (lam + B) : ℕ) : ℝ) = (K x₀ l : ℝ) * (lam + B) := by push_cast; ring
  have hX1 : 1 ≤ K x₀ l * (lam + B) := Nat.mul_pos (by omega) (by omega)
  have hs := small_le_sq (K x₀ l) lam B (by omega) hlam
  have s1 := size_cast_le hX1 hs.1
  have s2 := size_cast_le hX1 hs.2
  have s3 : (Nat.size B : ℝ) ≤ (1 : ℕ) * Real.logb 2 ((K x₀ l * (lam + B) : ℕ) : ℝ) + 1 := by
    apply size_cast_le hX1
    rw [pow_one]
    calc B ≤ lam + B := Nat.le_add_left _ _
      _ ≤ K x₀ l * (lam + B) := Nat.le_mul_of_pos_left _ (by omega)
  have s4 : (Nat.size (K x₀ l) : ℝ) ≤ (1 : ℕ) * Real.logb 2 ((K x₀ l * (lam + B) : ℕ) : ℝ) + 1 := by
    apply size_cast_le hX1
    rw [pow_one]
    exact Nat.le_mul_of_pos_right _ (by omega)
  rw [hX] at s1 s2 s3 s4
  have hf : (Nat.size (cnt * instLen (K x₀ l) lam B + 8 * z + 4 * lam + 40) : ℝ) ≤
      Nat.size cnt + Nat.size z + (((K x₀ l - 1) * lam : ℕ) : ℝ) + Nat.size (4 * lam + K x₀ l * (3 * B + 14) + 10) + Nat.size (4 * lam + 40) + 4 := by
    exact_mod_cast size_first_le (K x₀ l) lam B cnt z
  have hz : (Nat.size z : ℝ) ≤ Nat.size (z + Nat.size cnt) := by exact_mod_cast Nat.size_le_size (Nat.le_add_right _ _)
  have hkl : (((K x₀ l - 1) * lam : ℕ) : ℝ) ≤ (K x₀ l : ℝ) * lam := by
    exact_mod_cast Nat.mul_le_mul_right _ (Nat.sub_le _ _)
  have hk1 : (1 : ℝ) ≤ K x₀ l := by exact_mod_cast (by omega : 1 ≤ K x₀ l)
  have hlm : (1 : ℝ) ≤ lam := by exact_mod_cast hlam
  have he : (K x₀ l : ℝ) * lam ≤ e ρ x₀ l * (K x₀ l : ℝ) ^ 2 * lam := by
    have h := mul_le_mul_of_nonneg_right (PartAUse.one_le_e_mul_K (PartA.thmRunningTime_a ρ x₀ hρ hρ1 hx) hρ hx l) (by positivity : (0 : ℝ) ≤ (K x₀ l : ℝ) * lam)
    calc (K x₀ l : ℝ) * lam = 1 * ((K x₀ l : ℝ) * lam) := by ring
      _ ≤ e ρ x₀ l * K x₀ l * ((K x₀ l : ℝ) * lam) := h
      _ = e ρ x₀ l * (K x₀ l : ℝ) ^ 2 * lam := by ring
  have hl' : (lam : ℝ) ≤ (K x₀ l : ℝ) * lam := le_mul_of_one_le_left (by positivity) hk1
  unfold Bd
  generalize Real.logb 2 ((K x₀ l : ℝ) * (lam + B)) = L at *
  have hCL : 10 * L ≤ (6 * c + 14) * (K x₀ l : ℝ) ^ 2 * L := by
    have h1 : (1 : ℝ) ≤ (K x₀ l : ℝ) ^ 2 := one_le_pow₀ hk1
    have h2 : (0 : ℝ) ≤ c := by positivity
    have h3 : (10 : ℝ) ≤ (6 * c + 14) * (K x₀ l : ℝ) ^ 2 := by nlinarith
    exact mul_le_mul_of_nonneg_right h3 (by linarith)
  have p1 : (0 : ℝ) ≤ Nat.size cnt := by positivity
  have p2 : (0 : ℝ) ≤ Nat.size (z + Nat.size cnt) := by positivity
  push_cast at s1 s2 s3 s4
  rw [Nat.cast_max, Nat.cast_max, Nat.cast_max]
  refine max_le ?_ (max_le ?_ (max_le ?_ ?_)) <;> linarith

/-- The induction starts: the first budget, and brute force. -/
theorem base_le (hρ : 1 / 2 ≤ ρ) (hρ1 : ρ < 1) (hx : 18 ≤ x₀) (lam B cnt z : ℕ) (hlam : 1 ≤ lam) :
    (needG P (K x₀ 0) lam B cnt z (sched P x₀ 0) : ℝ) ≤ Nat.size cnt + Nat.size (z + Nat.size cnt) + Bd ρ c x₀ 0 lam B := by
  have hfirst := first_le (ρ := ρ) (c := c) hρ hρ1 hx 0 lam B cnt z hlam
  rw [show sched P x₀ 0 = [] from rfl, needG, Nat.cast_max]
  refine max_le hfirst ?_
  have hL1 := one_le_log hx 0 lam B hlam
  have h2 := brute_le ρ x₀ lam
  have p1 : (0 : ℝ) ≤ Nat.size cnt := by positivity
  have p2 : (0 : ℝ) ≤ Nat.size (z + Nat.size cnt) := by positivity
  have p3 : 0 ≤ (6 * (c : ℝ) + 14) * (K x₀ 0 : ℝ) ^ 2 * Real.logb 2 ((K x₀ 0 : ℝ) * (lam + B)) := by
    have : 0 ≤ Real.logb 2 ((K x₀ 0 : ℝ) * (lam + B)) := by linarith
    positivity
  unfold Bd
  linarith

/-! ### The number of terms of the sum over ι -/

/-- "The |I|^{|R|} ≤ Ξ^{cg⁴/4} functions ι". -/
theorem nPat_le_quarter (hP : Par P ρ c) (hx : 18 ≤ x₀) (l lam B : ℕ) (hlam : 1 ≤ lam) :
    nPat P (step P x₀ l) lam ≤ (g x₀ l ^ 2 * (lam + B)) ^ (c * (g x₀ l ^ 4 / 4)) := by
  refine (nPat_le hP hx l lam B hlam).trans (Nat.pow_le_pow_right ?_ (Nat.mul_le_mul_left _ ?_))
  · have := two_lam_le hx l lam B; omega
  · have := four_nRect_le (g x₀ l); omega

/-- In exponents: the bit length of the number of terms is at most c·g⁴·log Ξ + 1. -/
theorem size_nPat_le (hP : Par P ρ c) (hx : 18 ≤ x₀) (l lam B : ℕ) (hlam : 1 ≤ lam) :
    (Nat.size (nPat P (step P x₀ l) lam) : ℝ) ≤ c * (g x₀ l : ℝ) ^ 4 * Real.logb 2 ((K x₀ (l + 1) : ℝ) * (lam + B)) + 1 := by
  have hX1 : 1 ≤ g x₀ l ^ 2 * (lam + B) := by have := two_lam_le hx l lam B; omega
  have h := size_cast_le hX1 (nPat_le_quarter hP hx l lam B hlam)
  rw [X_cast] at h
  have hL := one_le_log hx (l + 1) lam B hlam
  have hR : ((c * (g x₀ l ^ 4 / 4) : ℕ) : ℝ) ≤ c * (g x₀ l : ℝ) ^ 4 := by
    exact_mod_cast Nat.mul_le_mul_left c (Nat.div_le_self (g x₀ l ^ 4) 4)
  have := mul_le_mul_of_nonneg_right hR (by linarith : 0 ≤ Real.logb 2 ((K x₀ (l + 1) : ℝ) * (lam + B)))
  linarith

/-- The bit length of the number of instances one level down. -/
theorem size_cnt_le (hP : Par P ρ c) (hx : 18 ≤ x₀) (l lam B cnt : ℕ) (hlam : 1 ≤ lam) :
    (Nat.size (cnt * nPat P (step P x₀ l) lam) : ℝ) ≤
      Nat.size cnt + (c * (g x₀ l : ℝ) ^ 4 * Real.logb 2 ((K x₀ (l + 1) : ℝ) * (lam + B)) + 1) := by
  have H1 : (Nat.size (cnt * nPat P (step P x₀ l) lam) : ℝ) ≤ Nat.size cnt + Nat.size (nPat P (step P x₀ l) lam) := by
    exact_mod_cast size_mul_le cnt _
  have H1r := size_nPat_le hP hx l lam B hlam
  linarith

/-! ### The label length L one level down -/

/-- "We have c^row ≤ 2λ as before": the two numbers of bits of a piece add up to at most 4λ. -/
theorem capSum_le_four (hP : Par P ρ c) (hm : P.m = 1) (lam : ℕ) (hlam : 1 ≤ lam) : capSum P 0 lam ≤ 4 * lam := by
  unfold capSum
  apply Finset.sup_le
  intro i hi
  have hi' := Finset.mem_range.1 hi
  have h1 := (hP.spec 0 lam hlam).cap_le false i hi'
  have h2 := (hP.spec 0 lam hlam).cap_le true i hi'
  rw [hm] at h1 h2
  omega

/-- The display "K²L ≤ U + 2ζN + K² ≤ (ρ + 3ζ)N + (c/4)g⁴·log(2λ) + K²"
(`GeneralPieces.Chain.K_sq_L_le`), with log Ξ in place of log(2λ). -/
theorem K2L_le' (hP : Par P ρ c) (hm : P.m = 1) (hx : 18 ≤ x₀) (l lam B : ℕ) (hlam : 1 ≤ lam) :
    (K x₀ l : ℝ) ^ 2 * lamNextG P (step P x₀ l) lam ≤ (ρ + 3 * zeta l) * ((g x₀ l : ℝ) ^ 4 * lam) +
      c / 4 * (g x₀ l : ℝ) ^ 4 * Real.logb 2 ((K x₀ (l + 1) : ℝ) * (lam + B)) + (K x₀ l : ℝ) ^ 2 := by
  have hlm : (1 : ℝ) ≤ lam := by exact_mod_cast hlam
  have hlog : Real.logb 2 (2 * (lam : ℝ)) ≤ Real.logb 2 ((K x₀ (l + 1) : ℝ) * (lam + B)) := by
    have h : ((2 * lam : ℕ) : ℝ) ≤ ((g x₀ l ^ 2 * (lam + B) : ℕ) : ℝ) := by exact_mod_cast two_lam_le hx l lam B
    rw [X_cast] at h
    push_cast at h
    exact Real.logb_le_logb_of_le (by norm_num) (by positivity) h
  have h1 := Chain.K_sq_L_le hP hm x₀ l lam hx hlam
  have h2 := mul_le_mul_of_nonneg_left hlog (by positivity : 0 ≤ (c : ℝ) / 4 * (g x₀ l : ℝ) ^ 4)
  linarith

/-! ### The crude bounds -/

/-- L ≤ N + 1 in plain variables. -/
theorem L_aux (D k a R u lam S : ℕ) (hD : 3 ≤ D) (hk : 2 ≤ k) (hS : S ≤ a ^ 4 * lam) (hR : 4 * R ≤ a ^ 4) (hu : u ≤ 4 * lam) :
    (D * (S + R * u) + 3 * a ^ 2 * (a ^ 2 * (1 * lam))) / (D * k ^ 2) ≤ a ^ 4 * lam := by
  apply Nat.div_le_of_le_mul
  have h1 : R * u ≤ a ^ 4 * lam := by
    calc R * u ≤ R * (4 * lam) := Nat.mul_le_mul_left _ hu
      _ = 4 * R * lam := by ring
      _ ≤ a ^ 4 * lam := Nat.mul_le_mul_right _ hR
  have h2 : 3 ≤ k ^ 2 := by nlinarith
  calc D * (S + R * u) + 3 * a ^ 2 * (a ^ 2 * (1 * lam))
      = D * (S + R * u) + 3 * (a ^ 4 * lam) := by ring
    _ ≤ D * (a ^ 4 * lam + a ^ 4 * lam) + D * (a ^ 4 * lam) := by gcongr
    _ = D * 3 * (a ^ 4 * lam) := by ring
    _ ≤ D * k ^ 2 * (a ^ 4 * lam) := by gcongr

/-- "Crude bounds give L ≤ N + 1". -/
theorem L_le (hP : Par P ρ c) (hm : P.m = 1) (hx : 18 ≤ x₀) (l lam : ℕ) (hlam : 1 ≤ lam) :
    lamNextG P (step P x₀ l) lam ≤ g x₀ l ^ 4 * lam + 1 := by
  rw [lamNext_eq, hm]
  have hK := big_le_K hx l
  have hg : 1 ≤ g x₀ l := le_trans (by omega) (K_le_g x₀ l)
  refine Nat.add_le_add_right (L_aux _ _ _ _ _ _ _ ?_ (by omega) ?_ (four_nRect_le _) (capSum_le_four hP hm lam hlam)) 1
  · have : 1 ≤ 2 ^ (l + 4) := Nat.one_le_two_pow
    omega
  · calc g x₀ l * (g x₀ l - 1) * g x₀ l * lam ≤ g x₀ l * g x₀ l * g x₀ l * lam := by gcongr; exact Nat.sub_le _ _
      _ = 1 * g x₀ l ^ 3 * lam := by ring
      _ ≤ g x₀ l * g x₀ l ^ 3 * lam := by gcongr
      _ = g x₀ l ^ 4 * lam := by ring

/-- B' ≤ N + g²B₁ in plain variables; q = 2g/K. -/
theorem B_aux (k a q lam B₁ : ℕ) (hk : 8 ≤ k) (ha : 4 ≤ a) (hq : q * k ≤ 2 * a) :
    1 * (a * a ^ 2 * lam) * q + B₁ * (q + q * q) * k ≤ a ^ 4 * lam + a ^ 2 * B₁ := by
  have h8 : q * 8 ≤ q * k := Nat.mul_le_mul_left _ hk
  have h1 : q ≤ a := by omega
  have h2 : 2 * (1 + q) ≤ a := by omega
  have h3 : (q + q * q) * k ≤ a ^ 2 := by
    calc (q + q * q) * k = (1 + q) * (q * k) := by ring
      _ ≤ (1 + q) * (2 * a) := Nat.mul_le_mul_left _ hq
      _ = 2 * (1 + q) * a := by ring
      _ ≤ a * a := Nat.mul_le_mul_right _ h2
      _ = a ^ 2 := by ring
  calc 1 * (a * a ^ 2 * lam) * q + B₁ * (q + q * q) * k = a * a ^ 2 * lam * q + B₁ * ((q + q * q) * k) := by ring
    _ ≤ a * a ^ 2 * lam * a + B₁ * a ^ 2 := by gcongr
    _ = a ^ 4 * lam + a ^ 2 * B₁ := by ring

/-- "Crude bounds give B' ≤ N + g²B₁", with B₁ = gB + g²(2λ)^c. -/
theorem B'_le (hP : Par P ρ c) (hm : P.m = 1) (hx : 18 ≤ x₀) (l lam B : ℕ) (hlam : 1 ≤ lam) :
    bNextG P (step P x₀ l) lam B ≤ g x₀ l ^ 4 * lam + g x₀ l ^ 2 * (g x₀ l * B + g x₀ l ^ 2 * (2 * lam) ^ c) := by
  rw [bNext_eq, hm]
  have hK := big_le_K hx l
  have hg := K_le_g x₀ l
  refine (B_aux (K x₀ l) (g x₀ l) _ lam _ (by omega) (by omega) (Nat.div_mul_le_self _ _)).trans ?_
  have := hP.bits 0 lam hlam
  gcongr

/-- The crude bounds g(P + B₁) ≤ Ξ^{c+4} and K(L + B') ≤ Ξ^{c+5} in plain variables. -/
theorem crude_aux (k a c lam B L B' : ℕ) (hlam : 1 ≤ lam) (hka : k ≤ a) (ha : 4 ≤ a) (hL : L ≤ a ^ 4 * lam + 1)
    (hB : B' ≤ a ^ 4 * lam + a ^ 2 * (a * B + a ^ 2 * (2 * lam) ^ c)) :
    a * (a ^ 3 * lam + (a * B + a ^ 2 * (2 * lam) ^ c)) ≤ (a ^ 2 * (lam + B)) ^ (c + 4) ∧ k * (L + B') ≤ (a ^ 2 * (lam + B)) ^ (c + 5) := by
  obtain ⟨A, hA⟩ : ∃ A, A = a ^ 2 := ⟨_, rfl⟩
  have haA : a ≤ A := by rw [hA, sq]; exact Nat.le_mul_of_pos_left _ (by omega)
  have e4 : a ^ 4 = A * A := by rw [hA]; ring
  have e3 : a * a ^ 3 = A * A := by rw [hA]; ring
  have e2 : a * a = A := by rw [hA]; ring
  rw [e4] at hL hB
  rw [← hA] at hB ⊢
  obtain ⟨X, hX⟩ : ∃ X, X = A * (lam + B) := ⟨_, rfl⟩
  rw [← hX]
  have hAX : A ≤ X := by rw [hX]; exact Nat.le_mul_of_pos_right _ (by omega)
  have hX5 : 5 ≤ X := by nlinarith
  obtain ⟨Y, hY⟩ : ∃ Y, Y = X ^ c := ⟨_, rfl⟩
  have hY1 : 1 ≤ Y := by rw [hY]; exact Nat.one_le_pow _ _ (by omega)
  have h1 : A * lam ≤ X := by rw [hX]; exact Nat.mul_le_mul_left _ (by omega)
  have h2 : A * B ≤ X := by rw [hX]; exact Nat.mul_le_mul_left _ (by omega)
  have h2l : 2 * lam ≤ X := le_trans (Nat.mul_le_mul_right _ (by omega)) h1
  have ht : (2 * lam) ^ c ≤ Y := by rw [hY]; exact Nat.pow_le_pow_left h2l c
  generalize (2 * lam) ^ c = t at *
  have hN : A * A * lam ≤ X * X * Y := by
    calc A * A * lam = A * (A * lam) * 1 := by ring
      _ ≤ X * X * Y := by gcongr
  have hXX : X ≤ X * X * Y := by
    calc X = 1 * X * 1 := by ring
      _ ≤ X * X * Y := by gcongr; omega
  have hT : A * A * t ≤ X * X * Y := by gcongr
  have p4 : X ^ (c + 4) = X * X * (X * X * Y) := by rw [hY]; ring
  have p5 : X ^ (c + 5) = X * (X * X) * (X * X * Y) := by rw [hY]; ring
  have hXX5 : 5 ≤ X * X := by nlinarith
  constructor
  · rw [p4]
    calc a * (a ^ 3 * lam + (a * B + A * t)) = a * a ^ 3 * lam + (a * a * B + a * A * t) := by ring
      _ = A * A * lam + (A * B + a * A * t) := by rw [e3, e2]
      _ ≤ X * X * Y + (X * X * Y + A * A * t) :=
          Nat.add_le_add hN (Nat.add_le_add (h2.trans hXX) (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ haA)))
      _ ≤ X * X * Y + (X * X * Y + X * X * Y) := by omega
      _ = 3 * (X * X * Y) := by ring
      _ ≤ X * X * (X * X * Y) := Nat.mul_le_mul_right _ (by omega)
  · rw [p5]
    have hs : L + B' ≤ 5 * (X * X * Y) := by
      have h3 : A * (a * B + A * t) ≤ 2 * (X * X * Y) := by
        calc A * (a * B + A * t) = a * (A * B) + A * A * t := by ring
          _ ≤ X * X * 1 + X * X * Y := Nat.add_le_add (by rw [mul_one]; exact Nat.mul_le_mul (haA.trans hAX) h2) hT
          _ ≤ X * X * Y + X * X * Y := Nat.add_le_add_right (Nat.mul_le_mul_left _ hY1) _
          _ = 2 * (X * X * Y) := by ring
      have h4 : 1 ≤ X * X * Y := le_trans (by omega) hXX
      omega
    calc k * (L + B') ≤ X * (5 * (X * X * Y)) := Nat.mul_le_mul (hka.trans (haA.trans hAX)) hs
      _ = X * 5 * (X * X * Y) := by ring
      _ ≤ X * (X * X) * (X * X * Y) := by gcongr

/-- "Crude bounds give K(L + B') ≤ Ξ^{c+5}". -/
theorem KLB_le (hP : Par P ρ c) (hm : P.m = 1) (hx : 18 ≤ x₀) (l lam B : ℕ) (hlam : 1 ≤ lam) :
    K x₀ l * (lamNextG P (step P x₀ l) lam + bNextG P (step P x₀ l) lam B) ≤ (g x₀ l ^ 2 * (lam + B)) ^ (c + 5) := by
  have hK := big_le_K hx l
  have hg := K_le_g x₀ l
  exact (crude_aux (K x₀ l) (g x₀ l) c lam B _ _ hlam hg (by omega) (L_le hP hm hx l lam hlam) (B'_le hP hm hx l lam B hlam)).2

/-- log(K(L + B')) ≤ (c + 5)·log Ξ. -/
theorem log_child (hP : Par P ρ c) (hm : P.m = 1) (hx : 18 ≤ x₀) (l lam B : ℕ) (hlam : 1 ≤ lam) :
    Real.logb 2 ((K x₀ l : ℝ) * ((lamNextG P (step P x₀ l) lam : ℝ) + (bNextG P (step P x₀ l) lam B : ℝ))) ≤
      (c + 5) * Real.logb 2 ((K x₀ (l + 1) : ℝ) * (lam + B)) := by
  have h3 := big_le_K hx l
  have hn := KLB_le hP hm hx l lam B hlam
  have hpos : 0 < K x₀ l * (lamNextG P (step P x₀ l) lam + bNextG P (step P x₀ l) lam B) :=
    Nat.mul_pos (by omega) (by have := one_le_lamNext P (step P x₀ l) lam; omega)
  have hr : ((K x₀ l * (lamNextG P (step P x₀ l) lam + bNextG P (step P x₀ l) lam B) : ℕ) : ℝ) ≤
      (((g x₀ l ^ 2 * (lam + B)) ^ (c + 5) : ℕ) : ℝ) := by exact_mod_cast hn
  have h5 := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by exact_mod_cast hpos) hr
  rw [Nat.cast_pow, Real.logb_pow, X_cast] at h5
  push_cast at h5
  exact h5

/-! ### The cost 𝒯 one level down -/

/-- The display for 𝒯 in real variables: k2 = K², G4 = g⁴, L = log Ξ, lg = log(K(L + B')). -/
theorem T_aux (e0 r N k2 G4 L c lam' lg C : ℝ) (he0 : 0 ≤ e0) (he1 : e0 ≤ 1)
    (H3 : k2 * lam' ≤ r * N + c / 4 * G4 * L + k2) (H4 : lg ≤ (c + 5) * L) (hL : 1 ≤ L) (hk2 : 0 ≤ k2) (hG : 0 ≤ G4) (hc : 0 ≤ c) (hC : 0 ≤ C) :
    e0 * k2 * lam' + C * k2 * lg ≤ e0 * r * N + (c / 4 * G4 + k2 + (c + 5) * C * k2) * L := by
  have a1 : e0 * (k2 * lam') ≤ e0 * (r * N + c / 4 * G4 * L + k2) := mul_le_mul_of_nonneg_left H3 he0
  have a2 : e0 * (c / 4 * G4 * L + k2) ≤ c / 4 * G4 * L + k2 := mul_le_of_le_one_left (by positivity) he1
  have a4 : C * k2 * lg ≤ C * k2 * ((c + 5) * L) := mul_le_mul_of_nonneg_left H4 (by positivity)
  have a5 : k2 ≤ k2 * L := le_mul_of_one_le_right hk2 hL
  nlinarith

/-! ### The budgets of size N/K -/

/-- c ≤ K_ℓ. -/
theorem c_le_K (hx : 18 ≤ x₀) (hc : c + 5 ≤ 2 ^ x₀) (l : ℕ) : c ≤ K x₀ l := by
  have := pow_le_K hx l; omega

/-- "cλ ≤ N/K". -/
theorem c_lam_le (hx : 18 ≤ x₀) (hc : c + 5 ≤ 2 ^ x₀) (l lam : ℕ) : K x₀ l * (c * lam) ≤ g x₀ l ^ 4 * lam := by
  have h1 := c_le_K hx hc l
  have h2 := K_le_g x₀ l
  have h3 : 1 ≤ g x₀ l := le_trans (by have := big_le_K hx l; omega) h2
  calc K x₀ l * (c * lam) = K x₀ l * c * 1 * lam := by ring
    _ ≤ g x₀ l * g x₀ l * g x₀ l ^ 2 * lam := by
        gcongr
        · exact h1.trans h2
        · exact Nat.one_le_pow _ _ h3
    _ = g x₀ l ^ 4 * lam := by ring

/-- 3 ≤ e_{ℓ+1}·K_ℓ: the term 3/K_ℓ of e_{ℓ+1} pays for 2^{2N/K + cλ} in the paper; here each of the
budgets of size N/K fits under e_{ℓ+1}·N by itself. -/
theorem three_le (hA : PartA.TheoremAa ρ x₀) (hρ : 0 ≤ ρ) (l : ℕ) : 3 ≤ e ρ x₀ (l + 1) * K x₀ l := by
  have hK : (0 : ℝ) < K x₀ l := by rw [K_cast]; positivity
  have h1 : 0 ≤ (ρ + 3 * zeta l) * e ρ x₀ l * K x₀ l :=
    mul_nonneg (mul_nonneg (by have := zeta_pos l; linarith) (PartAUse.e_nonneg hA hρ l)) hK.le
  have h2 : e ρ x₀ (l + 1) * K x₀ l = (ρ + 3 * zeta l) * e ρ x₀ l * K x₀ l + 3 := by rw [e]; field_simp
  linarith

/-- The budget of the states of a merged part, times K: at most 3N. -/
theorem st_le (hm : P.m = 1) (l lam : ℕ) :
    (K x₀ l : ℝ) * ((P.m * (g x₀ l * g x₀ l ^ 2 * lam) * (2 * g x₀ l / K x₀ l + 1) : ℕ) : ℝ) ≤ 3 * ((g x₀ l : ℝ) ^ 4 * lam) := by
  have n4 := K_le_g x₀ l
  have hq : K x₀ l * (2 * g x₀ l / K x₀ l) ≤ 2 * g x₀ l := Nat.mul_div_le _ _
  have h : K x₀ l * (P.m * (g x₀ l * g x₀ l ^ 2 * lam) * (2 * g x₀ l / K x₀ l + 1)) ≤ 3 * (g x₀ l ^ 4 * lam) := by
    rw [hm]
    calc K x₀ l * (1 * (g x₀ l * g x₀ l ^ 2 * lam) * (2 * g x₀ l / K x₀ l + 1))
        = (g x₀ l * g x₀ l ^ 2 * lam) * (K x₀ l * (2 * g x₀ l / K x₀ l) + K x₀ l) := by ring
      _ ≤ (g x₀ l * g x₀ l ^ 2 * lam) * (3 * g x₀ l) := Nat.mul_le_mul_left _ (by omega)
      _ = 3 * (g x₀ l ^ 4 * lam) := by ring
  exact_mod_cast h

/-- If k·v ≤ 3N and 3 ≤ e'·k then v ≤ e'·N. -/
theorem le_of_K_mul (k v N e' : ℝ) (hk : 0 < k) (h3 : 3 ≤ e' * k) (hN : 0 ≤ N) (hv : k * v ≤ 3 * N) : v ≤ e' * N := by
  have h : k * v ≤ k * (e' * N) := by
    calc k * v ≤ 3 * N := hv
      _ ≤ e' * k * N := mul_le_mul_of_nonneg_right h3 hN
      _ = k * (e' * N) := by ring
  exact le_of_mul_le_mul_left h hk

/-- The budget (K − 1)·L of a table one level down. -/
theorem tab_aux (k v r N c G4 L e' : ℝ) (hk : 1 ≤ k) (hv : k * v ≤ r * N + c / 4 * G4 * L + k ^ 2) (hr : r ≤ 2) (hc : 0 ≤ c)
    (h3 : 3 ≤ e' * k) (hN : 0 ≤ N) (hkG : k ≤ G4) (hL : 1 ≤ L) : v ≤ e' * N + (6 * c + 14) * G4 * L := by
  have hG0 : 0 ≤ G4 := by linarith
  have h1 : r * N ≤ e' * k * N := mul_le_mul_of_nonneg_right (by linarith) hN
  have hGL : G4 ≤ G4 * L := le_mul_of_one_le_right hG0 hL
  have hGL0 : 0 ≤ G4 * L := by linarith
  have hcGL : 0 ≤ c * (G4 * L) := mul_nonneg hc hGL0
  have h2 : 6 * (c * (G4 * L)) ≤ k * (6 * (c * (G4 * L))) := le_mul_of_one_le_left (by linarith) hk
  have h3 : k * k ≤ k * (G4 * L) := mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have h4 : 0 ≤ k * (G4 * L) := mul_nonneg (by linarith) hGL0
  have h : k * v ≤ k * (e' * N + (6 * c + 14) * G4 * L) := by nlinarith
  exact le_of_mul_le_mul_left h (by linarith)

/-! ### The exponent of Ξ -/

/-- "(c + 5)K² ≤ 2^{x₀}K² ≤ g⁴/2". -/
theorem half_const (hx : 18 ≤ x₀) (hc : c + 5 ≤ 2 ^ x₀) (l : ℕ) :
    (c + 5) * K x₀ l ^ 2 ≤ 2 ^ x₀ * K x₀ l ^ 2 ∧ 2 * (2 ^ x₀ * K x₀ l ^ 2) ≤ g x₀ l ^ 4 := by
  refine ⟨Nat.mul_le_mul_right _ hc, ?_⟩
  have h2 := pow_le_K hx l
  have h3 := big_le_K hx l
  have h4 := K_le_g x₀ l
  calc 2 * (2 ^ x₀ * K x₀ l ^ 2) = 2 * 2 ^ x₀ * K x₀ l ^ 2 := by ring
    _ ≤ g x₀ l * g x₀ l * g x₀ l ^ 2 := by
        gcongr
        · omega
        · omega
    _ = g x₀ l ^ 4 := by ring

/-- "The exponent of Ξ is at most (c + C₄ + 1)g⁴ + ½C₀g⁴ ≤ C₀g⁴ by the choice of C₀", together with
e(ρ + 3ζ) ≤ e_{ℓ+1}: the number of instances, the bit length of the sum so far and the
exponent one level down. Here k2 = K², G4 = g⁴, L = log Ξ, lg = log(K(L + B')). -/
theorem exponent_le (e0 e' r N k2 G4 L c lam' lg : ℝ) (he0 : 0 ≤ e0) (he1 : e0 ≤ 1) (hre : r * e0 ≤ e') (hN : 0 ≤ N)
    (H3 : k2 * lam' ≤ r * N + c / 4 * G4 * L + k2) (H4 : lg ≤ (c + 5) * L) (H5 : 2 * ((c + 5) * k2) ≤ G4) (hL : 1 ≤ L)
    (hk2 : 0 ≤ k2) (hkG : k2 ≤ G4) (hG : 1 ≤ G4) (hc : 0 ≤ c) :
    (c * G4 * L + 1) + (1 + ((c + 3) * L + 1)) + (e0 * k2 * lam' + (6 * c + 14) * k2 * lg) ≤ e' * N + (6 * c + 14) * G4 * L := by
  have a1 := T_aux e0 r N k2 G4 L c lam' lg (6 * c + 14) he0 he1 H3 H4 hL hk2 (by linarith) hc (by linarith)
  have a3 : r * e0 * N ≤ e' * N := mul_le_mul_of_nonneg_right hre hN
  have a2 : k2 * L ≤ G4 * L := mul_le_mul_of_nonneg_right hkG (by linarith)
  have a5 : 2 * ((c + 5) * k2) * ((3 * c + 7) * L) ≤ G4 * ((3 * c + 7) * L) := mul_le_mul_of_nonneg_right H5 (by positivity)
  have hGL : L ≤ G4 * L := le_mul_of_one_le_left (by linarith) hG
  have hGL' : G4 ≤ G4 * L := le_mul_of_one_le_right (by linarith) hL
  have a6 : (c + 3) * L ≤ (c + 3) * (G4 * L) := mul_le_mul_of_nonneg_left hGL (by linarith)
  have a7 : 0 ≤ c * (G4 * L) := mul_nonneg hc (by linarith)
  nlinarith

/-- All budgets of a step but the first, in real variables. -/
theorem step_real (nd sz' sc' sP lg L vt vs vg lam' sc sz vn e' e0 r k G4 lm cc : ℝ)
    (hIH : nd ≤ sc' + sz' + (e0 * k ^ 2 * lam' + (6 * cc + 14) * k ^ 2 * lg))
    (H1 : sc' ≤ sc + (cc * G4 * L + 1)) (HP : sP ≤ cc * G4 * L + 1) (H2 : sz' ≤ sz + 1 + ((cc + 3) * L + 1))
    (H3 : k ^ 2 * lam' ≤ r * (G4 * lm) + cc / 4 * G4 * L + k ^ 2) (H4 : lg ≤ (cc + 5) * L) (H5 : 2 * ((cc + 5) * k ^ 2) ≤ G4)
    (hk1 : 1 ≤ k) (hkG : k ≤ G4) (hc0 : 0 ≤ cc) (hlm : 1 ≤ lm) (hL1 : 1 ≤ L) (h3 : 3 ≤ e' * k)
    (he0 : 0 ≤ e0) (he1 : e0 ≤ 1) (he'0 : 0 ≤ e') (hre : r * e0 ≤ e') (hr2 : r ≤ 2) (hneed : k * vn ≤ G4 * lm) (hgK : vg ≤ G4)
    (hst : k * vs ≤ 3 * (G4 * lm)) (htab : vt ≤ k * lam') (p1 : 0 ≤ sc) (p2 : 0 ≤ sz) :
    max (max (max vn sP) (max vg vs)) (max (max vt 0) nd) ≤ sc + sz + (e' * (G4 * lm) + (6 * cc + 14) * G4 * L) := by
  have hG1 : 1 ≤ G4 := hk1.trans hkG
  have hk2 : 0 ≤ k ^ 2 := by positivity
  have hk2G : k ^ 2 ≤ G4 := by
    have : 0 ≤ cc * k ^ 2 := mul_nonneg hc0 hk2
    linarith
  have hN : 0 ≤ G4 * lm := mul_nonneg (by linarith) (by linarith)
  have heN : 0 ≤ e' * (G4 * lm) := mul_nonneg he'0 hN
  have hGL : G4 ≤ G4 * L := le_mul_of_one_le_right (by linarith) hL1
  have hcGL : 0 ≤ cc * (G4 * L) := mul_nonneg hc0 (by linarith)
  have hT : (6 * cc + 14) * G4 * L = 6 * (cc * (G4 * L)) + 14 * (G4 * L) := by ring
  have hcc : cc * G4 * L = cc * (G4 * L) := by ring
  have b2 : vn ≤ e' * (G4 * lm) := le_of_K_mul k vn (G4 * lm) e' (by linarith) h3 hN (by linarith)
  have b5 : vs ≤ e' * (G4 * lm) := le_of_K_mul k vs (G4 * lm) e' (by linarith) h3 hN hst
  have b6 : vt ≤ e' * (G4 * lm) + (6 * cc + 14) * G4 * L := by
    apply tab_aux k vt r (G4 * lm) cc G4 L e' hk1 _ hr2 hc0 h3 hN hkG hL1
    calc k * vt ≤ k * (k * lam') := mul_le_mul_of_nonneg_left htab (by linarith)
      _ = k ^ 2 * lam' := by ring
      _ ≤ _ := H3
  have b8 := exponent_le e0 e' r (G4 * lm) (k ^ 2) G4 L cc lam' lg he0 he1 hre hN H3 H4 H5 hL1 hk2 hk2G hG1 hc0
  rw [hT] at b6 b8 ⊢
  rw [hcc] at H1 HP b8
  refine max_le (max_le (max_le ?_ ?_) (max_le ?_ ?_)) (max_le (max_le ?_ ?_) ?_) <;> linarith

/-! ### The induction -/

/-- "For the step from ℓ to ℓ + 1". -/
theorem step_le (hρ : 1 / 2 ≤ ρ) (hρ1 : ρ < 1) (hP : Par P ρ c) (hm : P.m = 1) (hx : 18 ≤ x₀) (hc : c + 5 ≤ 2 ^ x₀) (l : ℕ)
    (IH : ∀ lam B cnt z : ℕ, 1 ≤ lam →
      (needG P (K x₀ l) lam B cnt z (sched P x₀ l) : ℝ) ≤ Nat.size cnt + Nat.size (z + Nat.size cnt) + Bd ρ c x₀ l lam B)
    (lam B cnt z : ℕ) (hlam : 1 ≤ lam) :
    (needG P (K x₀ (l + 1)) lam B cnt z (sched P x₀ (l + 1)) : ℝ) ≤ Nat.size cnt + Nat.size (z + Nat.size cnt) + Bd ρ c x₀ (l + 1) lam B := by
  have hfirst := first_le (ρ := ρ) (c := c) hρ hρ1 hx (l + 1) lam B cnt z hlam
  have hA := PartA.thmRunningTime_a ρ x₀ hρ hρ1 hx
  have hρ0 : 0 ≤ ρ := by linarith
  rw [needG_succ, Nat.cast_max]
  refine max_le hfirst ?_
  have n3 := big_le_K hx l
  have hk1 : (1 : ℝ) ≤ K x₀ l := by exact_mod_cast (by omega : 1 ≤ K x₀ l)
  have hka : (K x₀ l : ℝ) ≤ g x₀ l := by exact_mod_cast K_le_g x₀ l
  have hre : (ρ + 3 * zeta l) * e ρ x₀ l ≤ e ρ x₀ (l + 1) := by
    rw [show e ρ x₀ (l + 1) = (ρ + 3 * zeta l) * e ρ x₀ l + 3 / (K x₀ l : ℝ) from rfl]
    have : 0 ≤ 3 / (K x₀ l : ℝ) := by positivity
    linarith
  have hhalf : 2 * ((c + 5) * K x₀ l ^ 2) ≤ g x₀ l ^ 4 := by have := half_const hx hc l; omega
  have hneed : K x₀ l * P.need 0 lam ≤ g x₀ l ^ 4 * lam :=
    (Nat.mul_le_mul_left _ (hP.need 0 lam hlam)).trans (c_lam_le hx hc l lam)
  rw [Bd_succ]
  simp only [Nat.cast_max, Nat.cast_zero]
  exact step_real _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (IH _ _ _ _ (one_le_lamNext _ _ _)) (size_cnt_le hP hx l lam B cnt hlam) (size_nPat_le hP hx l lam B hlam)
    (pot_real hP hx l lam B cnt z hlam) (K2L_le' hP hm hx l lam B hlam) (log_child hP hm hx l lam B hlam)
    (by exact_mod_cast hhalf) hk1 (hka.trans (le_self_pow₀ (hk1.trans hka) (by norm_num)))
    (by positivity) (by exact_mod_cast hlam) (one_le_log hx (l + 1) lam B hlam) (three_le hA hρ0 l)
    (PartAUse.e_nonneg hA hρ0 l) (PartAUse.e_le_one hA hρ0 hρ1.le l) (PartAUse.e_nonneg hA hρ0 (l + 1)) hre (by have := zeta_le l; linarith)
    (by exact_mod_cast hneed) (col_le hx l) (st_le hm l lam)
    (by exact_mod_cast Nat.mul_le_mul_right _ (Nat.sub_le _ _)) (by positivity) (by positivity)

/-- "By induction on ℓ": the bound at every level, for all λ ≥ 1 and all B, cnt and z. -/
theorem main_le (hρ : 1 / 2 ≤ ρ) (hρ1 : ρ < 1) (hP : Par P ρ c) (hm : P.m = 1) (hx : 18 ≤ x₀) (hc : c + 5 ≤ 2 ^ x₀) (l : ℕ) :
    ∀ lam B cnt z : ℕ, 1 ≤ lam →
      (needG P (K x₀ l) lam B cnt z (sched P x₀ l) : ℝ) ≤ Nat.size cnt + Nat.size (z + Nat.size cnt) + Bd ρ c x₀ l lam B := by
  induction l with
  | zero => exact fun lam B cnt z h => base_le hρ hρ1 hx lam B cnt z h
  | succ l ih => exact step_le hρ hρ1 hP hm hx hc l ih

end GeneralPieces.Rate

namespace GeneralPieces

open Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.Gen ClauseBound.Gen.Rate Levels.Gen

/-- Theorem A, part (b), for the exponent of the pad, for every x₀ ≥ 18 with 2^x₀ ≥ c + 5, with C₀ =
6c + 17. -/
theorem stRate2 : StRate2 := by
  intro c
  refine ⟨6 * c + 17, fun P ρ x₀ hρ hρ1 hP hm hx hc l lam B hlam _ => ?_⟩
  have h := Rate.main_le hρ hρ1 hP hm hx hc l lam B 1 1 hlam
  have s1 : Nat.size 1 ≤ 1 := size_le_self 1
  have s2 : Nat.size (1 + Nat.size 1) ≤ 2 := (size_le_self _).trans (by omega)
  have s1' : (Nat.size 1 : ℝ) ≤ 1 := by exact_mod_cast s1
  have s2' : (Nat.size (1 + Nat.size 1) : ℝ) ≤ 2 := by exact_mod_cast s2
  have hL := one_le_log hx l lam B hlam
  have hk1 : (1 : ℝ) ≤ K x₀ l := by
    have := big_le_K hx l
    exact_mod_cast (by omega : 1 ≤ K x₀ l)
  have hk2 : (1 : ℝ) ≤ (K x₀ l : ℝ) ^ 2 := one_le_pow₀ hk1
  have h3 : (1 : ℝ) ≤ (K x₀ l : ℝ) ^ 2 * Real.logb 2 ((K x₀ l : ℝ) * (lam + B)) := by nlinarith
  unfold Bd at h
  push_cast
  linarith

end GeneralPieces
