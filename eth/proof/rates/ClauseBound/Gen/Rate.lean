/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ClauseBound.Gen.RateAux
public import ClauseBound.Gen.PartA

/-! # Lemmas toward part (b) of the theorem on the general recursion, as an inequality for the exponent of the pad

Arithmetic facts on the numbers of one level of the recursion: K_ℓ and g_ℓ, the label length λ' one
level down, the number of patterns and the bit lengths that grow from level to level;
the bound Bd ρ c x₀ ℓ λ B = e_ℓ·K_ℓ²·λ + C·K_ℓ²·log(K_ℓ·(λ + B)), C = 6c + 14; and the exponent
needG at level ℓ + 1, written out. They are the pieces of an induction on ℓ for
  needG … ≤ size cnt + size (z + size cnt) + Bd ρ c x₀ ℓ λ B. -/

public section

namespace ClauseBound.Gen.Rate

open Groundwork PaddedDescent.F ClauseBound.Alg Levels.Gen

variable {P : PiecesF} {ρ : ℝ} {c x₀ : ℕ}

/-! ### The numbers of a step -/

theorem step_K (P : PiecesF) (x₀ l : ℕ) : (step P x₀ l).K = K x₀ l := by simp [step, Step.K, rep]
theorem step_p (P : PiecesF) (x₀ l : ℕ) : (step P x₀ l).p = g x₀ l := by simp [step, Step.p, rep]
theorem step_d (P : PiecesF) (x₀ l : ℕ) : (step P x₀ l).d = g x₀ l := by simp [step, Step.d, rep]
theorem step_D (P : PiecesF) (x₀ l : ℕ) : (step P x₀ l).D = 3 * P.m * 2 ^ (l + 4) := by simp [step, Step.D, rep]
theorem step_h (P : PiecesF) (x₀ l : ℕ) : (step P x₀ l).h = 0 := by simp [step, Step.h]
theorem step_thin (P : PiecesF) (x₀ l : ℕ) : (step P x₀ l).thin = false := by simp [step, Step.thin]

/-- 1 ≤ c. -/
theorem c_pos (hP : Par P ρ c) : 1 ≤ c := le_trans (hP.spec 0 1 le_rfl).m_pos hP.m_le

/-- 2^{x₀}·2^ℓ ≤ K_ℓ. -/
theorem pow_mul_le_K (hx : 18 ≤ x₀) (l : ℕ) : 2 ^ x₀ * 2 ^ l ≤ K x₀ l := by
  rw [ClauseBound.Gen.K_eq, ← pow_add]
  exact Nat.pow_le_pow_right (by norm_num) (by have := ClauseBound.Gen.x_ge x₀ l hx; omega)

/-- 2^{x₀} ≤ K_ℓ. -/
theorem pow_le_K (hx : 18 ≤ x₀) (l : ℕ) : 2 ^ x₀ ≤ K x₀ l :=
  le_trans (Nat.le_mul_of_pos_right _ (by positivity)) (pow_mul_le_K hx l)

/-- 2^18 ≤ K_ℓ. -/
theorem big_le_K (hx : 18 ≤ x₀) (l : ℕ) : 2 ^ 18 ≤ K x₀ l :=
  le_trans (Nat.pow_le_pow_right (by norm_num) hx) (pow_le_K hx l)

/-- K_ℓ ≤ g_ℓ. -/
theorem K_le_g (x₀ l : ℕ) : K x₀ l ≤ g x₀ l := by
  unfold g; exact Nat.le_mul_of_pos_left _ (by positivity)

/-- 2^{ℓ+5} ≤ g_ℓ. -/
theorem pow_le_g (hx : 18 ≤ x₀) (l : ℕ) : 2 ^ (l + 5) ≤ g x₀ l := by
  unfold g
  calc 2 ^ (l + 5) ≤ 2 ^ (3 * l + x₀) := Nat.pow_le_pow_right (by norm_num) (by omega)
    _ ≤ 2 ^ (3 * l + x₀) * K x₀ l := Nat.le_mul_of_pos_right _ (by have := big_le_K hx l; omega)

/-- K_{ℓ+1} = g_ℓ². -/
theorem K_succ (x₀ l : ℕ) : K x₀ (l + 1) = g x₀ l ^ 2 := rfl

/-! ### The label length one level down -/

/-- The label length one level down, written out. -/
theorem lamNext_eq (P : PiecesF) (x₀ l lam : ℕ) : lamNextG P (step P x₀ l) lam =
    (3 * P.m * 2 ^ (l + 4) * (g x₀ l * (g x₀ l - 1) * g x₀ l * lam + nRectG (g x₀ l) (g x₀ l) * capSum P 0 lam) +
      3 * g x₀ l ^ 2 * (g x₀ l ^ 2 * (P.m * lam))) / (3 * P.m * 2 ^ (l + 4) * K x₀ l ^ 2) + 1 := by
  simp [lamNextG, ubarG, step_K, step_p, step_d, step_D, step_h, step_thin]

/-! ### The bound -/

/-- The bound on the exponent at level ℓ, without the part that depends on cnt and z. -/
noncomputable def Bd (ρ : ℝ) (c x₀ l lam B : ℕ) : ℝ :=
  e ρ x₀ l * (K x₀ l : ℝ) ^ 2 * lam + (6 * c + 14) * (K x₀ l : ℝ) ^ 2 * Real.logb 2 (K x₀ l * (lam + B))

/-- 1 ≤ log(K_ℓ·(λ + B)). -/
theorem one_le_log (hx : 18 ≤ x₀) (l lam B : ℕ) (hlam : 1 ≤ lam) : 1 ≤ Real.logb 2 ((K x₀ l : ℝ) * (lam + B)) := by
  have h1 : 2 ≤ K x₀ l * (lam + B) := by
    have := big_le_K hx l
    calc 2 ≤ K x₀ l := by omega
      _ ≤ K x₀ l * (lam + B) := Nat.le_mul_of_pos_right _ (by omega)
  have h2 : (2 : ℝ) ≤ (K x₀ l : ℝ) * (lam + B) := by exact_mod_cast h1
  have h3 := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by norm_num) h2
  rwa [Real.logb_self_eq_one (by norm_num)] at h3

/-! ### The quantities of one level -/

/-- 2λ ≤ g²·(λ + B). -/
theorem two_lam_le (hx : 18 ≤ x₀) (l lam B : ℕ) : 2 * lam ≤ g x₀ l ^ 2 * (lam + B) := by
  have h1 := big_le_K hx l
  have h2 := K_le_g x₀ l
  have h3 : 2 ≤ g x₀ l ^ 2 := by
    calc 2 ≤ g x₀ l := by omega
      _ ≤ g x₀ l ^ 2 := Nat.le_self_pow two_ne_zero _
  calc 2 * lam ≤ g x₀ l ^ 2 * lam := Nat.mul_le_mul_right _ h3
    _ ≤ g x₀ l ^ 2 * (lam + B) := Nat.mul_le_mul_left _ (Nat.le_add_right _ _)

/-- The number of patterns, written out. -/
theorem nPat_eq (P : PiecesF) (x₀ l lam : ℕ) : nPat P (step P x₀ l) lam = P.cnt 0 lam ^ nRectG (g x₀ l) (g x₀ l) := by
  simp only [nPat, step_p, step_d, step_h]

/-- The number of patterns is at most X^(c·R). -/
theorem nPat_le (hP : Par P ρ c) (hx : 18 ≤ x₀) (l lam B : ℕ) (hlam : 1 ≤ lam) :
    nPat P (step P x₀ l) lam ≤ (g x₀ l ^ 2 * (lam + B)) ^ (c * nRectG (g x₀ l) (g x₀ l)) := by
  rw [nPat_eq, pow_mul]
  exact Nat.pow_le_pow_left ((hP.cnt 0 lam hlam).trans (Nat.pow_le_pow_left (two_lam_le hx l lam B) c)) _

/-- A crude bound on the bit length of the number of patterns. -/
theorem size_nPat_le (hP : Par P ρ c) (l lam : ℕ) (hlam : 1 ≤ lam) :
    Nat.size (nPat P (step P x₀ l) lam) ≤ nRectG (g x₀ l) (g x₀ l) * (2 * lam) ^ c + 1 := by
  rw [nPat_eq]
  refine (size_pow_le _ _).trans ?_
  have := (size_le_self (P.cnt 0 lam)).trans (hP.cnt 0 lam hlam)
  exact Nat.add_le_add_right (Nat.mul_le_mul_left _ this) 1

/-- X as a real number. -/
theorem X_cast (x₀ l lam B : ℕ) : ((g x₀ l ^ 2 * (lam + B) : ℕ) : ℝ) = (K x₀ (l + 1) : ℝ) * (lam + B) := by
  rw [K_succ]; push_cast; ring

/-- How Nat.size (z + Nat.size cnt) grows at one level. -/
theorem pot_step (z cnt nP a b d : ℕ) :
    Nat.size (z + a + Nat.size (cnt * nP) + b + d + 2 + Nat.size (cnt * nP)) ≤ Nat.size (z + Nat.size cnt) + 1 + Nat.size (a + b + d + 2 + 2 * Nat.size nP) := by
  have h := size_mul_le cnt nP
  have h1 : z + a + Nat.size (cnt * nP) + b + d + 2 + Nat.size (cnt * nP) ≤ 2 * (z + Nat.size cnt) + (a + b + d + 2 + 2 * Nat.size nP) := by omega
  have h2 := size_two_mul_le (z + Nat.size cnt)
  exact (Nat.size_le_size h1).trans ((size_add_le _ _).trans (by omega))

/-- 1 ≤ λ'. -/
theorem one_le_lamNext (P : PiecesF) (s : Step) (lam : ℕ) : 1 ≤ lamNextG P s lam := by
  unfold lamNextG; exact Nat.le_add_left 1 _

/-- B', written out. -/
theorem bNext_eq (P : PiecesF) (x₀ l lam B : ℕ) : bNextG P (step P x₀ l) lam B =
    P.m * (g x₀ l * g x₀ l ^ 2 * lam) * (2 * g x₀ l / K x₀ l) +
      (g x₀ l * B + g x₀ l ^ 2 * P.bits 0 lam) * (2 * g x₀ l / K x₀ l + 2 * g x₀ l / K x₀ l * (2 * g x₀ l / K x₀ l)) * K x₀ l := by
  simp only [bNextG, PnG, step_K, step_p, step_d, step_h]

/-- ζ_ℓ ≤ 1/32. -/
theorem zeta_le (l : ℕ) : zeta l ≤ 1 / 32 := by
  unfold zeta
  apply one_div_le_one_div_of_le (by norm_num)
  calc (32 : ℝ) = 2 ^ 5 := by norm_num
    _ ≤ 2 ^ (l + 5) := pow_le_pow_right₀ (by norm_num) (by omega)

/-- The exponent at level ℓ + 1, written out. -/
theorem needG_succ (P : PiecesF) (x₀ l Kup lam B cnt z : ℕ) : needG P Kup lam B cnt z (sched P x₀ (l + 1)) =
    max (max (Nat.size (cnt * instLen Kup lam B + 8 * z + 4 * lam + 40)) (max lam (max (Nat.size B) (Nat.size Kup))))
      (max (max (max (P.need 0 lam) (Nat.size (nPat P (step P x₀ l) lam)))
          (max (g x₀ l * Nat.size (K x₀ l)) (P.m * (g x₀ l * g x₀ l ^ 2 * lam) * (2 * g x₀ l / K x₀ l + 1))))
        (max (max ((K x₀ l - 1) * lamNextG P (step P x₀ l) lam) 0)
          (needG P (K x₀ l) (lamNextG P (step P x₀ l) lam) (bNextG P (step P x₀ l) lam B) (cnt * nPat P (step P x₀ l) lam)
            (z + nRectG (g x₀ l) (g x₀ l) * Nat.size (P.d 0 lam) + Nat.size (cnt * nPat P (step P x₀ l) lam) + (g x₀ l * g x₀ l) ^ 2 * lam +
              g x₀ l ^ 2 * (g x₀ l * B + g x₀ l ^ 2 * P.bits 0 lam + 1) + 2) (sched P x₀ l)))) := by
  rw [show sched P x₀ (l + 1) = step P x₀ l :: sched P x₀ l from rfl, needG]
  simp only [step_K, step_p, step_d, step_h, step_thin, Nof, PnG, Bool.false_eq_true, if_false]

/-! ### The quantities of one level, as real numbers -/

/-- The bit length of z + Nat.size cnt one level down. -/
theorem pot_real (hP : Par P ρ c) (hx : 18 ≤ x₀) (l lam B cnt z : ℕ) (hlam : 1 ≤ lam) :
    (Nat.size (z + nRectG (g x₀ l) (g x₀ l) * Nat.size (P.d 0 lam) + Nat.size (cnt * nPat P (step P x₀ l) lam) + (g x₀ l * g x₀ l) ^ 2 * lam +
      g x₀ l ^ 2 * (g x₀ l * B + g x₀ l ^ 2 * P.bits 0 lam + 1) + 2 + Nat.size (cnt * nPat P (step P x₀ l) lam)) : ℝ) ≤
      Nat.size (z + Nat.size cnt) + 1 + ((c + 3) * Real.logb 2 ((K x₀ (l + 1) : ℝ) * (lam + B)) + 1) := by
  have n3 := big_le_K hx l
  have n4 := K_le_g x₀ l
  have hX1 : 1 ≤ g x₀ l ^ 2 * (lam + B) := by have := two_lam_le hx l lam B; omega
  have hR : nRectG (g x₀ l) (g x₀ l) ≤ g x₀ l ^ 4 := by have := four_nRect_le (g x₀ l); omega
  have H2 := Nat.cast_le (α := ℝ).2 (pot_step z cnt (nPat P (step P x₀ l) lam) (nRectG (g x₀ l) (g x₀ l) * Nat.size (P.d 0 lam))
    ((g x₀ l * g x₀ l) ^ 2 * lam) (g x₀ l ^ 2 * (g x₀ l * B + g x₀ l ^ 2 * P.bits 0 lam + 1)))
  rw [Nat.cast_add, Nat.cast_add, Nat.cast_one] at H2
  have H2r := size_cast_le hX1 (rest_le (g x₀ l) c lam B (P.bits 0 lam) (Nat.size (P.d 0 lam)) (nRectG (g x₀ l) (g x₀ l))
    (Nat.size (nPat P (step P x₀ l) lam)) (c_pos hP) hlam (by omega) (hP.bits 0 lam hlam) (Nat.size_le.2 (hP.d 0 lam hlam)) hR
    (size_nPat_le hP l lam hlam))
  rw [X_cast, Nat.cast_add, Nat.cast_ofNat] at H2r
  linarith

/-- The bound at level ℓ + 1 in terms of g_ℓ. -/
theorem Bd_succ (ρ : ℝ) (c x₀ l lam B : ℕ) : Bd ρ c x₀ (l + 1) lam B = e ρ x₀ (l + 1) * ((g x₀ l : ℝ) ^ 4 * lam) +
    (6 * c + 14) * (g x₀ l : ℝ) ^ 4 * Real.logb 2 ((K x₀ (l + 1) : ℝ) * (lam + B)) := by
  have h : (K x₀ (l + 1) : ℝ) ^ 2 = (g x₀ l : ℝ) ^ 4 := by rw [K_succ]; push_cast; ring
  unfold Bd; rw [h]; ring

/-- The budget of the colourings: g·Nat.size K ≤ g⁴. -/
theorem col_le (hx : 18 ≤ x₀) (l : ℕ) : ((g x₀ l * Nat.size (K x₀ l) : ℕ) : ℝ) ≤ (g x₀ l : ℝ) ^ 4 := by
  have n3 := big_le_K hx l
  have n4 := K_le_g x₀ l
  have h : g x₀ l * Nat.size (K x₀ l) ≤ g x₀ l ^ 4 := by
    calc g x₀ l * Nat.size (K x₀ l) ≤ g x₀ l * g x₀ l := Nat.mul_le_mul_left _ ((size_le_self _).trans n4)
      _ = g x₀ l ^ 2 := by ring
      _ ≤ g x₀ l ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
  exact_mod_cast h

end ClauseBound.Gen.Rate
