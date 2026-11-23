/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.G.PlayThm
import Nc.Tow.Slp4
import Nc.Tow.Slp5
import Nc.Tow.EndC
import Nc.Tow.CapOk
import Nc.Tow.Cards
import Nc.Tow.Ever7
import Nc.Tow.PlaceE
import NS1.Accel

/-!
# The conditions on a tower and its laws, and the numbers that follow
-/

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 20000

namespace Nc.Tow

open Finset Nc.G
open NS1 (lg)

variable {F : Type} [CommRing F] {h b D J r m Uu : ℕ} {T : Tower h b D J r}

/-- The conditions on the tower and the laws. -/
structure THypR (FL : FlagLaws F T) (ρ : ℝ) : Prop where
  r_pos : 0 < r
  b_pos : 0 < b
  h_pos : 0 < h
  bD : b ≤ 2 * D
  ρ_pos : 0 < ρ
  ρ_lt : ρ < 1
  gain : 1 + 8 * FL.C₁ ≤ ρ ^ 2 * h
  two : 2 ≤ ρ * D
  near : ∀ f : T.Fl, ∃ ν, T.cN ν = f ∨ T.dN ν = f

/-- The roles of the relay and of finitely many laws. -/
noncomputable def kindList (F : Type) [CommRing F] (laws : List (Law F)) : List (Σ L : Law F, L.Ro) :=
  (relay F :: laws).flatMap fun L => (univ : Finset L.Ro).toList.map fun p => ⟨L, p⟩

/-- The conditions on the tower and the laws, with one constant. -/
structure TCst (FL : FlagLaws F T) (laws : List (Law F)) (c : ℕ) (ρ : ℝ) (p q : ℕ) : Prop extends THypR FL ρ where
  h_le : h ≤ c
  b_le : b ≤ c
  r_le : r ≤ c
  nr_le : Fintype.card T.Nr ≤ c
  g_le : FL.G₁ ≤ c
  di_le : Fintype.card FL.Di ≤ c
  fl_le : Fintype.card (Sym2 T.Fl) ≤ c
  sl_le : ∀ d, Fintype.card (FL.L d).Sl ≤ c
  bot : Fintype.card (T.X J) ≤ c
  bot_pos : 0 < Fintype.card (T.X J)
  cst : √h * r + √FL.C₁ * FL.a₁ ≤ c
  inv : 1 / (1 - ρ) ≤ c
  pq : 2 * p ≤ q
  pow : ρ ^ q * (D : ℝ) ^ p ≤ 1
  mem : ∀ d, FL.L d ∈ laws
  len : ∀ L ∈ laws, L.Le c ∧ L.lam ≤ c

/-- The bound for the norms, a natural number. -/
def kapB (c m X lh : ℕ) : ℕ := c * (m * X * (lh + 2 * X ^ 2))

/-- The bound for the numbers of units of moves. -/
def capB (c m X lh U0 : ℕ) : ℕ := U0 + 2 + 3 * c * kapB c m X lh

section

variable {FL : FlagLaws F T} {laws : List (Law F)} {c p q U0 : ℕ} {ρ : ℝ} (hC : TCst FL laws c ρ p q)
include hC

theorem TCst.D_two : 2 ≤ D := by
  have h1 := hC.two
  have h2 := hC.ρ_lt
  have h3 := hC.ρ_pos
  by_contra hcon
  have h4 : D ≤ 1 := by omega
  have h5 : (D : ℝ) ≤ 1 := by exact_mod_cast h4
  nlinarith

theorem TCst.X_pos : 0 < Fintype.card (T.X 0) := by
  have hD := hC.D_two
  have h1 := Tower.card_X_le (T := T) (by omega : 0 < D) J le_rfl
  have := hC.bot_pos
  omega

theorem TCst.c_pos : 1 ≤ c := hC.h_pos.trans_le hC.h_le

theorem kbar_kapB {AA lh : ℕ} (hm : 1 ≤ m) (hUu : Uu ≤ 2 * Fintype.card (T.X 0) * m) (hAA : AA ≤ Fintype.card (T.X 0)) :
    kbar FL Uu AA lh ≤ (kapB c m (Fintype.card (T.X 0)) lh : ℕ) := by
  refine (kbar_le hm hUu hAA hC.X_pos hC.b_pos).trans ?_
  unfold kapB
  push_cast
  exact mul_le_mul_of_nonneg_right hC.cst (by positivity)

theorem capN_capB {AA lh : ℕ} (hm : 1 ≤ m) (hUu : Uu ≤ 2 * Fintype.card (T.X 0) * m) (hAA : AA ≤ Fintype.card (T.X 0)) :
    capN FL U0 Uu AA lh ≤ capB c m (Fintype.card (T.X 0)) lh U0 := by
  have h1 := kbar_kapB (lh := lh) hC hm hUu hAA
  have h0 := kbar_nonneg (FL := FL) (Uu := Uu) (AA := AA) (lhat := lh)
  unfold capN capB
  refine Nat.add_le_add_left (Nat.ceil_le.2 ?_) _
  push_cast
  have hb : (b : ℝ) ≤ c := by exact_mod_cast hC.b_le
  have hc0 : (0 : ℝ) ≤ c := Nat.cast_nonneg _
  calc 3 * (b : ℝ) * kbar FL Uu AA lh ≤ 3 * c * kbar FL Uu AA lh := by gcongr
    _ ≤ _ := by gcongr

theorem YhN_le {AA lh : ℕ} (hm : 1 ≤ m) (hUu : Uu ≤ 2 * Fintype.card (T.X 0) * m) (hAA : AA ≤ Fintype.card (T.X 0)) :
    YhN FL Uu AA lh ρ ≤ 2 * c * kapB c m (Fintype.card (T.X 0)) lh * c := by
  have h1 := kbar_kapB (lh := lh) hC hm hUu hAA
  have h0 := kbar_nonneg (FL := FL) (Uu := Uu) (AA := AA) (lhat := lh)
  unfold YhN
  refine Nat.ceil_le.2 ?_
  push_cast
  have hρ : 0 < 1 - ρ := by have := hC.ρ_lt; linarith
  have hh1 : (1 : ℝ) ≤ h := by exact_mod_cast hC.h_pos
  have hs : √(h : ℝ) ≤ c := by
    have h2 : √(h : ℝ) ≤ h := by
      rw [Real.sqrt_le_left (by linarith)]
      nlinarith
    exact h2.trans (by exact_mod_cast hC.h_le)
  have hi := hC.inv
  have hi0 : 0 ≤ 1 / (1 - ρ) := by positivity
  have hc0 : (0 : ℝ) ≤ c := Nat.cast_nonneg _
  have hs0 := Real.sqrt_nonneg (h : ℝ)
  calc 2 * √(h : ℝ) * kbar FL Uu AA lh / (1 - ρ) = 2 * √(h : ℝ) * kbar FL Uu AA lh * (1 / (1 - ρ)) := by ring
    _ ≤ 2 * c * kbar FL Uu AA lh * (1 / (1 - ρ)) := by gcongr
    _ ≤ 2 * c * (kapB c m (Fintype.card (T.X 0)) lh : ℕ) * (1 / (1 - ρ)) := by gcongr
    _ ≤ _ := by gcongr

theorem BhN_le {AA lh : ℕ} (hm : 1 ≤ m) (hUu : Uu ≤ 2 * Fintype.card (T.X 0) * m) (hAA : AA ≤ Fintype.card (T.X 0)) :
    BhN FL Uu AA lh ρ ^ q * Fintype.card (T.X 0) ^ p ≤ (2 * c * kapB c m (Fintype.card (T.X 0)) lh) ^ q := by
  have h1 := kbar_kapB (lh := lh) hC hm hUu hAA
  have h0 := kbar_nonneg (FL := FL) (Uu := Uu) (AA := AA) (lhat := lh)
  have h2 := BhN_pow_le (FL := FL) (Uu := Uu) (AA := AA) (lhat := lh) hC.b_pos hC.h_pos hC.bD hC.ρ_pos hC.bot_pos
    hC.pq hC.pow
  have hh : (h : ℝ) ≤ c := by exact_mod_cast hC.h_le
  have h3 : (2 * (h : ℝ)) ^ q * kbar FL Uu AA lh ^ q ≤
      (2 * (c : ℝ)) ^ q * ((kapB c m (Fintype.card (T.X 0)) lh : ℕ) : ℝ) ^ q := by
    have hh0 : (0 : ℝ) ≤ h := Nat.cast_nonneg _
    gcongr
  have h4 := h2.trans h3
  rw [← mul_pow] at h4
  exact_mod_cast h4

end

/-- Names of targets. -/
theorem card_Tg_le {V : ℕ} (hD : 0 < D) (hb : 0 < b) (hV : 1 ≤ V) (hh : h ≤ V) (hr : r ≤ V) (hm : m ≤ V) (hJ : J ≤ V)
    {AA : ℕ} (hAA : AA ≤ V) (hX : Fintype.card (T.X 0) ≤ V) (hfl : Fintype.card (Sym2 T.Fl) ≤ V) :
    Fintype.card (Tg T m AA) ≤ 12 * V ^ 5 := by
  rw [Fintype.card_congr (tgEquiv T m AA), Fintype.card_sum, Fintype.card_sum, Fintype.card_sum, Fintype.card_unit,
    Fintype.card_sigma, Fintype.card_sigma]
  have h1 : ∑ j : Fin (J + 1), Fintype.card (T.Ed j) ≤ 2 * V ^ 4 := by
    calc _ ≤ ∑ _j : Fin (J + 1), V * V * V := by
          refine Finset.sum_le_sum fun j _ => ?_
          refine (Tower.card_ed_le hD (Nat.le_of_lt_succ j.2)).trans ?_
          gcongr
      _ = (J + 1) * (V * V * V) := by simp
      _ ≤ (2 * V) * (V * V * V) := Nat.mul_le_mul_right _ (by omega)
      _ = 2 * V ^ 4 := by ring
  have h2 := (card_RM_le (T := T) (m := m) (AA := AA) hD).trans
    (rmN_le (X0 := Fintype.card (T.X 0)) hV hh hr hm hJ hAA hX)
  have h3 : ∑ j : Fin J, Fintype.card (Σ i : Fin h, T.V (j + 1) i × Sym2 T.Fl) ≤ V ^ 4 := by
    calc _ ≤ ∑ _j : Fin J, V * (V * V) := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [Fintype.card_sigma]
          calc _ ≤ ∑ _i : Fin h, V * V := by
                refine Finset.sum_le_sum fun i _ => ?_
                rw [Fintype.card_prod]
                exact Nat.mul_le_mul ((Tower.card_V_le hD hb j.2 i).trans hX) hfl
            _ = h * (V * V) := by simp
            _ ≤ V * (V * V) := Nat.mul_le_mul_right _ hh
      _ = J * (V * (V * V)) := by simp
      _ ≤ V * (V * (V * V)) := Nat.mul_le_mul_right _ hJ
      _ = V ^ 4 := by ring
  have h4 : V ^ 4 ≤ V ^ 5 := Nat.pow_le_pow_right hV (by norm_num)
  have h5 : 1 ≤ V ^ 5 := Nat.one_le_pow _ _ hV
  omega

section Numbers

/-- The depth of a tower is logarithmic. -/
theorem two_pow_le {h b D J r : ℕ} {T : Tower h b D J r} (hD : 2 ≤ D) (hX : 0 < Fintype.card (T.X J)) :
    2 ^ J ≤ Fintype.card (T.X 0) := by
  have key : ∀ n ≤ J, 2 ^ n * Fintype.card (T.X n) ≤ Fintype.card (T.X 0) := by
    intro n
    induction n with
    | zero => intro _; simp
    | succ n ih =>
      intro hn
      refine le_trans ?_ (ih (by omega))
      rw [T.card_X n (by omega), pow_succ, mul_assoc]
      exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hD)
  refine le_trans ?_ (key J le_rfl)
  exact Nat.le_mul_of_pos_right _ hX

theorem depth_le {J X c K : ℕ} (hJ : 2 ^ J ≤ X) (hX : X ≤ c * (2 * K)) : J + 1 ≤ (2 * c + 1) * lg K := by
  have hl : 1 ≤ lg K := Nat.succ_le_succ (Nat.zero_le _)
  have h1 : K < 2 ^ lg K := Nat.lt_pow_succ_log_self (by norm_num) K
  have h2 : 2 * c < 2 ^ (2 * c) := Nat.lt_two_pow_self
  have h3 : 2 ^ J < 2 ^ (2 * c + lg K) := by
    calc 2 ^ J ≤ c * (2 * K) := hJ.trans hX
      _ = 2 * c * K := by ring
      _ < 2 ^ (2 * c) * 2 ^ lg K := Nat.mul_lt_mul'' h2 h1
      _ = _ := (pow_add _ _ _).symm
  have h4 : J < 2 * c + lg K := (Nat.pow_lt_pow_iff_right (by norm_num)).1 h3
  have h5 : 2 * c ≤ 2 * c * lg K := Nat.le_mul_of_pos_right _ hl
  have e : (2 * c + 1) * lg K = 2 * c * lg K + lg K := by ring
  omega

theorem m_le {c m J K : ℕ} (hm : m ≤ c * (J + 1) ^ 7) (hJ : J + 1 ≤ (2 * c + 1) * lg K) : m ≤ c * ((2 * c + 1) ^ 7 * lg K ^ 7) := by
  refine hm.trans (Nat.mul_le_mul_left _ ?_)
  rw [← mul_pow]
  exact Nat.pow_le_pow_left hJ 7

end Numbers

end Nc.Tow
