/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Tow.Load0
import Nc.Tow.Load3

/-!
# The tower plan: bounds for all stages
-/

set_option linter.unusedSectionVars false

namespace Nc.Tow

open Finset Nc.G

variable {F : Type} [CommRing F] {h b D J r m Uu AA : ℕ} {T : Tower h b D J r} {R : Routes T m Uu}
  {ch : Fin AA ↪ T.X 0} {FL : FlagLaws F T} {lhat : ℕ} {n : Fin AA → Fin AA → ℕ}
  {o : NM R FL (ch := ch) → ℕ}

namespace Tower

variable {j : ℕ}

theorem card_ed_real (hj : j ≤ J) : (Fintype.card (T.Ed j) : ℝ) = h * (r * Fintype.card (T.X j) / 2) := by
  have h1 : Fintype.card (T.Ed j) = ∑ i : Fin h, (univ.filter fun e : T.Ed j => T.ty e = i).card := by
    rw [← card_univ]
    exact card_eq_sum_card_fiberwise (fun _ _ => mem_coe.2 (mem_univ _))
  have h2 : 2 * Fintype.card (T.Ed j) = h * (r * Fintype.card (T.X j)) := by
    rw [h1, Finset.mul_sum, Finset.sum_congr rfl fun i _ => T.card_ed j hj i]
    simp
  have h3 : (2 : ℝ) * Fintype.card (T.Ed j) = h * (r * Fintype.card (T.X j)) := by exact_mod_cast h2
  linarith

/-- Units at a chamber. -/
def bet (n : T.Ed j → ℕ) (c : T.X j) : ℕ := ∑ e, if T.e0 e = c ∨ T.e1 e = c then n e else 0

theorem card_at (hj : j ≤ J) (c : T.X j) : (univ.filter fun e : T.Ed j => T.e0 e = c ∨ T.e1 e = c).card ≤ h * r := by
  have h1 : (univ.filter fun e : T.Ed j => T.e0 e = c ∨ T.e1 e = c).card =
      ∑ i : Fin h, (univ.filter fun e : T.Ed j => T.ty e = i ∧ (T.e0 e = c ∨ T.e1 e = c)).card := by
    rw [card_eq_sum_card_fiberwise (f := fun e : T.Ed j => T.ty e) (t := univ) (fun _ _ => mem_coe.2 (mem_univ _))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [filter_filter]
    congr 1
    ext e
    simp only [mem_filter, mem_univ, true_and]
    exact and_comm
  rw [h1]
  calc _ ≤ ∑ _i : Fin h, r := Finset.sum_le_sum fun i _ => T.deg j hj c i
    _ = h * r := by simp

theorem sum_sq_eq (hr : 0 < r) (hX : 0 < Fintype.card (T.X j)) (n : T.Ed j → ℕ) :
    ∑ e, (n e : ℝ) ^ 2 = 2 / (r * Fintype.card (T.X j)) * T.kap n ^ 2 := by
  rw [kap_sq]
  have h1 : (0 : ℝ) < r := by exact_mod_cast hr
  have h2 : (0 : ℝ) < Fintype.card (T.X j) := by exact_mod_cast hX
  field_simp

/-- Units at a chamber. -/
theorem bet_le (hj : j ≤ J) (hr : 0 < r) (n : T.Ed j → ℕ) (c : T.X j) :
    (T.bet n c : ℝ) ≤ √(2 * h / Fintype.card (T.X j)) * T.kap n := by
  have hX : 0 < Fintype.card (T.X j) := Fintype.card_pos_iff.2 ⟨c⟩
  have hXR : (0 : ℝ) < Fintype.card (T.X j) := by exact_mod_cast hX
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have e1 : (T.bet n c : ℝ) = ∑ e ∈ univ.filter (fun e : T.Ed j => T.e0 e = c ∨ T.e1 e = c), (n e : ℝ) := by
    unfold bet
    rw [Finset.sum_filter]
    push_cast
    rfl
  have h1 : (T.bet n c : ℝ) ^ 2 ≤ 2 * h / Fintype.card (T.X j) * T.kap n ^ 2 := by
    rw [e1]
    refine (sq_sum_le _ _ (T.card_at hj c)).trans ?_
    have h2 : ∑ e ∈ univ.filter (fun e : T.Ed j => T.e0 e = c ∨ T.e1 e = c), (n e : ℝ) ^ 2 ≤ ∑ e, (n e : ℝ) ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (subset_univ _) fun _ _ _ => sq_nonneg _
    rw [sum_sq_eq hr hX] at h2
    push_cast
    calc (h : ℝ) * r * _ ≤ h * r * (2 / (r * Fintype.card (T.X j)) * T.kap n ^ 2) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = _ := by field_simp
  have h0 : 0 ≤ √(2 * h / Fintype.card (T.X j)) * T.kap n := mul_nonneg (Real.sqrt_nonneg _) (kap_nonneg n)
  refine (abs_le_of_sq_le_sq' ?_ h0).2
  rw [mul_pow, Real.sq_sqrt (by positivity)]
  exact h1

theorem sum_bet (n : T.Ed j → ℕ) : ∑ c, T.bet n c = 2 * ∑ e, n e := by
  unfold bet
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  have h1 : ∀ c, (if T.e0 e = c ∨ T.e1 e = c then n e else 0) =
      (if T.e0 e = c then n e else 0) + if T.e1 e = c then n e else 0 := by
    intro c
    have hne := T.e_ne e
    by_cases h0 : T.e0 e = c
    · have h1 : ¬ T.e1 e = c := fun hh => hne (h0.trans hh.symm)
      simp [h0, h1]
    · by_cases h1 : T.e1 e = c <;> simp [h0, h1]
  rw [Finset.sum_congr rfl fun c _ => h1 c, Finset.sum_add_distrib]
  simp
  ring

/-- All units of a stage. -/
theorem sum_bet_le (hj : j ≤ J) (hr : 0 < r) (n : T.Ed j → ℕ) :
    ((∑ c, T.bet n c : ℕ) : ℝ) ≤ 2 * (√h * T.kap n) := by
  rw [sum_bet]
  push_cast
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  rcases Nat.eq_zero_or_pos (Fintype.card (T.X j)) with hX | hX
  · have h1 := card_ed_real (T := T) hj
    rw [hX] at h1
    have h2 : Fintype.card (T.Ed j) = 0 := by
      have : (Fintype.card (T.Ed j) : ℝ) = 0 := by rw [h1]; simp
      exact_mod_cast this
    have : IsEmpty (T.Ed j) := Fintype.card_eq_zero_iff.1 h2
    rw [Finset.univ_eq_empty, Finset.sum_empty]
    exact mul_nonneg (Real.sqrt_nonneg _) (kap_nonneg n)
  have hXR : (0 : ℝ) < Fintype.card (T.X j) := by exact_mod_cast hX
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have h0 : 0 ≤ √h * T.kap n := mul_nonneg (Real.sqrt_nonneg _) (kap_nonneg n)
  refine (abs_le_of_sq_le_sq' ?_ h0).2
  rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg h)]
  have h1 := sq_sum_le_card_mul_sum_sq (s := (univ : Finset (T.Ed j))) (f := fun e => (n e : ℝ))
  rw [card_univ, sum_sq_eq hr hX, card_ed_real hj] at h1
  refine h1.trans (le_of_eq ?_)
  field_simp

end Tower

/-- Loads of a stage. -/
noncomputable def lds (R : Routes T m Uu) (ch : Fin AA ↪ T.X 0) (FL : FlagLaws F T) (lhat : ℕ) (n : Fin AA → Fin AA → ℕ)
    (o : NM R FL (ch := ch) → ℕ) (j : Fin (J + 1)) : T.Ed j → ℕ := fun e => load R ch FL lhat n o (.edge j e)

/-- The bound for the loads after the start. -/
def nhat (T : Tower h b D J r) (Uu AA lhat : ℕ) : ℕ := Uu * (lhat / Fintype.card (T.X 0) + 2 * AA)

/-- The bound for the norms. -/
noncomputable def kbar (FL : FlagLaws F T) (Uu AA lhat : ℕ) : ℝ :=
  √h * (r * Fintype.card (T.X 0) / 2) * nhat T Uu AA lhat + √FL.C₁ * FL.a₁ / b * Fintype.card (T.X 0)

section

variable (hr : 0 < r) (hb : 0 < b) (hh : 0 < h) (hbD : b ≤ 2 * D) {ρ : ℝ} (hρ : 0 < ρ)
  (hρ1 : 1 + 8 * FL.C₁ ≤ ρ ^ 2 * h) (hρD : 2 ≤ ρ * D)

theorem kbar_nonneg : 0 ≤ kbar FL Uu AA lhat := by
  unfold kbar
  have := Real.sqrt_nonneg FL.C₁
  positivity

include hr hb in
theorem kap_zero_le : T.kap (lds R ch FL lhat n o 0) ≤ √h * (r * Fintype.card (T.X 0) / 2) * nhat T Uu AA lhat := by
  have h1 : ∀ e : T.Ed 0, (lds R ch FL lhat n o 0 e : ℝ) ^ 2 ≤ (nhat T Uu AA lhat : ℝ) ^ 2 := by
    intro e
    refine pow_le_pow_left₀ (Nat.cast_nonneg _) ?_ 2
    exact_mod_cast Paper.thm_tree_start (R := R) (ch := ch) (FL := FL) (n := n) (o := o) hr hb e
  have h0 : 0 ≤ √h * (r * Fintype.card (T.X 0) / 2) * nhat T Uu AA lhat := by positivity
  refine (abs_le_of_sq_le_sq' ?_ h0).2
  rw [Tower.kap_sq, mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg h)]
  have h2 : ∑ e : T.Ed 0, (lds R ch FL lhat n o 0 e : ℝ) ^ 2 ≤ Fintype.card (T.Ed 0) * (nhat T Uu AA lhat : ℝ) ^ 2 := by
    refine (Finset.sum_le_sum fun e _ => h1 e).trans (le_of_eq ?_)
    rw [Finset.sum_const, card_univ, nsmul_eq_mul]
  rw [Tower.card_ed_real (T := T) (Nat.zero_le _)] at h2
  have hA : (0 : ℝ) ≤ r * Fintype.card (T.X 0) / 2 := by positivity
  refine (mul_le_mul_of_nonneg_left h2 hA).trans (le_of_eq ?_)
  ring

include hr hb hh hbD hρ hρ1 hρD in
/-- **The norms of the loads.** -/
theorem kap_le : ∀ j : ℕ, ∀ hj : j < J + 1, T.kap (lds R ch FL lhat n o ⟨j, hj⟩) +
    √FL.C₁ * FL.a₁ / b * Fintype.card (T.X j) ≤ ρ ^ j * kbar FL Uu AA lhat := by
  intro j
  induction j with
  | zero =>
    intro hj
    have h1 := kap_zero_le (R := R) (ch := ch) (FL := FL) (lhat := lhat) (n := n) (o := o) hr hb
    rw [pow_zero, one_mul]
    unfold kbar
    exact add_le_add h1 le_rfl
  | succ j ih =>
    intro hj
    have h1 := ih (by omega)
    have hjJ : j < J := by omega
    have h2 := Paper.thm_tree_kappa (R := R) (ch := ch) (FL := FL) (lhat := lhat) (n := n) (o := o) hr hb hh hbD hρ.le hρ1 ⟨j, hjJ⟩
    have hcX : (Fintype.card (T.X j) : ℝ) = D * Fintype.card (T.X (j + 1)) := by exact_mod_cast T.card_X j hjJ
    set c : ℝ := √FL.C₁ * FL.a₁ / b with hc
    have hc0 : 0 ≤ c := by
      have := Real.sqrt_nonneg FL.C₁
      positivity
    have hX0 : (0 : ℝ) ≤ Fintype.card (T.X (j + 1)) := Nat.cast_nonneg _
    have h3 : T.kap (lds R ch FL lhat n o ⟨j + 1, hj⟩) ≤ ρ * T.kap (lds R ch FL lhat n o ⟨j, by omega⟩) +
        c * Fintype.card (T.X (j + 1)) := h2
    have h4 := mul_le_mul_of_nonneg_left h1 hρ.le
    rw [hcX] at h4
    have h5 : 2 * (c * Fintype.card (T.X (j + 1))) ≤ ρ * D * (c * Fintype.card (T.X (j + 1))) :=
      mul_le_mul_of_nonneg_right hρD (mul_nonneg hc0 hX0)
    rw [pow_succ]
    linarith

include hr hb hh hbD hρ hρ1 hρD in
theorem kap_le' (j : Fin (J + 1)) : T.kap (lds R ch FL lhat n o j) ≤ ρ ^ j.1 * kbar FL Uu AA lhat := by
  have h1 := kap_le (R := R) (ch := ch) (FL := FL) (lhat := lhat) (n := n) (o := o) hr hb hh hbD hρ hρ1 hρD j.1 j.2
  have : 0 ≤ √FL.C₁ * FL.a₁ / b * Fintype.card (T.X j.1) := by
    have := Real.sqrt_nonneg FL.C₁
    positivity
  linarith

theorem card_X_pow : ∀ j ≤ J, (Fintype.card (T.X 0) : ℝ) = (D : ℝ) ^ j * Fintype.card (T.X j) := by
  intro j
  induction j with
  | zero => intro _; simp
  | succ j ih =>
    intro hj
    rw [ih (by omega)]
    have : (Fintype.card (T.X j) : ℝ) = D * Fintype.card (T.X (j + 1)) := by exact_mod_cast T.card_X j (by omega)
    rw [this, pow_succ]
    ring

theorem sqrt_pow' {x : ℝ} (hx : 0 ≤ x) (j : ℕ) : √(x ^ j) = √x ^ j := by
  induction j with
  | zero => simp
  | succ j ih => rw [pow_succ, pow_succ, Real.sqrt_mul (pow_nonneg hx j), ih]

/-- The bound for the units between a node and its parent. -/
noncomputable def bhat (FL : FlagLaws F T) (Uu AA lhat : ℕ) (ρ : ℝ) : ℝ :=
  √(2 * h / Fintype.card (T.X 0)) * (max 1 (√D * ρ)) ^ J * kbar FL Uu AA lhat

include hr hb hh hbD hρ hρ1 hρD in
/-- **Units between a node and its parent.** -/
theorem bet_le_bhat (j : Fin (J + 1)) (c : T.X j) :
    (T.bet (lds R ch FL lhat n o j) c : ℝ) ≤ bhat FL Uu AA lhat ρ := by
  have hX : 0 < Fintype.card (T.X j.1) := Fintype.card_pos_iff.2 ⟨c⟩
  have hXR : (0 : ℝ) < Fintype.card (T.X j.1) := by exact_mod_cast hX
  have hDpos : 0 < D := by omega
  have hDR : (0 : ℝ) < D := by exact_mod_cast hDpos
  have hjJ : j.1 ≤ J := Nat.le_of_lt_succ j.2
  have h1 := T.bet_le hjJ hr (lds R ch FL lhat n o j) c
  have h2 := kap_le' (R := R) (ch := ch) (FL := FL) (lhat := lhat) (n := n) (o := o) hr hb hh hbD hρ hρ1 hρD j
  have h0 := card_X_pow (T := T) j.1 hjJ
  have hk := kbar_nonneg (FL := FL) (Uu := Uu) (AA := AA) (lhat := lhat)
  have e1 : √(2 * h / Fintype.card (T.X j.1)) = √(2 * h / Fintype.card (T.X 0)) * √D ^ j.1 := by
    rw [h0, ← sqrt_pow' (by positivity : (0 : ℝ) ≤ D), ← Real.sqrt_mul (by positivity)]
    congr 1
    field_simp
  refine h1.trans ?_
  rw [e1]
  calc √(2 * h / Fintype.card (T.X 0)) * √D ^ j.1 * T.kap (lds R ch FL lhat n o j) ≤
      √(2 * h / Fintype.card (T.X 0)) * √D ^ j.1 * (ρ ^ j.1 * kbar FL Uu AA lhat) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = √(2 * h / Fintype.card (T.X 0)) * (√D * ρ) ^ j.1 * kbar FL Uu AA lhat := by rw [mul_pow]; ring
    _ ≤ √(2 * h / Fintype.card (T.X 0)) * (max 1 (√D * ρ)) ^ J * kbar FL Uu AA lhat := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)) hk
        calc (√D * ρ) ^ j.1 ≤ (max 1 (√D * ρ)) ^ j.1 := pow_le_pow_left₀ (by positivity) (le_max_right _ _) _
          _ ≤ _ := pow_le_pow_right₀ (le_max_left _ _) hjJ

include hr hb hh hbD hρ hρ1 hρD in
/-- **Units of a stage.** -/
theorem sum_bet_le_kbar (j : Fin (J + 1)) :
    ((∑ c, T.bet (lds R ch FL lhat n o j) c : ℕ) : ℝ) ≤ 2 * √h * ρ ^ j.1 * kbar FL Uu AA lhat := by
  have h1 := T.sum_bet_le (Nat.le_of_lt_succ j.2) hr (lds R ch FL lhat n o j)
  have h2 := kap_le' (R := R) (ch := ch) (FL := FL) (lhat := lhat) (n := n) (o := o) hr hb hh hbD hρ hρ1 hρD j
  refine h1.trans ?_
  have := mul_le_mul_of_nonneg_left h2 (by positivity : 0 ≤ 2 * √h)
  linarith

end

end Nc.Tow
