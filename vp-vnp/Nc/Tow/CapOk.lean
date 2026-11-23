/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Tow.Cap
import Nc.Tow.Ok
import Nc.Tow.Tree

/-!
# The tower plan: rules, numbers of units of the tree
-/

set_option linter.unusedSectionVars false

namespace Nc.Tow

open Finset Nc.G

variable {F : Type} [CommRing F] {h b D J r m Uu AA A' U0 U1 : ℕ} {T : Tower h b D J r} {R : Routes T m Uu}
  {ch : Fin AA ↪ T.X 0} {FL : FlagLaws F T} {Pl : Place T ch A'} {lhat : ℕ}

/-- The bound for the units between a node and its parent, a natural number. -/
noncomputable def BhN (FL : FlagLaws F T) (Uu AA lhat : ℕ) (ρ : ℝ) : ℕ := ⌊bhat FL Uu AA lhat ρ⌋₊

theorem bhat_nonneg (ρ : ℝ) : 0 ≤ bhat FL Uu AA lhat ρ := by
  have hk0 := kbar_nonneg (FL := FL) (Uu := Uu) (AA := AA) (lhat := lhat)
  have h1 : (0 : ℝ) ≤ max 1 (√D * ρ) := le_trans zero_le_one (le_max_left _ _)
  unfold bhat
  positivity

theorem lev_eq (L : Tg T m AA → ℕ) (j : Fin (J + 1)) : lev L j.1 = fun e => L (.edge j e) := by
  funext e
  unfold lev
  rw [dif_pos j.2]

section

variable (hr : 0 < r) (hb : 0 < b) (hh : 0 < h) (hbD : b ≤ 2 * D) {ρ : ℝ} (hρ : 0 < ρ) (hρ' : ρ < 1)
  (hρ1 : 1 + 8 * FL.C₁ ≤ ρ ^ 2 * h) (hρD : 2 ≤ ρ * D)

include hr hb hh hbD hρ hρ' hρ1 hρD

/-- **The plan obeys the rules.** -/
theorem plan_ok_cap : (plan R FL Pl lhat U0 U1).Ok (capN FL U0 Uu AA lhat) :=
  plan_ok hr hb fun n _ mv => num_le_cap hr hb hh hbD hρ hρ'.le hρ1 hρD
    (fun a c => Nat.le_of_lt_succ (n a c).2) mv

/-- All units of the tree. -/
theorem sum_fb_le {n : Fin AA → Fin AA → ℕ} {o : NM R FL (ch := ch) → ℕ} :
    ∑ i ∈ range (J + 1), ∑ c, fb (lev (load R ch FL lhat n o)) i c ≤ YhN FL Uu AA lhat ρ := by
  rw [Finset.sum_range]
  refine le_trans (le_of_eq ?_) (sum_bet_le_YhN (R := R) (ch := ch) (FL := FL) (lhat := lhat) (n := n) (o := o)
    hr hb hh hbD hρ hρ' hρ1 hρD)
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun c _ => ?_
  unfold fb
  rw [lev_eq]
  rfl

omit hρ' in
/-- Units between a node and its parent. -/
theorem fb_le {n : Fin AA → Fin AA → ℕ} {o : NM R FL (ch := ch) → ℕ} (j : ℕ) (hj : j ≤ J) (c : T.X j) :
    fb (lev (load R ch FL lhat n o)) j c ≤ BhN FL Uu AA lhat ρ := by
  refine Nat.le_floor ?_
  have h1 := bet_le_bhat (R := R) (ch := ch) (FL := FL) (lhat := lhat) (n := n) (o := o) hr hb hh hbD hρ hρ1 hρD
    ⟨j, Nat.lt_succ_of_le hj⟩ c
  refine le_trans (le_of_eq ?_) h1
  unfold fb
  have := lev_eq (load R ch FL lhat n o) ⟨j, Nat.lt_succ_of_le hj⟩
  rw [this]
  rfl

omit hr hρ' hρ1 hρD in
/-- **The gain of the tower.** -/
theorem BhN_pow_le (hX : 0 < Fintype.card (T.X J)) {p q : ℕ} (hpq : 2 * p ≤ q) (hgain : ρ ^ q * (D : ℝ) ^ p ≤ 1) :
    (BhN FL Uu AA lhat ρ : ℝ) ^ q * (Fintype.card (T.X 0) : ℝ) ^ p ≤
      (2 * (h : ℝ)) ^ q * kbar FL Uu AA lhat ^ q := by
  refine le_trans ?_ (bhat_pow_le (FL := FL) (Uu := Uu) (AA := AA) (lhat := lhat) hb hbD hρ hh hX hpq hgain)
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  exact pow_le_pow_left₀ (Nat.cast_nonneg _) (Nat.floor_le (bhat_nonneg ρ)) q

end

end Nc.Tow
