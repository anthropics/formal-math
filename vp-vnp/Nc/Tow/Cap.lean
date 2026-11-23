/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Tow.Load4

/-!
# The number of units of a move; numbers
-/

set_option linter.unusedSectionVars false

namespace Nc.Tow

open Finset Nc.G

variable {F : Type} [CommRing F] {h b D J r m Uu AA : ℕ} {T : Tower h b D J r} {R : Routes T m Uu}
  {ch : Fin AA ↪ T.X 0} {FL : FlagLaws F T} {lhat : ℕ} {n : Fin AA → Fin AA → ℕ}
  {o : NM R FL (ch := ch) → ℕ}

/-- The bound for the number of units of a move. -/
noncomputable def capN (FL : FlagLaws F T) (U0 Uu AA lhat : ℕ) : ℕ := U0 + 2 + ⌈3 * (b : ℝ) * kbar FL Uu AA lhat⌉₊

section

variable (hr : 0 < r) (hb : 0 < b) (hh : 0 < h) (hbD : b ≤ 2 * D) {ρ : ℝ} (hρ : 0 < ρ) (hρ' : ρ ≤ 1)
  (hρ1 : 1 + 8 * FL.C₁ ≤ ρ ^ 2 * h) (hρD : 2 ≤ ρ * D)

include hr hb hh hbD hρ hρ' hρ1 hρD

theorem kap_le_kbar (j : Fin (J + 1)) : T.kap (lds R ch FL lhat n o j) ≤ kbar FL Uu AA lhat := by
  refine (kap_le' (R := R) (ch := ch) (FL := FL) (lhat := lhat) (n := n) (o := o) hr hb hh hbD hρ hρ1 hρD j).trans ?_
  exact mul_le_of_le_one_left kbar_nonneg (pow_le_one₀ hρ.le hρ')

/-- Loads of edges. -/
theorem load_edge_le (j : Fin (J + 1)) (e : T.Ed j) :
    (load R ch FL lhat n o (.edge j e) : ℝ) ≤ 2 * kbar FL Uu AA lhat := by
  have hX : 0 < Fintype.card (T.X j.1) := Fintype.card_pos_iff.2 ⟨T.e0 e⟩
  have hk := kap_le_kbar (R := R) (ch := ch) (FL := FL) (lhat := lhat) (n := n) (o := o) hr hb hh hbD hρ hρ' hρ1 hρD j
  have hk0 : 0 ≤ T.kap (lds R ch FL lhat n o j) := Tower.kap_nonneg _
  have h1 := Tower.sum_sq_eq (T := T) hr hX (lds R ch FL lhat n o j)
  have h2 : (load R ch FL lhat n o (.edge j e) : ℝ) ^ 2 ≤ ∑ e, (lds R ch FL lhat n o j e : ℝ) ^ 2 :=
    Finset.single_le_sum (f := fun e => (lds R ch FL lhat n o j e : ℝ) ^ 2) (fun _ _ => sq_nonneg _) (mem_univ e)
  have h3 : (1 : ℝ) ≤ r * Fintype.card (T.X j.1) := by exact_mod_cast Nat.mul_pos hr hX
  have h4 : (2 : ℝ) / (r * Fintype.card (T.X j.1)) ≤ 2 := by
    rw [div_le_iff₀ (by linarith)]
    linarith
  have h5 : (load R ch FL lhat n o (.edge j e) : ℝ) ^ 2 ≤ (2 * T.kap (lds R ch FL lhat n o j)) ^ 2 := by
    rw [h1] at h2
    have h6 := mul_le_mul_of_nonneg_right h4 (sq_nonneg (T.kap (lds R ch FL lhat n o j)))
    nlinarith [sq_nonneg (T.kap (lds R ch FL lhat n o j))]
  have h6 := (abs_le_of_sq_le_sq' h5 (by linarith)).2
  linarith

/-- Numbers of units of law moves. -/
theorem tmin_real_le (l : LMv T FL) : (tmin FL (load R ch FL lhat n o) l : ℝ) ≤ 3 * b * kbar FL Uu AA lhat + 1 := by
  obtain ⟨j, i, ω, d⟩ := l
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have ha1 : (1 : ℝ) ≤ FL.a₁ := by exact_mod_cast FL.a₁_pos
  set nf : T.Ed j → ℕ := lds R ch FL lhat n o j.castSucc with hnf
  have h1 : (FL.a₁ : ℝ) * tmin FL (load R ch FL lhat n o) (⟨j, i, ω, d⟩ : LMv T FL) ≤
      √(T.NN2 (T.nEnd i nf ω)) + FL.a₁ := tmin_le hb _ _ fun q => seg_le hr hb j i ω q
  have hX : 0 < Fintype.card (T.X (j.1 + 1)) := by
    rw [← Tower.card_V (T := T) (Nat.succ_le_of_lt j.2) i]
    exact Nat.mul_pos (Fintype.card_pos_iff.2 ⟨ω⟩) hb
  have hXR : (1 : ℝ) ≤ Fintype.card (T.X (j.1 + 1)) := by exact_mod_cast hX
  have h2 := Tower.end_norm (T := T) j.2 hb hbD (i := i) (n := nf)
  have h3 : √(T.NN2 (T.nEnd i nf ω)) ^ 2 ≤ ∑ ω, √(T.NN2 (T.nEnd i nf ω)) ^ 2 :=
    Finset.single_le_sum (f := fun ω => √(T.NN2 (T.nEnd i nf ω)) ^ 2) (fun _ _ => sq_nonneg _) (mem_univ ω)
  have hk0 : 0 ≤ T.kap nf := Tower.kap_nonneg _
  have h4 : (r : ℝ) * Fintype.card (T.X j.1) / 2 * ∑ e ∈ univ.filter (fun e : T.Ed j => T.ty e = i), (nf e : ℝ) ^ 2 ≤
      T.kap nf ^ 2 := by
    rw [Tower.kap_sq]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact Finset.sum_le_sum_of_subset_of_nonneg (subset_univ _) fun _ _ _ => sq_nonneg _
  have h5 : √(T.NN2 (T.nEnd i nf ω)) ^ 2 ≤ (3 * b * T.kap nf) ^ 2 := by
    have h6 : (Fintype.card (T.X (j.1 + 1)) : ℝ) / b * √(T.NN2 (T.nEnd i nf ω)) ^ 2 ≤ 8 * T.kap nf ^ 2 := by
      refine (mul_le_mul_of_nonneg_left h3 (by positivity)).trans (h2.trans ?_)
      exact mul_le_mul_of_nonneg_left h4 (by norm_num)
    have h7 : √(T.NN2 (T.nEnd i nf ω)) ^ 2 ≤ 8 * b * T.kap nf ^ 2 := by
      have h8 : (1 : ℝ) / b * √(T.NN2 (T.nEnd i nf ω)) ^ 2 ≤
          (Fintype.card (T.X (j.1 + 1)) : ℝ) / b * √(T.NN2 (T.nEnd i nf ω)) ^ 2 :=
        mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hXR hbR.le) (sq_nonneg _)
      have h9 := h8.trans h6
      rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hbR] at h9
      linarith
    have h10 : 8 * (b : ℝ) * T.kap nf ^ 2 ≤ (3 * b * T.kap nf) ^ 2 := by
      have : (3 * b * T.kap nf) ^ 2 = 9 * (b : ℝ) ^ 2 * T.kap nf ^ 2 := by ring
      rw [this]
      refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
      nlinarith
    exact h7.trans h10
  have h6 : √(T.NN2 (T.nEnd i nf ω)) ≤ 3 * b * T.kap nf :=
    (abs_le_of_sq_le_sq' h5 (by positivity)).2
  have hk := kap_le_kbar (R := R) (ch := ch) (FL := FL) (lhat := lhat) (n := n) (o := o) hr hb hh hbD hρ hρ' hρ1 hρD
    j.castSucc
  have h7 : 3 * b * T.kap nf ≤ 3 * b * kbar FL Uu AA lhat := mul_le_mul_of_nonneg_left hk (by positivity)
  set t : ℝ := (tmin FL (load R ch FL lhat n o) (⟨j, i, ω, d⟩ : LMv T FL) : ℝ) with ht
  set Q : ℝ := 3 * b * kbar FL Uu AA lhat with hQ
  have hQ0 : 0 ≤ Q := by
    have := kbar_nonneg (FL := FL) (Uu := Uu) (AA := AA) (lhat := lhat)
    positivity
  have h8 : (FL.a₁ : ℝ) * t ≤ FL.a₁ * (Q + 1) := by
    have h9 : Q ≤ FL.a₁ * Q := le_mul_of_one_le_left hQ0 ha1
    nlinarith
  exact le_of_mul_le_mul_left h8 (by linarith)

/-- **The numbers of units of the moves are bounded.** -/
theorem num_le_cap {U0 : ℕ} (hn : ∀ a c, n a c ≤ U0) (mv : Mv T R ch FL) :
    num R ch FL lhat n o mv ≤ capN FL U0 Uu AA lhat := by
  have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hk0 := kbar_nonneg (FL := FL) (Uu := Uu) (AA := AA) (lhat := lhat)
  have hceil : (3 * (b : ℝ) * kbar FL Uu AA lhat) ≤ ⌈3 * (b : ℝ) * kbar FL Uu AA lhat⌉₊ := Nat.le_ceil _
  have hedge : ∀ (j : Fin (J + 1)) (e : T.Ed j), load R ch FL lhat n o (.edge j e) ≤ capN FL U0 Uu AA lhat := by
    intro j e
    have h1 := load_edge_le (R := R) (ch := ch) (FL := FL) (lhat := lhat) (n := n) (o := o) hr hb hh hbD hρ hρ' hρ1
      hρD j e
    have h2 : (load R ch FL lhat n o (.edge j e) : ℝ) ≤ ⌈3 * (b : ℝ) * kbar FL Uu AA lhat⌉₊ := by
      refine h1.trans (le_trans ?_ hceil)
      nlinarith
    have h3 : load R ch FL lhat n o (.edge j e) ≤ ⌈3 * (b : ℝ) * kbar FL Uu AA lhat⌉₊ := by exact_mod_cast h2
    unfold capN
    omega
  rcases mv with ⟨x, hx⟩ | l
  · rcases x with ⟨a, c, γ, s⟩ | ⟨j, i, e⟩ | ⟨j, e, s⟩ | e
    · have h1 := num_start_le (FL := FL) (lhat := lhat) (n := n) (o := o) hr hb a c γ s hx
      have h2 := Bt_le (ch := ch) (lhat := lhat) (n := n) a c γ
      have h3 : n a c / Fintype.card (T.X 0) ≤ U0 := (Nat.div_le_self _ _).trans (hn a c)
      unfold capN
      omega
    · exact (num_inl hr hb _).trans (hedge j.castSucc e)
    · obtain ⟨hx0, h1⟩ := num_mid_le (FL := FL) (lhat := lhat) (n := n) (o := o) hr hb j e s hx
      exact h1.trans ((num_mid0 hr hb j e hx0).1.trans (hedge j.castSucc e))
    · exact (num_inl hr hb _).trans (hedge (Fin.last J) e)
  · have h1 := num_inr_le (R := R) (ch := ch) (FL := FL) (lhat := lhat) (n := n) (o := o) hr hb l
    have h2 := tmin_real_le (R := R) (ch := ch) (FL := FL) (lhat := lhat) (n := n) (o := o) hr hb hh hbD hρ hρ' hρ1
      hρD l
    have h3 : (tmin FL (load R ch FL lhat n o) l : ℝ) ≤ ((⌈3 * (b : ℝ) * kbar FL Uu AA lhat⌉₊ + 1 : ℕ) : ℝ) := by
      push_cast
      linarith
    have h4 : tmin FL (load R ch FL lhat n o) l ≤ ⌈3 * (b : ℝ) * kbar FL Uu AA lhat⌉₊ + 1 := by exact_mod_cast h3
    unfold capN
    omega

end

/-! ### Numbers -/

/-- The bound for all units of the tree. -/
noncomputable def YhN (FL : FlagLaws F T) (Uu AA lhat : ℕ) (ρ : ℝ) : ℕ := ⌈2 * √h * kbar FL Uu AA lhat / (1 - ρ)⌉₊

theorem le_YhN (ρ : ℝ) : 2 * √h * kbar FL Uu AA lhat / (1 - ρ) ≤ YhN FL Uu AA lhat ρ := Nat.le_ceil _

theorem geom_le {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) (k : ℕ) : ∑ j ∈ range k, ρ ^ j ≤ 1 / (1 - ρ) := by
  have h1 : 0 < 1 - ρ := by linarith
  rw [le_div_iff₀ h1]
  have h2 := geom_sum_mul ρ k
  have h3 : (∑ j ∈ range k, ρ ^ j) * (1 - ρ) = 1 - ρ ^ k := by linarith
  rw [h3]
  have := pow_nonneg hρ k
  linarith

section

variable (hr : 0 < r) (hb : 0 < b) (hh : 0 < h) (hbD : b ≤ 2 * D) {ρ : ℝ} (hρ : 0 < ρ) (hρ' : ρ < 1)
  (hρ1 : 1 + 8 * FL.C₁ ≤ ρ ^ 2 * h) (hρD : 2 ≤ ρ * D)

include hr hb hh hbD hρ hρ' hρ1 hρD in
/-- All units between nodes and their parents. -/
theorem sum_bet_le_YhN : ∑ j : Fin (J + 1), ∑ c, T.bet (lds R ch FL lhat n o j) c ≤ YhN FL Uu AA lhat ρ := by
  have h1 : ((∑ j : Fin (J + 1), ∑ c, T.bet (lds R ch FL lhat n o j) c : ℕ) : ℝ) ≤
      2 * √h * kbar FL Uu AA lhat / (1 - ρ) := by
    rw [Nat.cast_sum]
    have hk0 := kbar_nonneg (FL := FL) (Uu := Uu) (AA := AA) (lhat := lhat)
    calc ∑ j : Fin (J + 1), ((∑ c, T.bet (lds R ch FL lhat n o j) c : ℕ) : ℝ) ≤
        ∑ j : Fin (J + 1), 2 * √h * kbar FL Uu AA lhat * ρ ^ j.1 := by
          refine Finset.sum_le_sum fun j _ => ?_
          have := sum_bet_le_kbar (R := R) (ch := ch) (FL := FL) (lhat := lhat) (n := n) (o := o) hr hb hh hbD hρ hρ1
            hρD j
          linarith
      _ = 2 * √h * kbar FL Uu AA lhat * ∑ j ∈ range (J + 1), ρ ^ j := by
          rw [← Finset.mul_sum, Finset.sum_range]
      _ ≤ 2 * √h * kbar FL Uu AA lhat * (1 / (1 - ρ)) :=
          mul_le_mul_of_nonneg_left (geom_le hρ.le hρ' _) (by positivity)
      _ = _ := by ring
  exact_mod_cast h1.trans (le_YhN ρ)

omit hρ' in
include hb hρ hbD in
/-- **The gain of the tower.** -/
theorem bhat_pow_le (hh : 0 < h) (hX : 0 < Fintype.card (T.X J)) {p q : ℕ} (hpq : 2 * p ≤ q)
    (hgain : ρ ^ q * (D : ℝ) ^ p ≤ 1) :
    bhat FL Uu AA lhat ρ ^ q * (Fintype.card (T.X 0) : ℝ) ^ p ≤ (2 * (h : ℝ)) ^ q * kbar FL Uu AA lhat ^ q := by
  have hD : 0 < D := by omega
  have hDR : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hh1 : (1 : ℝ) ≤ 2 * h := by
    have : (1 : ℝ) ≤ h := by exact_mod_cast hh
    linarith
  have hk0 := kbar_nonneg (FL := FL) (Uu := Uu) (AA := AA) (lhat := lhat)
  have hXJ : (1 : ℝ) ≤ Fintype.card (T.X J) := by exact_mod_cast hX
  have hX0 : (Fintype.card (T.X 0) : ℝ) = (D : ℝ) ^ J * Fintype.card (T.X J) := card_X_pow J le_rfl
  set x : ℝ := (Fintype.card (T.X 0) : ℝ) with hx
  have hDJ : (D : ℝ) ^ J ≤ x := by
    rw [hX0]
    exact le_mul_of_one_le_right (by positivity) hXJ
  have hDJ1 : (1 : ℝ) ≤ (D : ℝ) ^ J := one_le_pow₀ hDR
  have hx1 : 1 ≤ x := hDJ1.trans hDJ
  have hx0 : 0 < x := by linarith
  set M : ℝ := max 1 (√D * ρ) with hM
  have hM0 : 0 ≤ M := le_trans zero_le_one (le_max_left _ _)
  -- the square of the base
  have hMq : (M ^ 2) ^ q ≤ (D : ℝ) ^ (q - 2 * p) := by
    have e1 : 1 ≤ (D : ℝ) ^ (q - 2 * p) := one_le_pow₀ hDR
    rcases le_total (√D * ρ) 1 with hle | hle
    · rw [hM, max_eq_left hle]
      simpa using e1
    · rw [hM, max_eq_right hle, mul_pow, Real.sq_sqrt (by linarith), mul_pow]
      have e2 : (ρ ^ 2) ^ q * ((D : ℝ) ^ p) ^ 2 ≤ 1 := by
        have : (ρ ^ 2) ^ q * ((D : ℝ) ^ p) ^ 2 = (ρ ^ q * (D : ℝ) ^ p) ^ 2 := by ring
        rw [this]
        exact pow_le_one₀ (by positivity) hgain
      have e3 : (D : ℝ) ^ q = (D : ℝ) ^ (q - 2 * p) * ((D : ℝ) ^ p) ^ 2 := by
        rw [← pow_mul, ← pow_add]
        congr 1
        omega
      rw [e3]
      calc (D : ℝ) ^ (q - 2 * p) * ((D : ℝ) ^ p) ^ 2 * (ρ ^ 2) ^ q =
          (D : ℝ) ^ (q - 2 * p) * ((ρ ^ 2) ^ q * ((D : ℝ) ^ p) ^ 2) := by ring
        _ ≤ (D : ℝ) ^ (q - 2 * p) * 1 := mul_le_mul_of_nonneg_left e2 (by positivity)
        _ = _ := mul_one _
  have hsq : (bhat FL Uu AA lhat ρ ^ q * x ^ p) ^ 2 ≤ ((2 * (h : ℝ)) ^ q * kbar FL Uu AA lhat ^ q) ^ 2 := by
    have e1 : (bhat FL Uu AA lhat ρ ^ q * x ^ p) ^ 2 =
        (2 * h / x) ^ q * ((M ^ 2) ^ q) ^ J * (kbar FL Uu AA lhat ^ q) ^ 2 * (x ^ p) ^ 2 := by
      have e0 : bhat FL Uu AA lhat ρ = √(2 * h / x) * M ^ J * kbar FL Uu AA lhat := rfl
      rw [e0]
      have e2 : √(2 * h / x) ^ 2 = 2 * h / x := Real.sq_sqrt (by positivity)
      have e3 : ∀ s : ℝ, ((s * M ^ J * kbar FL Uu AA lhat) ^ q * x ^ p) ^ 2 =
          (s ^ 2) ^ q * ((M ^ 2) ^ q) ^ J * (kbar FL Uu AA lhat ^ q) ^ 2 * (x ^ p) ^ 2 := fun s => by ring
      rw [e3, e2]
    rw [e1]
    have e3 : ((M ^ 2) ^ q) ^ J ≤ x ^ (q - 2 * p) := by
      calc ((M ^ 2) ^ q) ^ J ≤ ((D : ℝ) ^ (q - 2 * p)) ^ J := pow_le_pow_left₀ (by positivity) hMq J
        _ = ((D : ℝ) ^ J) ^ (q - 2 * p) := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
        _ ≤ _ := pow_le_pow_left₀ (by positivity) hDJ _
    have e4 : (2 * h / x) ^ q * x ^ (q - 2 * p) * (x ^ p) ^ 2 = (2 * (h : ℝ)) ^ q := by
      have : x ^ (q - 2 * p) * (x ^ p) ^ 2 = x ^ q := by
        rw [← pow_mul, ← pow_add]
        congr 1
        omega
      rw [mul_assoc, this, ← mul_pow, div_mul_cancel₀ _ hx0.ne']
    calc (2 * h / x) ^ q * ((M ^ 2) ^ q) ^ J * (kbar FL Uu AA lhat ^ q) ^ 2 * (x ^ p) ^ 2 ≤
        (2 * h / x) ^ q * x ^ (q - 2 * p) * (kbar FL Uu AA lhat ^ q) ^ 2 * (x ^ p) ^ 2 := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left e3 (by positivity)) (by positivity)) (by positivity)
      _ = (2 * h / x) ^ q * x ^ (q - 2 * p) * (x ^ p) ^ 2 * (kbar FL Uu AA lhat ^ q) ^ 2 := by ring
      _ = (2 * (h : ℝ)) ^ q * (kbar FL Uu AA lhat ^ q) ^ 2 := by rw [e4]
      _ ≤ ((2 * (h : ℝ)) ^ q) ^ 2 * (kbar FL Uu AA lhat ^ q) ^ 2 := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          have h1 : (1 : ℝ) ≤ (2 * (h : ℝ)) ^ q := one_le_pow₀ hh1
          exact le_self_pow₀ h1 (by norm_num)
      _ = _ := by ring
  have h0 : 0 ≤ (2 * (h : ℝ)) ^ q * kbar FL Uu AA lhat ^ q := by positivity
  exact (abs_le_of_sq_le_sq' hsq h0).2

/-- The norms at the start, for routes that use every edge at most `2 X₀ m` times. -/
theorem kbar_le (hm : 1 ≤ m) (hUu : Uu ≤ 2 * Fintype.card (T.X 0) * m) (hAA : AA ≤ Fintype.card (T.X 0))
    (hX : 0 < Fintype.card (T.X 0)) (hb : 0 < b) :
    kbar FL Uu AA lhat ≤ (√h * r + √FL.C₁ * FL.a₁) *
      (m * Fintype.card (T.X 0) * (lhat + 2 * (Fintype.card (T.X 0) : ℝ) ^ 2)) := by
  set X := Fintype.card (T.X 0) with hXd
  have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hn : nhat T Uu AA lhat ≤ 2 * m * (lhat + 2 * X ^ 2) := by
    unfold nhat
    rw [← hXd]
    have h1 : X * (lhat / X) ≤ lhat := Nat.mul_div_le lhat X
    calc Uu * (lhat / X + 2 * AA) ≤ 2 * X * m * (lhat / X + 2 * X) := by gcongr
      _ = 2 * m * (X * (lhat / X) + 2 * X ^ 2) := by ring
      _ ≤ 2 * m * (lhat + 2 * X ^ 2) := by gcongr
  have hnR : (nhat T Uu AA lhat : ℝ) ≤ 2 * m * (lhat + 2 * (X : ℝ) ^ 2) := by exact_mod_cast hn
  have hC := Real.sqrt_nonneg FL.C₁
  have hsh := Real.sqrt_nonneg (h : ℝ)
  have hl0 : (0 : ℝ) ≤ lhat := Nat.cast_nonneg _
  have h2 : (1 : ℝ) ≤ m * (lhat + 2 * (X : ℝ) ^ 2) := by
    have : (1 : ℝ) ≤ lhat + 2 * (X : ℝ) ^ 2 := by nlinarith
    nlinarith
  unfold kbar
  rw [← hXd]
  have p1 : √h * (r * X / 2) * nhat T Uu AA lhat ≤ √h * r * (m * X * (lhat + 2 * (X : ℝ) ^ 2)) := by
    calc √h * (r * X / 2) * nhat T Uu AA lhat ≤ √h * (r * X / 2) * (2 * m * (lhat + 2 * (X : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_left hnR (by positivity)
      _ = _ := by ring
  have p2 : √FL.C₁ * FL.a₁ / b * X ≤ √FL.C₁ * FL.a₁ * (m * X * (lhat + 2 * (X : ℝ) ^ 2)) := by
    have h3 : √FL.C₁ * FL.a₁ / b ≤ √FL.C₁ * FL.a₁ := div_le_self (by positivity) hb1
    calc √FL.C₁ * FL.a₁ / b * X ≤ √FL.C₁ * FL.a₁ * X := mul_le_mul_of_nonneg_right h3 (by positivity)
      _ = √FL.C₁ * FL.a₁ * X * 1 := (mul_one _).symm
      _ ≤ √FL.C₁ * FL.a₁ * X * (m * (lhat + 2 * (X : ℝ) ^ 2)) := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = _ := by ring
  linarith

end

end Nc.Tow
