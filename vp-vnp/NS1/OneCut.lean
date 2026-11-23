/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import NS1.Main
import NS1.Compose

/-!
# Cuts one after the other

From one cut by any factor k ≤ v ^ 64 at the scale v, cuts down to v ^ H steps: the induction on the numbers of steps,
sizes and pieces.
-/

set_option linter.unusedSectionVars false

namespace NS1

open _root_.NS1.Tree

variable {A : Type} [CommRing A] {θ : List Bool → A}

theorem Plain.mono {τ τ' : ℕ} {z : Tree} (h : Plain θ τ z) (hτ : τ ≤ τ') : Plain θ τ' z :=
  ⟨h.1, fun r hr => ⟨(h.2 r hr).1, (h.2 r hr).2.trans hτ⟩⟩

theorem CutD.mono {τ s τ' s' P t τ'' s'' P' t' : ℕ} {G : Tree} (h : CutD θ τ s τ' s' P t G) (h1 : τ' ≤ τ'')
    (h2 : s' ≤ s'') (h3 : P ≤ P') (h4 : t ≤ t') : CutD θ τ s τ'' s'' P' t' G := by
  intro z hz
  obtain ⟨Q, hD, hQ, hv⟩ := h z hz
  exact ⟨Q, hD.mono h4, fun q hq => ⟨(hQ q hq).1.trans h3, fun y hy => ((hQ q hq).2 y hy).trans h2⟩, fun hp =>
    ⟨fun q hq y hy => ((hv hp).1 q hq y hy).mono h1, (hv hp).2⟩⟩

section Iterate

variable {v a₀ α H Λ : ℕ}

/-- The hypothesis at one `v`. -/
def OneCutAt (θ : List Bool → A) (v a₀ α Λ : ℕ) : Prop := ∀ τ s k, v ^ a₀ ≤ τ → τ ≤ v ^ α → s ≤ τ →
  2 ≤ k → k ≤ v ^ 64 → ∃ G : Tree, G.size ≤ v ^ a₀ ∧ CutD θ τ s (τ * Λ / k)
    ((s / k + τ / v ^ 256) * Λ) (k * Λ) ((s + τ * k / v ^ 256) * Λ) G

set_option maxHeartbeats 1000000 in
/-- **Paper: Theorem thm:cut, the induction on (τ_i, s_i, P_i).** Cut by v^63 as long as the steps are many, and at last
once to v^H; sizes, pieces and time. -/
theorem _root_.Paper.thm_cut_iterate (hc : OneCutAt θ v a₀ α Λ) (hv : 1000 ≤ v) (hΛ2 : 2 ≤ Λ) (hΛv : Λ ≤ v) (hH : a₀ ≤ H) (hH' : 200 ≤ H) :
    ∀ r τ s c, v ^ H ≤ τ → τ ≤ v ^ α → τ * Λ < v ^ H * v ^ (64 + 62 * r) → s * v ^ 48 ≤ c * τ → 1 ≤ c →
      c * 4 ^ (r + 1) ≤ v → ∃ (G : Tree) (P t s' : ℕ), CutD θ τ s (v ^ H) s' P t G ∧
      P * v ^ H ≤ τ * (4 * Λ ^ 2) ^ (r + 1) ∧ t * v ^ 48 ≤ c * τ * (100 * Λ ^ 3) ^ (r + 1) ∧
      s' * v ^ 48 ≤ c * v ^ H * (8 * Λ) ^ (r + 1) ∧ G.size ≤ 4 ^ r * (v ^ a₀ + 3000) := by
  have hv1 : 1 ≤ v := by omega
  have hΛ1 : 1 ≤ Λ := by omega
  have ppos : ∀ a, 0 < v ^ a := fun a => Nat.pow_pos (by omega)
  have pmono : ∀ {a b}, a ≤ b → v ^ a ≤ v ^ b := fun h => Nat.pow_le_pow_right hv1 h
  -- the first cut to the target
  have base : ∀ τ s c, v ^ H ≤ τ → τ ≤ v ^ α → τ * Λ < v ^ H * v ^ 64 → s * v ^ 48 ≤ c * τ → 1 ≤ c → c ≤ v →
      ∃ (G : Tree) (P t s' : ℕ), CutD θ τ s (v ^ H) s' P t G ∧ P * v ^ H ≤ τ * (4 * Λ ^ 2) ∧
      t * v ^ 48 ≤ c * τ * (100 * Λ ^ 3) ∧ s' * v ^ 48 ≤ c * v ^ H * (8 * Λ) ∧ G.size ≤ v ^ a₀ := by
    intro τ s c hτ hτα hτΛ hs hc1 hcv
    obtain ⟨k, hk⟩ : ∃ k, k = τ * Λ / v ^ H + 1 := ⟨_, rfl⟩
    have hk1 : τ * Λ < k * v ^ H := by
      rw [hk]
      have := Nat.div_add_mod (τ * Λ) (v ^ H)
      have h2 := Nat.mod_lt (τ * Λ) (ppos H)
      rw [add_mul, one_mul, Nat.mul_comm (τ * Λ / v ^ H)]
      omega
    have hk2 : k ≤ v ^ 64 := by
      rw [hk]
      exact Nat.succ_le_of_lt ((Nat.div_lt_iff_lt_mul (ppos H)).2 (by rw [Nat.mul_comm (v ^ 64)]; exact hτΛ))
    have hk3 : k * v ^ H ≤ τ * Λ + v ^ H := by
      rw [hk, add_mul, one_mul]
      exact Nat.add_le_add_right (Nat.div_mul_le_self _ _) _
    have hk0 : 2 ≤ k := by
      rw [hk]
      have : Λ ≤ τ * Λ / v ^ H := by
        rw [Nat.le_div_iff_mul_le (ppos H), Nat.mul_comm]
        exact Nat.mul_le_mul_right _ hτ
      omega
    have hsτ : s ≤ τ := by
      have h1 : s * v ^ 48 ≤ τ * v ^ 48 := hs.trans (by
        rw [Nat.mul_comm]
        exact Nat.mul_le_mul_left _ (hcv.trans (Nat.le_self_pow (by norm_num) v)))
      exact Nat.le_of_mul_le_mul_right h1 (ppos 48)
    obtain ⟨G, hG, hcut⟩ := hc τ s k ((pmono hH).trans hτ) hτα hsτ hk0 hk2
    refine ⟨G, _, _, _, hcut.mono ?_ le_rfl le_rfl le_rfl, ?_, ?_, ?_, hG⟩
    · rw [Nat.div_le_iff_le_mul_add_pred (by omega)]
      rw [Nat.mul_comm k (v ^ H), Nat.mul_comm] at hk1
      have : v ^ H * k = k * v ^ H := Nat.mul_comm _ _
      nlinarith
    · calc k * Λ * v ^ H = k * v ^ H * Λ := by ring
        _ ≤ (τ * Λ + v ^ H) * Λ := Nat.mul_le_mul_right _ hk3
        _ ≤ (τ * Λ + τ * Λ) * Λ := Nat.mul_le_mul_right _ (Nat.add_le_add_left (hτ.trans (Nat.le_mul_of_pos_right _ hΛ1)) _)
        _ ≤ τ * (4 * Λ ^ 2) := by nlinarith [Nat.zero_le (τ * Λ ^ 2)]
    · have h1 : τ * k / v ^ 256 * v ^ 48 ≤ τ := by
        have h2 : τ * k / v ^ 256 * v ^ 256 ≤ τ * v ^ 64 :=
          (Nat.div_mul_le_self _ _).trans (Nat.mul_le_mul_left _ hk2)
        have h3 : τ * k / v ^ 256 * v ^ 48 * v ^ 208 ≤ τ * v ^ 208 := by
          calc τ * k / v ^ 256 * v ^ 48 * v ^ 208 = τ * k / v ^ 256 * v ^ 256 := by rw [Nat.mul_assoc, ← pow_add]
            _ ≤ τ * v ^ 64 := h2
            _ ≤ τ * v ^ 208 := Nat.mul_le_mul_left _ (pmono (by norm_num))
        exact Nat.le_of_mul_le_mul_right h3 (ppos 208)
      calc (s + τ * k / v ^ 256) * Λ * v ^ 48 = (s * v ^ 48 + τ * k / v ^ 256 * v ^ 48) * Λ := by ring
        _ ≤ (c * τ + c * τ) * Λ := Nat.mul_le_mul_right _ (Nat.add_le_add hs (h1.trans (Nat.le_mul_of_pos_left _ hc1)))
        _ = c * τ * (2 * Λ) := by ring
        _ ≤ c * τ * (100 * Λ ^ 3) := Nat.mul_le_mul_left _ (by
            have : Λ ≤ Λ ^ 3 := Nat.le_self_pow (by norm_num) Λ
            omega)
    · have h1 : s / k * v ^ 48 ≤ c * v ^ H := by
        have h2 : s / k * v ^ 48 * k ≤ c * v ^ H * k := by
          calc s / k * v ^ 48 * k = s / k * k * v ^ 48 := by ring
            _ ≤ s * v ^ 48 := Nat.mul_le_mul_right _ (Nat.div_mul_le_self _ _)
            _ ≤ c * τ := hs
            _ ≤ c * (τ * Λ) := Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_right _ hΛ1)
            _ ≤ c * (k * v ^ H) := Nat.mul_le_mul_left _ hk1.le
            _ = c * v ^ H * k := by ring
        exact Nat.le_of_mul_le_mul_right h2 (by omega)
      have h2 : τ / v ^ 256 * v ^ 48 ≤ c * v ^ H := by
        have h3 : τ / v ^ 256 * v ^ 48 * v ^ 208 ≤ c * v ^ H * v ^ 208 := by
          calc τ / v ^ 256 * v ^ 48 * v ^ 208 = τ / v ^ 256 * v ^ 256 := by rw [Nat.mul_assoc, ← pow_add]
            _ ≤ τ := Nat.div_mul_le_self _ _
            _ ≤ τ * Λ := Nat.le_mul_of_pos_right _ hΛ1
            _ ≤ v ^ H * v ^ 64 := hτΛ.le
            _ ≤ c * v ^ H * v ^ 208 := Nat.mul_le_mul (Nat.le_mul_of_pos_left _ hc1) (pmono (by norm_num))
        exact Nat.le_of_mul_le_mul_right h3 (ppos 208)
      calc (s / k + τ / v ^ 256) * Λ * v ^ 48 = (s / k * v ^ 48 + τ / v ^ 256 * v ^ 48) * Λ := by ring
        _ ≤ (c * v ^ H + c * v ^ H) * Λ := Nat.mul_le_mul_right _ (Nat.add_le_add h1 h2)
        _ = c * v ^ H * (2 * Λ) := by ring
        _ ≤ c * v ^ H * (8 * Λ) := Nat.mul_le_mul_left _ (by omega)
  intro r
  induction r with
  | zero =>
    intro τ s c hτ hτα hτΛ hs hc1 hcv
    obtain ⟨G, P, t, s', h1, h2, h3, h4, h5⟩ := base τ s c hτ hτα (by simpa using hτΛ) hs hc1 (by omega)
    refine ⟨G, P, t, s', h1, by simpa using h2, by simpa using h3, by simpa using h4, ?_⟩
    simp only [pow_zero, one_mul]
    omega
  | succ r ih =>
    intro τ s c hτ hτα hτΛ hs hc1 hcv
    have hc4 : 4 * c * 4 ^ (r + 1) ≤ v := by
      calc 4 * c * 4 ^ (r + 1) = c * 4 ^ (r + 1 + 1) := by rw [pow_succ 4 (r + 1)]; ring
        _ ≤ v := hcv
    have h41 : 1 ≤ 4 ^ (r + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hc4v : 4 * c ≤ v := (Nat.le_mul_of_pos_right _ h41).trans hc4
    have hX1 : 1 ≤ (4 * Λ ^ 2) ^ (r + 1) := Nat.one_le_pow _ _ (by positivity)
    have hX2 : 1 ≤ (100 * Λ ^ 3) ^ (r + 1) := Nat.one_le_pow _ _ (by positivity)
    have hX3 : 1 ≤ (8 * Λ) ^ (r + 1) := Nat.one_le_pow _ _ (by positivity)
    by_cases hbase : τ * Λ < v ^ H * v ^ 64
    · obtain ⟨G, P, t, s', h1, h2, h3, h4, h5⟩ := base τ s c hτ hτα hbase hs hc1 (by omega)
      refine ⟨G, P, t, s', h1, ?_, ?_, ?_, ?_⟩
      · refine h2.trans (Nat.mul_le_mul_left _ ?_)
        rw [pow_succ (4 * Λ ^ 2) (r + 1)]
        exact Nat.le_mul_of_pos_left _ hX1
      · refine h3.trans (Nat.mul_le_mul_left _ ?_)
        rw [pow_succ (100 * Λ ^ 3) (r + 1)]
        exact Nat.le_mul_of_pos_left _ hX2
      · refine h4.trans (Nat.mul_le_mul_left _ ?_)
        rw [pow_succ (8 * Λ) (r + 1)]
        exact Nat.le_mul_of_pos_left _ hX3
      · have : 1 ≤ 4 ^ (r + 1) := h41
        calc G.size ≤ 1 * (v ^ a₀ + 3000) := by omega
          _ ≤ 4 ^ (r + 1) * (v ^ a₀ + 3000) := Nat.mul_le_mul_right _ this
    -- one cut by v ^ 63, then the rest
    push Not at hbase
    have hsτ : s ≤ τ := by
      have h1 : s * v ^ 48 ≤ τ * v ^ 48 := hs.trans (by
        rw [Nat.mul_comm]
        exact Nat.mul_le_mul_left _ ((by omega : c ≤ v).trans (Nat.le_self_pow (by norm_num) v)))
      exact Nat.le_of_mul_le_mul_right h1 (ppos 48)
    have hk63 : 2 ≤ v ^ 63 := (by omega : 2 ≤ v).trans (Nat.le_self_pow (by norm_num) v)
    obtain ⟨G₁, hG₁, hcut₁⟩ := hc τ s (v ^ 63) ((pmono hH).trans hτ) hτα hsτ hk63 (pmono (by norm_num))
    obtain ⟨τ₁, hτ₁⟩ : ∃ n, n = τ * Λ / v ^ 63 := ⟨_, rfl⟩
    obtain ⟨s₁, hs₁⟩ : ∃ n, n = (s / v ^ 63 + τ / v ^ 256) * Λ := ⟨_, rfl⟩
    obtain ⟨t₁, ht₁⟩ : ∃ n, n = (s + τ * v ^ 63 / v ^ 256) * Λ := ⟨_, rfl⟩
    rw [← hτ₁, ← hs₁, ← ht₁] at hcut₁
    have hτ₁le : τ₁ * v ^ 63 ≤ τ * Λ := by rw [hτ₁]; exact Nat.div_mul_le_self _ _
    have hτ₁V : v ^ H ≤ τ₁ := by
      rw [hτ₁, Nat.le_div_iff_mul_le (ppos 63)]
      exact (Nat.mul_le_mul_left _ (pmono (by norm_num))).trans hbase
    have hτ₁half : τ * Λ ≤ 2 * (τ₁ * v ^ 63) := by
      have h1 := Nat.div_add_mod (τ * Λ) (v ^ 63)
      have h2 := Nat.mod_lt (τ * Λ) (ppos 63)
      have h3 : v ^ 63 ≤ τ₁ * v ^ 63 := Nat.le_mul_of_pos_left _ (lt_of_lt_of_le (ppos H) hτ₁V)
      rw [← hτ₁, Nat.mul_comm (v ^ 63)] at h1
      omega
    have hτ₁τ : τ₁ ≤ τ := by
      have : τ₁ * v ^ 63 ≤ τ * v ^ 63 := hτ₁le.trans (Nat.mul_le_mul_left _ (hΛv.trans (Nat.le_self_pow (by norm_num) v)))
      exact Nat.le_of_mul_le_mul_right this (ppos 63)
    have hτ₁Λ : τ₁ * Λ < v ^ H * v ^ (64 + 62 * r) := by
      have h1 : τ₁ * v ^ 63 < v ^ H * v ^ (63 + 62 * r) * v ^ 63 := by
        calc τ₁ * v ^ 63 ≤ τ * Λ := hτ₁le
          _ < v ^ H * v ^ (64 + 62 * (r + 1)) := hτΛ
          _ = v ^ H * v ^ (63 + 62 * r) * v ^ 63 := by
            rw [Nat.mul_assoc, ← pow_add]
            congr 2
            ring
      have h2 : τ₁ < v ^ H * v ^ (63 + 62 * r) := lt_of_mul_lt_mul_right h1 (Nat.zero_le _)
      calc τ₁ * Λ ≤ τ₁ * v := Nat.mul_le_mul_left _ hΛv
        _ < v ^ H * v ^ (63 + 62 * r) * v := Nat.mul_lt_mul_of_pos_right h2 (by omega)
        _ = v ^ H * v ^ (64 + 62 * r) := by
          rw [Nat.mul_assoc, ← pow_succ]
          congr 2
          ring
    have hs₁c : s₁ * v ^ 48 ≤ 4 * c * τ₁ := by
      have h1 : s₁ * v ^ 48 * v ^ 63 ≤ 4 * c * τ₁ * v ^ 63 := by
        have a1 : s / v ^ 63 * v ^ 63 * v ^ 48 ≤ c * τ := (Nat.mul_le_mul_right _ (Nat.div_mul_le_self _ _)).trans hs
        have a2 : τ / v ^ 256 * v ^ 63 * v ^ 48 ≤ c * τ := by
          calc τ / v ^ 256 * v ^ 63 * v ^ 48 = τ / v ^ 256 * v ^ 111 := by rw [Nat.mul_assoc, ← pow_add]
            _ ≤ τ / v ^ 256 * v ^ 256 := Nat.mul_le_mul_left _ (pmono (by norm_num))
            _ ≤ τ := Nat.div_mul_le_self _ _
            _ ≤ c * τ := Nat.le_mul_of_pos_left _ hc1
        calc s₁ * v ^ 48 * v ^ 63 = (s / v ^ 63 * v ^ 63 * v ^ 48 + τ / v ^ 256 * v ^ 63 * v ^ 48) * Λ := by
              rw [hs₁]; ring
          _ ≤ (c * τ + c * τ) * Λ := Nat.mul_le_mul_right _ (Nat.add_le_add a1 a2)
          _ = 2 * c * (τ * Λ) := by ring
          _ ≤ 2 * c * (2 * (τ₁ * v ^ 63)) := Nat.mul_le_mul_left _ hτ₁half
          _ = 4 * c * τ₁ * v ^ 63 := by ring
      exact Nat.le_of_mul_le_mul_right h1 (ppos 63)
    obtain ⟨G₂, P₂, t₂, s₂, hcut₂, hP₂, ht₂, hs₂, hG₂⟩ := ih τ₁ s₁ (4 * c) hτ₁V (hτ₁τ.trans hτα) hτ₁Λ hs₁c (by omega) hc4
    have hP : v ^ 63 * Λ * P₂ * v ^ H ≤ τ * (4 * Λ ^ 2) ^ (r + 1 + 1) := by
      calc v ^ 63 * Λ * P₂ * v ^ H = v ^ 63 * Λ * (P₂ * v ^ H) := by ring
        _ ≤ v ^ 63 * Λ * (τ₁ * (4 * Λ ^ 2) ^ (r + 1)) := Nat.mul_le_mul_left _ hP₂
        _ = τ₁ * v ^ 63 * (Λ * (4 * Λ ^ 2) ^ (r + 1)) := by ring
        _ ≤ τ * Λ * (Λ * (4 * Λ ^ 2) ^ (r + 1)) := Nat.mul_le_mul_right _ hτ₁le
        _ = τ * (Λ ^ 2 * (4 * Λ ^ 2) ^ (r + 1)) := by ring
        _ ≤ τ * (4 * Λ ^ 2 * (4 * Λ ^ 2) ^ (r + 1)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (by omega))
        _ = τ * (4 * Λ ^ 2) ^ (r + 1 + 1) := by rw [pow_succ (4 * Λ ^ 2) (r + 1)]; ring
    refine ⟨_, _, _, _, Paper.thm_cut_compose hcut₁ hcut₂, hP, ?_, ?_, ?_⟩
    · -- time
      have b1 : t₁ * v ^ 48 ≤ c * τ * (2 * Λ) := by
        have h1 : τ * v ^ 63 / v ^ 256 * v ^ 48 ≤ τ := by
          have h2 : τ * v ^ 63 / v ^ 256 * v ^ 48 * v ^ 208 ≤ τ * v ^ 208 := by
            calc τ * v ^ 63 / v ^ 256 * v ^ 48 * v ^ 208 = τ * v ^ 63 / v ^ 256 * v ^ 256 := by
                  rw [Nat.mul_assoc, ← pow_add]
              _ ≤ τ * v ^ 63 := Nat.div_mul_le_self _ _
              _ ≤ τ * v ^ 208 := Nat.mul_le_mul_left _ (pmono (by norm_num))
          exact Nat.le_of_mul_le_mul_right h2 (ppos 208)
        calc t₁ * v ^ 48 = (s * v ^ 48 + τ * v ^ 63 / v ^ 256 * v ^ 48) * Λ := by rw [ht₁]; ring
          _ ≤ (c * τ + c * τ) * Λ := Nat.mul_le_mul_right _ (Nat.add_le_add hs (h1.trans (Nat.le_mul_of_pos_left _ hc1)))
          _ = c * τ * (2 * Λ) := by ring
      have b2 : v ^ 63 * Λ * t₂ * v ^ 48 ≤ c * τ * (4 * Λ ^ 2 * (100 * Λ ^ 3) ^ (r + 1)) := by
        calc v ^ 63 * Λ * t₂ * v ^ 48 = v ^ 63 * Λ * (t₂ * v ^ 48) := by ring
          _ ≤ v ^ 63 * Λ * (4 * c * τ₁ * (100 * Λ ^ 3) ^ (r + 1)) := Nat.mul_le_mul_left _ ht₂
          _ = τ₁ * v ^ 63 * (4 * c * Λ * (100 * Λ ^ 3) ^ (r + 1)) := by ring
          _ ≤ τ * Λ * (4 * c * Λ * (100 * Λ ^ 3) ^ (r + 1)) := Nat.mul_le_mul_right _ hτ₁le
          _ = c * τ * (4 * Λ ^ 2 * (100 * Λ ^ 3) ^ (r + 1)) := by ring
      have b3 : v ^ 63 * Λ * (62 * P₂) * v ^ 48 ≤ c * τ * (4 * Λ ^ 2) ^ (r + 1 + 1) := by
        have hv62 : 62 * v ^ 48 ≤ v ^ H := by
          calc 62 * v ^ 48 ≤ v * v ^ 48 := Nat.mul_le_mul_right _ (by omega)
            _ = v ^ 49 := by rw [← pow_succ']
            _ ≤ v ^ H := pmono (by omega)
        calc v ^ 63 * Λ * (62 * P₂) * v ^ 48 = v ^ 63 * Λ * P₂ * (62 * v ^ 48) := by ring
          _ ≤ v ^ 63 * Λ * P₂ * v ^ H := Nat.mul_le_mul_left _ hv62
          _ ≤ τ * (4 * Λ ^ 2) ^ (r + 1 + 1) := hP
          _ ≤ c * (τ * (4 * Λ ^ 2) ^ (r + 1 + 1)) := Nat.le_mul_of_pos_left _ hc1
          _ = c * τ * (4 * Λ ^ 2) ^ (r + 1 + 1) := by ring
      have b4 : v ^ 63 * Λ * 110 * v ^ 48 + 100 * v ^ 48 ≤ c * τ * 2 := by
        have h1 : v ^ 63 * Λ * 110 * v ^ 48 ≤ τ := by
          calc v ^ 63 * Λ * 110 * v ^ 48 ≤ v ^ 63 * v * v * v ^ 48 :=
                Nat.mul_le_mul_right _ (Nat.mul_le_mul (Nat.mul_le_mul_left _ hΛv) (by omega))
            _ = v ^ 113 := by ring
            _ ≤ v ^ H := pmono (by omega)
            _ ≤ τ := hτ
        have h2 : 100 * v ^ 48 ≤ τ := by
          calc 100 * v ^ 48 ≤ v * v ^ 48 := Nat.mul_le_mul_right _ (by omega)
            _ = v ^ 49 := by rw [← pow_succ']
            _ ≤ v ^ H := pmono (by omega)
            _ ≤ τ := hτ
        have h3 : τ ≤ c * τ := Nat.le_mul_of_pos_left _ hc1
        omega
      have hL3 : Λ ≤ Λ ^ 3 := Nat.le_self_pow (by norm_num) Λ
      have hL2 : Λ ^ 2 ≤ Λ ^ 3 := Nat.pow_le_pow_right hΛ1 (by norm_num)
      obtain ⟨X, hX⟩ : ∃ X, X = (100 * Λ ^ 3) ^ (r + 1) := ⟨_, rfl⟩
      have c1 : 2 * Λ ≤ 2 * Λ ^ 3 * X := by
        rw [hX]
        calc 2 * Λ ≤ 2 * Λ ^ 3 * 1 := by omega
          _ ≤ _ := Nat.mul_le_mul_left _ hX2
      have c2 : 4 * Λ ^ 2 * X ≤ 4 * Λ ^ 3 * X := Nat.mul_le_mul_right _ (by omega)
      have c3 : (4 * Λ ^ 2) ^ (r + 1 + 1) ≤ 4 * Λ ^ 3 * X := by
        rw [pow_succ, hX, Nat.mul_comm]
        exact Nat.mul_le_mul (by omega) (Nat.pow_le_pow_left (by omega) _)
      have c4 : 2 ≤ 2 * Λ ^ 3 * X := by
        have : 1 ≤ Λ ^ 3 := Nat.one_le_pow _ _ hΛ1
        have hX' : 1 ≤ X := hX ▸ hX2
        calc 2 = 2 * 1 * 1 := rfl
          _ ≤ 2 * Λ ^ 3 * X := Nat.mul_le_mul (Nat.mul_le_mul_left 2 this) hX'
      have c5 : (100 * Λ ^ 3) ^ (r + 1 + 1) = 100 * Λ ^ 3 * X := by rw [pow_succ, hX]; ring
      calc (t₁ + v ^ 63 * Λ * (t₂ + 62 * P₂ + 110) + 100) * v ^ 48 = t₁ * v ^ 48 + v ^ 63 * Λ * t₂ * v ^ 48 +
            v ^ 63 * Λ * (62 * P₂) * v ^ 48 + (v ^ 63 * Λ * 110 * v ^ 48 + 100 * v ^ 48) := by ring
        _ ≤ c * τ * (2 * Λ) + c * τ * (4 * Λ ^ 2 * X) + c * τ * (4 * Λ ^ 2) ^ (r + 1 + 1) + c * τ * 2 := by
            rw [hX]
            exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add b1 b2) b3) b4
        _ = c * τ * (2 * Λ + 4 * Λ ^ 2 * X + (4 * Λ ^ 2) ^ (r + 1 + 1) + 2) := by ring
        _ ≤ c * τ * (100 * Λ ^ 3 * X) := Nat.mul_le_mul_left _ (by
            have : 2 * Λ ^ 3 * X + 4 * Λ ^ 3 * X + 4 * Λ ^ 3 * X + 2 * Λ ^ 3 * X ≤ 100 * Λ ^ 3 * X := by
              have e : 2 * Λ ^ 3 * X + 4 * Λ ^ 3 * X + 4 * Λ ^ 3 * X + 2 * Λ ^ 3 * X = 12 * (Λ ^ 3 * X) := by ring
              have e' : 100 * Λ ^ 3 * X = 100 * (Λ ^ 3 * X) := by ring
              omega
            omega)
        _ = c * τ * (100 * Λ ^ 3) ^ (r + 1 + 1) := by rw [c5]
    · calc s₂ * v ^ 48 ≤ 4 * c * v ^ H * (8 * Λ) ^ (r + 1) := hs₂
        _ = c * v ^ H * (4 * (8 * Λ) ^ (r + 1)) := by ring
        _ ≤ c * v ^ H * (8 * Λ * (8 * Λ) ^ (r + 1)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (by omega))
        _ = c * v ^ H * (8 * Λ) ^ (r + 1 + 1) := by rw [pow_succ (8 * Λ) (r + 1)]; ring
    · have := size_compC G₁ G₂
      have e : 4 ^ (r + 1) * (v ^ a₀ + 3000) = 4 * (4 ^ r * (v ^ a₀ + 3000)) := by rw [pow_succ]; ring
      have h4r : 1 ≤ 4 ^ r := Nat.one_le_pow _ _ (by norm_num)
      have : v ^ a₀ + 3000 ≤ 4 ^ r * (v ^ a₀ + 3000) := Nat.le_mul_of_pos_left _ h4r
      omega

end Iterate

theorem OneCutAt.mono {v a₀ α Λ Λ' : ℕ} (h : OneCutAt θ v a₀ α Λ) (hΛ : Λ ≤ Λ') : OneCutAt θ v a₀ α Λ' := by
  intro τ s k h1 h2 h3 h4 h5
  obtain ⟨G, hG, hcut⟩ := h τ s k h1 h2 h3 h4 h5
  exact ⟨G, hG, hcut.mono (Nat.div_le_div_right (Nat.mul_le_mul_left _ hΛ)) (Nat.mul_le_mul_left _ hΛ)
    (Nat.mul_le_mul_left _ hΛ) (Nat.mul_le_mul_left _ hΛ)⟩

/-- Powers of the logarithm that are at most `v` bound the exponent by the logarithm. -/
theorem le_lg_of_lg_pow_le {v k : ℕ} (hv : 4 ≤ v) (hk : lg v ^ k ≤ v) : k ≤ lg v := by
  have h1 : 2 ^ k < 2 ^ lg v :=
    lt_of_le_of_lt ((Nat.pow_le_pow_left (lg_ge_two hv) k).trans hk) (lt_two_pow_lg v)
  exact ((Nat.pow_lt_pow_iff_right (by norm_num)).1 h1).le

/-- The iterated cuts lose at most `v`, if `(lg v) ^ (C₀ * α) ≤ v` for the constant `C₀` below. -/
theorem polylog_loss_le {h C v α : ℕ} (hl : 100 ≤ lg v) (hα : 1 ≤ α)
    (hlog : lg v ^ ((3 * C + 4) * (32 * h + 2) * α) ≤ v) :
    (100 * (lg v ^ (C + 1)) ^ 3) ^ (16 * h * α + 1) ≤ v := by
  calc (100 * (lg v ^ (C + 1)) ^ 3) ^ (16 * h * α + 1) ≤ (lg v * (lg v ^ (C + 1)) ^ 3) ^ (16 * h * α + 1) :=
        Nat.pow_le_pow_left (Nat.mul_le_mul_right _ hl) _
    _ = lg v ^ ((3 * C + 4) * (16 * h * α + 1)) := by
        rw [← pow_mul (lg v) (C + 1) 3, ← pow_succ', ← pow_mul]
        congr 1
        ring
    _ ≤ lg v ^ ((3 * C + 4) * (32 * h + 2) * α) := Nat.pow_le_pow_right (by omega) (by
        rw [Nat.mul_assoc (3 * C + 4) (32 * h + 2)]
        refine Nat.mul_le_mul_left _ ?_
        have : (32 * h + 2) * α = 16 * h * α + 16 * h * α + 2 * α := by ring
        omega)
    _ ≤ v := hlog

end NS1
