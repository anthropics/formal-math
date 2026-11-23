/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Paper.NoAcc
import Paper.Circuit
import Paper.Cuts

/-!
# The paper, section "One scale is all scales"
-/

namespace Paper

open Finset NS1
open _root_.NS1.Tree

/-- **Paper: Definition def:acc.** "An accelerator at scale v with Q constants from R and exponent bound B is a program
D with two properties. On every instance z with |z| ≤ v^(H−32) all its runs halt, the accepting ones within v^(H−16) steps, and every name
in their bills stands for a power κ_l^(2^i) with i < B. If moreover z is v^H-plain, its value, the sum over accepting
runs of the weight times the named powers, is pv(z). The constants sit at the leaves of a binary trie with Q nodes, and
their names are paths. It is of size s if Q and the size of D are at most s and, with L = lg(max(v^H, s)), the height of
the trie is at most L² and B ≤ L³." -/
theorem def_acc {A : Type} [CommRing A] (θ : List Bool → A) (R : Type) [CommRing R] [Algebra A R] (H v s : ℕ) :
    HasAcc θ R H v s ↔ ∃ (K : KT R) (B : ℕ) (D : Tree),
      (∀ z, z.size ≤ v ^ (H - 32) → Hl θ (Fm.ofTree D) z ∧
        ∀ r ∈ evl θ (Fm.ofTree D) z, r.cost ≤ v ^ (H - 16) ∧ ∀ p ∈ r.bill, K.InB B p) ∧
      (∀ z, z.size ≤ v ^ (H - 32) → Plain θ (v ^ H) z →
        ((evl θ (Fm.ofTree D) z).map fun r => algebraMap A R r.th * (r.bill.map K.lk).prod).sum = algebraMap A R (pv θ z)) ∧
      K.nds ≤ s ∧ D.size ≤ s ∧ K.ht ≤ lg (max (v ^ H) s) ^ 2 ∧ B ≤ lg (max (v ^ H) s) ^ 3 := by
  constructor
  · rintro ⟨K, B, D, ⟨h1, h2⟩, h3, h4, h5, h6⟩
    exact ⟨K, B, D, h1, h2, h3, h4, h5, h6⟩
  · rintro ⟨K, B, D, h1, h2, h3, h4, h5, h6⟩
    exact ⟨K, B, D, ⟨h1, h2⟩, h3, h4, h5, h6⟩

/-- If circuits with M^a gates are impossible whenever (lg M)^(Ca) ≤ M, then more than 2^(c(log M)²/log log M) gates
are needed. -/
theorem quasi_of_exponents {P : ℕ → ℕ → Prop} (hmono : ∀ M s t, s ≤ t → P M s → P M t) {C M₁ : ℕ}
    (h : ∀ M ≥ M₁, ∀ a : ℕ, lg M ^ (C * a) ≤ M → ¬ P M (M ^ a)) :
    ∃ c : ℝ, 0 < c ∧ ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ s, P m s →
      (2 : ℝ) ^ (c * Real.logb 2 m ^ 2 / Real.logb 2 (Real.logb 2 m)) < s := by
  refine ⟨1 / (4 * (C + 1)), by positivity, ?_⟩
  have ht : Filter.Tendsto (fun m : ℕ => Real.logb 2 m) Filter.atTop Filter.atTop :=
    (Real.tendsto_logb_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  have ho := Real.isLittleO_log_id_atTop.bound (show (0 : ℝ) < Real.log 2 / (4 * C + 4) by positivity)
  obtain ⟨M₀, hM₀⟩ := Filter.eventually_atTop.1 ((ht.eventually ho).and (ht.eventually_ge_atTop 2))
  refine ⟨M₀ + M₁ + 2, fun m hm s hs => ?_⟩
  obtain ⟨h1, hL⟩ := hM₀ m (by omega)
  set L := Real.logb 2 m with hLd
  set l := Real.logb 2 L with hld
  have hl1 : 1 ≤ l := by
    rw [hld, Real.le_logb_iff_rpow_le (by norm_num) (by linarith), Real.rpow_one]
    exact hL
  have hlb : (4 * (C : ℝ) + 4) * l ≤ L := by
    rw [Real.norm_eq_abs, Real.norm_eq_abs, id, abs_of_nonneg (Real.log_nonneg (by linarith)),
      abs_of_nonneg (by linarith)] at h1
    have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have : l ≤ L / (4 * C + 4) := by
      rw [hld, Real.logb, div_le_iff₀ hlog]
      calc Real.log L ≤ _ := h1
        _ = _ := by field_simp
    rwa [le_div_iff₀ (by positivity), mul_comm] at this
  obtain ⟨a, ha⟩ : ∃ a, a = ⌈1 / (4 * ((C : ℝ) + 1)) * L / l⌉₊ := ⟨_, rfl⟩
  have ha1 : (a : ℝ) ≤ 1 / (4 * ((C : ℝ) + 1)) * L / l + 1 := ha ▸ (Nat.ceil_lt_add_one (by positivity)).le
  have hmR : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hlgR : (0 : ℝ) < lg m := by exact_mod_cast Nat.succ_pos _
  by_contra hb
  push Not at hb
  have hlg : Real.logb 2 (lg m) ≤ 2 * l := by
    have e : (lg m : ℝ) ≤ L ^ 2 := by
      have : ((Nat.log 2 m + 1 : ℕ) : ℝ) ≤ L + 1 := by
        push_cast
        exact add_le_add (Real.natLog_le_logb m 2) le_rfl
      calc (lg m : ℝ) ≤ L + 1 := this
        _ ≤ L ^ 2 := by nlinarith
    calc Real.logb 2 (lg m) ≤ Real.logb 2 (L ^ 2) := Real.logb_le_logb_of_le (by norm_num) hlgR e
      _ = 2 * l := by rw [Real.logb_pow]; push_cast; rfl
  have hkey : lg m ^ (C * a) ≤ m := by
    have key : ((C * a : ℕ) : ℝ) * Real.logb 2 (lg m) ≤ L := by
      push_cast
      calc (C : ℝ) * a * Real.logb 2 (lg m) ≤ C * (1 / (4 * ((C : ℝ) + 1)) * L / l + 1) * (2 * l) := by
            gcongr
            exact Real.logb_nonneg (by norm_num) (by exact_mod_cast Nat.succ_pos _)
        _ = (C : ℝ) / (C + 1) * (L / 2) + 2 * C * l := by
            field_simp
            ring
        _ ≤ 1 * (L / 2) + 2 * C * l := by
            gcongr
            rw [div_le_one (by positivity)]
            linarith
        _ ≤ L := by linarith
    have h3 := Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ 2 by norm_num) key
    rw [hLd, Real.rpow_logb (by norm_num) (by norm_num) hmR, mul_comm, Real.rpow_mul (by norm_num),
      Real.rpow_logb (by norm_num) (by norm_num) hlgR, Real.rpow_natCast] at h3
    exact_mod_cast h3
  refine h m (by omega) a hkey (hmono m s _ ?_ hs)
  have h4 : (s : ℝ) ≤ (2 : ℝ) ^ (L * a) := by
    refine hb.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_)
    rw [pow_two, ← mul_assoc, mul_div_right_comm, mul_comm L]
    exact mul_le_mul_of_nonneg_right (ha ▸ Nat.le_ceil _) (by linarith)
  rw [Real.rpow_mul (by norm_num), hLd, Real.rpow_logb (by norm_num) (by norm_num) hmR, Real.rpow_natCast] at h4
  exact_mod_cast h4

/-- "Otherwise let v = ⌊m^(1/B₀)⌋": at a large m = M it is large, v^B₀ ≤ M, and M^a ≤ v^(a′) for a′ = 2B₀a with
(lg v)^(E(a′+1)) ≤ v, if (lg M)^(Ca) ≤ M for a suitable C. -/
theorem exists_scale (B₀ E n : ℕ) (hB : 0 < B₀) : ∃ C M₁ : ℕ, ∀ M, M₁ ≤ M → ∀ a, lg M ^ (C * a) ≤ M →
    ∃ v, n ≤ v ∧ v ^ B₀ ≤ M ∧ M ^ a ≤ v ^ (2 * B₀ * a) ∧ lg v ^ (E * (2 * B₀ * a + 1)) ≤ v := by
  obtain ⟨n1, hn1⟩ := poly_lg 1 (2 * (E * (2 * B₀ + 1)))
  refine ⟨2 * (2 * B₀) * (E * (2 * B₀ + 1)), (n + n1 + 4) ^ B₀, fun M hM a ha => ?_⟩
  obtain ⟨v, hv, hvM, hMv⟩ := exists_root B₀ (n + n1 + 4) M hB hM
  have hM2 : M ≤ v ^ (2 * B₀) := by
    refine hMv.le.trans ((Nat.pow_le_pow_left (aux3 (show 2 ≤ v by omega)) B₀).trans (le_of_eq ?_))
    rw [← pow_mul]
  refine ⟨v, by omega, hvM, (Nat.pow_le_pow_left hM2 a).trans (le_of_eq (pow_mul _ _ _).symm), ?_⟩
  refine le_trans (Nat.pow_le_pow_right (Nat.succ_pos _) ?_) (lg_pow_transport (b := 2 * B₀) (by omega)
    ((Nat.le_self_pow (by omega) v).trans hvM) hM2 ha (by simpa using hn1 v (by omega)))
  rw [mul_assoc E (2 * B₀ + 1)]
  refine Nat.mul_le_mul_left E ?_
  calc 2 * B₀ * a + 1 ≤ (2 * B₀ + 1) * a + (2 * B₀ + 1) := by rw [add_mul]; omega
    _ = (2 * B₀ + 1) * (a + 1) := by ring

/-- **Paper: "We keep A and H of Theorem thm:cut".** In the contracting case there are the ring A, its generators and
H = 16 h₀ with the conclusion of Theorem thm:cut, and for them Proposition prop:next and Theorem thm:noacc hold. -/
theorem scales_setting {K : Type} [Field K] (hK : Contracting K) :
    ∃ (A : Subring K) (_ : Algebra.FiniteType ℤ A) (θ : List Bool → A) (h C₀ v₀ : ℕ),
      Generates θ ∧ 17 ≤ h ∧ CutHyp θ (16 * h) C₀ v₀ ∧
      (∀ k, ∃ C v₁ : ℕ, ∀ (R : Type) [CommRing R] [Algebra A R], ∀ v, v₁ ≤ v → ∀ α, 5 ≤ α → lg v ^ (C * α) ≤ v →
        ∀ (K : KT R) (B : ℕ) (D : Tree),
        IsAccT θ (16 * h) v (v ^ (16 * h - 16)) K B D → K.nds ≤ v ^ (h * α) → D.size ≤ v ^ (h * α) →
        B ≤ (α * lg v) ^ k → K.ht ≤ (α * lg v) ^ k →
        ∃ D', IsAccT θ (16 * h) (v ^ α) ((v ^ α) ^ (16 * h - 17)) K (B + 51 * h * α ^ 2 * lg v) D' ∧
          D'.size ≤ (v ^ α) ^ (4 * h)) ∧
      ∃ C v₁ : ℕ, ∀ v, v₁ ≤ v → ∀ a, lg v ^ (C * a) ≤ v → ∀ (R : Type) [CommRing R] [Nontrivial R] [Algebra A R],
        ¬ HasAcc θ R (16 * h) v (v ^ a) := by
  obtain ⟨A, hA, θ, h, C₀, v₀, hθ, hh, hcut⟩ := exists_setting hK
  exact ⟨A, hA, θ, h, C₀, v₀, hθ, hh, hcut, fun k => prop_next hh hcut k, thm_noacc hh hcut⟩

/-- The contracting case for a family that is complete for grid sums. -/
theorem contracting_complete {K : Type} [Field K] (hK : Contracting K)
    {G : ∀ S, MvPolynomial (Fin S × Fin S) K} {κ : ℕ} (hG : Nc.GridComplete K G κ) :
    ∃ C M₁ : ℕ, ∀ M ≥ M₁, ∀ a : ℕ, lg M ^ (C * a) ≤ M → ¬ Nc.Computes (G M) (M ^ a) := by
  obtain ⟨A, hA, θ, h, C₀, v₀, hθ, hh, -, -, C₂, v₂, hno⟩ := scales_setting hK
  obtain ⟨B₀, C₁, v₁, hB₀, hacc⟩ := lem_circuit hθ.1 (H := 16 * h) (by omega) κ
  obtain ⟨C, M₁, hscale⟩ := exists_scale B₀ ((C₂ + 1) * C₁) (v₁ + v₂ + 4) hB₀
  refine ⟨C, M₁, fun M hM a ha hcomp => ?_⟩
  obtain ⟨v, hv, hvM, hsize, hlog⟩ := hscale M hM a ha
  have hl1 : 1 ≤ lg v := Nat.succ_pos _
  refine hno v (by omega) (C₁ * (2 * B₀ * a + 1)) (le_trans (Nat.pow_le_pow_right hl1 ?_) hlog) K
    (hacc K G hG v (by omega) (2 * B₀ * a) (le_trans (Nat.pow_le_pow_right hl1 ?_) hlog) M hvM (hcomp.mono hsize))
  · rw [← mul_assoc]
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.le_succ _))
  · exact Nat.mul_le_mul (Nat.le_mul_of_pos_left _ (Nat.succ_pos _)) (Nat.le_succ _)

/-- **Paper: Theorem thm:contracting.** "In the contracting case there are c > 0 and m₀ such that for m ≥ m₀ every
circuit over k for PERM_m has more than 2^(c(log m)²/log log m) gates." -/
theorem thm_contracting {K : Type} [Field K] (hK : Contracting K) (h2 : (2 : K) ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ s, Nc.Computes (Nc.genPerm K m) s →
      (2 : ℝ) ^ (c * Real.logb 2 m ^ 2 / Real.logb 2 (Real.logb 2 m)) < s := by
  obtain ⟨C, M₁, h⟩ := contracting_complete hK (gridComplete_perm h2)
  exact quasi_of_exponents (P := fun M s => Nc.Computes (Nc.genPerm K M) s)
    (fun _ _ _ hst hs => Nc.Computes.mono hs hst) h

end Paper
