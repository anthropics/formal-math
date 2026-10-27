/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Eight.ViaGrouping.LevelNet
public import Eight.Level.Arith
public import Eight.Level.Min
public import StepMachines.Prog.GridLoop
import Mathlib.Tactic

/-! # The cost of one level, on an algorithm for networks in the printed form

`stLevelP_of`: the paragraph «Cost» of the proof of Proposition 3, for the algorithm `levelAlgP`
(proof/networks/Eight/ViaGrouping/LevelDefs.lean), which calls an algorithm for networks as
Definition 2 prints them. For every ι : ℛ → {0, …, t}, t = ⌈λ/3⌉, that algorithm is run on
the network with the smaller total, which is at most N(ρ + 1/g) + 2g⁴, ρ = 11/12; both networks
satisfy Definition 2 with P = g³λ, so that gP = N, and this P is what the algorithm is given; there
are (t + 1)^{|ℛ|} functions ι; the values add up to 2^{t|ℛ|}·Z, and
the last step divides.
The proof follows the paragraph: the bound of Lemma 1 (`Correct`) is applied to the network
`levelNetP` of ι, which satisfies Definition 2 as printed by the sentence «Both networks satisfy
Definition 2 …» (`levelNetP_isNetworkP_of`, proof/networks/Eight/ViaGrouping/LevelNet.lean), has
the value Z_ι (`value_levelNetP`) and the total of the display (`U_levelNetP`). The other facts are
those of proof/networks/Eight/SecLevel_GridWords.lean and proof/networks/Eight/Level/Min.lean:
display (34) (`eqExpansion_words`), the bound on the values (`netOfι_sized_t`), display (36)
(`stMin`). -/

public section

namespace Eight.ViaGrouping

open Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Stepped Finset Eight.SecNetworks Eight.Level

/-- The paragraph «Cost» of the proof of Proposition 3, with ρ = 11/12, for the algorithm
`levelAlgP`: the bound of Lemma 1 is applied to the row network or the column network of ι, a
network in the sense of Definition 2 (`levelNetP_isNetworkP_of`); then displays (34) and (36). The
hypothesis: the procedures for W_a and f_{a,a'} present the
two networks. Same as in the paper, except for what LevelNet.lean lists for the two networks, and
that sizes are bounded too. -/
theorem stLevelP_of (hPr : StPresents) : StLevelP := by
  intro K g e psiR psiC NA hK hg h0 hΨr hΨc h
  have hg1 : 1 ≤ g := by omega
  obtain ⟨a, ha1, ha⟩ := levelNetP_isNetworkP_of hPr g hg1
  obtain ⟨A, hA⟩ := h.absorb
  obtain ⟨A1, hA1⟩ := level_time g K a A hK hg h0 (nRect g)
  obtain ⟨A2, hA2⟩ := level_size g a A (nRect g)
  refine ⟨A1 + A2, fun C _ lam R c B t S Rm hl ht hR => ?_⟩
  obtain ⟨n, hn⟩ : ∃ n, n = lam c := ⟨_, rfl⟩
  rw [← hn] at hl hR ⊢
  obtain ⟨M, hM⟩ : ∃ M, M = (tOf n + 1) * nRect g := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P, P = g ^ 3 * n := ⟨_, rfl⟩
  obtain ⟨B', hB'⟩ : ∃ B', B' = g * B + g ^ 2 * tOf n := ⟨_, rfl⟩
  obtain ⟨t', ht'⟩ : ∃ t', t' = a * (B + n) ^ a * t := ⟨_, rfl⟩
  obtain ⟨S', hS'⟩ : ∃ S', S' = S + a * (size c + B + n) ^ a := ⟨_, rfl⟩
  obtain ⟨Zt, hZt⟩ : ∃ Zt : ℕ → ℤ, Zt = fun y => Zι (gridR0 g g n Rm) (Level.patOf g n y) := ⟨_, rfl⟩
  have htn : tOf n ≤ n := by unfold tOf; omega
  have hP1 : 1 ≤ P := by rw [hP]; exact Nat.mul_pos (pow_pos hg1 3) hl
  have ht'1 : 1 ≤ t' := by
    rw [ht']
    exact Nat.mul_pos (Nat.mul_pos (by omega) (pow_pos (by omega) a)) ht
  have hNp : (tOf n + 1) ^ nRect g ≤ 2 ^ M := by
    rw [hM, pow_mul]
    exact Nat.pow_le_pow_left Nat.lt_two_pow_self.le _
  have hBd : BoundedInst n B Rm := fun v θ h1 h2 => (hR v θ h1 h2).2
  -- the two networks of ι: «Both networks satisfy Definition 2 …», «the value is Z_ι», the totals
  obtain ⟨Nr, hNr⟩ : ∃ Nr : ℕ → Net g, Nr = fun y => levelNetP g false n y Rm := ⟨_, rfl⟩
  obtain ⟨Nc, hNc⟩ : ∃ Nc : ℕ → Net g, Nc = fun y => levelNetP g true n y Rm := ⟨_, rfl⟩
  have hnet : ∀ y < (tOf n + 1) ^ nRect g,
      (IsNetworkP (levelProcs g false psiR lam R) (c, y) (Nr y) P (B' + 1) t' (S' + 2) ∧ (Nr y).value = Zt y ∧ (Nr y).U = totalG eightF g g false 0 n y) ∧
      (IsNetworkP (levelProcs g true psiC lam R) (c, y) (Nc y) P (B' + 1) t' (S' + 2) ∧ (Nc y).value = Zt y ∧ (Nc y).U = totalG eightF g g true 0 n y) := by
    intro y hy
    rw [hNr, hNc]
    refine ⟨⟨?_, ?_, U_levelNetP g false n y Rm⟩, ⟨?_, ?_, U_levelNetP g true n y Rm⟩⟩
    · have h1 := ha false psiR hΨr C lam R c B t S Rm y (hn ▸ hl) ht (hn ▸ hy) (hn ▸ hR)
      rw [← hn] at h1
      rw [hP, hB', ht', hS']
      exact h1
    · rw [hZt]; exact value_levelNetP hl g false y Rm
    · have h1 := ha true psiC hΨc C lam R c B t S Rm y (hn ▸ hl) ht (hn ▸ hy) (hn ▸ hR)
      rw [← hn] at h1
      rw [hP, hB', ht', hS']
      exact h1
    · rw [hZt]; exact value_levelNetP hl g true y Rm
  obtain ⟨Ub, hUb⟩ : ∃ Ub : ℝ, Ub = rho * ((g : ℝ) ^ 4 * n) + (g : ℝ) ^ 3 * n + 2 * (g : ℝ) ^ 4 := ⟨_, rfl⟩
  -- one ι
  have key : ∀ y : ℕ, ∃ τ : ℕ, y < (tOf n + 1) ^ nRect g →
      (Stepped.ite (useRowP g lam) (NA.app (levelProcs g false psiR lam R)) (NA.app (levelProcs g true psiC lam R))).Runs (c, y) τ
        (S' + A * (size c + (M + 1) + P + B') ^ A + 1) (Zt y) ∧
      (τ : ℝ) + 1 ≤ ((A : ℝ) + 1) * (2 : ℝ) ^ (e * Ub + (e + 2) * ((g : ℝ) * P) / K) * ((P : ℝ) + B') ^ A * t' := by
    intro y
    by_cases hy : y < (tOf n + 1) ^ nRect g
    swap
    · exact ⟨0, fun h => absurd h hy⟩
    obtain ⟨⟨hpr, hvr, hur⟩, ⟨hpc, hvc, huc⟩⟩ := hnet y hy
    have hsz : size (c, y) ≤ size c + (M + 1) := by
      have := Nat.size_le.2 (hy.trans_le hNp)
      simp only [size_prod, size_nat]
      omega
    have hmonoS : S' + A * (size (c, y) + P + B') ^ A ≤ S' + A * (size c + (M + 1) + P + B') ^ A :=
      Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)) _
    have hmin := stMin g n y hl
    have tail : ∀ U τ : ℕ, U ≤ min (totalG eightF g g false 0 n y) (totalG eightF g g true 0 n y) →
        (τ : ℝ) ≤ A * (2 : ℝ) ^ (e * (U : ℝ) + (e + 2) * ((g : ℝ) * P) / K) * ((P : ℝ) + B') ^ A * t' →
        (τ : ℝ) + 1 ≤ ((A : ℝ) + 1) * (2 : ℝ) ^ (e * Ub + (e + 2) * ((g : ℝ) * P) / K) * ((P : ℝ) + B') ^ A * t' := by
      intro U τ hU hτ
      have hU' : (U : ℝ) ≤ Ub := by
        have : (U : ℝ) ≤ ((min (totalG eightF g g false 0 n y) (totalG eightF g g true 0 n y) : ℕ) : ℝ) := by exact_mod_cast hU
        rw [hUb]
        linarith
      have hUb0 : 0 ≤ Ub := le_trans (Nat.cast_nonneg U) hU'
      have hX : (1 : ℝ) ≤ (2 : ℝ) ^ (e * Ub + (e + 2) * ((g : ℝ) * P) / K) :=
        Real.one_le_rpow (by norm_num)
          (add_nonneg (mul_nonneg h0 hUb0) (div_nonneg (mul_nonneg (by linarith) (by positivity)) (Nat.cast_nonneg _)))
      have hY : (1 : ℝ) ≤ ((P : ℝ) + B') ^ A := by
        refine one_le_pow₀ ?_
        have h5 : (1 : ℝ) ≤ P := by exact_mod_cast hP1
        have h6 : (0 : ℝ) ≤ (B' : ℝ) := Nat.cast_nonneg _
        linarith
      have htr : (1 : ℝ) ≤ t' := by exact_mod_cast ht'1
      have h3 := one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hX hY) htr
      have h4 : (τ : ℝ) ≤ A * (2 : ℝ) ^ (e * Ub + (e + 2) * ((g : ℝ) * P) / K) * ((P : ℝ) + B') ^ A * t' := by
        refine hτ.trans ?_
        gcongr
        norm_num
      calc _ ≤ _ := add_le_add h4 h3
        _ = _ := by ring
    by_cases hu : totalG eightF g g false 0 n y ≤ totalG eightF g g true 0 n y
    · obtain ⟨τ, hτ1, hτ2⟩ := hA _ (levelProcs g false psiR lam R) (c, y) (Nr y) P B' t' S' hpr
      rw [hvr] at hτ1
      have hdec : useRowP g lam (c, y) = true := by
        show decide (totalG eightF g g false 0 (lam c) y ≤ totalG eightF g g true 0 (lam c) y) = true
        rw [← hn]
        exact decide_eq_true hu
      exact ⟨τ, fun _ => ⟨ite_runs_true hdec (hτ1.mono le_rfl hmonoS), tail _ _ (by rw [min_eq_left hu, hur]) hτ2⟩⟩
    · obtain ⟨τ, hτ1, hτ2⟩ := hA _ (levelProcs g true psiC lam R) (c, y) (Nc y) P B' t' S' hpc
      rw [hvc] at hτ1
      have hdec : useRowP g lam (c, y) = false := by
        show decide (totalG eightF g g false 0 (lam c) y ≤ totalG eightF g g true 0 (lam c) y) = false
        rw [← hn]
        exact decide_eq_false hu
      exact ⟨τ, fun _ => ⟨ite_runs_false hdec (hτ1.mono le_rfl hmonoS), tail _ _ (by rw [min_eq_right (not_le.1 hu).le, huc]) hτ2⟩⟩
  choose τ hτ using key
  -- the loop
  obtain ⟨v, hv⟩ : ∃ v, v = g * (P + B') + g * g * B' := ⟨_, rfl⟩
  have hN : numPat8 g lam c = (tOf n + 1) ^ nRect g := by rw [hn]; rfl
  have habs : ∀ y < (tOf n + 1) ^ nRect g, (Zt y).natAbs ≤ 2 ^ v := fun y hy => by
    have h0 : Network.value (J := Fin g) (netOfι g false n y Rm) = Zt y := by rw [hZt]; exact value_netOfι hl g false y Rm
    have h1 := abs_value_le (J := Fin g) (netOfι g false n y Rm) (netOfι_sized_t hl g false y hBd)
    rw [h0, Int.abs_eq_natAbs, Fintype.card_fin, ← hP, ← hB', ← hv] at h1
    exact_mod_cast h1
  have hrun := sumRange_runs (N := numPat8 g lam) (a := c)
    (M := Stepped.ite (useRowP g lam) (NA.app (levelProcs g false psiR lam R)) (NA.app (levelProcs g true psiC lam R)))
    τ Zt (2 ^ v) (S' + A * (size c + (M + 1) + P + B') ^ A + 1)
    (fun y hy => (hτ y (hN ▸ hy)).1) (fun y hy => habs y (hN ▸ hy))
  rw [hN] at hrun
  -- the division
  have hZ : ((2 : ℤ) ^ tOf n) ^ nRect g * Inst.ZW n [] Rm = ∑ y ∈ range ((tOf n + 1) ^ nRect g), Zt y := by
    rw [hZt, ← pow_mul]
    exact eqExpansion_words hl Rm
  have hdiv : (∑ y ∈ range ((tOf n + 1) ^ nRect g), Zt y) / ((2 ^ (tOf (lam c) * nRect g) : ℕ) : ℤ) = Inst.ZW n [] Rm := by
    rw [← hZ, ← hn, ← pow_mul]
    push_cast
    exact Int.mul_ediv_cancel_left _ (by positivity)
  have hfin := ofFun_runs (fun p : C × ℤ => p.2 / ((2 ^ (tOf (lam p.1) * nRect g) : ℕ) : ℤ)) (c, ∑ y ∈ range ((tOf n + 1) ^ nRect g), Zt y)
  simp only [hdiv] at hfin
  have hall := bind_runs hrun hfin
  refine ⟨_, hall.mono le_rfl ?_, ?_⟩
  · -- sizes
    have h2 := hA2 (size c) B n M P B' hl
      (by
        rw [hM]
        calc (tOf n + 1) * nRect g ≤ 2 * n * nRect g := Nat.mul_le_mul_right _ (by omega)
          _ = 2 * nRect g * n := by ring)
      hP.le
      (by
        have e : (g + 2 * g ^ 2) * (B + n) = g * B + g ^ 2 * n + (g * n + 2 * g ^ 2 * B + g ^ 2 * n) := by ring
        have e2 : g ^ 2 * tOf n ≤ g ^ 2 * n := Nat.mul_le_mul_left _ htn
        omega)
    have h3 : A2 * (size c + B + n) ^ A2 ≤ (A1 + A2) * (size c + B + n) ^ (A1 + A2) :=
      Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right (by omega) (by omega))
    have s1 : size ((tOf n + 1) ^ nRect g) ≤ M + 2 := by
      rw [size_nat]
      have := Nat.size_le_size hNp
      rw [Nat.size_pow] at this
      omega
    have hNV : (tOf n + 1) ^ nRect g * 2 ^ v ≤ 2 ^ (M + v) := by
      rw [pow_add]
      exact Nat.mul_le_mul_right _ hNp
    have s2 : size ((tOf n + 1) ^ nRect g * 2 ^ v) ≤ M + v + 2 := by
      rw [size_nat]
      have := Nat.size_le_size hNV
      rw [Nat.size_pow] at this
      omega
    have hSum : (∑ y ∈ range ((tOf n + 1) ^ nRect g), Zt y).natAbs ≤ 2 ^ (M + v) := by
      refine (Int.natAbs_sum_le _ _).trans (le_trans ?_ hNV)
      calc ∑ y ∈ range ((tOf n + 1) ^ nRect g), (Zt y).natAbs ≤ ∑ _y ∈ range ((tOf n + 1) ^ nRect g), 2 ^ v :=
            Finset.sum_le_sum fun y hy => habs y (Finset.mem_range.1 hy)
        _ = (tOf n + 1) ^ nRect g * 2 ^ v := by rw [Finset.sum_const, card_range, smul_eq_mul]
    have s3 : size (∑ y ∈ range ((tOf n + 1) ^ nRect g), Zt y) ≤ M + v + 2 := by
      rw [size_int]
      have := Nat.size_le_size hSum
      rw [Nat.size_pow] at this
      omega
    have hZle : (Inst.ZW n [] Rm).natAbs ≤ 2 ^ (M + v) := by
      refine le_trans ?_ hSum
      rw [← hZ, Int.natAbs_mul]
      exact Nat.le_mul_of_pos_left _ (Int.natAbs_pos.2 (by positivity))
    have s4 : size (Inst.ZW n [] Rm) ≤ M + v + 2 := by
      rw [size_int]
      have := Nat.size_le_size hZle
      rw [Nat.size_pow] at this
      omega
    simp only [size_prod]
    rw [hS']
    omega
  · -- steps
    have hsum : ((∑ y ∈ range ((tOf n + 1) ^ nRect g), (τ y + 1) : ℕ) : ℝ) ≤ (((tOf n + 1) ^ nRect g : ℕ) : ℝ) *
        (((A : ℝ) + 1) * (2 : ℝ) ^ (e * Ub + (e + 2) * ((g : ℝ) * P) / K) * ((P : ℝ) + B') ^ A * t') := by
      rw [Nat.cast_sum]
      calc _ ≤ ∑ _y ∈ range ((tOf n + 1) ^ nRect g),
            (((A : ℝ) + 1) * (2 : ℝ) ^ (e * Ub + (e + 2) * ((g : ℝ) * P) / K) * ((P : ℝ) + B') ^ A * t') :=
            Finset.sum_le_sum fun y hy => by
              have := (hτ y (Finset.mem_range.1 hy)).2
              push_cast
              exact this
        _ = _ := by rw [Finset.sum_const, card_range, nsmul_eq_mul]
    have h4 := hA1 B n t hl ht
    rw [← hP, ← hB', ← ht', ← hUb] at h4
    have h5 : ((∑ y ∈ range ((tOf n + 1) ^ nRect g), (τ y + 1) + 1 + 1 : ℕ) : ℝ) =
        ((∑ y ∈ range ((tOf n + 1) ^ nRect g), (τ y + 1) : ℕ) : ℝ) + 2 := by push_cast; ring
    rw [h5]
    refine le_trans (by linarith) (h4.trans ?_)
    have hBl : (1 : ℝ) ≤ (B : ℝ) + n := by
      have h5 : (1 : ℝ) ≤ n := by exact_mod_cast hl
      have h6 : (0 : ℝ) ≤ (B : ℝ) := Nat.cast_nonneg _
      linarith
    gcongr
    · exact_mod_cast Nat.le_add_right A1 A2
    · exact Nat.le_add_right A1 A2

end Eight.ViaGrouping
