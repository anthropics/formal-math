/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Printed.LevelNetworks
public import Eight.ViaGrouping.Level
import Mathlib.Tactic

/-! # Proof of Proposition 3, «Cost», with a table query at the cost of one operation

The counterpart of `Eight.ViaGrouping.stLevelP_of` (proof/networks/Eight/ViaGrouping/Level.lean) for
the machine `levelMachine`. With the tables built in, that machine is the step machine of
proof/networks/Eight/ with `networkOnSteps` in the place of the algorithm for networks
(`levelMachine_close`). The bound of Lemma 1 enters through `StOnProcedures`, applied to the row
network or the column network of ι,
a network in the sense of Definition 2 with the printed B₁ given (`grid_isNetwork_of`). The other
facts are those of proof/networks/Eight/: the expansion Σ_ι Z_ι = 2^{t|ℛ|}·Z (`eqExpansion_words`),
the bound on the values (`netOfι_sized_t`), the smaller total (`stMin`), and the arithmetic
(`Eight.Level.level_time`, `level_size`).
At the end `QueryMachines.stClose` reads the number of steps as own steps plus queries. -/

public section

namespace Printed

open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines QueryMachines.QueryMachine

/-! ## Arithmetic -/

/-- A list of units of length n has size 2n + 1. -/
theorem size_units (l : List Unit) : size l = 2 * l.length + 1 := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    simp only [size_list, List.map_cons, List.sum_cons, size_unit, List.length_cons] at ih ⊢
    omega

/-- «Cost», the number of steps, with the printed B₁ = gB + g²λ + 1 and the factor 3 of
`StOnProcedures`: from `Eight.Level.level_time` at B + gλ + 1 in the place of B. -/
theorem level_time_printed (g K a C₁ : ℕ) {e : ℝ} (hK : 2 ≤ K) (hg : K ≤ g) (h0 : 0 ≤ e) (Rn : ℕ) : ∃ A1 : ℕ, ∀ B lam : ℕ, 1 ≤ lam →
    (((tOf lam + 1) ^ Rn : ℕ) : ℝ) * ((((3 * C₁ : ℕ) : ℝ) + 1)
        * (2 : ℝ) ^ (e * (rho * ((g : ℝ) ^ 4 * lam) + (g : ℝ) ^ 3 * lam + 2 * (g : ℝ) ^ 4) + (e + 2) * ((g : ℝ) * ((g ^ 3 * lam : ℕ) : ℝ)) / K)
        * (((g ^ 3 * lam : ℕ) : ℝ) + ((g * B + g ^ 2 * lam + 1 : ℕ) : ℝ)) ^ C₁ * ((a * (B + lam) ^ a : ℕ) : ℝ)) + 2
      ≤ (A1 : ℝ) * (2 : ℝ) ^ (((rho + 2 / K) * e + 2 / K) * (((g * g : ℕ) : ℝ)) ^ 2 * (lam : ℝ)) * ((B : ℝ) + lam) ^ A1 := by
  obtain ⟨A1, hA1⟩ := level_time g K a (3 * C₁) hK hg h0 Rn
  obtain ⟨A', hA'⟩ : ∃ A' : ℕ, A' = A1 * (g + 2) ^ A1 + A1 := ⟨_, rfl⟩
  refine ⟨A', fun B lam hl => ?_⟩
  have hg1 : 1 ≤ g := by omega
  have h := hA1 (B + g * lam + 1) lam 1 hl le_rfl
  have hX1 : 0 ≤ (2 : ℝ) ^ (e * (rho * ((g : ℝ) ^ 4 * lam) + (g : ℝ) ^ 3 * lam + 2 * (g : ℝ) ^ 4) + (e + 2) * ((g : ℝ) * ((g ^ 3 * lam : ℕ) : ℝ)) / K) := by positivity
  have hX : 0 ≤ (2 : ℝ) ^ (((rho + 2 / K) * e + 2 / K) * (((g * g : ℕ) : ℝ)) ^ 2 * (lam : ℝ)) := by positivity
  generalize (2 : ℝ) ^ (e * (rho * ((g : ℝ) ^ 4 * lam) + (g : ℝ) ^ 3 * lam + 2 * (g : ℝ) ^ 4) + (e + 2) * ((g : ℝ) * ((g ^ 3 * lam : ℕ) : ℝ)) / K) = X1 at h hX1 ⊢
  generalize (2 : ℝ) ^ (((rho + 2 / K) * e + 2 / K) * (((g * g : ℕ) : ℝ)) ^ 2 * (lam : ℝ)) = X at h hX ⊢
  have hb : g ^ 3 * lam + (g * B + g ^ 2 * lam + 1) ≤ g ^ 3 * lam + (g * (B + g * lam + 1) + g ^ 2 * tOf lam) := by
    have e1 : g * (B + g * lam + 1) = g * B + g ^ 2 * lam + g := by ring
    omega
  have hp : (((g ^ 3 * lam : ℕ) : ℝ) + ((g * B + g ^ 2 * lam + 1 : ℕ) : ℝ)) ^ C₁ ≤ (((g ^ 3 * lam : ℕ) : ℝ) + ((g * (B + g * lam + 1) + g ^ 2 * tOf lam : ℕ) : ℝ)) ^ (3 * C₁) := by
    have h1 : (g ^ 3 * lam + (g * B + g ^ 2 * lam + 1)) ^ C₁ ≤ (g ^ 3 * lam + (g * (B + g * lam + 1) + g ^ 2 * tOf lam)) ^ (3 * C₁) :=
      (Nat.pow_le_pow_left hb C₁).trans (Nat.pow_le_pow_right (by omega) (by omega))
    exact_mod_cast h1
  have ht : ((a * (B + lam) ^ a : ℕ) : ℝ) ≤ ((a * (B + g * lam + 1 + lam) ^ a * 1 : ℕ) : ℝ) := by
    have h1 : a * (B + lam) ^ a ≤ a * (B + g * lam + 1 + lam) ^ a * 1 := by
      rw [Nat.mul_one]
      exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) a)
    exact_mod_cast h1
  have hq : ((B + g * lam + 1 : ℕ) : ℝ) + lam ≤ ((g + 2 : ℕ) : ℝ) * ((B : ℝ) + lam) := by
    have h1 : B + g * lam + 1 + lam ≤ (g + 2) * (B + lam) := by
      have e1 : (g + 2) * (B + lam) = g * B + g * lam + 2 * B + 2 * lam := by ring
      omega
    exact_mod_cast h1
  have hY1 : (1 : ℝ) ≤ (B : ℝ) + lam := by
    have h5 : (1 : ℝ) ≤ lam := by exact_mod_cast hl
    have h6 : (0 : ℝ) ≤ (B : ℝ) := Nat.cast_nonneg _
    linarith
  have hq2 : (((B + g * lam + 1 : ℕ) : ℝ) + lam) ^ A1 ≤ ((g + 2 : ℕ) : ℝ) ^ A1 * ((B : ℝ) + lam) ^ A' := by
    calc (((B + g * lam + 1 : ℕ) : ℝ) + lam) ^ A1 ≤ (((g + 2 : ℕ) : ℝ) * ((B : ℝ) + lam)) ^ A1 := pow_le_pow_left₀ (by positivity) hq A1
      _ = ((g + 2 : ℕ) : ℝ) ^ A1 * ((B : ℝ) + lam) ^ A1 := mul_pow _ _ _
      _ ≤ ((g + 2 : ℕ) : ℝ) ^ A1 * ((B : ℝ) + lam) ^ A' := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hY1 (by omega)) (by positivity)
  have hc : (A1 : ℝ) * ((g + 2 : ℕ) : ℝ) ^ A1 ≤ (A' : ℝ) := by
    have h1 : A1 * (g + 2) ^ A1 ≤ A' := by omega
    exact_mod_cast h1
  have hfirst : (((tOf lam + 1) ^ Rn : ℕ) : ℝ) * ((((3 * C₁ : ℕ) : ℝ) + 1) * X1 * (((g ^ 3 * lam : ℕ) : ℝ) + ((g * B + g ^ 2 * lam + 1 : ℕ) : ℝ)) ^ C₁ * ((a * (B + lam) ^ a : ℕ) : ℝ)) + 2
      ≤ (((tOf lam + 1) ^ Rn : ℕ) : ℝ) * ((((3 * C₁ : ℕ) : ℝ) + 1) * X1 * (((g ^ 3 * lam : ℕ) : ℝ) + ((g * (B + g * lam + 1) + g ^ 2 * tOf lam : ℕ) : ℝ)) ^ (3 * C₁)
        * ((a * (B + g * lam + 1 + lam) ^ a * 1 : ℕ) : ℝ)) + 2 := by gcongr
  refine hfirst.trans (h.trans ?_)
  calc (A1 : ℝ) * X * (((B + g * lam + 1 : ℕ) : ℝ) + lam) ^ A1 * ((1 : ℕ) : ℝ) = (A1 : ℝ) * X * (((B + g * lam + 1 : ℕ) : ℝ) + lam) ^ A1 := by rw [Nat.cast_one, mul_one]
    _ ≤ (A1 : ℝ) * X * (((g + 2 : ℕ) : ℝ) ^ A1 * ((B : ℝ) + lam) ^ A') := mul_le_mul_of_nonneg_left hq2 (by positivity)
    _ = ((A1 : ℝ) * ((g + 2 : ℕ) : ℝ) ^ A1) * X * ((B : ℝ) + lam) ^ A' := by ring
    _ ≤ (A' : ℝ) * X * ((B : ℝ) + lam) ^ A' := by gcongr

/-- «Cost», the sizes: from `Eight.Level.level_size`; sc is the size of the pair (λ, B) in unary.
Not in the paper, which counts operations only. -/
theorem level_size_printed (g a C₁ Rn : ℕ) : ∃ A2 : ℕ, ∀ sc B lam M : ℕ, 1 ≤ lam → 1 ≤ g → M ≤ 2 * Rn * lam → sc ≤ 2 * (B + lam) + 2 →
    4 * sc + 3 * M + (g * (g ^ 3 * lam + (g * B + g ^ 2 * lam + 1)) + g * g * (g * B + g ^ 2 * lam + 1)) + B + size (g * g) + g * g * (2 * lam + 2) + 30
      + a * (sc + B + lam) ^ a + C₁ * (g ^ 3 * lam + (g * B + g ^ 2 * lam + 1)) ^ C₁ ≤ A2 * (B + lam) ^ A2 := by
  obtain ⟨A, hA⟩ := level_size g a C₁ Rn
  obtain ⟨A2, hA2⟩ := poly_absorb A (2 * Rn + size (g * g) + 4 * (g * g) + 13)
  refine ⟨A2, fun sc B lam M hl hg hM hsc => ?_⟩
  obtain ⟨P, hP⟩ : ∃ P, P = g ^ 3 * lam := ⟨_, rfl⟩
  obtain ⟨B₁, hB₁⟩ : ∃ B₁, B₁ = g * B + g ^ 2 * lam + 1 := ⟨_, rfl⟩
  obtain ⟨X, hX⟩ : ∃ X, X = sc + B + lam := ⟨_, rfl⟩
  rw [← hP, ← hB₁, ← hX]
  have h1 := hA sc B lam M P B₁ hl hM hP.le (by
    have e : (g + 2 * g ^ 2) * (B + lam) = g * B + g ^ 2 * lam + (g * lam + 2 * g ^ 2 * B + g ^ 2 * lam) := by ring
    have : 1 ≤ g * lam := Nat.mul_pos hg hl
    omega)
  rw [← hX] at h1
  have h2 := hA2 X (B + lam) (by omega) (by omega)
  have h3 : C₁ * (P + B₁) ^ C₁ ≤ C₁ * (sc + (M + 1) + P + B₁) ^ C₁ := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
  have h4 : size (g * g) ≤ size (g * g) * X := Nat.le_mul_of_pos_right _ (by omega)
  have h5 : g * g * (2 * lam + 2) ≤ g * g * (4 * X) := Nat.mul_le_mul_left _ (by omega)
  have h6 : M ≤ 2 * Rn * X := hM.trans (Nat.mul_le_mul_left _ (by omega))
  have e : (2 * Rn + size (g * g) + 4 * (g * g) + 13) * X = 2 * Rn * X + size (g * g) * X + g * g * (4 * X) + 13 * X := by ring
  omega

/-! ## One ι -/

/-- «Apply Lemma 1 to the network with the smaller total»: the run for one ι. The bound of Lemma 1
(`StOnProcedures`) on the row network or the column network, and the display on the smaller total
(`stMin`). -/
theorem level_one_of (hO : StOnProcedures) {K g C₁ a : ℕ} {e : ℝ} {NM : NetMachine} (h0 : 0 ≤ e) (hg1 : 1 ≤ g) (hNM : ComputesNetworks NM C₁ g K e)
    {c : List Unit × List Unit} {lam B S y : ℕ} {O : TableQuery → Option ℤ} {Rm : Inst (Fin (g * g)) (List Bool)} (hcl : c.1.length = lam) (hl : 1 ≤ lam)
    (hnet : ∀ tr, SecNetworks.IsNetwork ((gridProcs g tr).close O) (c, y) (levelNetP g tr lam y Rm) (g ^ 3 * lam) (g * B + g ^ 2 * lam + 1) (a * (B + lam) ^ a) S) :
    ∃ τ : ℕ, (Stepped.ite (useRowP g fun c : List Unit × List Unit => c.1.length) (networkOnSteps g NM ((gridProcs g false).close O)) (networkOnSteps g NM ((gridProcs g true).close O))).Runs (c, y) τ
        (size (c, y) + C₁ * (g ^ 3 * lam + (g * B + g ^ 2 * lam + 1)) ^ C₁ + S + 4 + 1) (Eight.Zι (gridR0 g g lam Rm) (Level.patOf g lam y)) ∧
      (τ : ℝ) + 1 ≤ (((3 * C₁ : ℕ) : ℝ) + 1) * (2 : ℝ) ^ (e * (rho * ((g : ℝ) ^ 4 * lam) + (g : ℝ) ^ 3 * lam + 2 * (g : ℝ) ^ 4) + (e + 2) * ((g : ℝ) * ((g ^ 3 * lam : ℕ) : ℝ)) / K)
        * (((g ^ 3 * lam : ℕ) : ℝ) + ((g * B + g ^ 2 * lam + 1 : ℕ) : ℝ)) ^ C₁ * ((a * (B + lam) ^ a : ℕ) : ℝ) := by
  obtain ⟨P, hP⟩ : ∃ P, P = g ^ 3 * lam := ⟨_, rfl⟩
  obtain ⟨B₁, hB₁⟩ : ∃ B₁, B₁ = g * B + g ^ 2 * lam + 1 := ⟨_, rfl⟩
  obtain ⟨t', ht'⟩ : ∃ t', t' = a * (B + lam) ^ a := ⟨_, rfl⟩
  obtain ⟨Ub, hUb⟩ : ∃ Ub : ℝ, Ub = rho * ((g : ℝ) ^ 4 * lam) + (g : ℝ) ^ 3 * lam + 2 * (g : ℝ) ^ 4 := ⟨_, rfl⟩
  rw [← hP, ← hB₁, ← ht', ← hUb]
  rw [← hP, ← hB₁, ← ht'] at hnet
  have hP1 : 1 ≤ P := by rw [hP]; exact Nat.mul_pos (pow_pos hg1 3) hl
  have ht'1 : 1 ≤ t' := (hnet false).τ_pos
  obtain ⟨Nr, hNr⟩ : ∃ Nr : Net g, Nr = levelNetP g false lam y Rm := ⟨_, rfl⟩
  obtain ⟨Nc, hNc⟩ : ∃ Nc : Net g, Nc = levelNetP g true lam y Rm := ⟨_, rfl⟩
  have hpr : SecNetworks.IsNetwork ((gridProcs g false).close O) (c, y) Nr P B₁ t' S := by rw [hNr]; exact hnet false
  have hpc : SecNetworks.IsNetwork ((gridProcs g true).close O) (c, y) Nc P B₁ t' S := by rw [hNc]; exact hnet true
  have hvr : Nr.value = Eight.Zι (gridR0 g g lam Rm) (Level.patOf g lam y) := by rw [hNr]; exact value_levelNetP hl g false y Rm
  have hvc : Nc.value = Eight.Zι (gridR0 g g lam Rm) (Level.patOf g lam y) := by rw [hNc]; exact value_levelNetP hl g true y Rm
  have hur : Nr.U = totalG eightF g g false 0 lam y := by rw [hNr]; exact U_levelNetP g false lam y Rm
  have huc : Nc.U = totalG eightF g g true 0 lam y := by rw [hNc]; exact U_levelNetP g true lam y Rm
  have hmin := stMin g lam y hl
  have tail : ∀ U τ : ℕ, U ≤ min (totalG eightF g g false 0 lam y) (totalG eightF g g true 0 lam y) →
      (τ : ℝ) ≤ 3 * ((C₁ : ℝ) * (2 : ℝ) ^ (e * ((U : ℝ) + (g : ℝ) * P / K) + 2 * ((g : ℝ) * P) / K) * ((P : ℝ) + B₁) ^ C₁) * t' →
      (τ : ℝ) + 1 ≤ (((3 * C₁ : ℕ) : ℝ) + 1) * (2 : ℝ) ^ (e * Ub + (e + 2) * ((g : ℝ) * P) / K) * ((P : ℝ) + B₁) ^ C₁ * t' := by
    intro U τ hU hτ
    have hU' : (U : ℝ) ≤ Ub := by
      have : (U : ℝ) ≤ ((min (totalG eightF g g false 0 lam y) (totalG eightF g g true 0 lam y) : ℕ) : ℝ) := by exact_mod_cast hU
      rw [hUb]
      linarith
    have hUb0 : 0 ≤ Ub := le_trans (Nat.cast_nonneg U) hU'
    have hX : (1 : ℝ) ≤ (2 : ℝ) ^ (e * Ub + (e + 2) * ((g : ℝ) * P) / K) :=
      Real.one_le_rpow (by norm_num)
        (add_nonneg (mul_nonneg h0 hUb0) (div_nonneg (mul_nonneg (by linarith) (by positivity)) (Nat.cast_nonneg _)))
    have hY : (1 : ℝ) ≤ ((P : ℝ) + B₁) ^ C₁ := by
      refine one_le_pow₀ ?_
      have h5 : (1 : ℝ) ≤ P := by exact_mod_cast hP1
      have h6 : (0 : ℝ) ≤ (B₁ : ℝ) := Nat.cast_nonneg _
      linarith
    have htr : (1 : ℝ) ≤ t' := by exact_mod_cast ht'1
    have h3 := one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hX hY) htr
    have hexp : e * ((U : ℝ) + (g : ℝ) * P / K) + 2 * ((g : ℝ) * P) / K ≤ e * Ub + (e + 2) * ((g : ℝ) * P) / K := by
      have e1 : e * ((U : ℝ) + (g : ℝ) * P / K) + 2 * ((g : ℝ) * P) / K = e * U + (e + 2) * ((g : ℝ) * P) / K := by ring
      have e2 := mul_le_mul_of_nonneg_left hU' h0
      rw [e1]
      linarith
    have hpow := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hexp
    have e3 : ((3 * C₁ : ℕ) : ℝ) = 3 * (C₁ : ℝ) := by push_cast; ring
    have h4 : (τ : ℝ) ≤ ((3 * C₁ : ℕ) : ℝ) * (2 : ℝ) ^ (e * Ub + (e + 2) * ((g : ℝ) * P) / K) * ((P : ℝ) + B₁) ^ C₁ * t' := by
      refine hτ.trans ?_
      rw [e3]
      calc 3 * ((C₁ : ℝ) * (2 : ℝ) ^ (e * ((U : ℝ) + (g : ℝ) * P / K) + 2 * ((g : ℝ) * P) / K) * ((P : ℝ) + B₁) ^ C₁) * t'
          ≤ 3 * ((C₁ : ℝ) * (2 : ℝ) ^ (e * Ub + (e + 2) * ((g : ℝ) * P) / K) * ((P : ℝ) + B₁) ^ C₁) * t' := by gcongr
        _ = _ := by ring
    calc _ ≤ _ := add_le_add h4 h3
      _ = _ := by ring
  by_cases hu : totalG eightF g g false 0 lam y ≤ totalG eightF g g true 0 lam y
  · obtain ⟨τ, hτ1, hτ2⟩ := hO NM C₁ g K e hNM _ ((gridProcs g false).close O) (c, y) Nr P B₁ t' S hpr
    rw [hvr] at hτ1
    have hdec : useRowP g (fun c : List Unit × List Unit => c.1.length) (c, y) = true := by
      show decide (totalG eightF g g false 0 c.1.length y ≤ totalG eightF g g true 0 c.1.length y) = true
      rw [hcl]
      exact decide_eq_true hu
    exact ⟨τ, Stepped.ite_runs_true hdec hτ1, tail _ _ (by rw [min_eq_left hu, hur]) hτ2⟩
  · obtain ⟨τ, hτ1, hτ2⟩ := hO NM C₁ g K e hNM _ ((gridProcs g true).close O) (c, y) Nc P B₁ t' S hpc
    rw [hvc] at hτ1
    have hdec : useRowP g (fun c : List Unit × List Unit => c.1.length) (c, y) = false := by
      show decide (totalG eightF g g false 0 c.1.length y ≤ totalG eightF g g true 0 c.1.length y) = false
      rw [hcl]
      exact decide_eq_false hu
    exact ⟨τ, Stepped.ite_runs_false hdec hτ1, tail _ _ (by rw [min_eq_right (not_le.1 hu).le, huc]) hτ2⟩

/-! ## The loop over ι and the division -/

/-- The paragraph «Cost» for the step machine that `levelMachine` becomes when the tables are built
in: value, number of steps, sizes. c holds λ and B in unary. -/
theorem level_runs_of (hA : StAskServes) (hO : StOnProcedures) {K g C₁ : ℕ} {e : ℝ} {NM : NetMachine} (hK : 2 ≤ K) (hg : K ≤ g) (h0 : 0 ≤ e) (hNM : ComputesNetworks NM C₁ g K e) :
    ∃ Cc' : ℕ, ∀ (c : List Unit × List Unit) (lam B : ℕ) (W : ℕ → List Bool → ℤ), c.1.length = lam → c.2.length = B → 1 ≤ lam → (∀ w < g * g, ∀ z ∈ words ((g * g - 1) * lam), |W w z| < 2 ^ B) →
      ∃ T : ℕ, (Stepped.bind (Stepped.sumRange (numPat8 g fun c : List Unit × List Unit => c.1.length)
            (Stepped.ite (useRowP g fun c : List Unit × List Unit => c.1.length) (networkOnSteps g NM ((gridProcs g false).close (tables (g * g) lam W))) (networkOnSteps g NM ((gridProcs g true).close (tables (g * g) lam W)))))
          (Stepped.ofFun fun p : (List Unit × List Unit) × ℤ => p.2 / ((2 ^ (tOf p.1.1.length * nRect g) : ℕ) : ℤ))).Runs c T (Cc' * (B + lam) ^ Cc') (Inst.ZW lam [] (listTables (g * g) W)) ∧
        (T : ℝ) ≤ Cc' * (2 : ℝ) ^ (((rho + 2 / K) * e + 2 / K) * (((g * g : ℕ) : ℝ)) ^ 2 * lam) * ((B : ℝ) + lam) ^ Cc' := by
  have hg1 : 1 ≤ g := by omega
  obtain ⟨a, ha⟩ := grid_isNetwork_of hA g hg1
  obtain ⟨A1, hA1⟩ := level_time_printed g K a C₁ hK hg h0 (nRect g)
  obtain ⟨A2, hA2⟩ := level_size_printed g a C₁ (nRect g)
  refine ⟨A1 + A2, fun c n B W hcl hcB hl hW => ?_⟩
  have hBd : BoundedInst n B (listTables (g * g) W) := fun v θ h1 h2 => (hA (List Unit × List Unit) (g * g) n B W c hW v θ h1 h2).2
  have hnet := fun (y : ℕ) (hy : y < (tOf n + 1) ^ nRect g) (tr : Bool) => ha tr c n B W y hcl hcB hl hW hy
  obtain ⟨Rm, hRm⟩ : ∃ Rm : Inst (Fin (g * g)) (List Bool), Rm = listTables (g * g) W := ⟨_, rfl⟩
  obtain ⟨O, hOd⟩ : ∃ O, O = tables (g * g) n W := ⟨_, rfl⟩
  rw [← hRm, ← hOd]
  rw [← hRm] at hBd
  simp only [← hRm, ← hOd] at hnet
  obtain ⟨M, hM⟩ : ∃ M, M = (tOf n + 1) * nRect g := ⟨_, rfl⟩
  obtain ⟨S', hS'⟩ : ∃ S', S' = size c + size (g * g) + g * g * (2 * n + 2) + B + 3 + a * (size c + B + n) ^ a + 2 := ⟨_, rfl⟩
  obtain ⟨Zt, hZt⟩ : ∃ Zt : ℕ → ℤ, Zt = fun y => Eight.Zι (gridR0 g g n Rm) (Level.patOf g n y) := ⟨_, rfl⟩
  obtain ⟨bd, hbd⟩ : ∃ bd : ℝ, bd = (((3 * C₁ : ℕ) : ℝ) + 1) * (2 : ℝ) ^ (e * (rho * ((g : ℝ) ^ 4 * n) + (g : ℝ) ^ 3 * n + 2 * (g : ℝ) ^ 4) + (e + 2) * ((g : ℝ) * ((g ^ 3 * n : ℕ) : ℝ)) / K)
        * (((g ^ 3 * n : ℕ) : ℝ) + ((g * B + g ^ 2 * n + 1 : ℕ) : ℝ)) ^ C₁ * ((a * (B + n) ^ a : ℕ) : ℝ) := ⟨_, rfl⟩
  rw [← hS'] at hnet
  have htn : tOf n ≤ n := by unfold tOf; omega
  have hNp : (tOf n + 1) ^ nRect g ≤ 2 ^ M := by
    rw [hM, pow_mul]
    exact Nat.pow_le_pow_left Nat.lt_two_pow_self.le _
  -- one ι
  have key : ∀ y : ℕ, ∃ τ : ℕ, y < (tOf n + 1) ^ nRect g →
      (Stepped.ite (useRowP g fun c : List Unit × List Unit => c.1.length) (networkOnSteps g NM ((gridProcs g false).close O)) (networkOnSteps g NM ((gridProcs g true).close O))).Runs (c, y) τ
        (size c + (M + 1) + C₁ * (g ^ 3 * n + (g * B + g ^ 2 * n + 1)) ^ C₁ + S' + 5) (Zt y) ∧ (τ : ℝ) + 1 ≤ bd := by
    intro y
    by_cases hy : y < (tOf n + 1) ^ nRect g
    swap
    · exact ⟨0, fun h => absurd h hy⟩
    obtain ⟨τ, hτ1, hτ2⟩ := level_one_of hO h0 hg1 hNM hcl hl (hnet y hy)
    have hsz : size (c, y) ≤ size c + (M + 1) := by
      have := Nat.size_le.2 (hy.trans_le hNp)
      simp only [size_prod, size_nat]
      omega
    refine ⟨τ, fun _ => ⟨?_, ?_⟩⟩
    · rw [hZt]
      exact hτ1.mono le_rfl (by omega)
    · rw [hbd]
      exact hτ2
  choose τ hτ using key
  -- the loop
  obtain ⟨v, hv⟩ : ∃ v, v = g * (g ^ 3 * n + (g * B + g ^ 2 * tOf n)) + g * g * (g * B + g ^ 2 * tOf n) := ⟨_, rfl⟩
  have hN : numPat8 g (fun c : List Unit × List Unit => c.1.length) c = (tOf n + 1) ^ nRect g := by
    show (tOf c.1.length + 1) ^ nRect g = _
    rw [hcl]
  have habs : ∀ y < (tOf n + 1) ^ nRect g, (Zt y).natAbs ≤ 2 ^ v := fun y hy => by
    have h0 : Network.value (J := Fin g) (netOfι g false n y Rm) = Zt y := by rw [hZt]; exact value_netOfι hl g false y Rm
    have h1 := Groundwork.Prog.abs_value_le (J := Fin g) (netOfι g false n y Rm) (netOfι_sized_t hl g false y hBd)
    rw [h0, Int.abs_eq_natAbs, Fintype.card_fin, ← hv] at h1
    exact_mod_cast h1
  have hrun := Stepped.sumRange_runs (N := numPat8 g fun c : List Unit × List Unit => c.1.length) (a := c)
    (M := Stepped.ite (useRowP g fun c : List Unit × List Unit => c.1.length) (networkOnSteps g NM ((gridProcs g false).close O)) (networkOnSteps g NM ((gridProcs g true).close O)))
    τ Zt (2 ^ v) (size c + (M + 1) + C₁ * (g ^ 3 * n + (g * B + g ^ 2 * n + 1)) ^ C₁ + S' + 5)
    (fun y hy => (hτ y (hN ▸ hy)).1) (fun y hy => habs y (hN ▸ hy))
  rw [hN] at hrun
  -- the division
  have hZ : ((2 : ℤ) ^ tOf n) ^ nRect g * Inst.ZW n [] Rm = ∑ y ∈ range ((tOf n + 1) ^ nRect g), Zt y := by
    rw [hZt, ← pow_mul]
    exact eqExpansion_words hl Rm
  have hdiv : (∑ y ∈ range ((tOf n + 1) ^ nRect g), Zt y) / ((2 ^ (tOf c.1.length * nRect g) : ℕ) : ℤ) = Inst.ZW n [] Rm := by
    rw [← hZ, hcl, ← pow_mul]
    push_cast
    exact Int.mul_ediv_cancel_left _ (by positivity)
  have hfin := Stepped.ofFun_runs (fun p : (List Unit × List Unit) × ℤ => p.2 / ((2 ^ (tOf p.1.1.length * nRect g) : ℕ) : ℤ)) (c, ∑ y ∈ range ((tOf n + 1) ^ nRect g), Zt y)
  simp only [hdiv] at hfin
  have hall := Stepped.bind_runs hrun hfin
  refine ⟨_, hall.mono le_rfl ?_, ?_⟩
  · -- sizes
    have hsc : size c = 2 * n + 1 + (2 * B + 1) := by rw [size_prod, size_units, size_units, hcl, hcB]
    have h2 := hA2 (size c) B n M hl hg1
      (by
        rw [hM]
        calc (tOf n + 1) * nRect g ≤ 2 * n * nRect g := Nat.mul_le_mul_right _ (by omega)
          _ = 2 * nRect g * n := by ring)
      (by omega)
    have h3 : A2 * (B + n) ^ A2 ≤ (A1 + A2) * (B + n) ^ (A1 + A2) :=
      Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right (by omega) (by omega))
    have hB' : g * B + g ^ 2 * tOf n ≤ g * B + g ^ 2 * n + 1 := by
      have := Nat.mul_le_mul_left (g ^ 2) htn
      omega
    have hv' : v ≤ g * (g ^ 3 * n + (g * B + g ^ 2 * n + 1)) + g * g * (g * B + g ^ 2 * n + 1) := by
      rw [hv]
      exact Nat.add_le_add (Nat.mul_le_mul_left _ (Nat.add_le_add_left hB' _)) (Nat.mul_le_mul_left _ hB')
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
    have e5 : size (c, ∑ y ∈ range ((tOf n + 1) ^ nRect g), Zt y) = size c + size (∑ y ∈ range ((tOf n + 1) ^ nRect g), Zt y) := rfl
    rw [e5]
    omega
  · -- steps
    have hsum : ((∑ y ∈ range ((tOf n + 1) ^ nRect g), (τ y + 1) : ℕ) : ℝ) ≤ (((tOf n + 1) ^ nRect g : ℕ) : ℝ) * bd := by
      rw [Nat.cast_sum]
      calc _ ≤ ∑ _y ∈ range ((tOf n + 1) ^ nRect g), bd :=
            Finset.sum_le_sum fun y hy => by
              have := (hτ y (Finset.mem_range.1 hy)).2
              push_cast
              exact this
        _ = _ := by rw [Finset.sum_const, card_range, nsmul_eq_mul]
    have h4 := hA1 B n hl
    rw [← hbd] at h4
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

/-! ## Proposition 3, first sentence, for the algorithm of its proof -/

/-- «Cost» for `levelMachine`: if the machine of Lemma 1 does what Lemma 1 says on networks on [g],
then `levelMachine K g M` does what Definition 4 asks for (g², (ρ + 2/K)e + 2/K). -/
theorem levelMachine_achieves_of (hA : StAskServes) (hV : StCliqueValue) (hO : StOnProcedures) {K g C₁ : ℕ} {e : ℝ} {M : CliqueMachine} (hK : 2 ≤ K) (hg : K ≤ g) (h0 : 0 ≤ e)
    (hNM : ComputesNetworks (groupingMachine K g M) C₁ g K e) : ∃ Cc' : ℕ, AchievedBy (levelMachine K g M) Cc' (g * g) ((rho + 2 / K) * e + 2 / K) := by
  obtain ⟨Cc', h⟩ := level_runs_of hA hO hK hg h0 hNM
  refine ⟨Cc', fun lam B W hl hB hW => ?_⟩
  obtain ⟨T, hT1, hT2⟩ := h (unary lam, unary B) lam B W (length_unary lam) (length_unary B) hl hW
  refine ⟨T, (stClose _ _ _ _ _ _ _ _ _ _).1 ?_, hT2⟩
  rw [levelMachine_close, hV (g * g) lam W (by nlinarith) hl]
  exact hT1

/-- **Proposition 3, first sentence, for the algorithm of its proof, from any machine that does what
Definition 4 asks.** The hypotheses: two statements on the coding of the tables (`StAskServes`,
`StCliqueValue`), Lemma 1 for the algorithm of its proof, and Lemma 1 for networks given by
procedures. -/
theorem stLevelTied_of (hA : StAskServes) (hV : StCliqueValue) (hG : StGroupingTied) (hO : StOnProcedures) : StLevelTied := by
  intro K e M Cc hK h0 hM
  obtain ⟨C₁, hC⟩ := hG K e M Cc hK h0 hM
  have hg : K ≤ 3 * K ^ 8 := by
    have : K ≤ K ^ 8 := Nat.le_self_pow (by norm_num) K
    omega
  rw [sq]
  exact levelMachine_achieves_of hA hV hO hK hg h0 hC

end Printed
