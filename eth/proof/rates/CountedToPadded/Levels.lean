/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import CountedToPadded.Defs
import CountedToPadded.Tables
import CountedToPadded.Need
import CountedToPadded.Pick
import QueryMachines.Runs
import StepMachines.Prog.SideBasics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-! # The sequence of levels

Proof of `SolverOfMachineLevelsFrom` (Defs.lean), and of `CliqueLevels.SolvesOfSolvesInFactor`
(CliqueLevelsStatement.lean). The field of the sequence of levels that takes the most work is that
the solver is right: `solver_right`. -/

public section

namespace QueryMachines.Bridge.Proof

open Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg Eight.SecNetworks Printed CliqueLevels

/-- The printed bound grows with e and with B. -/
theorem bound_mono {e e' : ℝ} (K C₀ lam : ℕ) {B B' : ℕ} (he : e ≤ e') (hB : B ≤ B') : bound e K C₀ lam B ≤ bound e' K C₀ lam B' := by
  have hB' : (B : ℝ) ≤ B' := by exact_mod_cast hB
  unfold bound
  refine mul_le_mul (Real.rpow_le_rpow_of_exponent_le one_le_two ?_) (pow_le_pow_left₀ (by positivity) ?_ _) (by positivity) (by positivity)
  · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right he (by positivity)) (by positivity)
  · exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)

/-- The printed bound is at least K(λ + B), for e ≥ 0, C₀ ≥ 1 and K ≥ 1, λ ≥ 1. -/
theorem le_bound {e : ℝ} {K C₀ lam : ℕ} (B : ℕ) (he : 0 ≤ e) (hC : 1 ≤ C₀) (hK : 1 ≤ K) (hlam : 1 ≤ lam) : (K : ℝ) * ((lam : ℝ) + B) ≤ bound e K C₀ lam B := by
  have hK' : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hl' : (1 : ℝ) ≤ lam := by exact_mod_cast hlam
  have hB' : (0 : ℝ) ≤ B := Nat.cast_nonneg _
  have hx : 1 ≤ (K : ℝ) * ((lam : ℝ) + B) := by nlinarith
  have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ (e * (K : ℝ) ^ 2 * lam) := Real.one_le_rpow one_le_two (by positivity)
  have h2 : (K : ℝ) * ((lam : ℝ) + B) ≤ ((K : ℝ) * ((lam : ℝ) + B)) ^ (C₀ * K ^ 2) := le_self_pow₀ hx (Nat.mul_ne_zero (by omega) (pow_ne_zero _ (by omega)))
  unfold bound
  calc (K : ℝ) * ((lam : ℝ) + B) = 1 * ((K : ℝ) * ((lam : ℝ) + B)) := (one_mul _).symm
    _ ≤ _ := mul_le_mul h1 h2 (by linarith) (by linarith)

/-- A query that the tables answer has size at most K + 2Kλ + 2. -/
theorem size_query_le {K lam : ℕ} {x : TableQuery} (h1 : x.1 < K) (h2 : x.2.length = (K - 1) * lam) : size x ≤ K + 2 * (K * lam) + 2 := by
  have h3 : Nat.size x.1 ≤ x.1 := Nat.size_le.2 Nat.lt_two_pow_self
  have h4 : (K - 1) * lam ≤ K * lam := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
  rw [size_prod, size_nat, size_bools, h2]
  omega

section

variable {M : QueryMachine TableQuery ℤ (U × U × U) ℤ} [QueryMachine.IsPolyQ M] {K : ℕ → ℕ} {e : ℕ → ℝ} {C₀ : ℕ} {num : U × U → ℕ × ℕ}

/-- The solver is right when the padding string has 2^need units. -/
theorem solver_right (hPlug : StPlug) (hRight : RunForIsRight) (hVal : TablesValue) (hBits : BitsOfTablesFacts) (hCut : CutNumberFacts) (hSuff : NeedSuffices)
    (hSol : Solves M K e C₀) (hL : Levels K e C₀) (hN : NumberBetween K e num) (pad : U) (l lam B : ℕ) (lu : U) (T : Tab) (hlam : 1 ≤ lam) (hW : WFe (K l) lam B (lu, T))
    (hpad : 2 ^ needOf num C₀ ((unary l, unary (K l)), unary lam, unary B) ≤ pad.length) :
    (solverOfMachine M num C₀).run (pad, (unary l, unary (K l)), (lu, T)) = zval (K l) (lu, T) := by
  obtain ⟨hb1, hbe, hbB⟩ := hBits T
  have hB' := hbB (K l) lam B lu hW
  have hlu : lu = unary lam := by rw [eq_unary lu]; exact congrArg unary hW.2
  subst hlu
  obtain ⟨hc0, hc1, -, -, -⟩ := (hCut K e C₀ num hL hN).2 l
  obtain ⟨T₀, S₀, ⟨own, L, hr, hc⟩, hT0, hS0⟩ := hSol l lam (bitsOfTables T) (fun w z => entry T (w, z)) hlam hb1 fun w _ z _ => hbe (w, z)
  have hK2 := hL.K_two l
  -- the bound β and what it covers
  have hβ := bound_mono (K l) C₀ lam hc1 hB'
  have h4 := hSuff K e C₀ num hL hN l lam B hlam
  have hle := le_bound (K := K l) (C₀ := C₀) (lam := lam) (B + 1) hc0.le hL.C₀_pos (by omega) hlam
  have hpad' : (2 : ℝ) ^ needOf num C₀ ((unary l, unary (K l)), unary lam, unary B) ≤ (pad.length : ℝ) := by exact_mod_cast hpad
  generalize bound (cutNumber K num l) (K l) C₀ lam (B + 1) = β at *
  -- the run of the machine with its queries answered from the tables
  have hq : ∀ x ∈ L, ∀ v, tables (K l) lam (fun w z => entry T (w, z)) x = some v → lookup.Runs (T, x) ((fun _ => 1) x) (size T + (K l + 2 * (K l * lam) + 2) + 1) v := by
    intro x _ v hv
    unfold tables at hv
    split at hv
    · rename_i hx
      obtain rfl : entry T x = v := Option.some.inj hv
      have h1 := size_query_le hx.1 hx.2
      have h2 := size_entry_le T x
      have h3 : size (T, x) = size T + size x := size_prod _
      refine (Stepped.ofFun_runs (fun p : Tab × TableQuery => entry p.1 p.2) (T, x)).mono le_rfl (Nat.succ_le_succ (max_le ?_ ?_))
      · rw [h3]; omega
      · exact h2.trans (Nat.le_add_right _ _)
    · cases hv
  have hrun := hPlug _ _ _ _ _ M lookup _ T _ own S₀ _ L _ (fun _ => 1) hr hq
  have hsum1 : (L.map QueryMachine.unitCost).sum = L.length := QueryMachine.sum_map_unitCost L
  have hsum3 : (L.map fun _ : TableQuery => 1 + 2).sum = L.length * (1 + 2) := QueryMachine.sum_map_const L (1 + 2)
  rw [hsum1] at hc
  have hTn : own + (L.map fun _ : TableQuery => 1 + 2).sum ≤ pad.length := by
    rw [hsum3]
    have h5 : ((own + L.length * (1 + 2) : ℕ) : ℝ) ≤ 3 * (T₀ : ℝ) := by
      have : ((own + L.length : ℕ) : ℝ) ≤ T₀ := Nat.cast_le.2 hc
      have h0 : (0 : ℝ) ≤ own := Nat.cast_nonneg _
      push_cast at this ⊢
      linarith
    have h6 : ((own + L.length * (1 + 2) : ℕ) : ℝ) ≤ (pad.length : ℝ) := by
      have : (0 : ℝ) ≤ β := le_trans (by positivity) hle
      linarith
    exact_mod_cast h6
  have hSn : S₀ + (K l + 2 * (K l * lam) + 2) + 2 ≤ pad.length := by
    have hK' : (2 : ℝ) ≤ K l := by exact_mod_cast hK2
    have hl' : (1 : ℝ) ≤ lam := by exact_mod_cast hlam
    have hB0 : (0 : ℝ) ≤ B := Nat.cast_nonneg _
    have h7 : ((S₀ + (K l + 2 * (K l * lam) + 2) + 2 : ℕ) : ℝ) ≤ (pad.length : ℝ) := by
      push_cast at hle ⊢
      nlinarith
    exact_mod_cast h7
  have hlen := size_le_len_tab T
  have hres := @hRight _ _ (onTables M) (inferInstanceAs (Enc (OnTablesState M))) (inferInstanceAs (Carried (OnTablesState M))) _ _ _ _ pad (7 * pad.length + 14 * len T + 2) hrun hTn (by omega)
  have hv := hVal (K l) lam T hK2 hlam
  exact (congrArg (fun o : Option ℤ => o.getD 0) hres).trans hv

end

end QueryMachines.Bridge.Proof

namespace QueryMachines.Bridge

open Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg Eight.SecNetworks Printed CliqueLevels Proof

/-- The main statement follows from `StPlug` and the statements of Defs.lean on the run, the tables,
the number between e_ℓ and 2e_ℓ, the exponent, polynomial time and the program that picks the level. -/
theorem solverOfMachineLevelsFrom : SolverOfMachineLevelsFrom := by
  intro hPlug hRight hVal hBits hCut hSuff hSmall hPoly hPick M _ K e C₀ kf num hSol hL hk hN
  obtain ⟨hpp, hpick⟩ := hPick K e C₀ kf hL hk
  have hcut := (hCut K e C₀ num hL hN).2
  have hKi : ∀ l : ℕ, (solverOfMachine M num C₀).K (unary l, unary (K l)) = K l := fun l => length_unary _
  refine ⟨hPoly M num C₀ hN.1, ⟨{
    idx := fun l => (unary l, unary (K l))
    K_two := fun l => by rw [hKi]; exact hL.K_two l
    K_lt := fun l => by rw [hKi, hKi]; exact hL.K_lt l
    K_le := fun l => by
      rw [hKi, hKi]
      exact (hL.K_le l).trans (Nat.pow_le_pow_right (by have := hL.K_two l; omega) (by omega))
    e_le := fun l => (hcut l).2.2.2.1
    e_ge := fun l => by
      rw [hKi]
      have h1 := one_le_logK hL l
      refine le_trans (one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ h1 (by omega : C₀ ≤ 2 * C₀ + 1))) ((hL.e_ge l).trans (hcut l).2.1)
    correct := by
      rintro pad _ lam B ⟨lu, T⟩ ⟨l, rfl⟩ hlam hW hpad
      rw [hKi] at hW ⊢
      exact solver_right hPlug hRight hVal hBits hCut hSuff hSol hL hN pad l lam B lu T hlam hW hpad
    rate := fun l lam B hlam hB => by
      rw [hKi]
      exact hSmall K e C₀ num hL hN l lam B hlam hB
    pick := pickOf kf (K 0)
    pick_poly := hpp
    pick_idx := fun b => (hpick b).1
    pick_le := fun b h => by
      rw [hKi] at h
      rw [(hpick b).1, hKi]
      exact (hpick b).2.1 h
    pick_max := fun b => by rw [hKi]; exact (hpick b).2.2 }, fun _ => rfl, hKi, rfl⟩⟩

end QueryMachines.Bridge

namespace CliqueLevels

open QueryMachines Printed

/-- The form with all states within the polynomial factor gives the form with all states within the
whole bound, for e ≥ 0. -/
theorem solvesOfSolvesInFactor : SolvesOfSolvesInFactor := by
  intro M K e C₀ he h l lam B W hlam hB hW
  obtain ⟨T, S, h1, h2, h3⟩ := h l lam B W hlam hB hW
  refine ⟨T, S, h1, h2, h3.trans ?_⟩
  have h4 : (1 : ℝ) ≤ (2 : ℝ) ^ (e l * (K l : ℝ) ^ 2 * lam) := Real.one_le_rpow one_le_two (mul_nonneg (mul_nonneg (he l) (by positivity)) (by positivity))
  unfold factor bound
  exact le_mul_of_one_le_left (by positivity) h4

end CliqueLevels
