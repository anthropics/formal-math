/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ClauseBound.Gen.Defs
public import ClauseBound.Alg.Prog
public import PaddedDescent.F.SideF
public import ClauseBound.Gen.PartA
import PaddedDescent.F.FuelCert

/-! # Toward part (c) of Theorem A: the solver of the pieces is polynomial-time, and inequalities on the exponent

For part (c) of Theorem A (Appendix A), where pieces with parameters (ρ, c), given as
polynomial-time programs, give #k-SAT in time 2^{O(km/(log m)^{α'})}, α' = log₂(1/ρ), this file
proves: the solver
that a family of pieces gives is polynomial-time (`solverOf_poly`); 0 ≤ log₂(1/ρ) ≤ 1 for 1/2 ≤ ρ <
1; log₂(m+2) ≥ 1; and 1/(c·(log₂(m+2))^c) ≤ 1/(log₂(m+2))^α for 0 ≤ α ≤ 1 ≤ c. -/

public section

namespace ClauseBound.Gen

open Groundwork PaddedDescent.F ClauseBound.Alg Levels.Gen

namespace End

/-! ### The solver of the pieces is polynomial-time -/

/-- The number of nodes at the top of a schedule, without a case distinction on the list. -/
theorem topK_eq (i : List Step × U) :
    topK i = bif i.1.isEmpty then i.2.length else (i.1.headD (([], [], []), ([], []), (false, [], []))).p * (i.1.headD (([], [], []), ([], []), (false, [], []))).d := by
  obtain ⟨l, u⟩ := i
  cases l <;> simp [topK]

/-- The number of nodes at the top of a schedule is computed in unary. -/
theorem topK_unary : Unary topK := by
  have h1 : Unary fun i : List Step × U =>
      i.2.length + (i.1.headD (([], [], []), ([], []), (false, [], []))).p * (i.1.headD (([], [], []), ([], []), (false, [], []))).d := by
    unfold Step.p Step.d; fun_prop
  have h2 : PolyT fun i : List Step × U =>
      bif i.1.isEmpty then i.2.length else (i.1.headD (([], [], []), ([], []), (false, [], []))).p * (i.1.headD (([], [], []), ([], []), (false, [], []))).d := by
    unfold Step.p Step.d; fun_prop
  refine Unary.of_le h1 (h2.congr fun i => (topK_eq i).symm) fun i => ?_
  rw [topK_eq]
  cases i.1.isEmpty <;> simp

/-- The solver that a family of pieces gives is polynomial-time, if the pieces are. -/
theorem solverOf_poly {P : PiecesF} (hCS : StCertSolveG P) (hCN : StCertNeedC P) (hNC : StNeedC P) (hP : P.Keeps) : (solverOf P).Poly where
  run := by
    have h1 : PolyT fun x : U × (List Step × U) × PInst => (x.1, x.2.1.2, x.2.1.1, x.2.2) := by fun_prop
    have h2 : PolyT fun x : U × (List Step × U) × PInst => solveG P x.1 x.2.1.2.length x.2.1.1 x.2.2 :=
      PolyT.comp (f := fun p : U × U × List Step × PInst => solveG P p.1 p.2.1.length p.2.2.1 p.2.2.2)
        (g := fun x : U × (List Step × U) × PInst => (x.1, x.2.1.2, x.2.1.1, x.2.2)) (hCS hP) h1
    exact h2
  K := topK_unary
  needC := by
    have h := hCN hP
    have hK : PolyT fun x : U × (List Step × U) × U × U => List.replicate (topK x.2.1) () := Unary.comp topK_unary (by fun_prop)
    have h1 : PolyT fun x : U × (List Step × U) × U × U => (x.1, (List.replicate (topK x.2.1) (), x.2.2.1, x.2.2.2), x.2.1.1) := by fun_prop
    change PolyT fun x : U × (List Step × U) × U × U => needC P x.1 (topK x.2.1) x.2.2.1.length x.2.2.2.length x.2.1.1
    refine (PolyT.comp h h1).congr fun x => ?_
    simp only [List.length_replicate]
  needC_eq := fun b x v h => (hNC b (topK x.1) x.2.1.length x.2.2.length x.1.1).1 v h
  needC_some := fun b x h => (hNC b (topK x.1) x.2.1.length x.2.2.length x.1.1).2 h

/-! ### Inequalities on the exponent -/

/-- 0 ≤ log₂(1/ρ) ≤ 1 for 1/2 ≤ ρ < 1. -/
theorem alpha_mem {ρ : ℝ} (hρ : 1 / 2 ≤ ρ) (hρ1 : ρ < 1) : 0 ≤ Real.logb 2 (1 / ρ) ∧ Real.logb 2 (1 / ρ) ≤ 1 := by
  have hρ0 : 0 < ρ := by linarith
  constructor
  · apply Real.logb_nonneg (by norm_num)
    rw [le_div_iff₀ hρ0]; linarith
  · rw [Real.logb_le_iff_le_rpow (by norm_num) (by positivity), Real.rpow_one, div_le_iff₀ hρ0]
    linarith

/-- log₂(m+2) ≥ 1. -/
theorem one_le_log (m : ℕ) : (1 : ℝ) ≤ Real.logb 2 ((m : ℝ) + 2) := by
  rw [Real.le_logb_iff_rpow_le (by norm_num) (by positivity)]
  norm_num

/-- 1/(c·(log₂(m+2))^c) ≤ 1/(log₂(m+2))^α for 0 ≤ α ≤ 1 ≤ c. -/
theorem le_rPow {α : ℝ} {c : ℕ} (ha1 : α ≤ 1) (hc : 1 ≤ c) (m : ℕ) : 1 / ((c : ℝ) * Real.logb 2 ((m : ℝ) + 2) ^ c) ≤ SatM.rPow α m := by
  have hy := one_le_log m
  unfold SatM.rPow
  set y := Real.logb 2 ((m : ℝ) + 2)
  have hc' : (1 : ℝ) ≤ c := by exact_mod_cast hc
  refine one_div_le_one_div_of_le (Real.rpow_pos_of_pos (by linarith) _) ?_
  calc y ^ α ≤ y ^ (c : ℝ) := Real.rpow_le_rpow_of_exponent_le hy (ha1.trans hc')
    _ = y ^ c := Real.rpow_natCast _ _
    _ ≤ (c : ℝ) * y ^ c := le_mul_of_one_le_left (by positivity) hc'

end End

open ClauseBound.Gen.End

end ClauseBound.Gen
