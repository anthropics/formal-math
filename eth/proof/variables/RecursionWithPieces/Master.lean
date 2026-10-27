/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import RecursionWithPieces.Defs
public import ClauseBound.Gen.Defs
import GeneralPieces.ThmRunningTime
import GeneralPieces.Num.PartAUse
import GeneralPieces.Num.Asymptotic
import UniformInK.Top.FallBack
import ClauseBound.MainBoth
import all ClauseBound.ParityChecks.MasterOL
import all ClauseBound.TopN.Arith
import ClauseBound.Gen.End
import ClauseBound.Alg.Need

/-! # Step 6 for the recursion of Appendix A: from its sequence of levels to the two rates, for a conclusion that may name the solver and the choice of the level

`VariableBound.StEndS R` says: for every solver for cliques with a sequence of levels, a precision
and two rates that satisfy a list of inequalities, the conclusion R holds of the solver, the
function `pick` of the sequence,
the precision and the rates. This file meets the list for the recursion of Appendix A, as follows.
* The sequence of levels is that of proof/rates/GeneralPieces/Rec/Seq.lean
  (`GeneralPieces.seq_of_pick`): every x₀ ≥ 18 with 2^x₀ ≥ c + 5, each step of the schedule of
  display (40) in order by the hypotheses of case (ii) of the lemma on groupings with explicit cost
  (`GeneralPieces.Chain.stChain2`, `GeneralPieces.solveG2`), the exponent of the pad by
  `GeneralPieces.stRate2`.
* `pick` is the named program `ClauseBound.Gen.Pick.pick P x₀`, and the conclusion says so.
* The inequalities between e_ℓ and the rates (e_ℓ·(ℓ + 2) against log log n/(log n)^α' for the
  largest ℓ with K_ℓ ≤ n^(1/17), e_ℓ against 1/(log m)^α' for the largest ℓ with K_ℓ ≤ m^(1/9),
  2^(−ℓ−1) ≤ e_ℓ, 2^(ℓ+1) ≤ (2/e_ℓ)^C) are drawn from part (a) of the
  theorem on the general recursion as proved in proof/rates/GeneralPieces/Num/PartA.lean, for every
  x₀ ≥ 18: `GeneralPieces.PartAUse.e_mul_le`, `e_le_rPow`, `inv_two_pow_le_e`, `two_pow_le_div`, as
  proof/rates/GeneralPieces/ThmRunningTime.lean uses them for part (c).
Of the two rates alone it is shown that they are not too small, not negative, and that the rate in n
allows the fall-back to exhaustive counting. -/

public section

namespace RecursionWithPieces

open Groundwork PaddedDescent PaddedDescent.F CountKSat CountKSatRate ClauseBound.Alg ClauseBound.Gen ClauseBound.Gen.End Levels.Gen ClauseBound.TopN ClauseBound.TopN.Arith ClauseBound.ParityChecks ClauseBound.Both UniformInK VariableBound GeneralPieces

/-- Programs P with parameters (ρ, c), 1/2 ≤ ρ < 1, whose numbers of bits are at most 2λ (`P.m = 1`)
and which are polynomial-time (`P.Keeps`), and an x₀ ≥ 18 with 2^x₀ ≥ c + 5, give the conclusion R
for the solver made of P, the choice of the
level by the program `Pick.pick P x₀`, the precision s(ℓ) = ℓ + 1, and the rates in n and in m with
the exponent log₂(1/ρ) of the logarithms. The statement `StEndS R` is a hypothesis. -/
theorem master_of_par {R : ∀ (Idx : Type) [Enc Idx], Solver Idx → (U → U × Idx) → (U → U) → (ℕ → ℝ) → (ℕ → ℝ) → Prop} (hEnd : StEndS R) {P : PiecesF} {ρ : ℝ} {c x₀ : ℕ} (hρ : 1 / 2 ≤ ρ) (hρ1 : ρ < 1)
    (hP : Par P ρ c) (hm : P.m = 1) (hKeeps : P.Keeps) (hx : 18 ≤ x₀) (hc : c + 5 ≤ 2 ^ x₀) :
    R _ (solverOf P) (Pick.pick P x₀) (fun u => () :: u) (SatK.rN 1 (Real.logb 2 (1 / ρ))) (SatM.rPow (Real.logb 2 (1 / ρ))) := by
  obtain ⟨hp1, hp2, hp3, hp4⟩ := pick_spec P x₀
  obtain ⟨C₀, Q, hQ, hpick⟩ := seq_of_pick Chain.stChain2 stRate2 solveG2 Need.stNeedG P ρ c x₀ hρ hρ1 hP hm hx hc (Pick.pick P x₀) hp1 hp2 hp3 hp4
  have hA := PartA.thmRunningTime_a ρ x₀ hρ hρ1 hx
  obtain ⟨C, hC⟩ : ∃ C : ℕ, ρ ^ C ≤ 1 / 2 := by
    obtain ⟨C, hC⟩ := exists_pow_lt_of_lt_one (by norm_num : (0 : ℝ) < 1 / 2) hρ1
    exact ⟨C, hC.le⟩
  rw [← hpick]
  refine hEnd _ (solverOf P) (e ρ x₀) C₀ Q (solver_poly P hKeeps) (fun u => () :: u) (C + 1) (by fun_prop) (fun l => ?_) (fun l => ?_) _ _ (3 * (171 * (3 * x₀ + 6)))
    (fun n _ => MasterOL.le_rN (alpha_mem hρ hρ1).2 (by omega) n) (fun n hn => ?_) (fallBack_rN_of (alpha_mem hρ hρ1).2)
    (fun m _ => le_rPow (alpha_mem hρ hρ1).2 (by omega) m) (fun m _ => ?_) (rN_nonneg _) (rPow_nonneg _)
  · simpa using PartAUse.inv_two_pow_le_e hA hρ l
  · simpa using PartAUse.two_pow_le_div hA hρ hρ1 hC l
  · obtain ⟨hr1, hr2⟩ := root17_spec n
    have hK0 : (solverOf P).K (Q.idx 0) ≤ (root17 n).length := by
      by_contra h
      have h' := Nat.pow_le_pow_left (Nat.succ_le_of_lt (not_le.1 h)) 17
      exact absurd (h'.trans hn) (not_le.2 hr2)
    have hle := Q.pick_le _ hK0
    have hmax := Q.pick_max (root17 n)
    rw [Q.pick_idx, hQ, K_idx] at hle
    rw [hQ, K_idx] at hmax
    have h := PartAUse.e_mul_le (l := (Q.pick (root17 n)).1.length) (n := n) hρ hρ1 hx ((Nat.pow_le_pow_left hle 17).trans hr1)
      (hr2.trans_le (Nat.pow_le_pow_left (Nat.succ_le_of_lt hmax) 17))
    simpa [SatK.rN] using h
  · have hmax := Q.pick_max (root9 m)
    rw [hQ, K_idx] at hmax
    refine (PartAUse.e_le_rPow hρ hρ1 hx hmax).trans (mul_le_mul_of_nonneg_right ?_ (rPow_nonneg _ m))
    exact_mod_cast (by omega : 91 * (3 * x₀ + 6) ≤ 3 * (171 * (3 * x₀ + 6)))

/-- Pieces (P₀, A, val) with parameters (ρ, c) as Appendix A defines them give the conclusion R for
the recursion on `recOf P₀ val c`, the choice of the level by `Pick.pick` with the least x₀ of the
theorem on the general recursion, the
precision s(ℓ) = ℓ + 1, and the rates with the exponent α' = log₂(1/ρ). The statement `StEndS R` is
a hypothesis. -/
theorem master_of_isPieces {R : ∀ (Idx : Type) [Enc Idx], Solver Idx → (U → U × Idx) → (U → U) → (ℕ → ℝ) → (ℕ → ℝ) → Prop} (hEnd : StEndS R) {ρ : ℝ} {c : ℕ} {P₀ : PiecesF}
    {A : (lam : ℕ) → ℕ → Pieces.Four lam} {val : AppRunningTime.ValQ → ℤ} (h : AppRunningTime.IsPieces ρ c P₀ A val) :
    R _ (solverOf (Tied.recOf P₀ val c)) (Pick.pick (Tied.recOf P₀ val c) (x₀Of c)) (fun u => () :: u) (SatK.rN 1 (AppRunningTime.alpha' ρ)) (SatM.rPow (AppRunningTime.alpha' ρ)) := by
  obtain ⟨hP, hKeeps, hm⟩ := par_of_isPieces h
  exact master_of_par hEnd h.rho_ge h.rho_lt hP hm hKeeps (x₀Of_ge c) (x₀Of_pow c)

/-- The pieces of Appendix B, with the constant c, give the conclusion R for `solverAB`, `pickAB`,
`prec` and the rates log₂ log₂(n+4)/√(log₂(n+4)) and 1/√(log₂(m+2)). The statement `StEndS R` is a
hypothesis. -/
theorem master_of_isPiecesB {R : ∀ (Idx : Type) [Enc Idx], Solver Idx → (U → U × Idx) → (U → U) → (ℕ → ℝ) → (ℕ → ℝ) → Prop} (hEnd : StEndS R) {c : ℕ} {P₀ : PiecesF}
    {A : (lam : ℕ) → ℕ → Pieces.Four lam} {val : AppRunningTime.ValQ → ℤ} (h : Tied.IsPiecesB c P₀ A val) :
    R _ (solverAB P₀ val c) (pickAB P₀ val c) prec (SatK.rN 1 (1 / 2)) (SatM.rPow (1 / 2)) := by
  have h1 := master_of_isPieces hEnd h.1
  rw [AppRunningTime.alpha', Asymptotic.alpha_half] at h1
  exact h1

end RecursionWithPieces
