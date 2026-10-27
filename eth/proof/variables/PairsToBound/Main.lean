/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import PairsToBound.Defs
public import PairsToBound.Pairs
public import PairsToBound.Arith
public import PairsToBound.Width
public import PairsToBound.FrontEnd
public import PairsToBound.Exhaust
import TwoMachines.Main
import VariableBound.Paper.Arith
import UniformInK.Top.Time
import GeneralPieces.ThmRunningTime
import Wrap.Sim
import ToTuring.Closure.Basic

/-! # Theorem D (b) from Theorem D (a): the main statement

Step 6 of Appendix D. Let x be the code of (k, φ), with k ≥ 1, n ≥ 4 and φ a k-CNF on n variables,
let k′ = `widthOr3 φ` be the width that the algorithm uses, and X = k²·n·log log n/√(log n).

* If the test is true, then n ≥ K₀^17 and k′ ≤ (log n)^(1/4). By `mainRegimeBound` the machine M of
  Theorem D (a), on the code rewritten at k′, puts out the count within 2^{C₁·k′²·n·log log n/√(log
  n)} ≤ 2^{9C₁·X} steps (`main_case_le`).
* If the test is false, the machine Mb puts out the count on x within 2^{c·n}·n^{c·k} steps. Either
  k′ > (log n)^(1/4), and then n ≤ 9·X (`le_of_wide`), or n < K₀^17, and then n ≤ √(17·log K₀)·X
  (`le_of_small`); and k·log n ≤ X (`mul_lg_le_expN`). The numbers are put together in
  `fall_back_case_le`.
* In both cases |x| + 1 ≤ (n+2)^(5k) (`UniformInK.Time.length_enc_succ_le`) ≤ 2^{10·X}
  (`length_le_rpow`), and the power q of the choice multiplies the constant (`choice_le`).

The constant C is chosen after the solver, its levels, a, M, C′, Mb, c and q, and before k, n and φ.
`thmVariablesBFromThmVariablesA` adds that such machines exist: a machine that tries all assignments
(`exhaustiveMachineExists`), the front end and the test (`frontEndAndTestExist`) and the choice
(`TwoMachines.everyTwoMachinesCanBeChosenBetween`).
`thmVariablesAImpliesThmVariablesB` applies Theorem D (a) to the pairs of Appendix A on the pieces
of Appendix B (`thePairsSatisfyTheHypothesis`), takes e_ℓ ≤ (3x₀+6)/√(log K_ℓ) from
`thetaOfThePairs`, and then applies `thmVariablesBFromThmVariablesA`. -/

public section

namespace PairsToBound

open Turing Groundwork PaddedDescent.F ClauseBound.Alg Wrap TwoMachines MainTheoremForms VariableBound.Paper
open Sat3 (CNF)

/-- **The main statement** (Step 6 of Appendix D): every machine that chooses, by the printed test,
between a machine with the conclusion of Theorem D (a) behind the front end and a machine that tries
all assignments meets the bound of Theorem D (b). -/
theorem everyChoiceMeetsThmVariablesB : EveryChoiceMeetsThmVariablesB := by
  intro Idx _ S e C₀ Q a he M C' hM Mb c hMb pre test hpre htest N q hN
  obtain ⟨C₁, hC₁⟩ := mainRegimeBound Idx S e C₀ Q a he M C' hM
  obtain ⟨D, hD⟩ := exists_nat_ge (Real.sqrt (17 * lg (S.K (Q.idx 0))))
  refine ⟨q * (9 * C₁ + c * (D + 9 + 1) + 10 + 2), fun k n φ hk hn hφ => ?_⟩
  obtain ⟨hw3, hwk, hwle⟩ := widthOr3Stmt n φ
  obtain ⟨-, hw9⟩ := hwle k hk hφ
  have hlen := UniformInK.Time.length_enc_succ_le hk hφ
  by_cases ht : test (SatM.enc k φ) = true
  · obtain ⟨t1, t2⟩ := (htest k n φ hk hφ).1 ht
    have hrun : Outputs M (pre (SatM.enc k φ)) (SatK.binary n (SatK.numSat φ)) (timeN C₁ (widthOr3 φ) n) := by
      rw [hpre k n φ hk hφ]
      exact hC₁ _ n φ t1 hw3 t2 (hwk hφ.2)
    exact Outputs.mono ((hN _ _ _).1 ht hrun) (main_case_le q C₁ _ (by omega) (by omega) hk hn hw9 hlen)
  · have hf : test (SatM.enc k φ) = false := Bool.eq_false_iff.2 ht
    have hrun : Outputs Mb (id (SatM.enc k φ)) (SatK.binary n (SatK.numSat φ)) (2 ^ (c * n) * n ^ (c * k)) := hMb k n φ hk (by omega) hφ
    have hnD : (n : ℝ) ≤ ((D + 9 : ℕ) : ℝ) * expN k n := by
      have hX := two_le_expN hk hn
      have hD0 : (0 : ℝ) ≤ D := Nat.cast_nonneg D
      by_cases hs : S.K (Q.idx 0) ^ 17 ≤ n
      · have hwide : lg n < ((widthOr3 φ : ℕ) : ℝ) ^ 4 := by
          by_contra hh
          exact ht ((htest k n φ hk hφ).2 ⟨hs, not_lt.1 hh⟩)
        have := le_of_wide hn hwide hw9
        push_cast
        nlinarith
      · have := le_of_small (Q.K_two 0) hk hn (not_le.1 hs) hD
        push_cast
        nlinarith
    exact Outputs.mono ((hN _ _ _).2 hf hrun) (fall_back_case_le q c (D + 9) _ (by omega) (by omega) hk hn hnD hlen)

/-- Existence and the main statement in one: for every machine with finite alphabets and the
conclusion of Theorem D (a) there are a machine that tries all assignments, a front end, a test and
a machine that chooses between the two machines, as in Step 6 of Appendix D; and every such choice
meets the bound of Theorem D (b). -/
theorem thmVariablesBFromThmVariablesA : ThmVariablesBFromThmVariablesA := by
  intro Idx _ S e C₀ Q a he M C' hfin hM
  refine ⟨?_, everyChoiceMeetsThmVariablesB Idx S e C₀ Q a he M C' hM⟩
  obtain ⟨Mb, c, qb, hfb, hMb, hcomp⟩ := exhaustiveMachineExists
  obtain ⟨⟨pre, hpp, hpre⟩, hT⟩ := frontEndAndTestExist
  obtain ⟨test, htp, htest⟩ := hT (S.K (Q.idx 0))
  obtain ⟨K₁, K₂, N, q₀, q, hfN, hH, hCh⟩ := everyTwoMachinesCanBeChosenBetween M Mb hfin hfb test pre id id id htp hpp PolyT.id' PolyT.id' PolyT.id'
  exact ⟨Mb, c, qb, pre, test, K₁, K₂, N, q₀, q, hfb, hMb, hcomp, hpp, hpre, htp, htest, hfN, hH, hCh⟩

/-- Theorem D (b) from Theorem D (a) and Theorem B, along Step 6 of Appendix D: the pairs of
Appendix A on the pieces of Appendix B meet the hypothesis of (a); (a) gives a machine; e_ℓ ≤
(3x₀+6)/√(log K_ℓ); the choice around that machine meets the bound of (b). -/
theorem thmVariablesAImpliesThmVariablesB : ThmVariablesAImpliesThmVariablesB := by
  intro hVariablesA hB
  obtain ⟨c, P, A, val, hP, -⟩ := hB
  obtain ⟨C₀, Cp, h⟩ := thePairsSatisfyTheHypothesis c
  obtain ⟨Q, hpoly, hK, -, -, hprec⟩ := h P A val hP
  obtain ⟨M, C', hfin, hM⟩ := hVariablesA _ _ _ C₀ Q hpoly RecursionWithPieces.prec Cp hprec
  have he : ∀ l : ℕ, Levels.Gen.e (1 / Real.sqrt 2) (GeneralPieces.x₀Of c) l ≤ ((3 * GeneralPieces.x₀Of c + 6 : ℕ) : ℝ) / Real.sqrt (lg ((RecursionWithPieces.solverAB P val c).K (Q.idx l))) := fun l => by
    rw [hK]
    obtain ⟨-, -, -, -, -, h6⟩ := thetaOfThePairs (GeneralPieces.x₀Of c) l (GeneralPieces.x₀Of_ge c)
    refine h6.trans (div_le_div_of_nonneg_right ?_ (Real.sqrt_nonneg _))
    have hx : (0 : ℝ) ≤ (GeneralPieces.x₀Of c : ℝ) := Nat.cast_nonneg _
    have hs : Real.sqrt (3 * (GeneralPieces.x₀Of c : ℝ) + 6) ≤ 3 * (GeneralPieces.x₀Of c : ℝ) + 6 := Real.sqrt_le_iff.2 ⟨by linarith, by nlinarith⟩
    have hs0 := Real.sqrt_nonneg (3 * (GeneralPieces.x₀Of c : ℝ) + 6)
    push_cast
    linarith
  obtain ⟨⟨Mb, c', qb, pre, test, K₁, K₂, N, q₀, q, -, hMb, -, -, hpre, -, htest, hfN, -, hCh⟩, hall⟩ := thmVariablesBFromThmVariablesA _ _ _ C₀ Q _ he M C' hfin hM
  obtain ⟨C, hC⟩ := hall Mb c' hMb pre test hpre htest N q hCh
  exact ⟨N, C, hfN, hC⟩

end PairsToBound
