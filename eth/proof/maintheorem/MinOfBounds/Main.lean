/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import MinOfBounds.Defs
import MinOfBounds.Rename
import MinOfBounds.Arith
import TwoMachines.Main
import Wrap.Sim
import ToTuring.Closure.Basic
import VariableBound.Paper.Arith
import VariableBound.Paper.MainTheorem
import VariableBound.Paper.Rename.Compact
import VariableBound.Paper.Rename.End

/-! # Corollary 11 from Theorem A (c) and Theorem D (b): the proofs

proof/maintheorem/MinOfBounds/Defs.lean divides the proof of Corollary 11 into five numbered
sentences. The proof here follows sentences (1) to (4); sentence (5), a second way to the same
bound, is not followed here.
* Sentence (1), the renaming of the variables that occur to 1, …, n, is in
  proof/maintheorem/MinOfBounds/Rename.lean; the printed proof of Corollary 11 does not have it.
* Sentence (3), «Both compute the same number», is `bothComputeTheSameNumber`: the two hypotheses
  are applied to the renamed formula, in which every variable occurs, which has as many clauses as φ
  and is a k-CNF on n variables.
* Sentence (2), the alternation, is `alternation_outputs`: let N run M₁ and M₂ in alternation behind
  a function that renames, with the same last step `post` after either. By the definition of
  `TwoMachines.Alternates` and by sentence (3), N puts out `post` of the number within
  q·(min(t₁, t₂) + L + 1)^q steps, where t₁ and t₂ are the two bounds and L is the length of the
  compact code.
* Sentence (4), «this constant goes into C», is `MinOfBounds.overheadGoesIntoC` of
  proof/maintheorem/MinOfBounds/Arith.lean; it needs that the code of the renamed formula is
  polynomially long (`MinOfBounds.renamedCodeIsPolynomial`).
* `everyAlternationMeetsMinBound` takes `post` to be the identity,
  `everyAlternationDecidesWithinMinBound` takes it to be “some bit is 1”.
* That a function that renames and a machine that alternates exist is
  `MinOfBounds.renamingFrontEndExists` and `TwoMachines.everyTwoMachinesCanBeAlternated`.
* The sentence that follows the proof, «This is the Main Theorem», is `minBoundIsTheMainTheorem`:
  the minimum of the two powers of 2 is 2 to the minimum of the two exponents
  (`VariableBound.Paper.timeCor_eq`). -/

public section

namespace MinOfBounds

open Turing Groundwork Wrap TwoMachines MainTheoremForms
open Sat3 (CNF)

/-- The three propositions unfold to “there are a machine with finite alphabets and a constant with
this body”. -/
theorem propositionsUnfold : PropositionsUnfold := ⟨Iff.rfl, Iff.rfl, Iff.rfl⟩

/-- Every machine with the body of `AppRunningTime.BoundInM` and the constant C meets the bound in m
with the constant 3C: the factor C in front goes into the exponent (`bound_le_timeM`), and the
polynomial that is added only makes the bound larger. -/
theorem boundInMSuffices : BoundInMSuffices := fun M C hM =>
  ⟨3 * C, fun k n φ hk hφ hm ho => Outputs.mono (hM k n φ hk (by omega) hφ ho) ((bound_le_timeM C hk hm).trans (Nat.le_add_right _ _))⟩

/-- «Both compute the same number.» The two hypotheses are applied to the renamed formula
`VariableBound.Rename.ren φ`. -/
theorem bothComputeTheSameNumber : BothComputeTheSameNumber := by
  intro M₁ C₁ h₁ M₂ C₂ h₂ k V φ hk hφ hm hn
  obtain ⟨φ', hcode, -, -, -, hlen, hK, hocc, hnum⟩ := renamedCodeIsTheCodeOfARenaming k V φ
  have a₁ := h₁ k (numOcc φ) φ' hk (hK hφ) (hlen ▸ hm) hocc
  have a₂ := h₂ k (numOcc φ) φ' hk hn (hK hφ)
  unfold CountsWithin at a₁ a₂
  rw [hnum, ← hcode] at a₁ a₂
  rw [hlen] at a₁
  exact ⟨a₁, a₂⟩

/-- The alternation with any last step. Let `pre` rename the variables that occur, let M₁ with C₁
meet the bound in m and M₂ with C₂ the bound of Theorem D (b), and let N run M₁ and M₂ in
alternation behind `pre`, with the same function `post` after either. Then there is a constant C
such that, for every k ≥ 1 and every
k-CNF φ with m ≥ 2 clauses in which n ≥ 4 variables occur, N, started on the compact code of (k, φ),
puts out `post` of the number of satisfying assignments of φ, as assignments of these n variables,
within the bound of Corollary 11 with the constant C. -/
theorem alternation_outputs {pre : List Bool → List Bool} (hpre : RenamesTheVariablesThatOccur pre) {M₁ : TM2ComputableAux Bool Bool} {C₁ : ℕ} (h₁ : MeetsBoundInM M₁ C₁)
    {M₂ : TM2ComputableAux Bool Bool} {C₂ : ℕ} (h₂ : ThmVariablesBFor M₂ C₂) {post : List Bool → List Bool} {N : TM2ComputableAux Bool Bool} {q : ℕ} (hN : Alternates M₁ M₂ pre pre post post N q) :
    ∃ C : ℕ, ∀ (k V : ℕ) (φ : CNF V), 1 ≤ k → SatK.IsKCNF k φ → 2 ≤ φ.length → 4 ≤ numOcc φ →
      Outputs N (encC k φ) (post (SatK.binary (numOcc φ) (numSatOcc φ))) (timeCor C k φ.length (numOcc φ) + C * (encC k φ).length ^ C) := by
  obtain ⟨a, ha⟩ := renamedCodeIsPolynomial
  obtain ⟨C, hC⟩ := overheadGoesIntoC C₁ C₂ q a
  refine ⟨C, fun k V φ hk hφ hm hn => ?_⟩
  obtain ⟨b₁, b₂⟩ := bothComputeTheSameNumber M₁ C₁ h₁ M₂ C₂ h₂ k V φ hk hφ hm hn
  rw [← hpre k V φ hk hφ] at b₁ b₂
  have hL : 1 ≤ (encC k φ).length := by
    rw [VariableBound.Rename.lengthEncC]
    omega
  refine Outputs.mono (hN (encC k φ) _ _ _ _ b₁ b₂ rfl) ?_
  rw [hpre k V φ hk hφ]
  exact hC k φ.length (numOcc φ) (encC k φ).length (renamedCode k φ).length hk hm hn hL (ha k V φ hk hφ)

/-- **The main statement.** Every machine that runs M₁ and M₂ in alternation behind a function that
renames the variables that occur meets the bound of Corollary 11. -/
theorem everyAlternationMeetsMinBound : EveryAlternationMeetsMinBound := fun _ hpre _ _ h₁ _ _ h₂ _ _ hN => alternation_outputs hpre h₁ h₂ hN

/-- The same for deciding: “some bit is 1” of the number of satisfying assignments in n + 1 bits is
the bit “this number is not 0”, and φ is satisfiable if and only if this number is not 0. -/
theorem everyAlternationDecidesWithinMinBound : EveryAlternationDecidesWithinMinBound := by
  intro pre hpre M₁ C₁ h₁ M₂ C₂ h₂ N q hN
  obtain ⟨C, hC⟩ := alternation_outputs hpre h₁ h₂ hN
  refine ⟨C, fun k V φ hk hφ hm hn => ⟨decide (numSatOcc φ ≠ 0), by rw [decide_eq_true_iff, VariableBound.Paper.satisfiable_iff], ?_⟩⟩
  have h := hC k V φ hk hφ hm hn
  have e : someBit (SatK.binary (numOcc φ) (numSatOcc φ)) = [decide (numSatOcc φ ≠ 0)] := VariableBound.Rename.anyBit_binary (VariableBound.Paper.numSatOcc_lt φ)
  rw [e] at h
  exact h

/-- Existence, by `renamingFrontEndExists` and `TwoMachines.everyTwoMachinesCanBeAlternated`, and
the main statement. -/
theorem minBoundFromTheTwoTheorems : MinBoundFromTheTwoTheorems := by
  intro M₁ C₁ hf₁ h₁ M₂ C₂ hf₂ h₂
  obtain ⟨pre, hpoly, hpre⟩ := renamingFrontEndExists
  obtain ⟨K₁, K₂, N, q₀, q, hfin, hhost, halt⟩ := everyTwoMachinesCanBeAlternated M₁ M₂ hf₁ hf₂ pre pre id id hpoly hpoly PolyT.id' PolyT.id'
  exact ⟨⟨pre, K₁, K₂, N, q₀, q, hpoly, hpre, hfin, hhost, halt⟩, fun pre hpre N q hN => everyAlternationMeetsMinBound pre hpre M₁ C₁ h₁ M₂ C₂ h₂ N q hN⟩

/-- The same for deciding; “some bit is 1” is polynomial-time (`VariableBound.Rename.anyBit_polyT`). -/
theorem decidingFromTheTwoTheorems : DecidingFromTheTwoTheorems := by
  intro M₁ C₁ hf₁ h₁ M₂ C₂ hf₂ h₂
  obtain ⟨pre, hpoly, hpre⟩ := renamingFrontEndExists
  have hs : PolyT someBit := VariableBound.Rename.anyBit_polyT
  obtain ⟨K₁, K₂, N, q₀, q, hfin, hhost, halt⟩ := everyTwoMachinesCanBeAlternated M₁ M₂ hf₁ hf₂ pre pre someBit someBit hpoly hpoly hs hs
  exact ⟨⟨pre, K₁, K₂, N, q₀, q, hpoly, hpre, hfin, hhost, halt⟩, fun pre hpre N q hN => everyAlternationDecidesWithinMinBound pre hpre M₁ C₁ h₁ M₂ C₂ h₂ N q hN⟩

/-- The bound in m and Theorem D (b) imply Corollary 11 on the compact code: take a machine for each
of the two, a machine that runs them in alternation behind the renaming, and the constant that the
main statement gives for it. -/
theorem theTwoTheoremsImplyMinBound : TheTwoTheoremsImplyMinBound := by
  intro hA hD
  obtain ⟨M₁, C, hf₁, hM₁⟩ := propositionsUnfold.1.1 hA
  obtain ⟨M₂, C₂, hf₂, h₂⟩ := propositionsUnfold.2.1.1 hD
  obtain ⟨C₁, h₁⟩ := boundInMSuffices M₁ C hM₁
  obtain ⟨⟨pre, -, -, N, -, q, -, hpre, hfin, -, halt⟩, hall⟩ := minBoundFromTheTwoTheorems M₁ C₁ hf₁ h₁ M₂ C₂ hf₂ h₂
  obtain ⟨C', hC'⟩ := hall pre hpre N q halt
  exact propositionsUnfold.2.2.2 ⟨N, C', hfin, hC'⟩

/-- «This is the Main Theorem.» The two bounds are the same number, because the minimum of the two
powers of 2 is 2 to the minimum of the two exponents. -/
theorem minBoundIsTheMainTheorem : MinBoundIsTheMainTheorem := fun N C => by
  unfold MeetsMinBound CountsCompactKCNFWithinMinBound
  simp only [VariableBound.Paper.timeCor_eq]

end MinOfBounds
