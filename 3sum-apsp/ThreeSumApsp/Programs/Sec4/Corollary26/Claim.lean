/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec4.Corollary26.AllInstances
public import ThreeSumApsp.Programs.Sec4.Corollary26.Program

/-!
# Corollary 26, the offline form, for programs of the light language

Corollary 26: "Hence, for every set W of positions of an N × N matrix, the entries (XY)[I, J], (I,
J) ∈ W, can be computed deterministically in O(|W| D^{0.437} + N²/D^{0.063}) time". This is
`Claim.Corollary_26_wanted`, here with "is solved in time T" read as a statement about programs of
the light language (`claim_corollary_26_wanted`).

The program is `program26`: for m = ⌈log₄ D⌉ ≥ 60 it builds and asks the data structure of Theorem
30 with L = 21 m and t = ⌈m/9⌉, and for m < 60 it computes inner products. The procedure
allInstances26 of that program solves the task on all instances (`allInstances26_program26`), with a
polynomially bounded need (`allInstancesNeed26_poly`), and for N ≥ D^18 its time is within the bound
(`allInstancesTime26_le`).

This is the form of Corollary 26 on which Corollary 16, and through it the second bounds of Theorems
19 and 22, rest: a procedure that other procedures call. The statement about one program that reads
the input of the problem is `wordRam_corollary_26_wanted`.
-/

public section

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.Spec

/-- The time of allInstances26 is monotone in the number of wanted positions and does not depend on
the bound on the entries. -/
private theorem allInstancesTime26_mono (c N D₀ : ℕ) {w w' : ℕ} (U U' : ℕ) (hw : w ≤ w') :
    allInstancesTime26 c [N, D₀, w, U] ≤ allInstancesTime26 c [N, D₀, w', U'] := by
  change 400 + (if D₀ ^ 18 ≤ N then tOffline32 c ratParams26 N D₀ w else 40 * ((w + 1) * (D₀ + 1)))
    ≤ 400 + (if D₀ ^ 18 ≤ N then tOffline32 c ratParams26 N D₀ w' else 40 * ((w' + 1) * (D₀ + 1)))
  split_ifs
  · unfold tOffline32
    have := Nat.mul_le_mul_right (tQuery31 ratParams26 D₀ + 30) hw
    omega
  · have := Nat.mul_le_mul_right (D₀ + 1) (show w + 1 ≤ w' + 1 by omega)
    omega

/-- **The procedure allInstances26 of `program26` solves the task on all instances**: the program
holds allInstances26, regimeTest26 and the brute force at their numbers. -/
theorem allInstances26_program26 : SolvesN thinTask program26 Proc.allInstances26
    (allInstancesTime26 cShared30) allInstancesNeed26 :=
  allInstances26_solves (program31_at _ Proc.allInstances26) (program31_at _ Proc.regimeTest26)
    (at_base58 rfl _) fun R lim => (offline32_program31 _ lim).append R

/-- **Corollary 26, last sentence, for programs of the light language.** -/
theorem claim_corollary_26_wanted : Claim.Corollary_26_wanted lightModel := by
  intro _
  obtain ⟨C, hC⟩ := allInstancesTime26_le cShared30
  refine ⟨C, fun N D₀ w _ => (allInstancesTime26 cShared30 [N, D₀, w, 0] : ℝ),
    ⟨_, _, _, _, allInstancesNeed26_poly, allInstances26_program26,
      fun N D₀ w w' U u _ _ _ hw _ => ?_⟩,
    fun N D₀ w u hD hN _ => hC N D₀ w 0 hD hN⟩
  change (allInstancesTime26 cShared30 [N, D₀, w, U] : ℝ) ≤
      (allInstancesTime26 cShared30 [N, D₀, w', 0] : ℝ)
  exact_mod_cast allInstancesTime26_mono cShared30 N D₀ U 0 hw

end Light.Sec4
