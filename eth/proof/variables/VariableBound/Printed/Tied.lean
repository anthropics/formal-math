/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import VariableBound.Printed.TiedDefs
import UniformInK.Top.End
import ClauseBound.Both.End

/-! # The end of this proof, tied to its functions: the machine and the counting statement

* `tied_of_alg`: the padding machine (`StPaddedW`), run on an algorithm (A, e) followed by a
  polynomial-time `post`, is a machine as in `TiedOut A e post`, with the clause of `StPaddedW`
  kept in the conclusion; the constant is the largest of q and the two constants of the bounds.
* `count_of_tied`: the statement that names no function follows by forgetting that clause. -/

public section

namespace VariableBound

open Groundwork Turing PaddedDescent PaddedDescent.F CountKSat CountKSatRate ClauseBound.Alg ClauseBound.TopN ClauseBound.ParityChecks ClauseBound.Both.End UniformInK UniformInK.End VariableBound.Decide

/-- q·y^q grows with q, for y ≥ 1. -/
theorem mul_pow_mono {q C y : ℕ} (h : q ≤ C) (hy : 1 ≤ y) : q * y ^ q ≤ C * y ^ C :=
  Nat.mul_le_mul h (Nat.pow_le_pow_right hy h)

/-- For an algorithm (A, e) for the rates rn, rm ≥ 0 and a polynomial-time function `post`: one
machine and one constant such that the machine runs `post` after A on every input, with the pad of
2^(e x) units, and puts out
`post` of the count within the three bounds. The padding machine is a hypothesis. -/
theorem tied_of_alg (hP : StPaddedW) {rn rm : ℕ → ℝ} {A : List Bool × U → List Bool} {e : List Bool → ℕ} (h : Alg rn rm A e) {post : List Bool → List Bool} (hpost : PolyT post)
    (hrn0 : ∀ n, 0 ≤ rn n) (hrm0 : ∀ m, 0 ≤ rm m) : TiedOut A e post rn rm := by
  obtain ⟨N, q, hfin, hN⟩ := hP e (fun p => post (A p)) h.polyE (hpost.comp h.polyA)
  obtain ⟨D, hD⟩ := h.timeN q
  obtain ⟨D', hD'⟩ := h.timeM q
  have hrun : ∀ (k n : ℕ) (φ : Sat3.CNF n), 1 ≤ k → SatK.IsKCNF k φ → ∀ t : ℕ, q * ((SatM.enc k φ).length + 2 ^ e (SatM.enc k φ) + 1) ^ q ≤ t →
      Nonempty (TM2OutputsInTime N.tm ((SatM.enc k φ).map N.inputAlphabet.invFun) (some ((post (SatK.binary n (SatK.numSat φ))).map N.outputAlphabet.invFun)) t) := by
    intro k n φ hk hφ t ht
    have hx := hN (SatM.enc k φ)
    rw [h.correct k n φ hk hφ (pad (e (SatM.enc k φ))) (by simp [pad])] at hx
    obtain ⟨ev⟩ := hx
    exact ⟨⟨ev.toEvalsTo, ev.steps_le_m.trans ht⟩⟩
  have hn : ∀ (k n : ℕ) (φ : Sat3.CNF n), 1 ≤ k → 1 ≤ n → SatK.IsKCNF k φ →
      q * ((SatM.enc k φ).length + 2 ^ e (SatM.enc k φ) + 1) ^ q ≤ SatM.boundNK rn (max q (max D D')) k n := fun k n φ hk hn1 hφ =>
    (hD k n φ hk hn1 hφ).trans (boundNK_mono ((le_max_left _ _).trans (le_max_right _ _)) k n (hrn0 n))
  have hm : ∀ (k n : ℕ) (φ : Sat3.CNF n), 1 ≤ k → 1 ≤ φ.length → SatK.IsKCNF k φ → SatM.AllOccur φ →
      q * ((SatM.enc k φ).length + 2 ^ e (SatM.enc k φ) + 1) ^ q ≤ SatM.bound rm (max q (max D D')) k φ.length := fun k n φ hk hm1 hφ ho =>
    (hD' k n φ hk hm1 hφ ho).trans (bound_mono ((le_max_right _ _).trans (le_max_right _ _)) k φ.length (hrm0 _))
  refine ⟨N, max q (max D D'), hfin, fun x => ?_, fun k n φ hk hn1 hφ => hrun k n φ hk hφ _ (hn k n φ hk hn1 hφ), fun k n φ hk hm1 hφ ho => hrun k n φ hk hφ _ (hm k n φ hk hm1 hφ ho),
    fun k n φ hk hn1 hφ ho => hrun k n φ hk hφ _ ?_⟩
  · obtain ⟨ev⟩ := hN x
    exact ⟨⟨ev.toEvalsTo, ev.steps_le_m.trans (mul_pow_mono (le_max_left _ _) (Nat.le_add_left 1 _))⟩⟩
  · rcases le_total ((k : ℝ) ^ 2 * n * rn n) ((k : ℝ) * φ.length * rm φ.length) with hle | hle
    · rw [boundBothK_of_le hle]
      exact hn k n φ hk hn1 hφ
    · rw [boundBothK_of_ge hle]
      exact hm k n φ hk (one_le_length hn1 ho) hφ ho

/-- A machine that runs A on every input and counts within the three bounds is a machine that counts
within the three bounds. This statement names no function. -/
theorem count_of_tied {A : List Bool × U → List Bool} {e : List Bool → ℕ} {rn rm : ℕ → ℝ} (h : TiedOut A e id rn rm) : SatM.CountUniformInRate rn rm :=
  let ⟨M, C, hfin, _, h1, h2, h3⟩ := h
  ⟨M, C, hfin, h1, h2, h3⟩

end VariableBound
