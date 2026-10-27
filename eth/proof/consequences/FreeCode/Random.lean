/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import KSatFreeCodeStatement
import Mathlib.Tactic

/-! # After Definition 6: «A deterministic algorithm is a randomized algorithm that uses no random bits, so allowing randomness can only make s_k smaller»

The statements are in KSatFreeCodeStatement.lean.
* `deterministicIsRandomized`: a machine that decides k-SAT in time t is a randomized algorithm with
  no random bits and no error. There is one string of no bits; on it the input is the code alone.
* `inTimeRand_of_inTime`: so «in time O(2^{δn})» passes from deterministic to randomized algorithms
  with any error p ≥ 0: the same machine and constant, and ⌊0·2^{0·n}⌋ = 0 random bits.
* `randomnessHelps`: «so allowing randomness can only make s_k smaller».
«and Corollary 5 holds under each of these conventions» is in proof/consequences/FreeCode/Main.lean. -/

public section

namespace SatFree

open Turing
open Sat3 (CNF Satisfiable)
open scoped NNReal ENNReal

/-- With no random bits the input is the code alone: if M halts on the word x with the bit b within
t steps, it does so for every string of no bits behind x, and the number of such strings, 1, is at
least (1 − 0)·2^0. -/
theorem noBits (M : TM2ComputableAux Bool Bool) (x : List Bool) (b : Bool) (t : ℕ)
    (ev : Nonempty (TM2OutputsInTime M.tm (x.map M.inputAlphabet.invFun) (some ([b].map M.outputAlphabet.invFun)) t)) :
    (∀ w : Fin 0 → Bool, ∃ b : Bool, Nonempty (TM2OutputsInTime M.tm ((x ++ List.ofFn w).map M.inputAlphabet.invFun) (some ([b].map M.outputAlphabet.invFun)) t)) ∧
    (1 - (0 : ℝ)) * (2 : ℝ) ^ 0 ≤ (Nat.card {w : Fin 0 → Bool //
      Nonempty (TM2OutputsInTime M.tm ((x ++ List.ofFn w).map M.inputAlphabet.invFun) (some ([b].map M.outputAlphabet.invFun)) t)} : ℝ) := by
  have e : ∀ w : Fin 0 → Bool, x ++ List.ofFn w = x := fun w => by simp
  have h : ∀ w : Fin 0 → Bool, Nonempty (TM2OutputsInTime M.tm ((x ++ List.ofFn w).map M.inputAlphabet.invFun) (some ([b].map M.outputAlphabet.invFun)) t) :=
    fun w => by rw [e w]; exact ev
  refine ⟨fun w => ⟨b, h w⟩, ?_⟩
  have : Nonempty {w : Fin 0 → Bool //
      Nonempty (TM2OutputsInTime M.tm ((x ++ List.ofFn w).map M.inputAlphabet.invFun) (some ([b].map M.outputAlphabet.invFun)) t)} := ⟨⟨fun i => i.elim0, h _⟩⟩
  have h1 : 1 ≤ Nat.card {w : Fin 0 → Bool //
      Nonempty (TM2OutputsInTime M.tm ((x ++ List.ofFn w).map M.inputAlphabet.invFun) (some ([b].map M.outputAlphabet.invFun)) t)} := Nat.card_pos
  have h2 : (1 : ℝ) ≤ (Nat.card {w : Fin 0 → Bool //
      Nonempty (TM2OutputsInTime M.tm ((x ++ List.ofFn w).map M.inputAlphabet.invFun) (some ([b].map M.outputAlphabet.invFun)) t)} : ℝ) := by exact_mod_cast h1
  simpa using h2

/-- «A deterministic algorithm is a randomized algorithm that uses no random bits»: a machine that
decides k-SAT in time t is a randomized algorithm with no random bits and no error. -/
theorem deterministicIsRandomized : DeterministicIsRandomized := fun _ M t h n φ hφ => by
  obtain ⟨b, hb, ev⟩ := h n φ hφ
  obtain ⟨h1, h2⟩ := noBits M (enc φ) b (t n) ev
  exact ⟨h1, b, hb, h2⟩

/-- An algorithm with error at most p has error at most p', if p ≤ p'. -/
theorem decidesRandTM_mono {p p' : ℝ} (hp : p ≤ p') {k : ℕ} {M : TM2ComputableAux Bool Bool} {r t : ℕ → ℕ} (h : DecidesRandTM p k M r t) :
    DecidesRandTM p' k M r t := fun n φ hφ => by
  obtain ⟨h1, b, hb, h2⟩ := h n φ hφ
  refine ⟨h1, b, hb, le_trans ?_ h2⟩
  exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)

/-- If a deterministic algorithm decides k-SAT in time O(2^{δn}), so does a randomized algorithm
with error at most p, for every p ≥ 0: the same machine, with no random bits. -/
theorem inTimeRand_of_inTime {p : ℝ} (hp : 0 ≤ p) {k : ℕ} {δ : ℝ≥0} (h : InTime k δ) : InTimeRand p k δ := by
  obtain ⟨M, c, hfin, h⟩ := h
  refine ⟨M, c, 0, 0, le_rfl, hfin, ?_⟩
  have hr : (fun n : ℕ => ⌊((0 : ℕ) : ℝ) * (2 : ℝ) ^ (((0 : ℚ) : ℝ) * n)⌋₊) = fun _ => 0 := by
    funext n
    simp
  rw [hr]
  exact decidesRandTM_mono hp (deterministicIsRandomized k M _ h)

/-- «so allowing randomness can only make s_k smaller». -/
theorem randomnessHelps : RandomnessHelps := fun _ hp _ => le_iInf₂ fun δ hδ => iInf₂_le δ (inTimeRand_of_inTime hp hδ)

end SatFree
