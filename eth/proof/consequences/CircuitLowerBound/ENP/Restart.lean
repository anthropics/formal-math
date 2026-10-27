/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import CircuitLowerBound.ENP.Round
import CircuitLowerBound.Small
import CountKSatRate.Pad
import Mathlib.Tactic

/-! # The circuit lower bound for E^NP (Section 7): the language L0 is in E^NP, in the restart form

`stENP'_of`: the language `L0` is decided by an ordinary machine that is started again after every
answer of the oracle (`ENP.InENP'`). The machine computes the function `roundF` of
`proof/consequences/CircuitLowerBound/ENP/Round.lean`, after
writing a pad of 2^(2m+4) units by doubling (`CountKSatRate.stPaddedW`,
proof/consequences/CountKSatRate/Pad.lean). On a word x of length m that writes the number i, the
protocol makes i + 1 ≤ 2^m queries. After j answers, the negated answers
are the first j values of the search `greedy (Phi m)`: the answer «satisfiable with 0 for the next
variable» means the value 0. The result is value number i.
The hypotheses are interface statements: the chains and the formulas are computed in polynomial time
(`StCertSched`, `StCertTabF`, `StFlip`). That the variables of the formula of a table have L bits
(`StVars`) is taken from
`proof/consequences/CircuitLowerBound/Small.lean`. -/

public section

namespace CircuitLowerBound

open ENP Groundwork PaddedDescent Turing

namespace Restart

/-- The search has set j variables after j steps. -/
theorem length_greedy (φ : Cnf) (j : ℕ) : (greedy φ j).length = j := by
  induction j with
  | zero => rfl
  | succ j ih => rw [greedy, List.length_append, ih]; rfl

/-- The time of a round on x and a ≤ 2^m answers, m = |x|. -/
theorem time_le (q m a : ℕ) (ha : a ≤ 2 ^ m) : q * (2 * m + 1 + a + 2 ^ (2 * m + 4) + 1) ^ q ≤ 2 ^ ((6 * q + 1) * (m + 1)) := by
  have h1 : 2 * m + 1 + a + 2 ^ (2 * m + 4) + 1 ≤ 2 ^ (2 * m + 5) := by
    have a1 : m < 2 ^ m := Nat.lt_two_pow_self
    have a2 : 2 ^ (m + 2) ≤ 2 ^ (2 * m + 4) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have a3 : 2 ^ (m + 2) = 2 ^ m * 4 := by rw [pow_add]; norm_num
    have a4 : 2 ^ (2 * m + 5) = 2 ^ (2 * m + 4) * 2 := pow_succ 2 _
    omega
  have h2 : q + (2 * m + 5) * q + (4 * q * m + m + 1) = (6 * q + 1) * (m + 1) := by ring
  calc q * (2 * m + 1 + a + 2 ^ (2 * m + 4) + 1) ^ q ≤ 2 ^ q * (2 ^ (2 * m + 5)) ^ q :=
        Nat.mul_le_mul Nat.lt_two_pow_self.le (Nat.pow_le_pow_left h1 q)
    _ = 2 ^ (q + (2 * m + 5) * q) := by rw [← pow_mul, ← pow_add]
    _ ≤ 2 ^ ((6 * q + 1) * (m + 1)) := Nat.pow_le_pow_right (by norm_num) (by omega)

open Classical in
/-- The protocol, from what the rounds return. After j answers the negated answers are the first j
values of the search; d more rounds with a query follow, and the round with the result. -/
theorem protocol {N : TM2ComputableAux Bool Bool} {T : ℕ} {x : List Bool} {φ : Cnf}
    (hq : ∀ j ≤ ofWord x, ENP.Round N T x ((greedy φ j).map fun b => !b) (true :: encCnf (φ ++ units (greedy φ j ++ [false]))))
    (hd : ENP.Round N T x ((greedy φ (ofWord x + 1)).map fun b => !b) [false, (greedy φ (ofWord x + 1)).getD (ofWord x) false]) :
    ∀ d j r : ℕ, j + d = ofWord x + 1 → d ≤ r →
      Protocol N T x ((greedy φ (ofWord x + 1)).getD (ofWord x) false) ((greedy φ j).map fun b => !b) r
  | 0, j, r, hj, _ => by
    obtain rfl : j = ofWord x + 1 := by omega
    exact .done hd
  | d + 1, j, r, hj, hr => by
    obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
    refine .query (hq j (by omega)) ?_
    have e1 : decide (SAT (encCnf (φ ++ units (greedy φ j ++ [false])))) = decide (Sat (φ ++ units (greedy φ j ++ [false]))) :=
      decide_eq_decide.2 (Round.sat_encCnf _)
    have e : ((greedy φ j).map fun b => !b) ++ [decide (SAT (encCnf (φ ++ units (greedy φ j ++ [false]))))] = (greedy φ (j + 1)).map fun b => !b := by
      rw [e1, greedy, List.map_append, List.map_singleton, Bool.not_not]
    rw [e]
    exact protocol hq hd d (j + 1) r' (by omega) (by omega)

end Restart

open Restart

/-- The language L0 is in E^NP, in the form with a machine that is started again after every answer;
with the bound on the variables as a hypothesis. -/
theorem stENP'_of_vars (h1 : StCertSched) (h2 : StCertTabF) (h3 : StFlip) (h4 : StVars) : StENP' := by
  obtain ⟨G, hG, hGs⟩ := h2
  obtain ⟨fb, hfb, hfbs⟩ := h3
  obtain ⟨N, q, hfin, hN⟩ := CountKSatRate.stPaddedW eW (roundF G fb) Round.eW_polyT (Round.roundF_polyT h1 hG hfb)
  refine ⟨N, 6 * q + 1, hfin, fun x => ⟨(greedy (Phi x.length) (ofWord x + 1)).getD (ofWord x) false, Iff.rfl, ?_⟩⟩
  have hi : ofWord x < 2 ^ x.length := ofWord_lt x
  -- what a round returns, and its time
  have hR : ∀ ans : List Bool, ans.length ≤ 2 ^ x.length → ENP.Round N (2 ^ ((6 * q + 1) * (x.length + 1))) x ans
      (bif decide (ans.length ≤ ofWord x) then true :: encCnf (Phi x.length ++ units (ans.map (fun b => !b) ++ [false]))
        else [false, !ans.getD (ofWord x) false]) := by
    intro ans ha
    have h := hN (roundInput x ans)
    rw [Round.eW_roundInput, Round.roundF_roundInput hGs hfbs h4 x ans ha (by rw [pad, List.length_replicate]), Round.length_roundInput] at h
    obtain ⟨ev⟩ := h
    exact ⟨⟨ev.toEvalsTo, ev.steps_le_m.trans (time_le q x.length ans.length ha)⟩⟩
  have hnn : ∀ l : List Bool, (l.map fun b => !b).map (fun b => !b) = l := by
    intro l
    have e : ((fun b : Bool => !b) ∘ fun b : Bool => !b) = id := funext fun b => Bool.not_not b
    rw [List.map_map, e, List.map_id]
  have hP := protocol (N := N) (T := 2 ^ ((6 * q + 1) * (x.length + 1))) (x := x) (φ := Phi x.length) (fun j hj => ?_) ?_ (ofWord x + 1) 0
    (2 ^ ((6 * q + 1) * (x.length + 1))) (by omega) ?_
  · exact hP
  · have h := hR ((greedy (Phi x.length) j).map fun b => !b) (by rw [List.length_map, length_greedy]; omega)
    rw [List.length_map, length_greedy, decide_eq_true hj, cond_true, hnn] at h
    exact h
  · have h := hR ((greedy (Phi x.length) (ofWord x + 1)).map fun b => !b) (by rw [List.length_map, length_greedy]; omega)
    have hlen : ofWord x < (greedy (Phi x.length) (ofWord x + 1)).length := by rw [length_greedy]; omega
    rw [List.length_map, length_greedy, decide_eq_false (by omega), cond_false,
      List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hlen), List.getElem_map, Bool.not_not, ← List.getD_eq_getElem _ false hlen] at h
    exact h
  · have h5 : 2 ^ x.length ≤ 2 ^ ((6 * q + 1) * (x.length + 1)) := Nat.pow_le_pow_right (by norm_num) (by nlinarith)
    omega

/-- The language L0 is in E^NP, in the form with a machine that is started again after every answer. -/
theorem stENP'_of (h1 : StCertSched) (h2 : StCertTabF) (h3 : StFlip) : StENP' := stENP'_of_vars h1 h2 h3 stVars

end CircuitLowerBound
