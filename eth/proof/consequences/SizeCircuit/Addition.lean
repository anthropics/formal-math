/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import SizeCircuit.CircuitDefs
import Mathlib.Tactic

/-! # Section 7, proof of Corollary 7: the circuit counts the ones

Facts on `addStep` and `added` of proof/consequences/SizeCircuit/CircuitDefs.lean, for «a circuit
with O(n) gates of two inputs tests whether |S| = s» (proof of Corollary 7).

* `AddGood n st`: all wires named in the state exist, the gates read earlier wires only, and wires
  of the next weight wait only while wires of the present weight do. A step keeps this
  (`addGood_addStep`).
* While a wire waits, a step lowers the number of waiting wires by exactly one; it writes at most 5
  gates and finds at most one digit (`counts_addStep`). So after n steps no wire waits
  (`added_spec`).
* `addValue v st`: under the values v of the wires, the number written by the digits found so far
  plus the waiting wires that are 1, each with its weight. A step keeps it if v obeys the gates
  (`addValue_addStep`). So at the end the digits write the number of inputs that are 1
  (`addValue_added`). -/

public section

namespace SizeCircuit

open Groundwork CircuitLowerBound CircuitLowerBound.Blocks

/-! ### A step when wires of the present weight wait -/

/-- The step if at least three wires of the present weight wait: a full adder. -/
theorem addStep_three (n a u w : ℕ) (r nxt dig : List ℕ) (K : List GateD) : addStep n (a :: u :: w :: r, nxt, dig, K) =
    ((n + K.length + 1) :: r, (n + K.length + 4) :: nxt, dig, K ++ fullAdder (n + K.length) a u w) := rfl

/-- The step if exactly two wires of the present weight wait: a half adder, and its sum is the next
digit. -/
theorem addStep_two (n a u : ℕ) (nxt dig : List ℕ) (K : List GateD) : addStep n ([a, u], nxt, dig, K) =
    ((n + K.length + 1) :: nxt, [], dig ++ [n + K.length], K ++ halfAdder a u) := rfl

/-- The step if exactly one wire of the present weight waits: it is the next digit. -/
theorem addStep_one (n a : ℕ) (nxt dig : List ℕ) (K : List GateD) : addStep n ([a], nxt, dig, K) = (nxt, [], dig ++ [a], K) := rfl

/-! ### The two adders -/

/-- The sum and twice the carry of a full adder make the number of ones among its three inputs. -/
theorem fullAdder_spec (v : ℕ → Bool) (N a u w : ℕ) (h : Obeys v N (fullAdder N a u w)) :
    (v (N + 1)).toNat + 2 * (v (N + 4)).toNat = (v a).toNat + (v u).toNat + (v w).toNat := by
  have h' : v N = gval v (opXor, a, u) ∧ v (N + 1) = gval v (opXor, N, w) ∧ v (N + 2) = gval v (opAnd, a, u) ∧ v (N + 3) = gval v (opAnd, N, w) ∧
      v (N + 4) = gval v (opOr, N + 2, N + 3) ∧ True := h
  obtain ⟨h0, h1, h2, h3, h4, -⟩ := h'
  rw [gval_xor] at h0 h1
  rw [gval_and] at h2 h3
  rw [gval_or] at h4
  rw [h1, h4, h2, h3, h0]
  cases v a <;> cases v u <;> cases v w <;> rfl

/-- The sum and twice the carry of a half adder make the number of ones among its two inputs. -/
theorem halfAdder_spec (v : ℕ → Bool) (N a u : ℕ) (h : Obeys v N (halfAdder a u)) :
    (v N).toNat + 2 * (v (N + 1)).toNat = (v a).toNat + (v u).toNat := by
  have h' : v N = gval v (opXor, a, u) ∧ v (N + 1) = gval v (opAnd, a, u) ∧ True := h
  obtain ⟨h0, h1, -⟩ := h'
  rw [gval_xor] at h0
  rw [gval_and] at h1
  rw [h0, h1]
  cases v a <;> cases v u <;> rfl

/-- The gates of a full adder read earlier wires only. -/
theorem wfa_fullAdder {N a u w : ℕ} (ha : a < N) (hu : u < N) (hw : w < N) : WFa N (fullAdder N a u w) := by
  have h : (a < N ∧ u < N) ∧ (N < N + 1 ∧ w < N + 1) ∧ (a < N + 2 ∧ u < N + 2) ∧ (N < N + 3 ∧ w < N + 3) ∧ (N + 2 < N + 4 ∧ N + 3 < N + 4) ∧ True := by
    refine ⟨?_, ?_, ?_, ?_, ?_, trivial⟩ <;> omega
  exact h

/-- The gates of a half adder read earlier wires only. -/
theorem wfa_halfAdder {N a u : ℕ} (ha : a < N) (hu : u < N) : WFa N (halfAdder a u) := by
  have h : (a < N ∧ u < N) ∧ (a < N + 1 ∧ u < N + 1) ∧ True := by
    refine ⟨?_, ?_, trivial⟩ <;> omega
  exact h

/-- A full adder has 5 gates. -/
theorem length_fullAdder (N a u w : ℕ) : (fullAdder N a u w).length = 5 := rfl

/-- A half adder has 2 gates. -/
theorem length_halfAdder (a u : ℕ) : (halfAdder a u).length = 2 := rfl

/-! ### What a step keeps -/

/-- All wires named in the state exist, the gates read earlier wires only, and wires of the next
weight wait only while wires of the present weight do. -/
@[expose] def AddGood (n : ℕ) (st : AddState) : Prop :=
  (∀ x ∈ st.1, x < n + st.2.2.2.length) ∧ (∀ x ∈ st.2.1, x < n + st.2.2.2.length) ∧ (∀ x ∈ st.2.2.1, x < n + st.2.2.2.length) ∧
    WFa n st.2.2.2 ∧ (st.1 = [] → st.2.1 = [])

/-- The start is good. -/
theorem addGood_addStart (n : ℕ) : AddGood n (addStart n) :=
  ⟨fun x hx => by simpa [addStart] using hx, fun x hx => absurd hx List.not_mem_nil, fun x hx => absurd hx List.not_mem_nil, trivial, fun _ => rfl⟩

/-- A step keeps a good state good. -/
theorem addGood_addStep {n : ℕ} {st : AddState} (h : AddGood n st) : AddGood n (addStep n st) := by
  obtain ⟨cur, nxt, dig, K⟩ := st
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  dsimp only at h1 h2 h3 h4 h5
  rcases cur with _ | ⟨a, _ | ⟨u, _ | ⟨w, r⟩⟩⟩
  · exact ⟨h1, h2, h3, h4, h5⟩
  · rw [addStep_one]
    refine ⟨h2, fun x hx => absurd hx List.not_mem_nil, fun x hx => ?_, h4, fun _ => rfl⟩
    rcases List.mem_append.1 hx with hx | hx
    · exact h3 x hx
    · exact h1 x hx
  · rw [addStep_two]
    have hl : (K ++ halfAdder a u).length = K.length + 2 := by rw [List.length_append, length_halfAdder]
    have ha := h1 a (by simp)
    have hu := h1 u (by simp)
    refine ⟨fun x hx => ?_, fun x hx => absurd hx List.not_mem_nil, fun x hx => ?_, (wfa_append n K _).2 ⟨h4, wfa_halfAdder ha hu⟩,
      fun h => absurd h (List.cons_ne_nil _ _)⟩
    · dsimp only at hx ⊢
      rw [hl]
      rcases List.mem_cons.1 hx with rfl | hx
      · omega
      · have := h2 x hx
        omega
    · dsimp only at hx ⊢
      rw [hl]
      rcases List.mem_append.1 hx with hx | hx
      · have := h3 x hx
        omega
      · rw [List.mem_singleton.1 hx]
        omega
  · rw [addStep_three]
    have hl : (K ++ fullAdder (n + K.length) a u w).length = K.length + 5 := by rw [List.length_append, length_fullAdder]
    have ha := h1 a (by simp)
    have hu := h1 u (by simp)
    have hw := h1 w (by simp)
    refine ⟨fun x hx => ?_, fun x hx => ?_, fun x hx => ?_, (wfa_append n K _).2 ⟨h4, wfa_fullAdder ha hu hw⟩,
      fun h => absurd h (List.cons_ne_nil _ _)⟩
    · dsimp only at hx ⊢
      rw [hl]
      rcases List.mem_cons.1 hx with rfl | hx
      · omega
      · have := h1 x (by simp [hx])
        omega
    · dsimp only at hx ⊢
      rw [hl]
      rcases List.mem_cons.1 hx with rfl | hx
      · omega
      · have := h2 x hx
        omega
    · dsimp only at hx ⊢
      rw [hl]
      have := h3 x hx
      omega

/-- While a wire waits, a step lowers the number of waiting wires by exactly one; it writes at most
5 gates and finds at most one digit. -/
theorem counts_addStep (n : ℕ) (st : AddState) (h5 : st.1 = [] → st.2.1 = []) (hp : 0 < st.1.length + st.2.1.length) :
    (addStep n st).1.length + (addStep n st).2.1.length + 1 = st.1.length + st.2.1.length ∧
      (addStep n st).2.2.2.length ≤ st.2.2.2.length + 5 ∧ (addStep n st).2.2.1.length ≤ st.2.2.1.length + 1 := by
  obtain ⟨cur, nxt, dig, K⟩ := st
  dsimp only at h5 hp
  rcases cur with _ | ⟨a, _ | ⟨u, _ | ⟨w, r⟩⟩⟩
  · rw [h5 rfl] at hp
    exact absurd hp (by simp)
  · rw [addStep_one]
    dsimp only
    simp only [List.length_cons, List.length_append, List.length_nil]
    omega
  · rw [addStep_two]
    dsimp only
    simp only [List.length_cons, List.length_append, List.length_nil, length_halfAdder]
    omega
  · rw [addStep_three]
    dsimp only
    simp only [List.length_cons, List.length_append, length_fullAdder]
    omega

/-- After k ≤ n steps: the state is good, n − k wires wait, at most 5k gates are written and at most
k digits found. -/
theorem iterate_spec (n : ℕ) : ∀ k ≤ n, AddGood n ((addStep n)^[k] (addStart n)) ∧
    ((addStep n)^[k] (addStart n)).1.length + ((addStep n)^[k] (addStart n)).2.1.length + k = n ∧
    ((addStep n)^[k] (addStart n)).2.2.2.length ≤ 5 * k ∧ ((addStep n)^[k] (addStart n)).2.2.1.length ≤ k := by
  intro k
  induction k with
  | zero =>
    intro _
    exact ⟨addGood_addStart n, by simp [addStart], by simp [addStart], by simp [addStart]⟩
  | succ k ih =>
    intro hk
    obtain ⟨g, h1, h2, h3⟩ := ih (by omega)
    rw [Function.iterate_succ_apply']
    obtain ⟨c1, c2, c3⟩ := counts_addStep n _ g.2.2.2.2 (by omega)
    exact ⟨addGood_addStep g, by omega, by omega, by omega⟩

/-- **After the n steps**: no wire waits; all digit wires exist; the gates read earlier wires only;
there are at most 5n gates and at most n digits. -/
theorem added_spec (n : ℕ) : (added n).1 = [] ∧ (added n).2.1 = [] ∧ (∀ x ∈ (added n).2.2.1, x < n + (added n).2.2.2.length) ∧ WFa n (added n).2.2.2 ∧
    (added n).2.2.2.length ≤ 5 * n ∧ (added n).2.2.1.length ≤ n := by
  obtain ⟨g, h1, h2, h3⟩ := iterate_spec n n le_rfl
  exact ⟨List.length_eq_zero_iff.1 (by unfold added; omega), List.length_eq_zero_iff.1 (by unfold added; omega), g.2.2.1, g.2.2.2.1, h2, h3⟩

/-! ### The number that is kept -/

/-- The number of wires of the list that are 1 under v. -/
@[expose] def onesAmong (v : ℕ → Bool) (l : List ℕ) : ℕ := (l.map fun x => (v x).toNat).sum

/-- No wire, no one. -/
theorem onesAmong_nil (v : ℕ → Bool) : onesAmong v [] = 0 := rfl

/-- The number of ones of a list of wires: the first wire and the rest. -/
theorem onesAmong_cons (v : ℕ → Bool) (x : ℕ) (l : List ℕ) : onesAmong v (x :: l) = (v x).toNat + onesAmong v l := by
  simp only [onesAmong, List.map_cons, List.sum_cons]

/-- The number written by the digits found so far, plus 2^j for each waiting wire of the present
weight 2^j that is 1, plus 2^{j+1} for each waiting wire of the next weight that is 1. -/
@[expose] def addValue (v : ℕ → Bool) (st : AddState) : ℕ := ofWord (st.2.2.1.map v) + 2 ^ st.2.2.1.length * (onesAmong v st.1 + 2 * onesAmong v st.2.1)

/-- The value of a state given by its four parts. -/
theorem addValue_mk (v : ℕ → Bool) (cur nxt dig : List ℕ) (K : List GateD) :
    addValue v (cur, nxt, dig, K) = ofWord (dig.map v) + 2 ^ dig.length * (onesAmong v cur + 2 * onesAmong v nxt) := rfl

/-- The value after a new digit d has been found and the next weight has become the present one. -/
theorem addValue_push (v : ℕ → Bool) (cur dig : List ℕ) (d : ℕ) (K : List GateD) :
    addValue v (cur, [], dig ++ [d], K) = ofWord (dig.map v) + 2 ^ dig.length * ((v d).toNat + 2 * onesAmong v cur) := by
  rw [addValue_mk, List.map_append, ofWord_append, List.length_map, List.length_append, List.length_singleton, onesAmong_nil, pow_succ]
  simp only [List.map_cons, List.map_nil, ofWord]
  ring

/-- If v obeys the gates after a step, it obeys the gates before it, and the step has kept the
value. -/
theorem addValue_addStep (v : ℕ → Bool) (n : ℕ) (st : AddState) (h : Obeys v n (addStep n st).2.2.2) :
    Obeys v n st.2.2.2 ∧ addValue v (addStep n st) = addValue v st := by
  obtain ⟨cur, nxt, dig, K⟩ := st
  rcases cur with _ | ⟨a, _ | ⟨u, _ | ⟨w, r⟩⟩⟩
  · exact ⟨h, rfl⟩
  · refine ⟨h, ?_⟩
    rw [addStep_one, addValue_push, addValue_mk, onesAmong_cons, onesAmong_nil, Nat.add_zero]
  · rw [addStep_two] at h ⊢
    obtain ⟨hK, hA⟩ := (obeys_append v n K _).1 h
    have e := halfAdder_spec v _ a u hA
    refine ⟨hK, ?_⟩
    rw [addValue_push, addValue_mk, onesAmong_cons, onesAmong_cons, onesAmong_cons, onesAmong_nil]
    congr 2
    omega
  · rw [addStep_three] at h ⊢
    obtain ⟨hK, hA⟩ := (obeys_append v n K _).1 h
    have e := fullAdder_spec v _ a u w hA
    refine ⟨hK, ?_⟩
    rw [addValue_mk, addValue_mk, onesAmong_cons, onesAmong_cons, onesAmong_cons, onesAmong_cons, onesAmong_cons]
    congr 2
    omega

/-- If v obeys the gates after k steps, the value is still the number of inputs that are 1. -/
theorem addValue_iterate (v : ℕ → Bool) (n : ℕ) : ∀ k : ℕ, Obeys v n ((addStep n)^[k] (addStart n)).2.2.2 →
    addValue v ((addStep n)^[k] (addStart n)) = onesAmong v (List.range n) := by
  intro k
  induction k with
  | zero =>
    intro _
    simp [addStart, addValue_mk, onesAmong_nil, ofWord]
  | succ k ih =>
    intro h
    rw [Function.iterate_succ_apply'] at h ⊢
    obtain ⟨h1, h2⟩ := addValue_addStep v n _ h
    rw [h2, ih h1]

/-- **At the end the digits write the number of inputs that are 1**, under all values v of the wires
that obey the gates of the addition. -/
theorem addValue_added (v : ℕ → Bool) (n : ℕ) (h : Obeys v n (added n).2.2.2) : ofWord ((added n).2.2.1.map v) = onesAmong v (List.range n) := by
  have h1 := addValue_iterate v n n h
  obtain ⟨e1, e2, -⟩ := added_spec n
  have h2 : addValue v (added n) = onesAmong v (List.range n) := h1
  rw [addValue, e1, e2, onesAmong_nil] at h2
  simpa using h2

end SizeCircuit
