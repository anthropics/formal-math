/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import SizeCircuit.CircuitDefs
import SizeCircuit.Addition
import ToTuring.Lib.Unary
import ToTuring.Lib.Nat2
import ToTuring.Lib.Nat1b
import ToTuring.Lib.List3
import Mathlib.Tactic

/-! # Section 7, proof of Corollary 7: the circuits are computed in polynomial time

`certGates_sizeGates`: from n in unary and s in binary, the list of gates `sizeGates n s` of
proof/consequences/SizeCircuit/CircuitDefs.lean is computed in polynomial time (`Groundwork.PolyT`).
The paper does not say this; it is needed because the formula Γ is written by a machine.

The n steps of the addition are a fold along the n strokes of the unary number. A fold is polynomial
time if its step is and the words of all its states have polynomial length. The step is written
without case distinction on lists (`addStepE`). The states are short because, by `iterate_spec`,
they hold at most 3n wire numbers (in three lists of at most n each) and 5n gates, all naming wires
below 6n. -/

public section

namespace SizeCircuit

open Groundwork CircuitLowerBound CircuitLowerBound.Blocks

/-! ### The step -/

/-- `addStep` written with lengths, places and `drop`. -/
@[expose] def addStepE (n : ℕ) (st : AddState) : AddState :=
  if 3 ≤ st.1.length then
    ((n + st.2.2.2.length + 1) :: st.1.drop 3, (n + st.2.2.2.length + 4) :: st.2.1, st.2.2.1,
      st.2.2.2 ++ fullAdder (n + st.2.2.2.length) (st.1.getD 0 0) (st.1.getD 1 0) (st.1.getD 2 0))
  else if 2 ≤ st.1.length then
    ((n + st.2.2.2.length + 1) :: st.2.1, [], st.2.2.1 ++ [n + st.2.2.2.length], st.2.2.2 ++ halfAdder (st.1.getD 0 0) (st.1.getD 1 0))
  else if 1 ≤ st.1.length then (st.2.1, [], st.2.2.1 ++ [st.1.getD 0 0], st.2.2.2)
  else st

/-- The two ways to write the step agree. -/
theorem addStep_eq (n : ℕ) (st : AddState) : addStep n st = addStepE n st := by
  obtain ⟨cur, nxt, dig, K⟩ := st
  rcases cur with _ | ⟨a, _ | ⟨u, _ | ⟨w, r⟩⟩⟩
  · rfl
  · rfl
  · rfl
  · have h : 3 ≤ (a :: u :: w :: r).length := by
      simp only [List.length_cons]
      omega
    exact (if_pos h).symm

/-- The step is polynomial time, as a function of n in binary and the state. -/
theorem addStep_polyT : PolyT fun p : ℕ × AddState => addStep p.1 p.2 := by
  have h : PolyT fun p : ℕ × AddState => addStepE p.1 p.2 := by
    unfold addStepE fullAdder halfAdder
    fun_prop
  exact h.congr fun p => (addStep_eq p.1 p.2).symm

/-! ### The words of the states are short -/

/-- The word of a list whose elements have words of length at most B has length at most (number of
elements)·(B + 2) + 2. -/
theorem len_list_le' {α : Type} [Enc α] {B : ℕ} : ∀ l : List α, (∀ a ∈ l, len a ≤ B) → len l ≤ l.length * (B + 2) + 2
  | [], _ => by rw [len_nil]; omega
  | a :: l, h => by
    have h1 := h a (by simp)
    have h2 := len_list_le' l fun b hb => h b (by simp [hb])
    rw [len_cons, List.length_cons, Nat.succ_mul]
    omega

/-- The word of a list of at most L elements with words of length at most B. -/
theorem len_list_le {α : Type} [Enc α] {B L : ℕ} {l : List α} (h : ∀ a ∈ l, len a ≤ B) (hL : l.length ≤ L) : len l ≤ L * (B + 2) + 2 :=
  (len_list_le' l h).trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ hL) 2)

/-- The word of a number x ≤ M has length at most 3M + 2. -/
theorem len_nat_le {x M : ℕ} (h : x ≤ M) : len x ≤ 3 * M + 2 := by
  have h1 : Nat.size x ≤ x := Nat.size_le.2 Nat.lt_two_pow_self
  rw [len_nat]
  omega

/-- The word of a gate that names wires up to M has length at most 6M + 18. -/
theorem len_gate_le (g : GateD) {M : ℕ} (h1 : g.2.1 ≤ M) (h2 : g.2.2 ≤ M) : len g ≤ 6 * M + 18 := by
  obtain ⟨⟨b0, b1, b2, b3⟩, i, j⟩ := g
  dsimp only at h1 h2
  have e1 := len_nat_le h1
  have e2 := len_nat_le h2
  simp only [len_pair, len_bool]
  omega

/-- Gates that read earlier wires only name wires below the number of all wires. -/
theorem lt_of_wfa : ∀ {K : List GateD} {n : ℕ}, WFa n K → ∀ g ∈ K, g.2.1 < n + K.length ∧ g.2.2 < n + K.length
  | [], _, _, g, hg => absurd hg List.not_mem_nil
  | g' :: K, n, h, g, hg => by
    rw [List.length_cons]
    rcases List.mem_cons.1 hg with e | hg
    · have := h.1
      rw [e]
      omega
    · have := lt_of_wfa h.2 g hg
      omega

/-- The bound on the length of the words of the states. -/
@[expose] def stateLen (m : ℕ) : ℕ := 3 * (m * (3 * (6 * m) + 2 + 2) + 2) + (5 * m * (6 * (6 * m) + 18 + 2) + 2) + 6

/-- The bound is below a polynomial. -/
theorem stateLen_pb : PB stateLen :=
  (((PB.const 3).mul ((PB.id'.mul ((((PB.const 3).mul ((PB.const 6).mul PB.id')).add (PB.const 2)).add (PB.const 2))).add (PB.const 2))).add
    ((((PB.const 5).mul PB.id').mul ((((PB.const 6).mul ((PB.const 6).mul PB.id')).add (PB.const 18)).add (PB.const 2))).add (PB.const 2))).add (PB.const 6)

/-- After k ≤ n steps the word of the state has length at most `stateLen m`, for every m ≥ n. -/
theorem len_iterate_le (n k m : ℕ) (hk : k ≤ n) (hm : n ≤ m) : len ((addStep n)^[k] (addStart n)) ≤ stateLen m := by
  obtain ⟨⟨g1, g2, g3, g4, -⟩, h1, h2, h3⟩ := iterate_spec n k hk
  generalize (addStep n)^[k] (addStart n) = st at g1 g2 g3 g4 h1 h2 h3 ⊢
  obtain ⟨cur, nxt, dig, K⟩ := st
  dsimp only at g1 g2 g3 g4 h1 h2 h3
  have e1 : len cur ≤ m * (3 * (6 * m) + 2 + 2) + 2 := len_list_le (fun x hx => len_nat_le (by have := g1 x hx; omega)) (by omega)
  have e2 : len nxt ≤ m * (3 * (6 * m) + 2 + 2) + 2 := len_list_le (fun x hx => len_nat_le (by have := g2 x hx; omega)) (by omega)
  have e3 : len dig ≤ m * (3 * (6 * m) + 2 + 2) + 2 := len_list_le (fun x hx => len_nat_le (by have := g3 x hx; omega)) (by omega)
  have e4 : len K ≤ 5 * m * (6 * (6 * m) + 18 + 2) + 2 :=
    len_list_le (fun g hg => len_gate_le g (by have := lt_of_wfa g4 g hg; omega) (by have := lt_of_wfa g4 g hg; omega)) (by omega)
  simp only [len_pair, stateLen]
  omega

/-! ### The addition -/

/-- A fold along a list of strokes that applies f at each stroke applies f as often as the list is
long. -/
theorem foldl_eq_iterate {γ : Type} (f : γ → γ) : ∀ (l : List Unit) (a : γ), l.foldl (fun c _ => f c) a = f^[l.length] a
  | [], _ => rfl
  | _ :: l, a => by rw [List.foldl_cons, foldl_eq_iterate f l, List.length_cons, Function.iterate_succ_apply]

/-- The addition is polynomial time in n in unary. -/
theorem added_polyT : PolyT fun p : List Unit × ℕ => added p.1.length := by
  have h : PolyT fun p : List Unit × ℕ => p.1.foldl (fun c _ => addStep p.1.length c) (addStart p.1.length) := by
    refine PolyT.foldl (l := fun p : List Unit × ℕ => p.1) (a := fun p => addStart p.1.length) (g := fun p c _ => addStep p.1.length c) (by fun_prop) ?_ ?_
      ⟨stateLen, stateLen_pb, ?_⟩
    · have hr : PolyT fun p : List Unit × ℕ => List.range p.1.length := PolyT.range (Unary.of_length (by fun_prop))
      exact hr.prodMk (PolyT.const _)
    · exact PolyT.comp (f := fun p : ℕ × AddState => addStep p.1 p.2) (g := fun q : (List Unit × ℕ) × AddState × Unit => (q.1.1.length, q.2.1))
        addStep_polyT (by fun_prop)
    · rintro ⟨l, s⟩ k
      dsimp only
      rw [foldl_eq_iterate]
      refine len_iterate_le _ _ _ (List.length_take_le' _ _) ?_
      rw [len_pair, len_units]
      omega
  exact h.congr fun p => foldl_eq_iterate _ _ _

/-! ### The comparison, and the circuit -/

/-- The gates of the comparison are polynomial time in (N, s, the list of digit wires). -/
theorem compareGates_polyT : PolyT fun q : ℕ × ℕ × List ℕ => compareGates q.1 q.2.1 q.2.2 := by
  have h1 : PolyT fun q : ℕ × ℕ × List ℕ => 2 ^ q.2.2.length := PolyT.two_pow (Unary.of_length (by fun_prop))
  have h2 : PolyT fun q : ℕ × ℕ × List ℕ => List.range q.2.2.length := PolyT.range (Unary.of_length (by fun_prop))
  have key : ∀ (P : ℕ × ℕ × List ℕ → ℕ) (R : ℕ × ℕ × List ℕ → List ℕ), PolyT P → PolyT R → PolyT fun q : ℕ × ℕ × List ℕ =>
      (((if q.2.1 < P q then opOne else opZero), 0, 0) : GateD) :: (R q).map fun i => ((if q.2.1.testBit i then opAnd else opAndN), q.1 + i, q.2.2.getD i 0) := by
    intro P R _ _
    fun_prop
  exact key _ _ h1 h2

/-- **The circuits are computed in polynomial time** from n in unary and s in binary. -/
theorem certGates_sizeGates : CertGates sizeGates := by
  have key : ∀ A : List Unit × ℕ → AddState, PolyT A → PolyT fun p : List Unit × ℕ =>
      (A p).2.2.2 ++ compareGates (p.1.length + (A p).2.2.2.length) p.2 (A p).2.2.1 := by
    intro A hA
    exact PolyT.append (by fun_prop) (PolyT.comp (f := fun q : ℕ × ℕ × List ℕ => compareGates q.1 q.2.1 q.2.2)
      (g := fun p : List Unit × ℕ => (p.1.length + (A p).2.2.2.length, p.2, (A p).2.2.1)) compareGates_polyT (by fun_prop))
  exact key _ added_polyT

end SizeCircuit
