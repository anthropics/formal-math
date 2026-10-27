/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import SizeCircuit.Defs
public import CircuitLowerBound.Circ.Blocks
import CircuitLowerBound.Circ.Form
import Mathlib.Tactic

/-! # Section 7, proof of Corollary 7: clauses that force the values of the gates

Proofs of `StForces` and `StUniqueExtension` of proof/consequences/SizeCircuit/Defs.lean. The paper:
«a new variable for each gate, clauses of at most 3 literals that force it to equal the value of the
gate».

The clauses of all gates hold under an assignment a exactly if a obeys the circuit
(`CircuitLowerBound.Blocks.Obeys`: the variable of every gate has the value of the gate;
`holds_wiresFormula`). Two assignments that obey a circuit whose gates read earlier wires only, and
agree on the inputs, agree on all wires (`obeys_unique`, by induction over the gates). The values of
the wires on the input (`wireVal`) obey the circuit. -/

public section

namespace SizeCircuit

open Groundwork Groundwork.Prog CountKSat CircuitLowerBound CircuitLowerBound.Blocks ENP

/-! ### Formulas -/

/-- The formula without clauses holds. -/
theorem holds_nil (a : ℕ → Bool) : Holds a [] := fun _ hC => absurd hC List.not_mem_nil

/-- A formula with one more clause holds exactly if that clause has a true literal and the rest
holds. -/
theorem holds_cons (a : ℕ → Bool) (C : List (ℕ × Bool)) (ψ : Fml) : Holds a (C :: ψ) ↔ (∃ l ∈ C, a l.1 = l.2) ∧ Holds a ψ := by
  simp only [Holds, List.mem_cons, forall_eq_or_imp]

/-- Two formulas written one after the other hold exactly if both hold. -/
theorem holds_append (a : ℕ → Bool) (φ ψ : Fml) : Holds a (φ ++ ψ) ↔ Holds a φ ∧ Holds a ψ := by
  simp only [Holds, List.mem_append, or_imp, forall_and]

/-- Whether a formula holds depends only on the values of the variables that occur in it. -/
theorem holds_congr {a a' : ℕ → Bool} {ψ : Fml} (h : ∀ C ∈ ψ, ∀ l ∈ C, a l.1 = a' l.1) : Holds a ψ ↔ Holds a' ψ := by
  constructor
  · intro H C hC
    obtain ⟨l, hl, e⟩ := H C hC
    exact ⟨l, hl, by rw [← h C hC l hl]; exact e⟩
  · intro H C hC
    obtain ⟨l, hl, e⟩ := H C hC
    exact ⟨l, hl, by rw [h C hC l hl]; exact e⟩

/-! ### One gate -/

/-- The table behind `stForces`: for bits x, y, z and a function of two bits with the values b0, b1,
b2, b3 at 00, 01, 10, 11, the four clauses "not (inputs x, y and the wrong value z)" hold exactly if
z is the value of the function at x, y. -/
private theorem forces_table : ∀ x y z b0 b1 b2 b3 : Bool,
    ((x = true ∨ y = true ∨ z = b0) ∧ (x = true ∨ y = false ∨ z = b1) ∧ (x = false ∨ y = true ∨ z = b2) ∧ (x = false ∨ y = false ∨ z = b3)) ↔
      z = (if x then (if y then b3 else b2) else (if y then b1 else b0)) := by
  intro x y z b0 b1 b2 b3
  cases x <;> cases y <;> simp

/-- **`StForces`.** «clauses of at most 3 literals that force it to equal the value of the gate»:
the four clauses of a gate hold exactly if the variable of its wire has the value of the gate, and
each has at most 3 literals. -/
theorem stForces : StForces := by
  rintro a i ⟨⟨b0, b1, b2, b3⟩, p, q⟩
  refine ⟨?_, ?_⟩
  · have h := forces_table (a p) (a q) (a i) b0 b1 b2 b3
    simp only [Holds, gateClauses, GateD.toGate, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, exists_eq_or_imp, exists_eq_left]
    exact h
  · intro C hC
    simp only [gateClauses, List.mem_cons, List.not_mem_nil, or_false] at hC
    rcases hC with rfl | rfl | rfl | rfl <;> exact le_refl 3

/-- The four clauses of a gate hold exactly if the variable of its wire has the value of the gate. -/
theorem holds_gateClauses (a : ℕ → Bool) (i : ℕ) (g : GateD) : Holds a (gateClauses i g) ↔ a i = gval a g := (stForces a i g).1

/-! ### All gates -/

/-- The clauses of the gates of K, numbered from j on, hold under a exactly if a obeys K with the
wires n + j, n + j + 1, …. -/
private theorem holds_zipIdx (a : ℕ → Bool) (n : ℕ) : ∀ (K : List GateD) (j : ℕ),
    Holds a ((K.zipIdx j).flatMap fun gt => gateClauses (n + gt.2) gt.1) ↔ Obeys a (n + j) K
  | [], j => by
    simp only [List.zipIdx_nil, List.flatMap_nil, Obeys, iff_true]
    exact holds_nil a
  | g :: K, j => by
    have h1 : Holds a (((g :: K).zipIdx j).flatMap fun gt => gateClauses (n + gt.2) gt.1) ↔
        (a (n + j) = gval a g ∧ Holds a ((K.zipIdx (j + 1)).flatMap fun gt => gateClauses (n + gt.2) gt.1)) := by
      rw [List.zipIdx_cons, List.flatMap_cons, holds_append]
      exact and_congr_left' (holds_gateClauses a (n + j) g)
    exact h1.trans (and_congr_right' (holds_zipIdx a n K (j + 1)))

/-- The clauses of all gates hold under a exactly if, under a, the variable of every gate has the
value of the gate. -/
theorem holds_wiresFormula (a : ℕ → Bool) (n : ℕ) (K : List GateD) : Holds a (wiresFormula n K) ↔ Obeys a n K :=
  holds_zipIdx a n K 0

/-- If every gate reads earlier wires only, counted by its place in the list (`WF`), then also
counted gate by gate (`WFa`). -/
theorem wfa_of_wf : ∀ {K : List GateD} {n : ℕ}, WF n K → WFa n K
  | [], _, _ => trivial
  | g :: K, n, h => by
    have h0 := h 0 (by simp)
    simp only [List.getElem_cons_zero, Nat.add_zero] at h0
    exact ⟨h0, wfa_of_wf (Form.wf_tail h)⟩

/-- Two assignments that obey a circuit whose gates read earlier wires only, and agree on the wires
below n, agree on the wires of all gates. -/
theorem obeys_unique {a a' : ℕ → Bool} : ∀ {K : List GateD} {n : ℕ}, WFa n K → Obeys a n K → Obeys a' n K → (∀ i < n, a i = a' i) →
    ∀ i < n + K.length, a i = a' i
  | [], n, _, _, _, h => by simpa using h
  | g :: K, n, hw, h1, h2, h => by
    have e : gval a g = gval a' g := by simp only [gval, h _ hw.1.1, h _ hw.1.2]
    have hn : a n = a' n := h1.1.trans (e.trans h2.1.symm)
    have h' : ∀ i < n + 1, a i = a' i := fun i hi => by
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h3 | rfl
      · exact h i h3
      · exact hn
    intro i hi
    exact obeys_unique hw.2 h1.2 h2.2 h' i (by simp only [List.length_cons] at hi; omega)

/-! ### The values of the wires on an input -/

/-- The value of the wire i of the circuit K on the input x (0 if there is no such wire). -/
@[expose] def wireVal (x : List Bool) (K : List GateD) (i : ℕ) : Bool := (wires x (toC K)).getD i false

/-- The values of the wires obey the circuit. -/
theorem obeys_wireVal (x : List Bool) (K : List GateD) (h : WFa x.length K) : Obeys (wireVal x K) x.length K := obeys_wires x K h

/-- The input wires carry the input. -/
theorem wireVal_input (x : List Bool) (K : List GateD) {i : ℕ} (hi : i < x.length) : wireVal x K i = x.getD i false := wires_input x (toC K) hi

/-- The output of a circuit is the value of its last wire. -/
theorem eval_eq_wireVal (x : List Bool) (K : List GateD) : eval (toC K) x = wireVal x K (x.length + K.length - 1) := by
  rw [Form.eval_eq, toC, List.length_map]
  rfl

/-- Beyond the last wire the value is 0. -/
theorem wireVal_of_le (x : List Bool) (K : List GateD) {i : ℕ} (hi : x.length + K.length ≤ i) : wireVal x K i = false := by
  refine List.getD_eq_default _ _ ?_
  rw [Form.length_wires, toC, List.length_map]
  exact hi

/-! ### Assignments on finitely many variables -/

/-- Below N, the assignment b on N variables, read on all numbers, has the value of b. -/
theorem ext_of_lt {N : ℕ} (b : Fin N → Bool) {i : ℕ} (h : i < N) : ext b i = b ⟨i, h⟩ := dif_pos h

/-- From N on, the assignment b on N variables, read on all numbers, is 0. -/
theorem ext_of_le {N : ℕ} (b : Fin N → Bool) {i : ℕ} (h : N ≤ i) : ext b i = false := dif_neg (Nat.not_lt.2 h)

/-- **`StUniqueExtension`.** For every non-empty circuit K on n inputs whose gates read earlier
wires only, every assignment of x₀ … xₙ₋₁ extends in exactly one way to the variables of the gates
so that the clauses of all gates hold, and then the variable of the last wire has the value of the
circuit. -/
theorem stUniqueExtension : StUniqueExtension := by
  intro n K hK hne x
  have hW : WFa n K := wfa_of_wf hK
  have hXl : (List.ofFn x).length = n := List.length_ofFn
  have hOb : Obeys (wireVal (List.ofFn x) K) n K := by
    have h := obeys_wireVal (List.ofFn x) K (by rw [hXl]; exact hW)
    rwa [hXl] at h
  have hin : ∀ i : Fin n, wireVal (List.ofFn x) K i.1 = x i := by
    intro i
    rw [wireVal_input _ _ (by rw [hXl]; exact i.2), List.getD_eq_getElem _ _ (by rw [hXl]; exact i.2), List.getElem_ofFn]
  have key : ∀ b : Fin (n + K.length) → Bool, (∀ i : Fin n, b (Fin.castAdd K.length i) = x i) → Holds (ext b) (wiresFormula n K) →
      ∀ i < n + K.length, ext b i = wireVal (List.ofFn x) K i := by
    intro b hb hH
    refine obeys_unique hW ((holds_wiresFormula _ n K).1 hH) hOb fun i hi => ?_
    rw [ext_of_lt b (by omega : i < n + K.length)]
    exact (hb ⟨i, hi⟩).trans (hin ⟨i, hi⟩).symm
  have hext : ext (fun i : Fin (n + K.length) => wireVal (List.ofFn x) K i.1) = wireVal (List.ofFn x) K := by
    funext i
    rcases Nat.lt_or_ge i (n + K.length) with h | h
    · rw [ext_of_lt _ h]
    · rw [ext_of_le _ h, wireVal_of_le _ _ (by rw [hXl]; exact h)]
  refine ⟨⟨fun i => wireVal (List.ofFn x) K i.1, ⟨fun i => hin i, ?_⟩, ?_⟩, ?_⟩
  · rw [hext]
    exact (holds_wiresFormula _ n K).2 hOb
  · rintro b ⟨hb, hH⟩
    funext i
    have h := key b hb hH i.1 i.2
    rwa [ext_of_lt b i.2] at h
  · intro b hb hH
    have hp : 0 < K.length := List.length_pos_iff.2 hne
    rw [key b hb hH _ (by omega), eval_eq_wireVal, hXl]

end SizeCircuit
