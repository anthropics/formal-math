/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import CircuitLowerBound.InterfacesPolyT
public import PaddedDescent.F.FuelCert
public import ToTuring.Poly.Words
import Mathlib.Tactic

/-! # The circuit lower bound for E^NP (Section 7): circuits as words

The guess of the nondeterministic algorithm is a circuit, written as a word: the number W of bits of
a wire in unary (1^W 0), then for each gate its four values and the numbers of its two wires with W
bits each, lowest bit
first. The decoder `decC` reads every word as a list of gates (what is left over at the end is not
read); `wfB` tests whether every gate reads inputs and earlier gates only. Every list of gates whose
wires have numbers
below 2^W is read back from its code (`decC_encC`). Both functions are polynomial-time. -/

@[expose] public section

namespace CircuitLowerBound

open ENP Groundwork

namespace Parse

/-- A gate as a word: its four values, then the numbers of its two wires with W bits each. -/
def gateW (W : ℕ) (g : GateD) : List Bool := [g.1.1, g.1.2.1, g.1.2.2.1, g.1.2.2.2] ++ (toWord W g.2.1 ++ toWord W g.2.2)

/-- A list of gates as a word. -/
def encC (W : ℕ) (C : List GateD) : List Bool := unary W ++ (C.map (gateW W)).flatten

/-- The gate written by a word of 4 + 2W bits. -/
def gateOfW (W : ℕ) (b : List Bool) : GateD :=
  ((b.getD 0 false, b.getD 1 false, b.getD 2 false, b.getD 3 false), ofWord ((b.drop 4).take W), ofWord (b.drop (4 + W)))

/-- The list of gates written by a word. -/
def decC (y : List Bool) : List GateD :=
  (List.range ((rest y).length / (4 + 2 * ones y))).map fun t => gateOfW (ones y) (block (4 + 2 * ones y) t (rest y))

/-- Does every gate read inputs and earlier gates only? -/
def wfB (n : ℕ) (C : List GateD) : Bool :=
  (List.range C.length).all fun t =>
    decide ((C.getD t ((false, false, false, false), 0, 0)).2.1 < n + t) && decide ((C.getD t ((false, false, false, false), 0, 0)).2.2 < n + t)

/-- The number of ones at the start of 1^P 0 y. -/
theorem ones_unary_append (P : ℕ) (y : List Bool) : ones (unary P ++ y) = P := by
  unfold ones unary
  induction P with
  | zero => simp
  | succ P _ => simp [List.replicate_succ]

/-- What follows 1^P 0 in 1^P 0 y. -/
theorem rest_unary_append (P : ℕ) (y : List Bool) : rest (unary P ++ y) = y := by
  unfold rest unary
  induction P with
  | zero => simp
  | succ P _ => simp [List.replicate_succ]

/-- The word of a gate has 4 + 2W bits. -/
theorem length_gateW (W : ℕ) (g : GateD) : (gateW W g).length = 4 + 2 * W := by
  simp [gateW]; ring

/-- A gate is read back from its word. -/
theorem gateOfW_gateW {W : ℕ} {g : GateD} (h1 : g.2.1 < 2 ^ W) (h2 : g.2.2 < 2 ^ W) : gateOfW W (gateW W g) = g := by
  obtain ⟨⟨b0, b1, b2, b3⟩, i, j⟩ := g
  have e1 : ((gateW W ((b0, b1, b2, b3), i, j)).drop 4).take W = toWord W i := by
    simp [gateW]
  have e2 : (gateW W ((b0, b1, b2, b3), i, j)).drop (4 + W) = toWord W j := by
    rw [← List.drop_drop]
    simp [gateW]
  unfold gateOfW
  rw [e1, e2, ofWord_toWord h1, ofWord_toWord h2]
  simp [gateW]

/-- The j-th block of a concatenation of words of length ℓ. -/
theorem block_flatten {ℓ : ℕ} : ∀ (L : List (List Bool)) (j : ℕ) (hj : j < L.length), (∀ w ∈ L, w.length = ℓ) → block ℓ j L.flatten = L[j]
  | [], j, hj, _ => by simp at hj
  | a :: L, 0, _, h => by
    have ha : a.length = ℓ := h a List.mem_cons_self
    simp [block, ha]
  | a :: L, j + 1, hj, h => by
    have ha : a.length = ℓ := h a List.mem_cons_self
    have ih := block_flatten L j (by simpa using hj) fun w hw => h w (List.mem_cons_of_mem _ hw)
    have e : (j + 1) * ℓ = a.length + j * ℓ := by rw [ha]; ring
    unfold block at ih ⊢
    rw [List.flatten_cons, e, ← List.drop_drop, List.drop_left, ih]
    simp

/-- The words of the gates have |C|·(4 + 2W) bits together. -/
theorem length_flatten_gateW (W : ℕ) (C : List GateD) : ((C.map (gateW W)).flatten).length = C.length * (4 + 2 * W) := by
  induction C with
  | nil => simp
  | cons g C ih => rw [List.map_cons, List.flatten_cons, List.length_append, ih, length_gateW, List.length_cons]; ring

/-- The length of the code. -/
theorem length_encC (W : ℕ) (C : List GateD) : (encC W C).length = W + 1 + C.length * (4 + 2 * W) := by
  rw [encC, List.length_append, Parse.length_flatten_gateW]
  simp [unary]

/-- A list of gates whose wires have numbers below 2^W is read back from its code. -/
theorem decC_encC {W : ℕ} {C : List GateD} (h : ∀ g ∈ C, g.2.1 < 2 ^ W ∧ g.2.2 < 2 ^ W) : decC (encC W C) = C := by
  unfold decC encC
  rw [Parse.ones_unary_append, Parse.rest_unary_append, Parse.length_flatten_gateW, Nat.mul_div_cancel _ (by omega)]
  refine List.ext_getElem (by simp) fun t h1 h2 => ?_
  rw [List.getElem_map, List.getElem_range, Parse.block_flatten _ t (by simpa using h2) (by
    intro w hw
    obtain ⟨g, _, rfl⟩ := List.mem_map.1 hw
    exact Parse.length_gateW W g), List.getElem_map]
  exact Parse.gateOfW_gateW (h _ (List.getElem_mem _)).1 (h _ (List.getElem_mem _)).2

/-- The test is right. -/
theorem wfB_iff (n : ℕ) (C : List GateD) : wfB n C = true ↔ WF n C := by
  unfold wfB WF
  rw [List.all_eq_true]
  constructor
  · intro h t ht
    have := h t (List.mem_range.2 ht)
    rw [List.getD_eq_getElem _ _ ht] at this
    simpa using this
  · intro h t ht
    have ht' := List.mem_range.1 ht
    rw [List.getD_eq_getElem _ _ ht']
    simpa using h t ht'

/-! ### Polynomial time -/

section cert

variable {α : Type} [Enc α]

/-- The number of ones at the start of a word, in unary. -/
@[fun_prop] theorem ones_unary {x : α → List Bool} (hx : PolyT x) : Unary fun a => ones (x a) := by
  unfold ones; fun_prop

/-- The number of ones at the start of a word. -/
@[fun_prop] theorem ones_polyT {x : α → List Bool} (hx : PolyT x) : PolyT fun a => ones (x a) := (ones_unary hx).poly

/-- The word after its first ones and the zero that ends them. -/
@[fun_prop] theorem rest_polyT {x : α → List Bool} (hx : PolyT x) : PolyT fun a => rest (x a) := by
  unfold rest; fun_prop

/-- The gate written by a word. -/
@[fun_prop] theorem gateOfW_polyT {W : α → ℕ} {b : α → List Bool} (hW : PolyT W) (hb : PolyT b) : PolyT fun a => gateOfW (W a) (b a) := by
  unfold gateOfW; fun_prop

/-- The decoder. -/
@[fun_prop] theorem decC_polyT {y : α → List Bool} (hy : PolyT y) : PolyT fun a => decC (y a) := by
  unfold decC; fun_prop

/-- The test. -/
@[fun_prop] theorem wfB_polyT {n : α → ℕ} {C : α → List GateD} (hn : PolyT n) (hC : PolyT C) : PolyT fun a => wfB (n a) (C a) := by
  unfold wfB; fun_prop

end cert

end Parse

end CircuitLowerBound
