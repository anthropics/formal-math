/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Wrap.Defs
public import StepMachines.Prog.Decode
import StepMachines.Math.Formula
import ToTuring.Poly.Decode
import Mathlib.Tactic.Linarith

/-! # The front end for 3-SAT

Three results.
* `pad4KeepsSatAndMeetsSideConditions`: the formula `pad4 φ` (φ with four more variables, each
  forced to be true by a unit clause) is a 3-CNF without repeated clauses, has four clauses more
  than φ, between 4 and n + 4 variables occur in it, and it is satisfiable if and only if φ is.
* `frontEndExists`: the function `frontEnd` on bit strings is polynomial-time and maps the plain
  code `Sat3.enc φ` to the compact code `MainTheoremForms.encC 3 (pad4 φ)`. It decodes the plain
  code to the number n and the list of clauses, with natural numbers as
  variables; puts the four unit clauses behind them; and writes the compact code by its formula,
  with the number of bits of a slot computed from n + 4.
* `length_encC_pad4_le`: both codes have at most a·(n + 2)^d bits, for some a and d; the proof takes
  a = 100 and d = 4. -/

@[expose] public section

namespace Wrap

open Groundwork Groundwork.Decode

/-! ### The padded formula -/

/-- The map on literals inside `pad4`, which keeps the number of the variable and the sign, is
injective. -/
theorem castLit_injective (n : ℕ) : Function.Injective fun l : Sat3.Lit n => ((Fin.castAdd 4 l.1, l.2) : Sat3.Lit (n + 4)) := by
  rintro ⟨i, b⟩ ⟨j, c⟩ h
  simp only [Prod.mk.injEq] at h
  exact Prod.ext (Fin.castAdd_injective n 4 h.1) h.2

/-- A clause is in `pad4 φ` if and only if it is a clause of φ with its variables carried over, or
one of the four unit clauses. -/
theorem mem_pad4 {n : ℕ} {φ : Sat3.CNF n} {D : List (Sat3.Lit (n + 4))} :
    D ∈ pad4 φ ↔ (∃ C ∈ φ, (C.map fun l => (Fin.castAdd 4 l.1, l.2)) = D) ∨ ∃ j : Fin 4, [(Fin.natAdd n j, true)] = D := by
  simp [pad4]

/-- At most N variables occur in a formula over N names. -/
theorem numOcc_le {N : ℕ} (ψ : Sat3.CNF N) : MainTheoremForms.numOcc ψ ≤ N := by
  have h := Nat.card_le_card_of_injective (Subtype.val : {i : Fin N // MainTheoremForms.Occurs ψ i} → Fin N) Subtype.val_injective
  simpa [MainTheoremForms.numOcc] using h

/-- Each of the four new variables occurs in `pad4 φ`. -/
theorem occurs_pad4 {n : ℕ} (φ : Sat3.CNF n) (j : Fin 4) : MainTheoremForms.Occurs (pad4 φ) (Fin.natAdd n j) :=
  ⟨[(Fin.natAdd n j, true)], mem_pad4.2 (Or.inr ⟨j, rfl⟩), (Fin.natAdd n j, true), by simp, rfl⟩

/-- The facts on the padded formula: it is a 3-CNF without repeated clauses, has four clauses more,
between 4 and n + 4 variables occur in it, and it is satisfiable if and only if φ is. -/
theorem pad4KeepsSatAndMeetsSideConditions : Pad4KeepsSatAndMeetsSideConditions := by
  intro n φ hφ
  obtain ⟨h3, hnd⟩ := hφ
  refine ⟨⟨?_, ?_⟩, ?_, ?_, numOcc_le _, ?_, ?_⟩
  · intro D hD
    rcases mem_pad4.1 hD with ⟨C, hC, rfl⟩ | ⟨j, rfl⟩
    · simpa using h3 C hC
    · simp
  · unfold pad4
    refine List.Nodup.append (hnd.map (List.map_injective_iff.2 (castLit_injective n))) ((List.nodup_finRange 4).map ?_) ?_
    · intro a b h
      simpa using h
    · intro D h1 h2
      obtain ⟨C, -, rfl⟩ := List.mem_map.1 h1
      obtain ⟨j, -, h⟩ := List.mem_map.1 h2
      match C, h with
      | [], h => simp at h
      | [l], h =>
        simp only [List.map_cons, List.map_nil, List.cons.injEq, Prod.mk.injEq, and_true] at h
        have := congrArg Fin.val h.1
        simp only [Fin.val_natAdd, Fin.val_castAdd] at this
        have := l.1.2
        omega
      | _ :: _ :: _, h => simp at h
  · simp [pad4]
  · have h := Nat.card_le_card_of_injective (fun j : Fin 4 => (⟨Fin.natAdd n j, occurs_pad4 φ j⟩ : {i : Fin (n + 4) // MainTheoremForms.Occurs (pad4 φ) i})) (by
      intro a b h
      simpa using h)
    simpa [MainTheoremForms.numOcc] using h
  · rintro ⟨a, ha⟩
    refine ⟨fun i => a (Fin.castAdd 4 i), fun C hC => ?_⟩
    obtain ⟨l, hl, h⟩ := ha _ (mem_pad4.2 (Or.inl ⟨C, hC, rfl⟩))
    obtain ⟨l', hl', rfl⟩ := List.mem_map.1 hl
    exact ⟨l', hl', h⟩
  · rintro ⟨a, ha⟩
    refine ⟨Fin.addCases a fun _ => true, fun D hD => ?_⟩
    rcases mem_pad4.1 hD with ⟨C, hC, rfl⟩ | ⟨j, rfl⟩
    · obtain ⟨l, hl, h⟩ := ha C hC
      exact ⟨_, List.mem_map.2 ⟨l, hl, rfl⟩, by simpa using h⟩
    · exact ⟨_, List.mem_singleton.2 rfl, by simp⟩

/-! ### The front end as a function on bit strings -/

/-- A slot of a clause as a number, as `Sat3.slot`, with natural numbers as variables: 0 = no
literal, 2i+1 = ¬xᵢ, 2i+2 = xᵢ. -/
def slotNat (o : Option (ℕ × Bool)) : ℕ := o.elim 0 fun l => 2 * l.1 + 1 + l.2.toNat

/-- The clauses of the padded formula, from the number n of variables and the clauses of φ, with
natural numbers as variables. -/
def addFour (d : ℕ × NCNF) : NCNF := d.2 ++ [[(d.1, true)], [(d.1 + 1, true)], [(d.1 + 2, true)], [(d.1 + 3, true)]]

/-- The compact code at width 3, from the number w of bits of a slot, in unary, and the clauses: 1³
0, then 1ʷ 0, then 3 slots per clause, w bits per slot, low bit first. -/
def encUnary (w : List Unit) (F : NCNF) : List Bool :=
  List.replicate 3 true ++ false :: (w.map (fun _ => true) ++ false :: F.flatMap fun C => (List.range 3).flatMap fun j =>
    (List.range w.length).map (slotNat C[j]?).testBit)

/-- The number of bits of a slot of the padded formula, from the plain code: ⌊log₂(2(n + 4))⌋ + 1,
where n is the number of ones at the beginning. -/
def slotBits (x : List Bool) : ℕ := Nat.log2 (2 * ((x.takeWhile id).length + 4)) + 1

/-- The front end: decode the plain code to n and the clauses, add the four unit clauses, write the
compact code for n + 4 names. -/
def frontEnd (x : List Bool) : List Bool := encUnary (List.replicate (slotBits x) ()) (addFour (dec x))

/-- The number of a slot, with natural numbers as variables, is that of `Sat3.slot`. -/
theorem slotNat_map {n : ℕ} (o : Option (Sat3.Lit n)) : slotNat (o.map fun l => (l.1.val, l.2)) = Sat3.slot o := by
  cases o <;> rfl

/-- On w = ⌊log₂(2N)⌋ + 1 in unary and a formula over N names, with natural numbers as variables,
`encUnary` is the compact code at width 3. -/
theorem encUnary_toN {N : ℕ} (ψ : Sat3.CNF N) : encUnary (List.replicate (Nat.log2 (2 * N) + 1) ()) (toN ψ) = MainTheoremForms.encC 3 ψ := by
  simp only [encUnary, MainTheoremForms.encC, toN, List.map_replicate, List.length_replicate, List.flatMap_map, List.getElem?_map, slotNat_map]

/-- The padded formula, with natural numbers as variables, is φ with natural numbers as variables
and the four unit clauses on n, …, n + 3 behind it. -/
theorem toN_pad4 {n : ℕ} (φ : Sat3.CNF n) : toN (pad4 φ) = addFour (n, toN φ) := by
  have h4 : List.finRange 4 = [0, 1, 2, 3] := rfl
  simp [toN, pad4, addFour, h4, Function.comp_def]

/-- The front end maps the plain code of φ to the compact code of (3, `pad4 φ`), if every clause of
φ has at most 3 literals. -/
theorem frontEnd_enc {n : ℕ} {φ : Sat3.CNF n} (hφ : ∀ C ∈ φ, C.length ≤ 3) : frontEnd (Sat3.enc φ) = MainTheoremForms.encC 3 (pad4 φ) := by
  have h1 : ((Sat3.enc φ).takeWhile id).length = n := congrArg Prod.fst (dec_enc hφ)
  rw [frontEnd, slotBits, h1, dec_enc hφ, ← toN_pad4, encUnary_toN]

/-- The number of bits of a slot is polynomial-time in unary: it is at most 2·(|x| + 4) + 1. -/
theorem slotBits_unary : Unary slotBits := by
  have hl : PolyT fun x : List Bool => x.takeWhile id := by fun_prop
  refine Unary.of_le (g := fun x => 2 * ((x.takeWhile id).length + 4) + 1) (((Unary.const 2).mul ((Unary.of_length hl).add (Unary.const 4))).add (Unary.const 1)) (by unfold slotBits; fun_prop) fun x => ?_
  have := Nat.log2_le_self (2 * ((x.takeWhile id).length + 4))
  unfold slotBits
  omega

/-- The number of a slot is polynomial-time. -/
theorem slotNat_polyT {α : Type} [Enc α] {o : α → Option (ℕ × Bool)} (ho : PolyT o) : PolyT fun x => slotNat (o x) := by
  unfold slotNat
  fun_prop

/-- Adding the four unit clauses is polynomial-time. -/
theorem addFour_polyT {α : Type} [Enc α] {d : α → ℕ × NCNF} (hd : PolyT d) : PolyT fun x => addFour (d x) := by
  unfold addFour
  fun_prop

/-- Writing the compact code at width 3 is polynomial-time, with the number of bits of a slot in
unary. -/
theorem encUnary_polyT {α : Type} [Enc α] {w : α → List Unit} {F : α → NCNF} (hw : PolyT w) (hF : PolyT F) : PolyT fun x => encUnary (w x) (F x) := by
  have hr : PolyT fun p : ((α × List (ℕ × Bool)) × ℕ) => List.range (w p.1.1).length := PolyT.range ((Unary.of_length hw).comp PolyT.id'.fst.fst)
  have hs : PolyT fun p : (((α × List (ℕ × Bool)) × ℕ) × ℕ) => (slotNat p.1.1.2[p.1.2]?).testBit p.2 :=
    PolyT.testBit (slotNat_polyT (by fun_prop)) (by fun_prop)
  unfold encUnary
  fun_prop

/-- The front end is polynomial-time. -/
theorem frontEnd_polyT : PolyT frontEnd :=
  encUnary_polyT slotBits_unary (addFour_polyT dec_polyT)

/-- There is a front end: `frontEnd`. -/
theorem frontEndExists : FrontEndExists :=
  ⟨frontEnd, frontEnd_polyT, fun _ _ hφ => frontEnd_enc hφ.1⟩

/-! ### The lengths of the two codes -/

/-- The length of the compact code: k + w + 2 + m·k·w with w = ⌊log₂(2N)⌋ + 1. -/
theorem length_encC (k : ℕ) {N : ℕ} (ψ : Sat3.CNF N) :
    (MainTheoremForms.encC k ψ).length = k + (Nat.log2 (2 * N) + 1) + 2 + ψ.length * (k * (Nat.log2 (2 * N) + 1)) := by
  have h : ∀ ψ : Sat3.CNF N, (ψ.flatMap fun C => (List.range k).flatMap fun j =>
      (List.range (Nat.log2 (2 * N) + 1)).map (Sat3.slot C[j]?).testBit).length = ψ.length * (k * (Nat.log2 (2 * N) + 1)) := by
    intro ψ
    simp [List.length_flatMap]
  simp only [MainTheoremForms.encC, List.length_append, List.length_cons, List.length_replicate, h]
  omega

/-- Both codes are polynomially long in n: the compact code of the padded formula and the plain code
of φ have at most a·(n + 2)^d bits, for every 3-CNF φ on n variables without repeated clauses. The
proof takes a = 100 and d = 4. -/
theorem length_encC_pad4_le : ∃ a d : ℕ, ∀ (n : ℕ) (φ : Sat3.CNF n), Sat3.Is3CNF φ →
    (MainTheoremForms.encC 3 (pad4 φ)).length ≤ a * (n + 2) ^ d ∧ (Sat3.enc φ).length ≤ a * (n + 2) ^ d := by
  refine ⟨100, 4, fun n φ hφ => ⟨?_, ?_⟩⟩
  · have hm : (pad4 φ).length = φ.length + 4 := (pad4KeepsSatAndMeetsSideConditions n φ hφ).2.1
    have h1 : φ.length ≤ (2 * n + 1) ^ 3 := hφ.length_le
    have h2 : Nat.log2 (2 * (n + 4)) + 1 ≤ n + 4 + 1 := bitLen_le (n + 4)
    rw [length_encC, hm]
    generalize Nat.log2 (2 * (n + 4)) + 1 = w at h2 ⊢
    have h3 : (φ.length + 4) * (3 * w) ≤ ((2 * n + 1) ^ 3 + 4) * (3 * (n + 5)) :=
      Nat.mul_le_mul (by omega) (by omega)
    have h4 : 3 + (n + 5) + 2 + ((2 * n + 1) ^ 3 + 4) * (3 * (n + 5)) ≤ 100 * (n + 2) ^ 4 := by nlinarith [sq_nonneg n]
    omega
  · have := length_enc_succ_le hφ
    have : 0 ≤ (n + 2) ^ 4 := Nat.zero_le _
    omega

end Wrap
