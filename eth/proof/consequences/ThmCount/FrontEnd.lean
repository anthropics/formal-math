/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThmCount.Defs
public import Wrap.FrontEnd
import WidthK.Decode
import ToTuring.Poly.Decode
import Mathlib.Tactic

/-! # Theorem C from Theorem D(b): the front end and the last step

No sentence of the paper stands behind this file: the paper derives Theorem C otherwise (see the
head of proof/consequences/ThmCount/Defs.lean).
* `stFrontEnd`: the function `frontEnd` is polynomial time and maps the plain code of a 3-CNF φ to
  1³0 followed by the plain code of `Wrap.pad4 φ`. It is built like `Wrap.frontEnd`
  (proof/machines/Wrap/FrontEnd.lean), which writes the compact code, and uses its pieces
  `Wrap.addFour`, `Wrap.slotNat`, `Wrap.slotBits` with their certificates.
* `stPadKeepsCount`: the four forced variables keep the number of satisfying assignments: a
  satisfying assignment of `pad4 φ` is a satisfying assignment of φ with the value 1 on the four new
  variables.
* `stInputLength`, `stLastStep`. -/

@[expose] public section

namespace ThmCount

open Groundwork Groundwork.Decode

/-- 1³0, then the plain code at width 3, from the number of variables in unary, the number w of bits
of a slot in unary, and the clauses with numbers as variables. -/
def encPlain (u w : List Unit) (F : NCNF) : List Bool :=
  List.replicate 3 true ++ false :: (u.map (fun _ => true) ++ false :: F.flatMap fun C => (List.range 3).flatMap fun j =>
    (List.range w.length).map (Wrap.slotNat C[j]?).testBit)

/-- The front end: read the plain code as n and the clauses, add the four clauses of one literal,
write 1³0 and the plain code for n + 4 variables. -/
def frontEnd (x : List Bool) : List Bool :=
  encPlain (List.replicate ((x.takeWhile id).length + 4) ()) (List.replicate (Wrap.slotBits x) ()) (Wrap.addFour (dec x))

end ThmCount

public section

namespace ThmCount

open Groundwork Groundwork.Decode

/-- On N in unary, w = ⌊log₂(2N)⌋ + 1 in unary and a formula on N variables with numbers as
variables, `encPlain` is the code of (3, formula). -/
theorem encPlain_toN {N : ℕ} (ψ : Sat3.CNF N) : encPlain (List.replicate N ()) (List.replicate (Nat.log2 (2 * N) + 1) ()) (toN ψ) = SatM.enc 3 ψ := by
  simp only [encPlain, SatM.enc, SatK.enc, toN, List.map_replicate, List.length_replicate, List.flatMap_map, List.getElem?_map, Wrap.slotNat_map]

/-- The front end maps the plain code of φ to the code of (3, `pad4 φ`), if every clause of φ has at
most 3 literals. -/
theorem frontEnd_enc {n : ℕ} {φ : Sat3.CNF n} (hφ : ∀ C ∈ φ, C.length ≤ 3) : frontEnd (Sat3.enc φ) = SatM.enc 3 (Wrap.pad4 φ) := by
  have h1 : ((Sat3.enc φ).takeWhile id).length = n := congrArg Prod.fst (dec_enc hφ)
  rw [frontEnd, Wrap.slotBits, h1, dec_enc hφ, ← Wrap.toN_pad4, encPlain_toN]

/-- Writing the code is polynomial time, with the number of variables and the number of bits of a
slot in unary. -/
theorem encPlain_polyT {α : Type} [Enc α] {u w : α → List Unit} {F : α → NCNF} (hu : PolyT u) (hw : PolyT w) (hF : PolyT F) :
    PolyT fun x => encPlain (u x) (w x) (F x) := by
  have hr : PolyT fun p : ((α × List (ℕ × Bool)) × ℕ) => List.range (w p.1.1).length := PolyT.range ((Unary.of_length hw).comp PolyT.id'.fst.fst)
  have hs : PolyT fun p : (((α × List (ℕ × Bool)) × ℕ) × ℕ) => (Wrap.slotNat p.1.1.2[p.1.2]?).testBit p.2 :=
    PolyT.testBit (Wrap.slotNat_polyT (by fun_prop)) (by fun_prop)
  unfold encPlain
  fun_prop

/-- The front end is polynomial time. -/
theorem frontEnd_polyT : PolyT frontEnd := by
  have hl : PolyT fun x : List Bool => x.takeWhile id := by fun_prop
  have hu : Unary fun x : List Bool => (x.takeWhile id).length + 4 := (Unary.of_length hl).add (Unary.const 4)
  exact encPlain_polyT hu Wrap.slotBits_unary (Wrap.addFour_polyT dec_polyT)

/-- There is a polynomial-time front end: the statement `ThmCount.StFrontEnd`. The front end is
`frontEnd`. -/
theorem stFrontEnd : StFrontEnd := ⟨frontEnd, frontEnd_polyT, fun _ _ hφ => frontEnd_enc hφ.1⟩

/-- An assignment satisfies `pad4 φ` exactly if, read on the old variables, it satisfies φ, and it
gives the four new variables the value 1. -/
theorem holds_pad4 {n : ℕ} (φ : Sat3.CNF n) (b : Fin (n + 4) → Bool) :
    (∀ D ∈ Wrap.pad4 φ, ∃ l ∈ D, b l.1 = l.2) ↔ (∀ C ∈ φ, ∃ l ∈ C, b (Fin.castAdd 4 l.1) = l.2) ∧ ∀ j : Fin 4, b (Fin.natAdd n j) = true := by
  constructor
  · intro h
    refine ⟨fun C hC => ?_, fun j => ?_⟩
    · obtain ⟨l, hl, e⟩ := h _ (Wrap.mem_pad4.2 (Or.inl ⟨C, hC, rfl⟩))
      obtain ⟨l', hl', rfl⟩ := List.mem_map.1 hl
      exact ⟨l', hl', e⟩
    · obtain ⟨l, hl, e⟩ := h _ (Wrap.mem_pad4.2 (Or.inr ⟨j, rfl⟩))
      rw [List.mem_singleton] at hl
      subst hl
      exact e
  · rintro ⟨h1, h2⟩ D hD
    rcases Wrap.mem_pad4.1 hD with ⟨C, hC, rfl⟩ | ⟨j, rfl⟩
    · obtain ⟨l, hl, e⟩ := h1 C hC
      exact ⟨_, List.mem_map_of_mem hl, e⟩
    · exact ⟨_, List.mem_singleton.2 rfl, h2 j⟩

/-- The four forced variables keep the number of satisfying assignments. -/
theorem numSat_pad4 {n : ℕ} (φ : Sat3.CNF n) : SatK.numSat (Wrap.pad4 φ) = SatK.numSat φ := by
  unfold SatK.numSat
  symm
  refine Finset.card_bij (fun a _ => Fin.append a fun _ : Fin 4 => true) ?_ ?_ ?_
  · intro a ha
    rw [Finset.mem_filter] at ha ⊢
    refine ⟨Finset.mem_univ _, (holds_pad4 φ _).2 ⟨fun C hC => ?_, fun j => by rw [Fin.append_right]⟩⟩
    obtain ⟨l, hl, e⟩ := ha.2 C hC
    exact ⟨l, hl, by rw [Fin.append_left]; exact e⟩
  · intro a _ a' _ h
    funext i
    have := congrFun h (Fin.castAdd 4 i)
    rwa [Fin.append_left, Fin.append_left] at this
  · intro b hb
    rw [Finset.mem_filter] at hb
    obtain ⟨h1, h2⟩ := (holds_pad4 φ b).1 hb.2
    refine ⟨fun i => b (Fin.castAdd 4 i), Finset.mem_filter.2 ⟨Finset.mem_univ _, h1⟩, ?_⟩
    funext x
    refine Fin.addCases (fun i => ?_) (fun j => ?_) x
    · rw [Fin.append_left]
    · rw [Fin.append_right, h2 j]

/-- A number in n + 5 bits without its four highest bits is the number in n + 1 bits. -/
theorem dropFour_binary (n N : ℕ) : dropFour (SatK.binary (n + 4) N) = SatK.binary n N := by
  have h : (SatK.binary (n + 4) N).length - 4 = n + 1 := by simp [SatK.binary]
  rw [dropFour, h, SatK.binary, SatK.binary, ← List.map_take, List.take_range]
  congr 2
  omega

/-- The four forced variables keep the number of satisfying assignments, and the number in n + 5
bits without its four highest bits is the number in n + 1 bits: the statement
`ThmCount.StPadKeepsCount`. -/
theorem stPadKeepsCount : StPadKeepsCount := fun n φ h =>
  ⟨(Wrap.pad4KeepsSatAndMeetsSideConditions n φ h).1, numSat_pad4 φ, by rw [dropFour_binary, numSat_pad4]⟩

/-- The plain code of a 3-CNF on n variables has length at most 25·(n+2)^4: the statement
`ThmCount.StInputLength`. -/
theorem stInputLength : StInputLength := ⟨3 * 2 ^ 3 + 1, 3 + 1, fun _ _ h => (Nat.le_succ _).trans (DecodeK.length_enc_succ_le h)⟩

/-- The last step is polynomial time: the statement `ThmCount.StLastStep`. -/
theorem stLastStep : StLastStep := by
  unfold StLastStep dropFour
  fun_prop

end ThmCount
