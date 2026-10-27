/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import PaddedDescent.Pad
public import StepMachines.Prog.Decode
import ToTuring.Poly.Decode
import Batteries.Data.Nat.Lemmas

/-! Plain exhaustive search for 3-SAT as a polynomial-time function of the padded input:
`bruteA (x, pad)` decodes the formula written
in x and tries the assignments number 0, 1, …, (length of the pad) − 1, where assignment number y
gives the variable i the i-th binary
digit of y. With a pad of length 2^n that is every assignment. It is polynomial-time in the sense of
`PolyT` (`bruteA_polyT`), and with a pad of length
at least 2^n it finds a satisfying assignment exactly if there is one (`bruteA_enc_of_le`).
`withBrute` in proof/rates/PaddedDescent/Reduce.lean uses it for those n
where `sOf n` is small. -/

namespace PaddedDescent

open Groundwork Groundwork.Decode Sat3 Turing

/-- The number of variables written in the bit string x. -/
@[expose] public def nOf (x : List Bool) : ℕ := (dec x).1

/-- Does assignment number y (variable i gets the i-th binary digit of y) make a literal of every
clause of ψ true? -/
@[expose] public def satAt (ψ : NCNF) (y : ℕ) : Bool := ψ.all fun C => C.any fun l => y.testBit l.1 == l.2

/-- Exhaustive search with fuel: try the assignments number 0, …, (length of the pad) − 1 on the
formula written in the bit string. -/
@[expose] public def bruteA (p : List Bool × List Unit) : Bool := (List.range p.2.length).any fun y => satAt (dec p.1).2 y

public theorem nOf_polyT : PolyT nOf := by
  have := dec_polyT
  unfold nOf; fun_prop

public theorem satAt_polyT {α : Type} [Enc α] {ψ : α → NCNF} {y : α → ℕ} (hψ : PolyT ψ) (hy : PolyT y) :
    PolyT fun x => satAt (ψ x) (y x) := by
  unfold satAt; fun_prop

public theorem bruteA_polyT : PolyT bruteA := by
  have hd := dec_polyT
  have hr : PolyT fun p : List Bool × List Unit => List.range p.2.length := PolyT.range (Unary.of_length (by fun_prop))
  have hψ : PolyT fun q : (List Bool × List Unit) × ℕ => (dec q.1.1).2 := by fun_prop
  have hf : PolyT fun q : (List Bool × List Unit) × ℕ => satAt (dec q.1.1).2 q.2 := satAt_polyT hψ (by fun_prop)
  unfold bruteA
  refine PolyT.any ?_ ?_
  · exact hf
  · exact hr

public theorem nOf_enc {n : ℕ} {φ : CNF n} (h : Is3CNF φ) : nOf (enc φ) = n := by
  rw [nOf, dec_enc h.1]

/-- With a pad of length at least 2^n, exhaustive search finds a satisfying assignment exactly if
there is one. -/
public theorem bruteA_enc_of_le {n : ℕ} {φ : CNF n} (h : Is3CNF φ) {w : List Unit} (hw : 2 ^ n ≤ w.length) :
    bruteA (enc φ, w) = true ↔ Satisfiable φ := by
  have e1 : bruteA (enc φ, w) = true ↔ ∃ y < w.length, ∀ D ∈ toN φ, ∃ l ∈ D, y.testBit l.1 = l.2 := by
    simp [bruteA, satAt, dec_enc h.1]
  rw [e1]
  constructor
  · rintro ⟨y, -, hy⟩
    exact (satN_toN φ).1 ⟨fun i => y.testBit i, hy⟩
  · rintro ⟨a, ha⟩
    refine ⟨Nat.ofBits a, (Nat.ofBits_lt_two_pow a).trans_le hw, fun D hD => ?_⟩
    obtain ⟨C, hC, rfl⟩ := List.mem_map.1 hD
    obtain ⟨l, hl, hal⟩ := ha C hC
    exact ⟨_, List.mem_map.2 ⟨l, hl, rfl⟩, by rw [Nat.testBit_ofBits_lt a _ l.1.2]; exact hal⟩

end PaddedDescent
