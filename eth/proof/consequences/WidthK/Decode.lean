/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import KSatStatement
public import StepMachines.Prog.Decode
import all StepMachines.Prog.Decode
import all StepMachines.Math.Formula

/-! # Reading the code of a k-SAT instance

`SatK.enc k φ` is `n` ones, a zero, then for every clause k slots of `width n` bits, each holding a
literal or nothing. This file defines the decoder
`decK k` and proves: `decK k (enc k φ) = (n, toN φ)` for k ≥ 1 when no clause has more than k
literals (`decK_enc`); and, for an instance of k-SAT,
the code has length less than (k·2^k + 1)·(n+2)^(k+1) (`length_enc_succ_le`).
With k = 0 a clause takes no bits, and the formulas [] and [[]] have the same code.

The file follows proof/machines/StepMachines/Math/Formula.lean and
proof/machines/StepMachines/Prog/Decode.lean line by line, with a parameter k for their width 3, and
uses their
lemmas that do not mention the width. Where they write out the slots 0, 1, 2, this file uses
`filterMap_range_getElem?`, proved by induction on k.
`toN`, `SatN` and `satN_toN` (φ is satisfiable iff `toN φ` is) are those of Prog/Decode.lean,
unchanged. -/

namespace Groundwork.DecodeK

open Sat3 (Lit CNF Satisfiable slot)
open SatK
open Groundwork.Decode

/-- The clause written in a block of k slots of `w` bits. -/
@[expose] public def clauseDec (k w : ℕ) (b : List Bool) : List (ℕ × Bool) :=
  (List.range k).filterMap fun j => slotDec (ofWord (block w j b))

/-- The number of variables and the clauses written in a bit string, k slots per clause. -/
@[expose] public def decK (k : ℕ) (x : List Bool) : ℕ × NCNF :=
  let n := (x.takeWhile id).length
  let body := (x.dropWhile id).tail
  let w := width n
  (n, ((List.range body.length).take (body.length / (k * w))).map fun c => clauseDec k w (block (k * w) c body))

/-! ### The number of clauses -/

/-- A clause of at most k literals is determined by its entries at the places 0 to k − 1. -/
theorem eq_of_slots {k n : ℕ} {C D : List (Lit n)} (hC : C.length ≤ k) (hD : D.length ≤ k)
    (h : ∀ j < k, C[j]? = D[j]?) : C = D :=
  List.ext_getElem? fun j => by
    by_cases hj : j < k
    · exact h j hj
    · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]

/-- An instance on n variables has at most (2n+1)^k clauses, so its code is polynomially long. -/
public theorem IsKCNF.length_le {k n : ℕ} {φ : CNF n} (h : IsKCNF k φ) : φ.length ≤ (2 * n + 1) ^ k := by
  have := (h.2.map_on (f := fun C (j : Fin k) => C[(j : ℕ)]?) fun C hC D hD e =>
    eq_of_slots (h.1 C hC) (h.1 D hD) fun j hj => congrFun e ⟨j, hj⟩).length_le_card
  simpa [mul_comm] using this

/-! ### Decoding -/

/-- Reading the first k places of a list one by one gives its first k members. -/
theorem filterMap_range_getElem? {α : Type} (l : List α) (k : ℕ) : (List.range k).filterMap (fun j => l[j]?) = l.take k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.range_succ, List.filterMap_append, ih, List.take_add_one]
    congr 1

/-- The bits of clause `C` in the code. -/
def blk (k n : ℕ) (C : List (Lit n)) : List Bool :=
  (List.range k).flatMap fun j => (List.range ((Nat.log2 (2 * n) + 1))).map (slot C[j]?).testBit

/-- The bits of a clause are the words of its k slots, laid end to end. -/
theorem blk_eq (k n : ℕ) (C : List (Lit n)) : blk k n C =
    ((List.range k).map fun j => toWord (Nat.log2 (2 * n) + 1) (slot C[j]?)).flatten := by
  simp only [blk, toWord_eq, List.flatMap_def]

/-- Every clause takes k·(⌊log₂ (2n)⌋ + 1) bits. -/
theorem length_blk (k n : ℕ) (C : List (Lit n)) : (blk k n C).length = k * (Nat.log2 (2 * n) + 1) := by
  simp [blk]

/-- Reading the bits of a clause of at most k literals gives the clause back, with its variables as
natural numbers. -/
theorem clauseDec_blk {k n : ℕ} {C : List (Lit n)} (hC : C.length ≤ k) :
    clauseDec k (Nat.log2 (2 * n) + 1) (blk k n C) = C.map fun l => (l.1.val, l.2) := by
  have key : ∀ j ∈ List.range k, slotDec (ofWord (block (Nat.log2 (2 * n) + 1) j (blk k n C))) =
      (C.map fun l => (l.1.val, l.2))[j]? := fun j hj => by
    have hj : j < k := List.mem_range.1 hj
    rw [blk_eq, block_flatten (fun l hl => by obtain ⟨_, _, rfl⟩ := List.mem_map.1 hl; simp) j (by simpa using hj)]
    simp only [List.getElem_map, List.getElem_range, ofWord_toWord (slot_lt _), slotDec_slot, List.getElem?_map]
  rw [clauseDec, List.filterMap_congr key, filterMap_range_getElem?, List.take_of_length_le (by simpa using hC)]

/-- The code is the header 1ⁿ 0 followed by the bits of the clauses. -/
theorem enc_eq (k : ℕ) {n : ℕ} (φ : CNF n) : enc k φ = List.replicate n true ++ false :: (φ.map (blk k n)).flatten := by
  rw [enc, List.flatMap_def]
  rfl

/-- The number of bits after the header. -/
theorem length_body (k : ℕ) {n : ℕ} (φ : CNF n) :
    (φ.map (blk k n)).flatten.length = φ.length * (k * (Nat.log2 (2 * n) + 1)) := by
  induction φ with
  | nil => simp
  | cons C φ ih => simp only [List.map_cons, List.flatten_cons, List.length_append, ih, length_blk, List.length_cons]; ring

/-- For k ≥ 1, decoding the code of a formula with at most k literals in every clause gives back `n`
and the formula, with
its variables as natural numbers. -/
public theorem decK_enc {k n : ℕ} (hk : 1 ≤ k) {φ : CNF n} (hφ : ∀ C ∈ φ, C.length ≤ k) :
    decK k (enc k φ) = (n, toN φ) := by
  have hB : 0 < k * (Nat.log2 (2 * n) + 1) := Nat.mul_pos hk (Nat.succ_pos _)
  simp only [decK, enc_eq, takeWhile_header, dropWhile_header, List.length_replicate, List.tail_cons, width_eq,
    length_body, Nat.mul_div_cancel _ hB, List.take_range, toN]
  congr 1
  rw [min_eq_left (Nat.le_mul_of_pos_right _ hB)]
  refine List.ext_getElem (by simp) fun c h1 h2 => ?_
  have hc : c < φ.length := by simpa using h1
  simp only [List.getElem_map, List.getElem_range]
  rw [block_flatten (fun l hl => by obtain ⟨C, _, rfl⟩ := List.mem_map.1 hl; exact length_blk k n C) c (by simpa using hc),
    List.getElem_map, clauseDec_blk (hφ _ (List.getElem_mem hc))]

/-! ### The length of the code -/

/-- The exact length of the code: the header, then k slots for every clause. -/
public theorem length_enc (k : ℕ) {n : ℕ} (φ : CNF n) :
    (enc k φ).length = n + 1 + φ.length * (k * (Nat.log2 (2 * n) + 1)) := by
  simp only [enc_eq, List.length_append, List.length_replicate, List.length_cons, length_body]; omega

/-- The code of an instance of k-SAT has at most n + 1 + k·(⌊log₂ (2n)⌋ + 1)·(2n+1)^k bits. -/
public theorem length_enc_le {k n : ℕ} {φ : CNF n} (h : IsKCNF k φ) :
    (enc k φ).length ≤ n + 1 + k * (Nat.log2 (2 * n) + 1) * (2 * n + 1) ^ k := by
  rw [length_enc, Nat.mul_comm φ.length]
  exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (IsKCNF.length_le h)) _

/-- The length of the code of an instance of k-SAT, plus one, is at most (k·2^k + 1)·(n+2)^(k+1):
polynomial in n for fixed k. -/
public theorem length_enc_succ_le {k n : ℕ} {φ : CNF n} (h : IsKCNF k φ) :
    (enc k φ).length + 1 ≤ (k * 2 ^ k + 1) * (n + 2) ^ (k + 1) := by
  have h1 := length_enc_le h
  have h2 : k * (Nat.log2 (2 * n) + 1) * (2 * n + 1) ^ k ≤ k * (n + 2) * (2 * (n + 2)) ^ k :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ ((bitLen_le n).trans (by omega))) (Nat.pow_le_pow_left (by omega) k)
  have h3 : k * (n + 2) * (2 * (n + 2)) ^ k = k * 2 ^ k * (n + 2) ^ (k + 1) := by rw [mul_pow]; ring
  have h4 : n + 2 ≤ (n + 2) ^ (k + 1) := Nat.le_self_pow (by omega) _
  rw [Nat.add_mul, Nat.one_mul]
  omega

end Groundwork.DecodeK
