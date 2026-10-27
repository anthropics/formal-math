/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSatStatement
public import StepMachines.Prog.Chunks
public import Mathlib.Data.Nat.Size
import StepMachines.Math.Formula

/-! Reading the input: `dec` recovers the number of variables and the clauses from the bit string
`Sat3.enc φ`.
The string is `n` ones, a zero, then for every clause three slots of `width n` bits, each holding a
literal or nothing.
Variables are natural numbers on the decoded side. -/

namespace Groundwork.Decode

open Sat3

/-- A formula with natural numbers as variables. -/
public abbrev NCNF : Type := List (List (ℕ × Bool))

/-- The number of bits of a slot: ⌊log₂ (2n)⌋ + 1. -/
@[expose] public def width (n : ℕ) : ℕ := if n = 0 then 1 else Nat.size (2 * n)

/-- A slot's number as a literal: 0 = none, 2i+1 = ¬xᵢ, 2i+2 = xᵢ. -/
@[expose] public def slotDec (v : ℕ) : Option (ℕ × Bool) :=
  if v = 0 then none else some ((v - 1) / 2, decide ((v - 1) % 2 = 1))

/-- The clause written in a block of three slots of `w` bits. -/
@[expose] public def clauseDec (w : ℕ) (b : List Bool) : List (ℕ × Bool) :=
  [0, 1, 2].filterMap fun j => slotDec (ofWord (block w j b))

/-- The number of variables and the clauses written in a bit string. -/
@[expose] public def dec (x : List Bool) : ℕ × NCNF :=
  let n := (x.takeWhile id).length
  let body := (x.dropWhile id).tail
  let w := width n
  (n, ((List.range body.length).take (body.length / (3 * w))).map fun c => clauseDec w (block (3 * w) c body))

/-- The formula with its variables read as natural numbers. -/
@[expose] public def toN {n : ℕ} (φ : CNF n) : NCNF := φ.map fun C => C.map fun l => (l.1.val, l.2)

/-- Satisfiability of a formula with natural numbers as variables. -/
@[expose] public def SatN (ψ : NCNF) : Prop := ∃ a : ℕ → Bool, ∀ C ∈ ψ, ∃ l ∈ C, a l.1 = l.2

public theorem width_eq (n : ℕ) : width n = (Nat.log2 (2 * n) + 1) := by
  unfold width
  split_ifs with h
  · subst h; simp
  · have h0 : 2 * n ≠ 0 := by omega
    apply le_antisymm
    · exact Nat.size_le.2 Nat.lt_log2_self
    · exact Nat.lt_size.2 (Nat.log2_self_le h0)

theorem toWord_eq (ℓ y : ℕ) : toWord ℓ y = (List.range ℓ).map y.testBit := by
  induction ℓ generalizing y with
  | zero => rfl
  | succ ℓ ih =>
    rw [toWord, ih, List.range_succ_eq_map, List.map_cons, List.map_map]
    congr 1
    · simp [Nat.testBit_zero]
    · refine List.map_congr_left fun i _ => ?_
      simp [Nat.testBit_succ]

theorem slot_lt {n : ℕ} (o : Option (Lit n)) : slot o < 2 ^ (Nat.log2 (2 * n) + 1) := by
  refine lt_of_le_of_lt ?_ Nat.lt_log2_self
  rcases o with _ | ⟨i, b⟩
  · exact Nat.zero_le _
  · have := i.2
    cases b <;> simp only [slot, Bool.toNat_false, Bool.toNat_true] <;> omega

theorem slotDec_slot {n : ℕ} (o : Option (Lit n)) : slotDec (slot o) = o.map fun l => (l.1.val, l.2) := by
  rcases o with _ | ⟨i, b⟩
  · rfl
  · cases b
    · simp [slotDec, slot]
    · simp [slotDec, slot]
      omega

/-- Blocks of one length, laid end to end, are read back by offset. -/
theorem block_flatten {w : ℕ} : ∀ {L : List (List Bool)} (_ : ∀ l ∈ L, l.length = w) (i : ℕ) (hi : i < L.length),
    block w i L.flatten = L[i]
  | [], _, _, hi => by simp at hi
  | l :: L, h, 0, _ => by
    have hl : l.length = w := h l (by simp)
    simp only [block, Nat.zero_mul, List.drop_zero, List.flatten_cons, List.getElem_cons_zero]
    exact List.take_left' hl
  | l :: L, h, i + 1, hi => by
    have hl : l.length = w := h l (by simp)
    have ih := block_flatten (L := L) (fun l hl => h l (List.mem_cons_of_mem _ hl)) i (by simpa using hi)
    simp only [List.getElem_cons_succ, ← ih, block, List.flatten_cons]
    rw [show (i + 1) * w = w + i * w by rw [Nat.succ_mul, Nat.add_comm], ← List.drop_drop, List.drop_left' hl]

/-- The bits of clause `C` in the code. -/
def blk (n : ℕ) (C : List (Lit n)) : List Bool :=
  (List.range 3).flatMap fun j => (List.range ((Nat.log2 (2 * n) + 1))).map (slot C[j]?).testBit

theorem blk_eq (n : ℕ) (C : List (Lit n)) : blk n C =
    [toWord ((Nat.log2 (2 * n) + 1)) (slot C[0]?), toWord ((Nat.log2 (2 * n) + 1)) (slot C[1]?),
      toWord ((Nat.log2 (2 * n) + 1)) (slot C[2]?)].flatten := by
  simp [blk, toWord_eq, show List.range 3 = [0, 1, 2] from rfl]

theorem length_blk (n : ℕ) (C : List (Lit n)) : (blk n C).length = 3 * (Nat.log2 (2 * n) + 1) := by
  simp [blk_eq]; omega

theorem clauseDec_blk {n : ℕ} {C : List (Lit n)} (hC : C.length ≤ 3) :
    clauseDec ((Nat.log2 (2 * n) + 1)) (blk n C) = C.map fun l => (l.1.val, l.2) := by
  have hw : ∀ l ∈ [toWord ((Nat.log2 (2 * n) + 1)) (slot C[0]?), toWord ((Nat.log2 (2 * n) + 1)) (slot C[1]?),
      toWord ((Nat.log2 (2 * n) + 1)) (slot C[2]?)], l.length = (Nat.log2 (2 * n) + 1) := by simp
  have h0 := block_flatten hw 0 (by simp)
  have h1 := block_flatten hw 1 (by simp)
  have h2 := block_flatten hw 2 (by simp)
  simp only [List.getElem_cons_zero, List.getElem_cons_succ] at h0 h1 h2
  simp only [clauseDec, blk_eq, List.filterMap_cons, List.filterMap_nil, h0, h1, h2, ofWord_toWord (slot_lt _),
    slotDec_slot]
  match C, hC with
  | [], _ => rfl
  | [_], _ => rfl
  | [_, _], _ => rfl
  | [_, _, _], _ => rfl
  | _ :: _ :: _ :: _ :: _, h => simp at h; omega

theorem takeWhile_header (n : ℕ) (l : List Bool) :
    (List.replicate n true ++ false :: l).takeWhile id = List.replicate n true := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.replicate_succ, ih]

theorem dropWhile_header (n : ℕ) (l : List Bool) :
    (List.replicate n true ++ false :: l).dropWhile id = false :: l := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.replicate_succ, ih]

theorem enc_eq {n : ℕ} (φ : CNF n) : enc φ = List.replicate n true ++ false :: (φ.map (blk n)).flatten := by
  rw [enc, List.flatMap_def]
  rfl

theorem length_body {n : ℕ} (φ : CNF n) : (φ.map (blk n)).flatten.length = φ.length * (3 * (Nat.log2 (2 * n) + 1)) := by
  induction φ with
  | nil => simp
  | cons C φ ih => simp only [List.map_cons, List.flatten_cons, List.length_append, ih, length_blk, List.length_cons]; ring

/-- Decoding the code of a formula with at most three literals in every clause gives back `n` and
the formula. -/
public theorem dec_enc {n : ℕ} {φ : CNF n} (hφ : ∀ C ∈ φ, C.length ≤ 3) : dec (enc φ) = (n, toN φ) := by
  have hB : 0 < 3 * (Nat.log2 (2 * n) + 1) := by omega
  simp only [dec, enc_eq, takeWhile_header, dropWhile_header, List.length_replicate, List.tail_cons, width_eq,
    length_body, Nat.mul_div_cancel _ hB, List.take_range, toN]
  congr 1
  rw [min_eq_left (Nat.le_mul_of_pos_right _ hB)]
  refine List.ext_getElem (by simp) fun c h1 h2 => ?_
  have hc : c < φ.length := by simpa using h1
  simp only [List.getElem_map, List.getElem_range]
  rw [block_flatten (fun l hl => by obtain ⟨C, _, rfl⟩ := List.mem_map.1 hl; exact length_blk n C) c (by simpa using hc),
    List.getElem_map, clauseDec_blk (hφ _ (List.getElem_mem hc))]

/-- The length of the code. -/
public theorem length_enc {n : ℕ} (φ : CNF n) : (enc φ).length = n + 1 + φ.length * (3 * (Nat.log2 (2 * n) + 1)) := by
  simp only [enc_eq, List.length_append, List.length_replicate, List.length_cons, length_body]; omega

public theorem length_enc_le {n : ℕ} {φ : CNF n} (h : Is3CNF φ) :
    (enc φ).length ≤ n + 1 + 3 * (Nat.log2 (2 * n) + 1) * (2 * n + 1) ^ 3 := by
  rw [length_enc, Nat.mul_comm φ.length]
  exact Nat.add_le_add_left (Nat.mul_le_mul_left _ h.length_le) _

public theorem bitLen_le (n : ℕ) : (Nat.log2 (2 * n) + 1) ≤ n + 1 := by
  rw [← width_eq, width]
  split_ifs with h
  · omega
  · refine Nat.size_le.2 ?_
    rw [pow_succ, Nat.mul_comm]
    exact Nat.mul_lt_mul_of_pos_right Nat.lt_two_pow_self (by norm_num)

/-- The code is polynomially long. -/
public theorem length_enc_succ_le {n : ℕ} {φ : CNF n} (h : Is3CNF φ) : (enc φ).length + 1 ≤ 25 * (n + 2) ^ 4 := by
  have h1 := length_enc_le h
  have h2 : 3 * (Nat.log2 (2 * n) + 1) * (2 * n + 1) ^ 3 ≤ 3 * (n + 2) * (2 * (n + 2)) ^ 3 :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ ((bitLen_le n).trans (by omega))) (Nat.pow_le_pow_left (by omega) 3)
  have h3 : 3 * (n + 2) * (2 * (n + 2)) ^ 3 = 24 * (n + 2) ^ 4 := by ring
  have h4 : n + 2 ≤ (n + 2) ^ 4 := Nat.le_self_pow (by norm_num) _
  omega

/-- Satisfiability does not depend on how variables are named. -/
public theorem satN_toN {n : ℕ} (φ : CNF n) : SatN (toN φ) ↔ Satisfiable φ := by
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨fun i => a i.val, fun C hC => ?_⟩
    obtain ⟨l, hl, h⟩ := ha _ (List.mem_map.2 ⟨C, hC, rfl⟩)
    obtain ⟨l', hl', rfl⟩ := List.mem_map.1 hl
    exact ⟨l', hl', h⟩
  · rintro ⟨a, ha⟩
    refine ⟨fun i => if h : i < n then a ⟨i, h⟩ else false, fun D hD => ?_⟩
    obtain ⟨C, hC, rfl⟩ := List.mem_map.1 hD
    obtain ⟨l, hl, h⟩ := ha C hC
    exact ⟨_, List.mem_map.2 ⟨l, hl, rfl⟩, by simp [l.1.2, h]⟩

/-- The empty clause is seen on the decoded side. -/
public theorem nil_mem_toN {n : ℕ} (φ : CNF n) : [] ∈ toN φ ↔ [] ∈ φ := by
  simp [toN]

public theorem length_toN {n : ℕ} (φ : CNF n) : (toN φ).length = φ.length := by simp [toN]

/-- Clauses keep their lengths, and the variables are below `n`. -/
public theorem mem_toN {n : ℕ} {φ : CNF n} {D : List (ℕ × Bool)} (hD : D ∈ toN φ) :
    (∃ C ∈ φ, D.length = C.length) ∧ ∀ l ∈ D, l.1 < n := by
  obtain ⟨C, hC, rfl⟩ := List.mem_map.1 hD
  refine ⟨⟨C, hC, by simp⟩, fun l hl => ?_⟩
  obtain ⟨l', _, rfl⟩ := List.mem_map.1 hl
  exact l'.1.2

end Groundwork.Decode
