/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import SplitCount.Defs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! # Small facts for proof/consequences/SplitCount/

Bounds on `size` (the measure of the states of a machine cut into steps) of lists, formulas, numbers
in unary, words and nodes of the tree; `cntN n x ≤ 2^n`; the output function `outW` writes
`SatK.binary`; two inequalities between polynomials.
The same facts are proved, as private theorems that an importing file cannot use, in
proof/machines/StepMachines/Prog/Sat.lean, proof/consequences/WidthK/Top/Sat.lean and
proof/consequences/CountKSat/Top/Count.lean. -/

public section

namespace SplitCount

open Groundwork Groundwork.Prog CountKSat

/-- A list of at most k entries of size at most s has size at most k(s+1) + 1. -/
theorem size_list_le {α : Type} [HasSize α] {l : List α} {k s : ℕ} (hl : l.length ≤ k) (hs : ∀ x ∈ l, size x ≤ s) : size l ≤ k * (s + 1) + 1 := by
  have h : ∀ l : List α, (∀ x ∈ l, size x ≤ s) → (l.map fun x => size x + 1).sum ≤ l.length * (s + 1) := by
    intro l
    induction l with
    | nil => intro _; simp
    | cons a l ih =>
      intro hs
      have h1 := hs a List.mem_cons_self
      have h2 := ih fun x hx => hs x (List.mem_cons_of_mem _ hx)
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      rw [Nat.succ_mul]
      omega
  rw [size_list]
  exact Nat.succ_le_succ ((h l hs).trans (Nat.mul_le_mul_right _ hl))

/-- A literal on a variable below n has size at most n + 2. -/
theorem size_lit_le {l : ℕ × Bool} {n : ℕ} (h : l.1 < n) : size l ≤ n + 2 := by
  have : l.1.size ≤ n := Nat.size_le.2 (h.trans Nat.lt_two_pow_self)
  rw [size_prod, size_nat, size_bool]
  omega

/-- A formula of at most m clauses of at most k literals with variables below n has size at most
m(k(n+3)+2) + 1. -/
theorem size_fml_le {k : ℕ} {x : Fml} {m n : ℕ} (hm : x.length ≤ m) (hx : ∀ C ∈ x, C.length ≤ k ∧ ∀ l ∈ C, l.1 < n) : size x ≤ m * (k * (n + 2 + 1) + 1 + 1) + 1 :=
  size_list_le hm fun C hC => size_list_le (hx C hC).1 fun l hl => size_lit_le ((hx C hC).2 l hl)

/-- The size of n in unary is at most 2n + 1. -/
theorem size_unary (n : ℕ) : size (List.replicate n ()) ≤ n * 2 + 1 :=
  size_list_le (k := n) (s := 1) (by simp) fun x _ => by simp

/-- The size of a word of n + 1 bits is at most 2(n+1) + 1. -/
theorem size_binary (n v : ℕ) : size (SatK.binary n v) ≤ (n + 1) * 2 + 1 :=
  size_list_le (k := n + 1) (s := 1) (by simp [SatK.binary]) fun x _ => by simp

/-- A number below 2^B has size at most B + 1. -/
theorem size_nat_le {v B : ℕ} (h : v < 2 ^ B) : size v ≤ B + 1 := by
  have : v.size ≤ B := Nat.size_le.2 h
  rw [size_nat]
  omega

/-- The size of a node of the tree, from bounds on the formula that is counted at it. -/
theorem size_node_le {w m n : ℕ} {x : CNode} (hm : (leafF x).length ≤ m) (hx : ∀ C ∈ leafF x, C.length ≤ w ∧ ∀ l ∈ C, l.1 < n) : size x ≤ 2 * (m * (w * (n + 2 + 1) + 1 + 1) + 1) := by
  have hl : x.2.length + x.1.length ≤ m := by simpa [leafF] using hm
  have h1 := size_fml_le (k := w) (x := x.1) (m := m) (n := n) (by omega) fun C hC => hx C (by simp [leafF, hC])
  have h2 := size_fml_le (k := w) (x := x.2) (m := m) (n := n) (by omega) fun C hC => hx C (by simp [leafF, hC])
  rw [size_prod]
  omega

/-- There are at most 2^n satisfying assignments on x₀ … xₙ₋₁. -/
theorem cntN_le (n : ℕ) (x : Fml) : cntN n x ≤ 2 ^ n := by
  refine (Finset.card_filter_le _ _).trans ?_
  simp

/-- A formula with an empty clause has no satisfying assignment. -/
theorem cntN_of_nil {n : ℕ} {x : Fml} (h : [] ∈ x) : cntN n x = 0 := by
  rw [cntN, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro a _ ha
  obtain ⟨l, hl, -⟩ := ha [] h
  simp at hl

/-- The ℓ-bit word of y lists the bits 0, …, ℓ − 1 of y. -/
theorem toWord_eq (ℓ y : ℕ) : toWord ℓ y = (List.range ℓ).map y.testBit := by
  induction ℓ generalizing y with
  | zero => rfl
  | succ ℓ ih =>
    rw [toWord, ih, List.range_succ_eq_map, List.map_cons, List.map_map]
    congr 1
    · simp [Nat.testBit_zero]
    · refine List.map_congr_left fun i _ => ?_
      simp [Nat.testBit_succ]

/-- The output function of the machine writes the word of the statement: v in n + 1 bits. -/
theorem outW_eq (n : ℕ) (ψ : Fml) (v : ℕ) : outW ((List.replicate n (), ψ), v) = SatK.binary n v := by
  simp [outW, SatK.binary, toWord_eq]

/-- For s ≥ 1: if x ≤ B·s^d + A·(P·s^e)^A then x ≤ c·s^c with c = B + d + A·P^A + e·A. -/
theorem poly_le {s A B P d e x : ℕ} (hs : 1 ≤ s) (hx : x ≤ B * s ^ d + A * (P * s ^ e) ^ A) :
    x ≤ (B + d + A * P ^ A + e * A) * s ^ (B + d + A * P ^ A + e * A) := by
  obtain ⟨c, hc⟩ : ∃ c, c = B + d + A * P ^ A + e * A := ⟨_, rfl⟩
  rw [← hc]
  have h1 : s ^ d ≤ s ^ c := Nat.pow_le_pow_right hs (by omega)
  have h2 : s ^ (e * A) ≤ s ^ c := Nat.pow_le_pow_right hs (by omega)
  calc x ≤ B * s ^ d + A * (P * s ^ e) ^ A := hx
    _ = B * s ^ d + A * P ^ A * s ^ (e * A) := by rw [mul_pow, ← pow_mul, mul_assoc]
    _ ≤ B * s ^ c + A * P ^ A * s ^ c := Nat.add_le_add (Nat.mul_le_mul_left _ h1) (Nat.mul_le_mul_left _ h2)
    _ = (B + A * P ^ A) * s ^ c := by ring
    _ ≤ c * s ^ c := Nat.mul_le_mul_right _ (by omega)

end SplitCount
