/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import SplitSat.Defs
import GraphProblems.Engine
import Mathlib.Tactic

/-! # Section 7, proof of Corollary 5: «split every long clause into clauses of 3 literals with new variables»

`stLeaf` proves `SplitSat.StLeaf`. The program `Eight.Width.widthP` works on formulas with numbers
as variables. A formula whose variables are below n is `Decode.toN φ` for a formula φ on n variables
(`GraphProblems.exists_toN`); on it the program returns `widthReduce φ` read in the same way
(`Eight.Width.toN_widthReduce`).
What is said of `widthReduce φ` is stated in proof/networks/Eight/Cor/WidthDefs.lean and proved in
proof/networks/Eight/Cor/Width.lean: if φ has m clauses of at most k literals, the image is an
instance of 3-SAT with at most (k − 3)·m new variables (`stWidth`); a satisfying assignment of the
image, read on the old variables, satisfies φ (`stRestrict`); a satisfying assignment of φ extends
to one of the image (`stExtend`).
The number of satisfying assignments is not used here. -/

public section

namespace SplitSat

open Groundwork Groundwork.Prog Eight.Width GraphProblems

/-- The program on (n in unary, x), written out: n + (number of new variables) in unary, and the
formula with its long clauses split. -/
theorem widthP_replicate (n : ℕ) (x : Fml) : widthP (List.replicate n (), x) = (List.replicate (n + numFresh x) (), splitN n x) := by
  simp [widthP]

/-- The first part of what the program returns is a number in unary. -/
theorem widthP_eq (p : List Unit × Fml) : widthP p = (List.replicate (widthP p).1.length (), (widthP p).2) := by
  simp [widthP]

/-- A formula in which no clause is written twice stays so when its variables are read as numbers. -/
theorem nodup_toN {n : ℕ} {φ : Sat3.CNF n} (h : φ.Nodup) : (Decode.toN φ).Nodup := by
  unfold Decode.toN
  refine List.Nodup.map (List.map_injective_iff.2 fun a b e => ?_) h
  exact Prod.ext (Fin.ext (Prod.mk.inj e).1) (Prod.mk.inj e).2

/-- A formula with numbers below n as variables, at most k literals per clause and no clause written
twice is `Decode.toN φ` for an instance φ of k-SAT on n variables. -/
theorem exists_instance {k n : ℕ} {ψ : Fml} (hψ : ∀ C ∈ ψ, C.length ≤ k ∧ ∀ l ∈ C, l.1 < n) (hnd : ψ.Nodup) :
    ∃ φ : Sat3.CNF n, SatK.IsKCNF k φ ∧ Decode.toN φ = ψ := by
  obtain ⟨φ, rfl⟩ := exists_toN fun C hC => (hψ C hC).2
  refine ⟨φ, ⟨fun C hC => ?_, List.Nodup.of_map _ hnd⟩, rfl⟩
  have := (hψ (C.map fun l => (l.1.val, l.2)) (List.mem_map_of_mem hC)).1
  simpa using this

/-- The formula with its long clauses split is satisfiable exactly if the formula is: one direction
restricts an assignment to the old variables, the other extends it to the new ones. -/
theorem satisfiable_widthReduce {n : ℕ} (φ : Sat3.CNF n) : Sat3.Satisfiable (widthReduce φ) ↔ Sat3.Satisfiable φ := by
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨fun i => b (Fin.castAdd (numFresh φ) i), stRestrict n φ b hb⟩
  · rintro ⟨a, ha⟩
    obtain ⟨b, ⟨hb, -⟩, -⟩ := stExtend n φ a ha
    exact ⟨b, hb⟩

/-- **One leaf**: «split every long clause into clauses of 3 literals with new variables». For a
formula x on x₀ … xₙ₋₁ with at most B·n clauses of at most k literals, `widthP` returns (N in unary,
x₃) with at most 3 literals per clause, variables below N, no clause twice, N ≤ (1 + (k−3)·B)·n, and
x₃ is satisfiable exactly if x is. -/
theorem stLeaf : StLeaf := by
  intro k B n x hx hl
  obtain ⟨φ, rfl⟩ := exists_toN fun C hC => (hx C hC).2
  rw [widthP_replicate, ← toN_widthReduce, numFresh_toN]
  dsimp only
  rw [List.length_replicate]
  obtain ⟨h3, -, hk⟩ := stWidth n φ
  have hφ : ∀ C ∈ φ, C.length ≤ k := fun C hC => by
    have := (hx (C.map fun l => (l.1.val, l.2)) (List.mem_map_of_mem hC)).1
    simpa using this
  obtain ⟨hf, -⟩ := hk k hφ
  rw [Decode.length_toN] at hl
  refine ⟨fun C hC => ?_, nodup_toN h3.2, ?_, ?_⟩
  · obtain ⟨⟨C', hC', hl'⟩, h⟩ := Decode.mem_toN hC
    exact ⟨hl' ▸ h3.1 C' hC', h⟩
  · calc n + numFresh φ ≤ n + (k - 3) * (B * n) := Nat.add_le_add_left (hf.trans (Nat.mul_le_mul_left _ hl)) _
      _ = (1 + (k - 3) * B) * n := by ring
  · exact (Decode.satN_toN _).trans ((satisfiable_widthReduce φ).trans (Decode.satN_toN φ).symm)

end SplitSat
