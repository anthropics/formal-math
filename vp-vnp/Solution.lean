/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Statement
import Paper.Approximate

/-!
# Proofs of the statements, each from the theorem of the paper with that statement
-/

namespace Solution

open Statement

universe u

/-- The classes of the statement are those of the proof. -/
def toNc {F : Type u} [CommSemiring F] (f : Family F) : Nc.Family F := { X := f.vars, fin := f.fin, poly := f.poly }

/-- And conversely. -/
def ofNc {F : Type u} [CommSemiring F] (f : Nc.Family F) : Family F := { vars := f.X, fin := f.fin, poly := f.poly }

/-- The main theorem (Theorem thm:allfields). -/
theorem mainTheorem : MainTheorem.{u} := by
  obtain ⟨c, hc, h⟩ := Paper.thm_allfields.{u}
  refine ⟨c, hc, fun p => ?_⟩
  by_cases hp : p = 0 ∨ p.Prime
  · exact h p hp
  · exact ⟨0, fun F _ _ => absurd (CharP.char_is_prime_or_zero F p).symm hp⟩

/-- VP is a proper subset of VNP over every field (Corollary cor:allclasses). -/
theorem separation : Separation.{u} := fun F _ =>
  ⟨fun f hf => ((Paper.cor_allclasses F).1 (hf : toNc f ∈ Nc.VP F) : toNc f ∈ Nc.VNP F),
    fun h => (Paper.cor_allclasses F).2 fun g hg => (h (a := ofNc g) hg : ofNc g ∈ VP F)⟩

/-- The main theorem for approximate circuits (Theorem thm:approx). -/
theorem mainTheoremApprox : MainTheoremApprox.{u} := by
  obtain ⟨c, hc, h⟩ := Paper.thm_approx.{u}.1
  refine ⟨c, hc, fun p => ?_⟩
  by_cases hp : p = 0 ∨ p.Prime
  · exact h p hp
  · exact ⟨0, fun F _ _ => absurd (CharP.char_is_prime_or_zero F p).symm hp⟩

/-- Over every field VNP is not contained in the closure of VP (Theorem thm:approx). -/
theorem separationClosure : SeparationClosure.{u} := fun F _ h =>
  Paper.thm_approx.{u}.2 F fun g hg => (h (a := ofNc g) hg : ofNc g ∈ VPBar F)

/-- The special case in the main text of the paper: the real numbers and the permanent (Theorem thm:main). -/
theorem permanent_over_real : ∃ c : ℝ, 0 < c ∧ ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ s : ℕ,
    Computes (perm ℝ m) s → Beyond c m s :=
  Paper.thm_main

end Solution
