/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Ov.Core.Tensor

/-!
# Gauges

A gauge (in Lean: `PreSpec`) is what a spectral point becomes when "multiplicative"
is weakened to "submultiplicative". Such a function is easy to write down, as an infimum over
certificates; `Paper.prop_gauge` finds a spectral point below it.
(Paper: the subsection "Gauges". The zero tensor is covered by the empty family, so a gauge is 0 at it.)
-/

namespace Ov

/-- A gauge on the parties I: a real function p ≥ 0 on tensors with p(1) = 1,
p(st) ≤ p(s)p(t), and p(s) ≤ ∑ p(b k) whenever s is a sum of restrictions of the b k. -/
structure PreSpec (K : Type) [Field K] (I : Type) [Fintype I] [DecidableEq I] where
  p : Ten K I → ℝ
  nonneg : ∀ t, 0 ≤ p t
  one : p 1 = 1
  mul_le : ∀ s t, p (s * t) ≤ p s * p t
  le_sum : ∀ {κ : Type} [Fintype κ] (s : Ten K I) (b : κ → Ten K I), Ten.SumRestr s b →
    p s ≤ ∑ k, p (b k)

namespace PreSpec

variable {K : Type} [Field K] {I : Type} [Fintype I] [DecidableEq I]

/-- A gauge is monotone under restriction. -/
theorem mono (P : PreSpec K I) {s t : Ten K I} (h : Ten.Restr s t) : P.p s ≤ P.p t := by
  obtain ⟨L, hL⟩ := h
  have h1 : Ten.SumRestr s (fun _ : Unit => t) := ⟨fun _ => L, fun x => by simpa using hL x⟩
  simpa using P.le_sum s _ h1

end PreSpec

end Ov
