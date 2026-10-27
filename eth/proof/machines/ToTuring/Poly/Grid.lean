/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ToTuring.Poly.Digits
public import ToTuring.Poly.Range
public import ToTuring.Poly.Comb
public import ToTuring.Poly.Spec
public import StepMachines.Prog.GridLoop

/-! The condition `NetFormer.Keeps` on a procedure that forms networks, used for the loop of one
level of the recursion (Section 5)
over the patterns ι (one digit in {0,…,λ} for each rectangle). -/

@[expose] public section

namespace Groundwork.Prog

open Stepped

/-- From a λ given in unary and a procedure `R` whose steps are polynomial-time (`IsPolyT`), `F`
forms a network that
satisfies `Keeps`, the condition under which an evaluator of networks stays polynomial-time. -/
def NetFormer.Keeps (F : NetFormer) : Prop :=
  ∀ (C : Type) [HasSize C] [Enc C] [Carried C] (lam : C → ℕ) (R : Stepped (C × IQ) ℤ),
    Unary lam → Nonempty (IsPolyT R) → (F lam R).Keeps

section

variable {C : Type} [Enc C] {lam : C → ℕ}

end

end Groundwork.Prog
