/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ToTuring.Lib.Unary
public import ToTuring.EncLemmas
public import StepMachines.Prog.Spec

/-! What it means that the transformers of the module `StepMachines.Prog.Spec` keep `IsPolyT` (every
step is polynomial-time):
if the lengths they are given are `Unary` and the procedures `IsPolyT`, so is the machine they
build. `IsPolyT` is data and
the predicates below are propositions, hence `Nonempty`. -/

@[expose] public section

namespace Groundwork.Prog

/-- `E` keeps `IsPolyT`: if the length `lam` is `Unary` and the procedure `R` is `IsPolyT`, then so
is `E.app lam R`. -/
def Evaluator.Keeps (E : Evaluator) : Prop :=
  ∀ (C : Type) [HasSize C] [Enc C] [Carried C] (lam : C → ℕ) (R : Stepped (C × IQ) ℤ),
    Unary lam → Nonempty (IsPolyT R) → Nonempty (IsPolyT (E.app lam R))

/-- The lengths `n` and `cap` are `Unary` and the two procedures `W` and `f` are `IsPolyT`. -/
structure PNet.Keeps {C : Type} [Enc C] (Np : PNet C) : Prop where
  n : Unary fun p : C × ℕ => Np.n p.1 p.2
  cap : Unary fun p : C × ℕ × ℕ => Np.cap p.1 p.2.1 p.2.2
  W : Nonempty (IsPolyT Np.W)
  f : Nonempty (IsPolyT Np.f)

/-- `NE` keeps `IsPolyT`: if the network `Np` satisfies `PNet.Keeps`, then `NE.app Np` is `IsPolyT`. -/
def NetEvaluator.Keeps (NE : NetEvaluator) : Prop :=
  ∀ (C : Type) [HasSize C] [Enc C] [Carried C] (Np : PNet C), Np.Keeps → Nonempty (IsPolyT (NE.app Np))

end Groundwork.Prog
