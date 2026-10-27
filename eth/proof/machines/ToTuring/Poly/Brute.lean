/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ToTuring.Poly.Words
public import ToTuring.Poly.Basic
public import ToTuring.Poly.Range
public import ToTuring.Poly.Spec
public import StepMachines.Prog.BruteE

/-! `brute`: brute force for the sum Z (the value of a clique, as in Definition 3 of the paper), the
sum over all labellings of the product over
the K nodes of the answers of a given machine `R`. If every step of `R` is polynomial-time
(`IsPolyT`), so is every step
of `brute`. -/

@[expose] public section

namespace Groundwork

open Stepped

section

variable {C : Type} [Enc C] {lam : C → ℕ} {dflt : C → List Bool}

/-- The number of bits of a labelling is given in unary if the length of a label is. -/
theorem bruteLen_unary (K : ℕ) (hl : Unary lam) : Unary fun c => K * (K - 1) / 2 * lam c :=
  (Unary.const _).mul hl

/-- The number of labellings is polynomial-time. -/
theorem bruteBound_polyT (K : ℕ) (hl : Unary lam) : PolyT (bruteBound K lam) :=
  PolyT.two_pow (bruteLen_unary K hl)

/-- The query sent to `R` is polynomial-time. -/
theorem bruteQuery_polyT (K : ℕ) (hl : Unary lam) (hd : PolyT dflt) : PolyT (bruteQuery K lam dflt) := by
  have h1 := hd
  have h2 := hl.poly
  have h3 : PolyT fun x : (C × ℕ) × ℕ => toWord (K * (K - 1) / 2 * lam x.1.1) x.1.2 :=
    PolyT.toWord' ((bruteLen_unary K hl).comp (h := fun x : (C × ℕ) × ℕ => x.1.1) (by fun_prop)) (by fun_prop)
  unfold bruteQuery
  fun_prop

/-- Brute force over the 2^(K(K-1)/2·lam) labellings, as a sum of products of K calls of `R`, is
`IsPolyT` if `R` is. -/
@[instance_reducible] def IsPolyT.brute [HasSize C] [Carried C] (K : ℕ)
    {R : Stepped (C × ℕ × List (List Bool)) ℤ} [IsPolyT R] (hl : Unary lam) (hd : PolyT dflt) :
    IsPolyT (Groundwork.brute K lam dflt R) :=
  haveI := IsPolyT.mapIn (M := R) (bruteQuery_polyT K hl hd)
  haveI := IsPolyT.prodRange (M := Stepped.mapIn (bruteQuery K lam dflt) R) (N := Function.const (C × ℕ) K)
    (by unfold Function.const; fun_prop)
  IsPolyT.sumRange (bruteBound_polyT K hl)

end

namespace Prog

/-- The brute-force evaluator `bruteE K` keeps `IsPolyT`: applied to an `IsPolyT` machine for the
tensors it gives one. -/
theorem bruteE_keeps (K : ℕ) : (bruteE K).Keeps := fun C _ _ _ lam R hl ⟨hR⟩ =>
  ⟨IsPolyT.brute K hl (by unfold nilC; fun_prop)⟩

end Prog

end Groundwork
