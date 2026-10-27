/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import SizeCircuit.Defs
import ToTuring.Poly.Basic
import ToTuring.Lib.Unary
import ToTuring.Lib.Nat2
import ToTuring.Lib.Nat1b
import ToTuring.Lib.List3
import Mathlib.Tactic

/-! # Section 7, proof of Corollary 7: ψ ∧ Γ is written in polynomial time

Proof of `StSizedCert` of proof/consequences/SizeCircuit/Defs.lean: if the circuits are computed in
polynomial time, then so is (n in unary, s, ψ) ↦ (number of variables in unary, ψ ∧ Γ), and the
steps of `sizedBy gates E` are polynomial time if those of E are. The paper does not say this; it is
needed because the formula is written by a machine. -/

public section

namespace SizeCircuit

open Groundwork Groundwork.Prog CountKSat GraphProblems CircuitLowerBound Eight

/-- The four clauses of a gate are polynomial time in (the number of its wire, the gate). -/
theorem gateClauses_polyT : PolyT fun p : ℕ × GateD => gateClauses p.1 p.2 := by
  unfold gateClauses
  fun_prop

/-- The clauses of all gates are polynomial time in (n in binary, the circuit). -/
theorem wiresFormula_polyT : PolyT fun p : ℕ × List GateD => wiresFormula p.1 p.2 := by
  have hz : PolyT fun p : ℕ × List GateD => p.2.zip (List.range p.2.length) :=
    PolyT.zip (by fun_prop) (PolyT.range (Unary.of_length (by fun_prop)))
  have h : PolyT fun p : ℕ × List GateD => (p.2.zip (List.range p.2.length)).flatMap fun gt => gateClauses (p.1 + gt.2) gt.1 :=
    PolyT.flatMap (f := fun (p : ℕ × List GateD) (gt : GateD × ℕ) => gateClauses (p.1 + gt.2) gt.1)
      (PolyT.comp (f := fun q : ℕ × GateD => gateClauses q.1 q.2) (g := fun r : (ℕ × List GateD) × (GateD × ℕ) => (r.1.1 + r.2.2, r.2.1))
        gateClauses_polyT (by fun_prop)) hz
  exact h.congr fun p => by rw [wiresFormula, List.zipIdx_eq_zip_range', ← List.range_eq_range']

/-- The formula of a circuit is polynomial time in (n in binary, the circuit). -/
theorem formulaOf_polyT : PolyT fun p : ℕ × List GateD => formulaOf p.1 p.2 :=
  PolyT.append wiresFormula_polyT (by fun_prop)

/-- (n in unary, s, ψ) ↦ (number of variables in unary, ψ ∧ Γ) is polynomial time if the circuits
are. -/
theorem withGamma_polyT {gates : ℕ → ℕ → List GateD} (hC : CertGates gates) : PolyT (withGamma gates) := by
  have hG : PolyT fun p : List Unit × ℕ × Fml => gates p.1.length p.2.1 :=
    PolyT.comp (f := fun q : List Unit × ℕ => gates q.1.length q.2) (g := fun p : List Unit × ℕ × Fml => (p.1, p.2.1)) hC (by fun_prop)
  have hF : PolyT fun p : List Unit × ℕ × Fml => formulaOf p.1.length (gates p.1.length p.2.1) :=
    PolyT.comp (f := fun q : ℕ × List GateD => formulaOf q.1 q.2) (g := fun p : List Unit × ℕ × Fml => (p.1.length, gates p.1.length p.2.1))
      formulaOf_polyT (PolyT.prodMk (by fun_prop) hG)
  have hg : PolyT fun p : List Unit × ℕ × Fml => gamma gates p.1.length p.2.1 :=
    PolyT.ite' (c := fun p : List Unit × ℕ × Fml => p.1.length = 0) (by fun_prop) (by fun_prop) hF
  have h1 : Unary fun p : List Unit × ℕ × Fml => p.1.length + (gates p.1.length p.2.1).length :=
    (Unary.of_length (by fun_prop)).add (Unary.of_length hG)
  have hU : PolyT fun p : List Unit × ℕ × Fml => List.replicate (numVars gates p.1.length p.2.1) () :=
    (PolyT.ite' (c := fun p : List Unit × ℕ × Fml => p.1.length = 0) (by fun_prop) (PolyT.const []) h1).congr fun p => by
      unfold numVars
      split_ifs <;> rfl
  exact hU.prodMk (PolyT.dedup (PolyT.append (by fun_prop) hg))

/-- **`StSizedCert`.** The steps of `sizedBy gates E` are polynomial time if those of E are and the
circuits are computed in polynomial time. -/
theorem stSizedCert : StSizedCert := by
  rintro gates hC E ⟨hE⟩
  have := hE
  have := IsPolyT.mapIn (M := E) (withGamma_polyT hC)
  exact ⟨IsPolyT.mapOut (M := Stepped.mapIn (withGamma gates) E) (f := ofWord) (by fun_prop)⟩

end SizeCircuit
