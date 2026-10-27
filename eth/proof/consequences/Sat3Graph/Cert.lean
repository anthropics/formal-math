/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Sat3Graph.Defs
import SizeCircuit.SizedCert
import GraphProblems.Cert
import ToTuring.Poly.Basic
import ToTuring.Poly.Walk
import Mathlib.Tactic

/-! # Section 7, Corollary 7: polynomial-time steps

Proof of `StCert` of proof/consequences/Sat3Graph/Defs.lean. The paper does not say this; it is what
makes a number of steps a time. Reading the input, writing Γ, striking out repeated clauses and
splitting long clauses are polynomial time, and so are the step, the root and the leaf of the tree
for Dominating Set (`GraphProblems.stCertDom`).
The certificates of the readers for cliques and vertex covers (`Complement.StReadersCert`) and of
the formula for independent sets (`Complement.StIndepAlone`) are hypotheses here; Main.lean puts
their proofs in. That the formula of the colorings is computed in polynomial time is proved here on
its own: proof/consequences/GraphProblems/ proves it only inside `GraphProblems.StCertForm`,
together with the same fact for its formulas for cliques and vertex covers. -/

public section

namespace Sat3Graph

open Groundwork Groundwork.Prog CountKSat GraphProblems Paper Eight.Width SizeCircuit Complement SplitSat

/-- The steps of `askSized gates D` are polynomial time if those of D are and the circuits are
computed in polynomial time. -/
theorem askSized_polyTimeSteps {gates : ℕ → ℕ → List CircuitLowerBound.GateD} (hC : CertGates gates) {D : StepMachine (List Unit × Fml) Bool} (hD : PolyTimeSteps D) :
    PolyTimeSteps (askSized gates D) := by
  obtain ⟨h⟩ := hD
  exact ⟨IsPolyT.mapIn (M := D) (f := fun p => widthP (withGamma gates p)) (PolyT.comp widthP_polyT (withGamma_polyT hC))⟩

/-- The formula of the colorings is computed in polynomial time from (n in unary, matrix). -/
theorem colorF_polyT (k : ℕ) : PolyT fun a : List Unit × List Bool => colorF k a.1.length a.2 := by
  have hu : Unary fun a : List Unit × List Bool => a.1.length := Unary.of_length (by fun_prop)
  have hr : PolyT fun a : List Unit × List Bool => List.range a.1.length := PolyT.range hu
  have hp : PolyT fun a : List Unit × List Bool => pairs a.1.length := pairs_polyT hu
  unfold colorF
  fun_prop

/-- Behind a polynomial-time reader r of (n in unary, matrix), the reader for colorings is
polynomial time. -/
theorem readC_behind_polyT (k : ℕ) {r : List Bool → List Unit × List Bool} (hr : PolyT r) :
    PolyT fun x => (List.replicate ((r x).1.length * k) (), (colorF k (r x).1.length (r x).2).dedup) := by
  have h1 : PolyT fun x : List Bool => List.replicate ((r x).1.length * k) () :=
    (Unary.of_length (w := fun x => (r x).1) (by fun_prop)).mul (Unary.const k)
  have h3 : PolyT fun x : List Bool => colorF k (r x).1.length (r x).2 := PolyT.comp (colorF_polyT k) hr
  exact PolyT.prodMk h1 (PolyT.dedup h3)

/-- The reader for colorings is polynomial time. -/
theorem readC_polyT_alone (k : ℕ) : PolyT (readC k) := readC_behind_polyT k stCertRead.1

/-- **`StCert`**, from the certificates of the readers for cliques and vertex covers and of the
formula for independent sets: the steps of the five deciders are polynomial time if those of D are
and the circuits are computed in polynomial time. -/
theorem stCert_of (hRC : Complement.StReadersCert) (hI : Complement.StIndepAlone) : StCert := by
  intro gates hC D hD
  obtain ⟨hA⟩ := askSized_polyTimeSteps hC hD
  obtain ⟨hD'⟩ := hD
  refine ⟨⟨IsPolyT.mapIn (M := askSized gates D) (readF_polyT stCertRead hI.1)⟩, ⟨IsPolyT.mapIn (M := askSized gates D) hRC.1⟩,
    ⟨IsPolyT.mapIn (M := askSized gates D) hRC.2⟩, fun w => ?_, fun k => ?_⟩
  · have := IsPolyT.mapIn (M := askSized gates D) stCertDom.2.2
    have := IsPolyT.walk (T := Stepped.mapIn leafD (askSized gates D)) (step := stepD w) (root := rootD) (stCertDom.1 w) stCertDom.2.1
    exact ⟨IsPolyT.mapIn (M := Stepped.walk (stepD w) rootD (Stepped.mapIn leafD (askSized gates D))) stCertRead.2⟩
  · exact ⟨IsPolyT.mapIn (M := D) (f := fun x => widthP (readC k x)) (PolyT.comp widthP_polyT (readC_polyT_alone k))⟩

end Sat3Graph
