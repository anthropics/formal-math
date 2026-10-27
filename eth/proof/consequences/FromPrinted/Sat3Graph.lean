/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import FromPrinted.SatDefs
import FromPrinted.Core
import SizeCircuit.CircuitDefs
import Sat3Graph.Sets
import Sat3Graph.Dominating
import Sat3Graph.Coloring
import Sat3Graph.Cert
import Sat3Graph.Host
import Sat3Graph.Main
import SizeCircuit.Circuit
import SizeCircuit.Cert
import Complement.Readers
import GraphProblems.DomTree
import Mathlib.Tactic

/-! # Section 7, Corollary 7 for the decision problems, from 3-SAT, on the machine `Printed.SAT`, which decides with Algorithm 1, as a machine of proof/threesat/Printed/

Proofs of `StWithThreeSatMachine` and `StTiedTM` of proof/consequences/FromPrinted/SatDefs.lean, and
the end theorem with the statement `GraphProblems.CorGraphsDecide`, in two pieces (`endFrom`,
`decideFromThreeSat`). What proof/consequences/Sat3Graph/ proves for every procedure D
(`Sat3Graph.stSets`, `stDominating`, `stColoring`, `stCert`, and the hosts of Host.lean) is used as
it stands.
The procedure for 3-SAT is the machine of Theorem 2 in its decision form without its reader
(`FromPrinted.SplitSat.core3 ℓ τ`, `FromPrinted.SplitSat.stCore3`). Given δ and k: take w so large
that the tree for Dominating Set has at most 2^{δn/2} leaves (`GraphProblems.stShortens`); all five
3-CNFs then have at most Q·(n+1) variables for Q = a + 1 + 3·(w − 3) + 2k, and the exponent δ₃ =
δ/(2Q) is small enough for all five.
On Turing machines: the five deciders are taken with δ/2 and hosted with polynomial overhead
(proof/consequences/Sat3Graph/Host.lean). -/

public section

section

open Groundwork Groundwork.Prog CountKSat GraphProblems Paper SizeCircuit Complement Sat3Graph
open SplitSat hiding core3 StCore3Eq StCore3 SATsplit StSATsplit StTiedTM StTiedThreeTM ThreeSatStatement
open FromPrinted.SplitSat

namespace FromPrinted.Sat3Graph

/-- **`StWithThreeSatMachine`.** For every family of circuits that tests the size and is computed in
polynomial time, every δ > 0 and k ≥ 3 there are ℓ, τ, w, c such that the five deciders with D =
`core3 ℓ τ` have polynomial-time steps and decide the five problems within c·2^{δn} steps. -/
theorem stWithThreeSatMachine : StWithThreeSatMachine := by
  intro gates a hT hC δ hδ k hk
  obtain ⟨w, -, hw⟩ := stShortens (δ / 2) (by positivity)
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ, Q = (a : ℝ) + 1 + 3 * ((w - 3 : ℕ) : ℝ) + 2 * (k : ℝ) := ⟨_, rfl⟩
  have hw0 : (0 : ℝ) ≤ ((w - 3 : ℕ) : ℝ) := Nat.cast_nonneg _
  have ha0 : (0 : ℝ) ≤ (a : ℝ) := Nat.cast_nonneg _
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg _
  have hQ0 : 0 < Q := by rw [hQ]; linarith
  obtain ⟨δ₃, hδ₃⟩ : ∃ δ₃ : ℝ, δ₃ = δ / (2 * Q) := ⟨_, rfl⟩
  have h0 : 0 < δ₃ := by rw [hδ₃]; positivity
  have hmul : δ₃ * Q = δ / 2 := by rw [hδ₃, div_mul_eq_mul_div, mul_div_mul_right _ _ hQ0.ne']
  have key : ∀ y : ℝ, y ≤ Q → δ₃ * y ≤ δ / 2 := fun y hy => (mul_le_mul_of_nonneg_left hy h0.le).trans hmul.le
  obtain ⟨ℓ, τ, hP, c, hD⟩ := stCore3 δ₃ h0
  obtain ⟨c₁, s1, s2, s3⟩ := stSets gates a hT δ δ₃ hδ h0.le ((key _ (by rw [hQ]; linarith)).trans (by linarith)) _ c hD
  obtain ⟨c₂, d1⟩ := stDominating gates a hT w δ δ₃ hδ h0.le hw (key _ (by rw [hQ]; linarith)) _ c hD
  obtain ⟨c₃, k1⟩ := stColoring k hk δ δ₃ hδ h0.le ((key _ (by rw [hQ]; linarith)).trans (by linarith)) _ c hD
  obtain ⟨p1, p2, p3, p4, p5⟩ := stCert gates hC _ hP
  exact ⟨ℓ, τ, w, c₁ + c₂ + c₃, ⟨p1, p2, p3, p4 w, p5 k⟩, decidesGraph_mono le_rfl (by omega) s1, decidesGraph_mono le_rfl (by omega) s2,
    decidesGraph_mono le_rfl (by omega) s3, decidesGraph_mono le_rfl (by omega) d1,
    decidesColor_mono (Ms := COLOR k (core3 ℓ τ)) (k := k) le_rfl (by omega) k1⟩

/-- **`StTiedTM`.** For every δ > 0 and k ≥ 3 there are a family of circuits that tests the size and
is computed in polynomial time (`sizeGates`), and ℓ, τ, w, c such that each of the five deciders
with D = `core3 ℓ τ` itself has polynomial-time steps and decides its problem within c·2^{δn} steps,
and is simulated with polynomial overhead by a Turing machine with finite alphabets that decides the
problem within ⌊C·2^{δn}⌋ steps. -/
theorem stTiedTM : StTiedTM := by
  intro δ hδ k hk
  have h2 : δ / 2 ≤ δ := by linarith
  obtain ⟨ℓ, τ, w, c, ⟨p1, p2, p3, p4, p5⟩, s1, s2, s3, d1, k1⟩ :=
    stWithThreeSatMachine sizeGates 6 testsSize_sizeGates certGates_sizeGates (δ / 2) (by positivity) k hk
  exact ⟨sizeGates, 6, ℓ, τ, w, c, testsSize_sizeGates, certGates_sizeGates,
    ⟨p1, decidesGraph_mono h2 le_rfl s1, hostedFor_of hδ p1 s1⟩, ⟨p2, decidesGraph_mono h2 le_rfl s2, hostedFor_of hδ p2 s2⟩,
    ⟨p3, decidesGraph_mono h2 le_rfl s3, hostedFor_of hδ p3 s3⟩, ⟨p4, decidesGraph_mono h2 le_rfl d1, hostedFor_of hδ p4 d1⟩,
    ⟨p5, decidesColor_mono (Ms := COLOR k (core3 ℓ τ)) (k := k) h2 le_rfl k1, hostedColor_of (k := k) hδ p5 k1⟩⟩

/-- **The end theorem, first piece**: from the tied statement `StTiedTM`, taken as a hypothesis, the
statement `GraphProblems.CorGraphsDecide`: for every δ > 0, Independent Set, Clique, Vertex Cover,
Dominating Set and, for every k ≥ 3, k-Coloring are decided by Turing machines in time O(2^{δn}).
The Turing machines are those that the hypothesis gives (for the four problems on sets, those at k = 3);
nothing else about a machine is used. -/
theorem endFrom : StTiedTM → ThreeSatStatement := by
  intro hTied δ hδ
  obtain ⟨gates, a, ℓ, τ, w, c, -, -, ⟨-, -, h1⟩, ⟨-, -, h2⟩, ⟨-, -, h3⟩, ⟨-, -, h4⟩, -⟩ := hTied δ hδ 3 le_rfl
  refine ⟨decidesInTime_of_hosted h1, decidesInTime_of_hosted h2, decidesInTime_of_hosted h3, decidesInTime_of_hosted h4, fun k hk => ?_⟩
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, M, C, q, hf, -, hM⟩ := hTied δ hδ k hk
  exact ⟨M, C, hf, hM⟩

/-- **The end theorem**, with the statement `GraphProblems.CorGraphsDecide`: `endFrom` applied to
`stTiedTM`. Each of the five deciders asks the machine of Theorem 2 in its decision form
(`FromPrinted.SplitSat.core3`) whether a 3-CNF is satisfiable; apart from procedure Count inside
that machine, nothing counts satisfying assignments. -/
theorem decideFromThreeSat : ThreeSatStatement := endFrom stTiedTM

end FromPrinted.Sat3Graph

end
