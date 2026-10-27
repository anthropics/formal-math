/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Complement.Defs
import Complement.Sets
import GraphProblems.Read
import GraphProblems.Sets
import GraphProblems.Cert
import Mathlib.Tactic

/-! # Section 7, proof of Corollary 7: cliques and vertex covers are counted with the ONE formula for independent sets

«Add the clause {¬x_u, ¬x_v} for each edge uv; Corollary 6 then counts the independent sets of size
s. The cliques of size s are the independent sets of size s of the complement graph, and the vertex
covers of size s are the complements of the independent sets of size n − s.» (proof of Corollary 7)
* `stIndepAlone`: the formula for independent sets is computed in polynomial time, has width 2,
  variables below n and at most n² clauses. It is proved from the lemmas of
  proof/consequences/GraphProblems/ on formulas with one clause per chosen pair
  (`GraphProblems.Sets.shaped_pairs`, `GraphProblems.pairs_polyT`), not from the bundled statements
  that also speak of the formulas for cliques and vertex covers.
* `stComplCert`, `stReadersCert`: the matrix of the complement graph and the two readers are
  computed in polynomial time.
* `stReaders`: what the readers return on `codeWith G s`, and what it counts.
* `stCounts`: every machine that counts with a prescribed number of true variables, put after the
  readers, counts cliques and vertex covers, within the same number of steps.
* `stFromSized`, `stFromGamma_of`: the same with the machine of `GraphProblems.StSized`, and with «Γ
  beside the formula, then E». -/

public section

namespace Complement

open Groundwork Groundwork.Prog CountKSat GraphProblems

/-- The formula for independent sets alone: it is computed in polynomial time from (n in unary,
matrix); it has at most 2 literals per clause, variables below n, and at most n² clauses. -/
theorem stIndepAlone : StIndepAlone := by
  have hu : Unary fun a : List Unit × List Bool => a.1.length := Unary.of_length (by fun_prop)
  have hp : PolyT fun a : List Unit × List Bool => pairs a.1.length := pairs_polyT hu
  refine ⟨?_, fun n m => Sets.shaped_pairs n _ _⟩
  unfold indepF
  fun_prop

/-- The matrix of the complement graph is computed in polynomial time from (n in unary, matrix). -/
theorem stComplCert : StComplCert := by
  have hu : Unary fun a : List Unit × List Bool => a.1.length := Unary.of_length (by fun_prop)
  have hp : PolyT fun a : List Unit × List Bool => pairs a.1.length := pairs_polyT hu
  unfold StComplCert complMatrix
  fun_prop

/-- The two readers are polynomial-time, with any polynomial-time function r in the place of
`read2`. -/
theorem readers_aux {r : List Bool → List Unit × ℕ × List Bool} (hr : PolyT r) :
    PolyT (fun x => ((r x).1, (r x).2.1, indepF (r x).1.length (complMatrix (r x).1.length (r x).2.2))) ∧
      PolyT (fun x => ((r x).1, (r x).1.length - (r x).2.1, indepF (r x).1.length (r x).2.2)) := by
  have hI := stIndepAlone.1
  have hC : PolyT fun a : List Unit × List Bool => complMatrix a.1.length a.2 := stComplCert
  have h1 : PolyT fun x : List Bool => complMatrix (r x).1.length (r x).2.2 :=
    PolyT.comp (g := fun x : List Bool => ((r x).1, (r x).2.2)) hC (by fun_prop)
  have h2 : PolyT fun x : List Bool => indepF (r x).1.length (complMatrix (r x).1.length (r x).2.2) :=
    PolyT.comp (g := fun x : List Bool => ((r x).1, complMatrix (r x).1.length (r x).2.2)) hI (PolyT.prodMk (by fun_prop) h1)
  have h3 : PolyT fun x : List Bool => indepF (r x).1.length (r x).2.2 :=
    PolyT.comp (g := fun x : List Bool => ((r x).1, (r x).2.2)) hI (by fun_prop)
  exact ⟨PolyT.prodMk (by fun_prop) (PolyT.prodMk (by fun_prop) h2), PolyT.prodMk (by fun_prop) (PolyT.prodMk (by fun_prop) h3)⟩

/-- The two readers are polynomial-time. -/
theorem stReadersCert : StReadersCert := readers_aux stCertRead.2

/-- What the two readers hand over counts cliques and vertex covers: on `codeWith G s`, s ≤ n,
`readClique` returns (n in unary, s, the formula for independent sets of the complement graph),
whose satisfying assignments with s true variables are as many as the cliques of size s; `readCover`
returns (n in unary, n − s, the formula for independent sets of G), whose satisfying assignments
with n − s true variables are as many as the vertex covers of size s. -/
theorem stReaders : StReaders := fun n G s hs => by
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · simp [readClique, stRead2 n G s, stComplMatrix n G]
  · rw [stIndep n Gᶜ s, (stCliques n G s).2]
  · simp [readCover, stRead2 n G s]
  · rw [stIndep n G (n - s), (stCovers n G s hs).2]

/-- **For every machine Z that counts with a prescribed number of true variables**, at width 2 with
the exponent δ: Z after `readClique` returns the number of cliques of size s, and Z after
`readCover` the number of vertex covers of size s, within the same number of steps. -/
theorem stCounts : StCounts := fun Z δ c hZ n G s hs => by
  obtain ⟨⟨r1, c1⟩, r2, c2⟩ := stReaders n G s hs
  constructor
  · obtain ⟨hsh, hl⟩ := stIndepAlone.2 n (matrix Gᶜ)
    obtain ⟨T, hr, hT⟩ := hZ n s _ hs hsh
    rw [← r1, c1] at hr
    exact ⟨T, (Stepped.mapIn_runs hr).mono le_rfl (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) c)), hT⟩
  · obtain ⟨hsh, hl⟩ := stIndepAlone.2 n (matrix G)
    obtain ⟨T, hr, hT⟩ := hZ n (n - s) _ (Nat.sub_le n s) hsh
    rw [← r2, c2] at hr
    exact ⟨T, (Stepped.mapIn_runs hr).mono le_rfl (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) c)), hT⟩

/-- **With the machines named.** From the interface `GraphProblems.StSized`: for every δ > 0 one
machine Z, put after the two readers, has polynomial-time steps and counts the cliques and the
vertex covers of size s ≤ n within c·2^{δn} steps. -/
theorem stFromSized : StFromSized := fun hS δ hδ => by
  obtain ⟨Z, ⟨hZp⟩, c, hc⟩ := hS 2 δ hδ
  exact ⟨Z, ⟨IsPolyT.mapIn stReadersCert.1⟩, ⟨IsPolyT.mapIn stReadersCert.2⟩, c, stCounts Z δ c hc⟩

/-- **The route from end to end, counted in steps**, from the statement `SizeCircuit.StSizedBy` on
the machine «Γ beside the formula, then E», taken at width 2: that machine, put after the reader of
the formula for independent sets, after `readClique` and after `readCover`, returns the numbers of
independent sets, cliques and vertex covers of size s ≤ n within c'·2^{δn} steps. -/
theorem stFromGamma_of (h : SizeCircuit.StSizedBy) : StFromGamma := fun gates a ht δ δE hδ h0 hle E c hE => by
  obtain ⟨c', hc'⟩ := h gates a ht 2 δ δE hδ h0 hle E c hE
  refine ⟨c', fun n G s hs => ⟨?_, stCounts _ δ c' hc' n G s hs⟩⟩
  obtain ⟨hsh, hl⟩ := stIndepAlone.2 n (matrix G)
  obtain ⟨T, hr, hT⟩ := hc' n s _ hs hsh
  have hread : readF indepF (codeWith G s) = (List.replicate n (), s, indepF n (matrix G)) := by simp [readF, stRead2 n G s]
  rw [← hread, stIndep n G s] at hr
  exact ⟨T, (Stepped.mapIn_runs hr).mono le_rfl (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) c')), hT⟩

end Complement
