/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Enumerate.Defs
import SparsificationLemma.Side
import SparsificationLemma.One
import SparsificationLemma.Gen
import SparsificationLemma.Len
import SparsificationLemma.Geo.Thr
import SparsificationLemma.Geo.Tau
import SparsificationLemma.Geo.Eps
import UniformInK.Spars.Thresholds
import CountKSat.Poly
import CountKSatRate.Cert

/-! # Lemma 4 as an enumeration: proofs

Lemma 4 (cited): for every ε > 0 there is a constant M(ε) ≥ 1 such that for every 3-CNF φ on n
variables one can compute, in time 2^{εn} times a polynomial in n, at most 2^{εn} 3-CNFs on the same
variables, each with at most M(ε)·n clauses, such that φ is satisfiable if and only if at least one
of them is (the paper's Lemma 4 states more: every satisfying assignment of φ satisfies exactly one
of them).
This file proves four statements of proof/threesat/Enumerate/Defs.lean.
* `stProducedIsList`: the formulas that the walk produces are the list
  `SparsificationLemma.Geo.outTau 3 n τ φ` (from `SparsificationLemma.stOutputsSame`: the clauses xᵢ
  ∨ ¬xᵢ with which the side list of the root starts do not reach an output).
* `stSameTree`: the first components of the nodes are the nodes of the procedure without side lists
  (from `SparsificationLemma.stUnchanged`: the rule never looks at the side list).
* `stEnumeratesTau`: the structure `Enumerates ε (τ⁶) τ`, clause by clause of the lemma, for τ ≥ 24
  with (3/τ)·log₂(e·τ·τ⁶) ≤ ε. The number of formulas, their form and «satisfiable if and only if»
  come from the theorem on sparsification `SparsificationLemma.Geo.stThmTau` at width 3, said of the
  list and carried over by `stProducedIsList`; that the walk ends, and the size of its stack, come
  from `SparsificationLemma.stTreeG`, the statement on the tree; the number of moves is
  `Groundwork.Stepped.length_visits`; the two functions are polynomial-time by
  `CountKSat.Poly.certStepC` and `CountKSatRate.Cert.leafM_polyT`.
* `stEnumeration`: for every ε > 0, with τ = ⌈(24/q)³⌉ for a rational q with 0 < q < min(ε, 1)
  (`SparsificationLemma.Geo.stTauE`), and M(ε) = τ⁶. -/

public section

namespace Enumerate

open Finset Groundwork Groundwork.Prog Groundwork.Stepped Groundwork.Sparsify WidthK WidthK.Prog CountKSat CountKSatRate UniformInK PaddedDescent SparsificationLemma SparsificationLemma.Geo

/-- Line 2 of Algorithm 1: «for each Φ in the list that Lemma 4 computes from φ and ε do». The
formulas that the walk produces, in its order, are the list `outTau 3 n τ φ`. -/
theorem stProducedIsList : StProducedIsList := fun τ n φ => stOutputsSame (thetaU τ) 3 (bsumU τ 3 * n) n φ

/-- The walk that produces the outputs ψ ∪ 𝒩 and the walk of
`SparsificationLemma.TreeWalk.lemSparsification_walk`, which tests ψ, go through the same tree: the
rule never looks at the side list 𝒩 (`SparsificationLemma.stUnchanged`). This ties the enumeration
to the form of Lemma 4 that `SparsificationLemma.TreeWalk.lemSparsification_walk` treats; no
sentence of the paper corresponds to it. -/
theorem stSameTree : StSameTree := fun τ n φ => (stUnchanged (thetaU τ) 3 (depth τ n) (rootP φ) (taut (List.replicate n ()).length)).symm

/-- The passage from a leaf (ψ, 𝒩) to its output ψ ∪ 𝒩 takes polynomial time. (Lemma 4: «in time
2^{εn} times a polynomial in n».) -/
theorem out_polyT : PolyT SparsificationLemma.out := by
  have := Cert.leafM_polyT
  unfold SparsificationLemma.out; fun_prop

/-- What `SparsificationLemma.stTreeG` says of the tree that the walk goes through, for τ ≥ 24: the
procedure has stopped at every leaf, and the stack is small. (Lemma 4: time 2^{εn} times a
polynomial in n.) -/
theorem stops_and_stack {τ : ℕ} (hτ : 24 ≤ τ) (n : ℕ) (φ : PFml) (hφ : IsKCNF 3 n φ) :
    (∀ x ∈ leaves (rule τ) (depth τ n) (start n φ), rule τ x = none) ∧
    ∀ i, ((Sparsify.round (rule τ))^[i] ([start n φ], [])).1.length ≤ depth τ n + 1 ∧
      ∀ x ∈ ((Sparsify.round (rule τ))^[i] ([start n φ], [])).1,
        x.1.length ≤ φ.length * 2 ^ 3 ∧ x.2.length ≤ 2 * n ∧ (∀ C ∈ x.1, C.length ≤ 3 ∧ ∀ l ∈ C, l.1 < n) ∧ ∀ C ∈ x.2, C.length ≤ 2 ∧ ∀ l ∈ C, l.1 < n := by
  obtain ⟨-, c2, -, c4⟩ := stTreeG stExactlyOne stCountOfExactlyOne stOutputsSame 3 τ n (bsumU τ 3 * n) (thetaU τ) (betaSU τ) (by norm_num) (by omega)
    (stThrGeo 3 τ (by norm_num) (by omega)) (Nat.mul_le_mul_right _ (stBetaSumU τ 3 (by omega))) φ hφ
  exact ⟨fun x hx => (c2 x hx).1, c4⟩

/-- φ is satisfiable if and only if at least one of them is, from the property that every assignment
that satisfies φ satisfies exactly one formula of the list, and no other assignment any. -/
theorem sat_iff_of_exactlyOne {φ : PFml} {L : List PFml} (h : ∀ b, ExactlyOne b φ L) : (∃ b, SparsificationLemma.Sat b φ) ↔ ∃ Φ ∈ L, ∃ b, SparsificationLemma.Sat b Φ := by
  constructor
  · rintro ⟨b, hb⟩
    obtain ⟨i, hi, -⟩ := (h b).1 hb
    exact ⟨L.get i, List.get_mem _ _, b, hi⟩
  · rintro ⟨Φ, hΦ, b, hb⟩
    by_contra hno
    exact (h b).2 (fun hs => hno ⟨b, hs⟩) Φ hΦ hb

/-- **Lemma 4 as an enumeration, for every parameter that is large enough for ε**: in time 2^{εn}
times a polynomial in n, at most 2^{εn} 3-CNFs on the same variables, each with at most M(ε)·n
clauses, such that φ is satisfiable if and only if at least one of them is, with M(ε) = τ⁶. -/
theorem stEnumeratesTau : StEnumeratesTau := by
  intro τ ε hτ hε
  have hε' : (((3 : ℕ) : ℝ) / (τ : ℝ)) * Real.logb 2 (Real.exp 1 * (τ : ℝ) * (bsumU τ 3 : ℝ)) ≤ ε := by rw [Nat.cast_ofNat]; exact hε
  have hT := fun (n : ℕ) (φ : PFml) (hφ : IsKCNF 3 n φ) => stThmTau 3 n τ ε φ (by norm_num) (by omega) hε' hφ
  refine ⟨fun n φ hφ => (stops_and_stack hτ n φ hφ).1, fun n φ hφ => ?_, fun n φ hφ Φ hΦ => ?_, fun n φ hφ => ?_, fun n φ => ?_,
    Poly.certStepC (thetaU τ) 3, out_polyT, fun n φ hφ => (stops_and_stack hτ n φ hφ).2⟩
  · rw [stProducedIsList]
    exact (hT n φ hφ).2.2.1
  · rw [stProducedIsList] at hΦ
    obtain ⟨-, t2, -, -, t5⟩ := hT n φ hφ
    exact ⟨(t2 Φ hΦ).1, (t2 Φ hΦ).2, stLenOfOcc 3 n (τ ^ 6) Φ (t2 Φ hΦ).1 (t5 Φ hΦ)⟩
  · rw [stProducedIsList]
    exact sat_iff_of_exactlyOne (hT n φ hφ).2.2.2.1
  · rw [produced, List.length_map]
    exact length_visits (rule τ) (depth τ n) (start n φ) []

/-- **Lemma 4 as an enumeration.** For every ε > 0 there is a constant M(ε) ≥ 1 such that for every
3-CNF φ on n variables one can compute, in time 2^{εn} times a polynomial in n, at most 2^{εn}
3-CNFs on the same variables, each with at most M(ε)·n clauses, such that φ is satisfiable if and
only if at least one of them is (the paper's Lemma 4 states more: every satisfying assignment of φ
satisfies exactly one of them). -/
theorem stEnumeration : StEnumeration := by
  intro ε hε
  obtain ⟨q, hq0, hq1⟩ := exists_rat_btwn (lt_min hε one_pos)
  have h0 : 0 < q := by exact_mod_cast hq0
  have h1 : q ≤ 1 := by exact_mod_cast (hq1.trans_le (min_le_right _ _)).le
  obtain ⟨a, b, -⟩ := stTauE 3 q (by norm_num) h0 h1
  rw [Nat.cast_ofNat] at b
  exact ⟨tauE 3 q ^ 6, tauE 3 q, Nat.one_le_pow _ _ (by omega), stEnumeratesTau (tauE 3 q) ε (by omega) (b.trans (hq1.trans_le (min_le_left _ _)).le)⟩

end Enumerate
