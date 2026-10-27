/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import StepSparsify.Defs
import StepSparsify.CalNumbers
import StepSparsify.CalLeaves
import StepSparsify.CertThCal
import SparsificationLemma.Cal.Thr
import SparsificationLemma.One
import SparsificationLemma.Side
import SparsificationLemma.Gen
import UniformInK.Cert.Sparsify
import CountKSat.Poly

/-! # Calabro's thresholds serve

This file proves `StServesCal` of proof/sparsification/StepSparsify/Defs.lean: first from
`StCertThCal`, the statement that Calabro's thresholds are polynomial-time (`stServesCal`), then
outright (`servesCal`), with the proof of that statement in
proof/sparsification/StepSparsify/CertThCal.lean. Throughout α = `alphaS k s` and τ = `tauOf s`.
The tree: Calabro's thresholds satisfy the four conditions `ThrC` with α in the role of τ
(`Cal.stThrCal`), k² ≤ α, and β₁ + … + β_{k−1} ≤ τ^(2k) (`stCalNumbers`); so the general theorem
`SparsificationLemma.stTreeG` applies with D = τ^(2k)·n.
Its bound on the number of leaves, a sum of binomial coefficients in D, is replaced by that of
`stCalLeaves`; the latter speaks of the tree that starts with the empty side list, which has as many
leaves (`SparsificationLemma.stSide`).
The hypothesis of `Serves.tree` that no clause of ψ contains a variable together with its negation
is not used.
The occurrences fit the code parameter by `stCalNumbers`.
The certificate is the twin of `thrList_polyT`, `polyT_pickKU`
(proof/sparsification/UniformInK/Cert/Sparsify.lean) and `polyT_stepCU`
(proof/sparsification/UniformInK/Cert/Walk.lean), with `StCertThCal` in the place of `thetaU_polyT`. -/

public section

namespace StepSparsify

open Finset Groundwork Groundwork.Sparsify WidthK.Prog CountKSat CountKSat.Poly PaddedDescent UniformInK UniformInK.CertSparsify SparsificationLemma

/-- The tree that starts with the n clauses xᵢ ∨ ¬xᵢ on the side list has as many leaves as the tree
that starts with the empty side list. -/
theorem length_leaves_rootC (θ : ℕ → ℕ) (k D n : ℕ) (ψ : PFml) :
    (leaves (stepC θ k) D (rootC (List.replicate n (), ψ))).length = (tree θ k D ψ).length := by
  rw [rootC, stSide, List.length_map, tree, root]

section
variable {α : Type} [Enc α]

/-- The list of the pairs (j, h), each with Calabro's threshold θ (j - h), is polynomial-time
jointly in k and s, both given in unary. -/
theorem thrListCal_polyT (hT : StCertThCal) {k s : α → ℕ} (hk : Unary k) (hs : Unary s) :
    PolyT fun x => (pairsK (k x)).map fun jh => (jh, thCal (k x) (s x) (jh.1 - jh.2)) := by
  have h1 := pairsK_polyT hk
  have h2 : PolyT fun p : α × ℕ × ℕ => thCal (k p.1) (s p.1) (min (p.2.1 - p.2.2) (k p.1)) :=
    hT (α × ℕ × ℕ) _ _ _ (hk.comp (h := fun p : α × ℕ × ℕ => p.1) (by fun_prop)) (hs.comp (h := fun p : α × ℕ × ℕ => p.1) (by fun_prop))
      ((hk.comp (h := fun p : α × ℕ × ℕ => p.1) (by fun_prop)).of_le (by have := hk.poly; fun_prop) fun p => Nat.min_le_right _ _)
  have h : PolyT fun x => (pairsK (k x)).map fun jh => (jh, thCal (k x) (s x) (min (jh.1 - jh.2) (k x))) := by fun_prop
  refine h.congr fun x => List.map_congr_left fun jh hjh => ?_
  rw [Nat.min_eq_left (by have := le_of_mem_pairsK hjh; omega)]

/-- The two children of a node of the counting tree with Calabro's thresholds are polynomial-time
jointly in k, s and the node, if k, 2^k and s are given in unary. -/
theorem polyT_stepCCal (hT : StCertThCal) {k s : α → ℕ} {x : α → CNode} (hk : Unary k) (h2 : Unary fun a => 2 ^ k a) (hs : Unary s) (hx : PolyT x) :
    PolyT fun a => stepC (thCal (k a) (s a)) (k a) (x a) := by
  have hp : PolyT fun a => pickK (thCal (k a) (s a)) (k a) (x a).1 := by
    simp only [pickK_eq_pickL]
    exact polyT_pickL (masks_polyT hk h2) (thrListCal_polyT hT hk hs) (by fun_prop)
  exact PolyT.optionMap (f := fun (a : α) (HP : PCl × PFml) => ((addP [HP.1] (x a).1, (x a).2), (addP HP.2 (x a).1, negU HP.1 ++ (x a).2)))
    (by fun_prop) hp

end

/-- Calabro's thresholds serve, if they are polynomial-time. -/
theorem stServesCal (hT : StCertThCal) : StServesCal where
  tree := by
    intro k n s hk hs ψ hψ _
    obtain ⟨n1, n2, n3, -⟩ := stCalNumbers k s hk hs
    have hD := Nat.mul_le_mul_right n n3
    obtain ⟨-, c2, c3, c4⟩ := stTreeG stExactlyOne stCountOfExactlyOne stOutputsSame k (alphaS k s) n (bsumU (tauOf s) k * n) (thCal k s)
      (Cal.betaC (alphaS k s)) hk n2 (Cal.stThrCal (alphaS k s) k n1) hD ψ hψ
    exact ⟨(length_leaves_rootC _ _ _ _ _).le.trans (stCalLeaves k n s _ ψ hk hD hψ), c2, c3, c4⟩
  par := fun k s hk hs => (stCalNumbers k s hk hs).2.2.2
  cert := fun _ _ _ _ _ hk h2 hs hx => polyT_stepCCal hT hk h2 hs hx

/-- Calabro's thresholds serve. -/
theorem servesCal : StServesCal := stServesCal (CertThCal.stCertThCal stAlphaS)

end StepSparsify
