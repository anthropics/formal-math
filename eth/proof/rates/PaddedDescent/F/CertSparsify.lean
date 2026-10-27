/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import PaddedDescent.F.Interfaces
public import PaddedDescent.F.FuelCert
public import SparsifyWidthK.Poly.Sparsify

/-! Polynomial-time certificates (`PolyT`) for the walk of the sparsification tree in which the
threshold τ is part of the DATA and not a constant of the
machine. The step is `stepK (theta τ) k` of proof/sparsification/SparsifyWidthK. Its certificate in
proof/sparsification/SparsifyWidthK/Poly/Sparsify.lean is for fixed thresholds. There `pickK_eq`
writes the
choice of the rule as a search along the list of the pairs (j, h), each with its threshold θ (j -
h). Here that list depends on τ, but its length does not, and each
of its members is polynomial-time in τ (`polyT_theta`). This gives `polyT_stepKU`, the two children
of a node, for every width k.
One round `roundB` of the depth-first walk follows. -/

public section

namespace PaddedDescent.F.CertTop

open Groundwork Groundwork.Sparsify
open WidthK (thrPair theta)
open WidthK.Prog (pairsK pickK pickK_eq stepK)

variable {α σ : Type} [Enc α] [Enc σ]

omit [Enc σ] in
/-- A list of fixed length whose members are polynomial-time functions of x is a polynomial-time
function of x. -/
theorem polyT_map_fixed {β γ : Type} [Enc γ] (l : List β) {f : β → α → γ} (hf : ∀ b, PolyT (f b)) :
    PolyT fun x => l.map fun b => f b x := by
  induction l with
  | nil => exact PolyT.const []
  | cons b l ih =>
    have := hf b
    simp only [List.map_cons]; fun_prop

omit [Enc σ] in
/-- For every fixed i, the pair (θ i, 2 + β 1 + … + β i) is polynomial-time in τ. -/
theorem polyT_thrPair (i : ℕ) {τ : α → ℕ} (hτ : PolyT τ) : PolyT fun x => thrPair (τ x) i := by
  induction i with
  | zero => exact PolyT.const (1, 2)
  | succ i ih => simp only [thrPair]; fun_prop

omit [Enc σ] in
/-- For every fixed i, the threshold θ i is polynomial-time in τ. -/
@[fun_prop] theorem polyT_theta (i : ℕ) {τ : α → ℕ} (hτ : PolyT τ) : PolyT fun x => theta (τ x) i := by
  have := polyT_thrPair i hτ
  unfold theta; fun_prop

omit [Enc σ] in
/-- The choice of the heart and its petals at a node is polynomial-time jointly in τ and the
formula. -/
@[fun_prop] theorem polyT_pickKU (k : ℕ) {τ : α → ℕ} {s : α → PFml} (hτ : PolyT τ) (hs : PolyT s) :
    PolyT fun x => pickK (theta (τ x)) k (s x) := by
  have hl : PolyT fun x => (pairsK k).map fun jh => (jh, theta (τ x) (jh.1 - jh.2)) :=
    polyT_map_fixed (pairsK k) (f := fun jh x => (jh, theta (τ x) (jh.1 - jh.2))) fun jh => by fun_prop
  simp only [pickK_eq]; fun_prop

omit [Enc σ] in
/-- The two children of a node of the sparsification tree, jointly in τ and the formula. -/
@[fun_prop] theorem polyT_stepKU (k : ℕ) {τ : α → ℕ} {s : α → PFml} (hτ : PolyT τ) (hs : PolyT s) :
    PolyT fun x => stepK (theta (τ x)) k (s x) := by
  unfold stepK; fun_prop

omit [Enc σ] in
/-- `roundB` with its case distinctions written by eliminators. -/
theorem roundB_eq (step : σ → Option (σ × σ)) (test : σ → Bool) (st : List σ × Bool) :
    roundB step test st = st.1.head?.elim ([], st.2) fun s =>
      (step s).elim (st.1.tail, test s || st.2) fun lh => (lh.1 :: lh.2 :: st.1.tail, st.2) := by
  obtain ⟨_ | ⟨s, r⟩, b⟩ := st
  · rfl
  · simp only [roundB, List.head?_cons, Option.elim_some, List.tail_cons]
    cases step s <;> rfl

/-- One round of the depth-first walk is polynomial-time, for a step function and a test that may
depend on the context. -/
theorem polyT_roundB {step : α → σ → Option (σ × σ)} {test : α → σ → Bool} {st : α → List σ × Bool}
    (h1 : PolyT fun p : α × σ => step p.1 p.2) (h2 : PolyT fun p : α × σ => test p.1 p.2) (h3 : PolyT st) :
    PolyT fun x => roundB (step x) (test x) (st x) := by
  simp only [roundB_eq]; fun_prop

end PaddedDescent.F.CertTop
