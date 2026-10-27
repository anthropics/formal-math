/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import CountKSatRate.Interfaces
public import CountKSat.Poly
public import CountKSat.InOut
public import PaddedDescent.F.CertA
import PaddedDescent.F.CertNet
import PaddedDescent.Col.CertG
import PaddedDescent.F.CertSide
import PaddedDescent.F.CertGrid
import PaddedDescent.F.CertMark

/-! Polynomial-time lemmas (`PolyT`) for functions of `proof/consequences/CountKSatRate/Defs.lean`,
for every width k: one step of the counting tree with the threshold τ as data, one round of the walk
that
adds up and the walk itself, the formula of a node, the decoded input and the number of variables
written in it, exhaustive counting `bruteN k`, and the number of the padded input
with its value function as an arbitrary function of a context. The interface statement proved is
`StCertWalkS` of `proof/consequences/CountKSatRate/Interfaces.lean`. -/

public section

namespace CountKSatRate

open Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat CountKSat.Poly PaddedDescent PaddedDescent.F PaddedDescent.F.CertTop
open WidthK (theta)

namespace Cert

variable {α σ : Type} [Enc α]

/-- The two children of a node of the counting tree, jointly in τ and the node. -/
@[fun_prop] theorem polyT_stepCU (k : ℕ) {τ : α → ℕ} {s : α → CNode} (hτ : PolyT τ) (hs : PolyT s) :
    PolyT fun x => stepC (theta (τ x)) k (s x) := by
  unfold stepC; fun_prop

omit [Enc α] in
/-- `roundS` with its case distinctions written by eliminators. -/
theorem roundS_eq (step : σ → Option (σ × σ)) (val : σ → ℕ) (st : List σ × ℕ) :
    roundS step val st = st.1.head?.elim ([], st.2) fun s =>
      (step s).elim (st.1.tail, st.2 + val s) fun lh => (lh.1 :: lh.2 :: st.1.tail, st.2) := by
  obtain ⟨_ | ⟨s, r⟩, c⟩ := st
  · rfl
  · simp only [roundS, List.head?_cons, Option.elim_some, List.tail_cons]
    cases step s <;> rfl

/-- One round of the walk that adds up is polynomial-time, for a step function and a value function
that may depend on the context. -/
theorem polyT_roundS [Enc σ] {step : α → σ → Option (σ × σ)} {val : α → σ → ℕ} {st : α → List σ × ℕ}
    (h1 : PolyT fun p : α × σ => step p.1 p.2) (h2 : PolyT fun p : α × σ => val p.1 p.2) (h3 : PolyT st) :
    PolyT fun x => roundS (step x) (val x) (st x) := by
  simp only [roundS_eq]; fun_prop

/-- The formula of a node as `countM` gets it is computed in polynomial time. -/
theorem leafM_polyT : PolyT leafM := by unfold leafM sideU; fun_prop

/-- The number of the padded input, with the decoded input d, the pad, the threshold τ and the value
function as arbitrary functions of a context. -/
theorem numC_polyT_aux (hW : StCertWalkS) (k : ℕ) {d : α → List Unit × Fml} {pad : α → U} {τ : α → ℕ} {val : α → CNode → ℕ} (hd : PolyT d)
    (hp : PolyT pad) (hτ : PolyT τ) (hv : PolyT fun q : α × CNode => val q.1 q.2) :
    PolyT fun p => bif hasNil (d p).2 then 0 else walkS k (pad p) (τ p) (val p) (rootC (d p)) :=
  PolyT.cond' (PolyT.comp hasNil_polyT hd.snd) (PolyT.const 0)
    (hW k α pad τ val (fun p => rootC (d p)) hp hτ hv (PolyT.comp rootC_polyT hd))

/-- The number `bruteN k` with the decoded input d and the pad as arbitrary functions of a context. -/
theorem bruteN_polyT_aux {d : α → List Unit × Fml} {pad : α → U} (hd : PolyT d) (hp : PolyT pad) :
    PolyT fun p => ((rng (pad p) (2 ^ (d p).1.length)).filter fun y => satAt (d p).2 y).length := by
  have hf : PolyT fun q : α × ℕ => satAt (d q.1).2 q.2 := satAt_polyT (by fun_prop) (by fun_prop)
  fun_prop

end Cert

open Cert

/-- The walk that adds up is polynomial-time jointly in the pad, τ, the root and whatever the value
function depends on. -/
theorem stCertWalkS : StCertWalkS := by
  intro k α _ pad τ val r hp hτ hv hr
  have h := foldl_cap (pad := pad) (l := pad) (a := fun x => ([r x], 0))
    (g := fun x st _ => roundS (stepC (theta (τ x)) k) (val x) st) ([], 0) hp hp (by fun_prop)
    (polyT_roundS (step := fun p : α × (List CNode × ℕ) × Unit => stepC (theta (τ p.1)) k) (val := fun p => val p.1) (st := fun p => p.2.1)
      (by fun_prop) (by fun_prop) (by fun_prop))
  unfold walkS
  exact PolyT.snd h

/-- The decoded input is polynomial-time in the padded input. -/
theorem Cert.decU_pad_polyT (k : ℕ) : PolyT fun p : List Bool × U => decU k p.1 := PolyT.comp (stCertDecU k) PolyT.id'.fst

/-- The number of variables written in the input is at most the length of the input, and
polynomial-time. -/
theorem Cert.nK_unary (k : ℕ) : Unary fun p : List Bool × U => nK k p.1 := Unary.of_length (decU_pad_polyT k).fst

/-- Exhaustive counting with fuel is polynomial-time. -/
theorem Cert.bruteN_polyT (k : ℕ) : PolyT (bruteN k) := by
  have h := bruteN_polyT_aux (decU_pad_polyT k) (pad := fun p : List Bool × U => p.2) (by fun_prop)
  unfold bruteN nK
  exact h

end CountKSatRate
