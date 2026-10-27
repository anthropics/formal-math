/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import SparsificationLemma.Mach.Walk
public import UniformInK.Cert.Walk
import ClauseBound.Alg.Decode
import ClauseBound.ParityChecks.CertLib

/-! # The function that writes the outputs is polynomial-time in (input, pad)

This file proves `polyT_BL : PolyT BL` and `polyT_eL : PolyT eL` (definitions in
proof/sparsification/SparsificationLemma/Mach/Walk.lean). These are the two hypotheses of the
padding machine `CountKSatRate.StPaddedW`.
The proof for one round of the walk follows `CountKSatRate.Cert.polyT_roundS`; the whole walk needs
the width k and 2^k given in unary.
In `BL` the width is cut off at ⌊log₂(length of the pad)⌋, so 2^k is at most the length of the pad. -/

public section

namespace SparsificationLemma.Mach.Cert

open Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat CountKSat.Poly CountKSatRate CountKSatRate.Cert UniformInK PaddedDescent PaddedDescent.F ClauseBound.Alg

variable {α σ : Type} [Enc α]

omit [Enc α] in
/-- `round` with its case distinctions written by eliminators. -/
theorem round_eq (step : σ → Option (σ × σ)) (st : List σ × List σ) :
    Sparsify.round step st = st.1.head?.elim ([], st.2) fun s =>
      (step s).elim (st.1.tail, s :: st.2) fun lh => (lh.1 :: lh.2 :: st.1.tail, st.2) := by
  obtain ⟨_ | ⟨s, r⟩, c⟩ := st
  · rfl
  · simp only [Sparsify.round, List.head?_cons, Option.elim_some, List.tail_cons]
    cases step s <;> rfl

/-- One round of the collecting walk is polynomial-time, for a step function that may depend on the
context. -/
theorem polyT_round [Enc σ] {step : α → σ → Option (σ × σ)} {st : α → List σ × List σ}
    (h1 : PolyT fun p : α × σ => step p.1 p.2) (h3 : PolyT st) : PolyT fun x => Sparsify.round (step x) (st x) := by
  simp only [round_eq]; fun_prop

/-- The collecting walk is polynomial-time jointly in k, the pad, τ and the root, if k and 2^k are
given in unary. -/
theorem polyT_walkL {k : α → ℕ} {pad : α → U} {τ : α → ℕ} {r : α → CNode} (hk : Unary k) (h2 : Unary fun x => 2 ^ k x) (hp : PolyT pad) (hτ : PolyT τ)
    (hr : PolyT r) : PolyT fun t => walkL (k t) (pad t) (τ t) (r t) := by
  have hs : PolyT fun q : (α × (List CNode × List CNode) × Unit) × CNode => stepC (thetaU (τ q.1.1)) (k q.1.1) q.2 :=
    CertWalk.polyT_stepCU (hk.comp (h := fun q : (α × (List CNode × List CNode) × Unit) × CNode => q.1.1) (by fun_prop))
      (h2.comp (h := fun q : (α × (List CNode × List CNode) × Unit) × CNode => q.1.1) (by fun_prop)) (by fun_prop) (by fun_prop)
  have h := foldl_cap (pad := pad) (l := pad) (a := fun x => ([r x], ([] : List CNode)))
    (g := fun x st _ => Sparsify.round (stepC (thetaU (τ x)) (k x)) st) ([], []) hp hp (by fun_prop)
    (polyT_round (step := fun p : α × (List CNode × List CNode) × Unit => stepC (thetaU (τ p.1)) (k p.1)) (st := fun p => p.2.1) hs (by fun_prop))
  unfold walkL
  exact PolyT.reverse (PolyT.snd h)

/-- The code of a number, cut off at the length of the pad, is polynomial-time. -/
theorem polyT_codeNatP {pad : α → U} {v : α → ℕ} (hp : PolyT pad) (hv : PolyT v) : PolyT fun x => codeNatP (pad x) (v x) := by
  unfold codeNatP; fun_prop

/-- The code of a clause, cut off, is polynomial-time. -/
theorem polyT_codeClP {pad : α → U} {C : α → PCl} (hp : PolyT pad) (hC : PolyT C) : PolyT fun x => codeClP (pad x) (C x) := by
  have h : PolyT fun p : α × PLit => codeNatP (pad p.1) p.2.1 := polyT_codeNatP (by fun_prop) (by fun_prop)
  unfold codeClP codeLitP; fun_prop

/-- The code of a formula, cut off, is polynomial-time. -/
theorem polyT_codeFmlP {pad : α → U} {ψ : α → PFml} (hp : PolyT pad) (hψ : PolyT ψ) : PolyT fun x => codeFmlP (pad x) (ψ x) := by
  have h : PolyT fun p : α × PCl => codeClP (pad p.1) p.2 := polyT_codeClP (by fun_prop) (by fun_prop)
  unfold codeFmlP; fun_prop

/-- The code of a list of formulas, cut off, is polynomial-time. -/
theorem polyT_codeP {pad : α → U} {L : α → List PFml} (hp : PolyT pad) (hL : PolyT L) : PolyT fun x => codeP (pad x) (L x) := by
  have h : PolyT fun p : α × PFml => codeFmlP (pad p.1) p.2 := polyT_codeFmlP (by fun_prop) (by fun_prop)
  unfold codeP; fun_prop

/-- The precision written in the input is given in unary. -/
theorem unary_sL : Unary sL := Unary.of_length Decode.kOf_polyT

/-- The width written in the input is given in unary. -/
theorem unary_kL : Unary kL := Unary.of_length (PolyT.comp (f := kOf) (g := restOf) Decode.kOf_polyT Decode.restOf_polyT)

/-- The number of variables and the formula written in the input are read in polynomial time. -/
theorem polyT_dL : PolyT dL := PolyT.comp (f := fmlOf) (g := restOf) Decode.stCertDecM.2 Decode.restOf_polyT

/-- The exponent of the length of the pad is polynomial-time. -/
theorem polyT_eL : PolyT eL := by
  have h1 : PolyT fun x : List Bool => 2 ^ sL x := pow_polyT (PolyT.const 2) unary_sL
  have h2 : PolyT fun x : List Bool => (dL x).1.length := (Unary.of_length polyT_dL.fst).poly
  have h3 : PolyT fun x : List Bool => Nat.size x.length := PolyT.size' (Unary.of_length PolyT.id').poly
  exact (((PolyT.div h2 h1).add unary_kL.poly).add ((PolyT.const 3).mul h3)).add (PolyT.const 9)

/-- The function that writes the outputs is polynomial-time in (input, pad). -/
theorem polyT_BL : PolyT BL := by
  have hk : Unary fun p : List Bool × U => kL p.1 := unary_kL.comp PolyT.id'.fst
  have hlen : Unary fun p : List Bool × U => p.2.length := Unary.of_length PolyT.id'.snd
  have hc : Unary fun p : List Bool × U => min (kL p.1) (Nat.log 2 p.2.length) :=
    hk.of_le (PolyT.min' hk.poly (ClauseBound.ParityChecks.CertLib.log_polyT hlen.poly)) fun _ => min_le_left _ _
  have h2 : Unary fun p : List Bool × U => 2 ^ min (kL p.1) (Nat.log 2 p.2.length) :=
    (hlen.add (Unary.const 1)).of_le (pow_polyT (PolyT.const 2) hc) fun p =>
      (Nat.pow_le_pow_right (by norm_num) (min_le_right _ _)).trans (by
        rcases Nat.eq_zero_or_pos p.2.length with h | h
        · simp [h]
        · exact (Nat.pow_log_le_self 2 (by omega)).trans (Nat.le_succ _))
  have hs : Unary fun p : List Bool × U => 4 * sL p.1 + 17 := ((Unary.const 4).mul (unary_sL.comp PolyT.id'.fst)).add (Unary.const 17)
  have hτ : PolyT fun p : List Bool × U => tauOf (sL p.1) := by
    unfold tauOf
    exact pow_polyT (PolyT.const 2) hs
  have hr : PolyT fun p : List Bool × U => rootC (dL p.1) := PolyT.comp rootC_polyT (PolyT.comp polyT_dL PolyT.id'.fst)
  have hw := polyT_walkL hc h2 (pad := fun p : List Bool × U => p.2) PolyT.id'.snd hτ hr
  have hl : PolyT out := by
    have := leafM_polyT
    unfold out; fun_prop
  unfold BL
  exact polyT_codeP PolyT.id'.snd (by fun_prop)

end SparsificationLemma.Mach.Cert
