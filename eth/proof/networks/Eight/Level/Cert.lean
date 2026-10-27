/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Eight.Level.Defs
public import ClauseBound.Alg.CertGridG
public import ClauseBound.Alg.CertLevel
public import ToTuring.Poly.GridSide

/-! # Polynomial-time steps for the networks and functions of one level

This file treats the pieces of Lemma 2 from the eight-square identity. A step of a step machine of
this development may be any polynomial-time function. Here: if the pieces of Lemma 2, «computable in
time poly(λ)», are computed in polynomial time
(`Eight.StKeeps`), then the row network and the column network of ι, given by procedures
(`levelNet`), have lengths of states and labels in unary and procedures with polynomial-time steps
(`stNetKeeps_of`); and some functions used by the algorithm of one
level (`levelAlg`) besides its calls (the count of functions ι, the choice of the network with the
smaller total, the final division by 2^{t|ℛ|}) are polynomial-time (namespace `Cert`). The
certificates of the plain functions come from proof/rates/ClauseBound/Alg/CertGridG.lean and
CertLevel.lean; the procedure for the
weights and its certificate come from the imported files. -/

public section

namespace Eight.Level

open Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F ClauseBound.Alg Stepped

namespace Cert

variable {C : Type} [Enc C] {lam : C → ℕ}

/-- t = ⌈λ/3⌉ in unary, for λ in unary. -/
theorem tOf_unary (hl : Unary lam) : Unary fun c => tOf (lam c) := by unfold tOf; fun_prop

/-- The number (t + 1)^{|ℛ|} of functions ι is polynomial-time, for λ in unary. -/
theorem numPat8_polyT (g : ℕ) (hl : Unary lam) : PolyT (numPat8 g lam) :=
  pow_polyT ((tOf_unary hl).add (Unary.const 1)).poly (Unary.const (nRect g))

/-- The choice of the network with the smaller total is polynomial-time, for λ in unary. -/
theorem useRowP_polyT (h : StKeeps) (g : ℕ) (hl : Unary lam) : PolyT (useRowP g lam) := by
  have hl' : Unary fun x : C × ℕ => lam x.1 := hl.comp PolyT.id'.fst
  unfold useRowP
  exact PolyT.decide_le
    (CertGridG.totalG_unary h (Unary.const g) (Unary.const g) (PolyT.const false) (Unary.const 0) hl' PolyT.id'.snd).poly
    (CertGridG.totalG_unary h (Unary.const g) (Unary.const g) (PolyT.const true) (Unary.const 0) hl' PolyT.id'.snd).poly

/-- The final division by 2^{t|ℛ|} is polynomial-time, for λ in unary. -/
theorem div_polyT (g : ℕ) (hl : Unary lam) : PolyT fun p : C × ℤ => p.2 / ((2 ^ (tOf (lam p.1) * nRect g) : ℕ) : ℤ) :=
  CertLevel.divZ_polyT PolyT.id'.snd (pow_polyT (PolyT.const 2) (((tOf_unary hl).comp PolyT.id'.fst).mul (Unary.const (nRect g))))

/-- A value of a factor of the network of ι is polynomial-time, for λ in unary. -/
theorem factor_polyT (h : StKeeps) (g : ℕ) (tr : Bool) (hl : Unary lam) :
    PolyT fun x : (C × ℕ) × FQ => gridFf eightF [] g g tr 0 (lam x.1.1) x.1.2 x.2 :=
  CertGridG.gridFf_polyT h (PolyT.const []) (Unary.const g) (Unary.const g) (PolyT.const tr) (Unary.const 0) (hl.comp PolyT.id'.fst.fst)
    PolyT.id'.fst.snd PolyT.id'.snd

end Cert

/-- The row network and the column network of ι, given by procedures, have lengths in unary and
procedures with polynomial-time steps, if the pieces are computed in polynomial time. -/
theorem stNetKeeps_of (h : StKeeps) : StNetKeeps := fun g tr C _ _ _ _ _ hl ⟨_⟩ =>
  { n := (Unary.const (nMemb g g tr * (g * g))).mul (hl.comp (h := fun p : (C × ℕ) × ℕ => p.1.1) PolyT.id'.fst.fst)
    cap := CertGridG.capG_unary h (Unary.const g) (Unary.const g) (PolyT.const tr) (Unary.const 0)
      (hl.comp (h := fun p : (C × ℕ) × ℕ × ℕ => p.1.1) PolyT.id'.fst.fst) PolyT.id'.fst.snd PolyT.id'.snd.fst PolyT.id'.snd.snd
    W := ⟨IsPolyT.sideWP g tr hl.poly⟩
    f := ⟨IsPolyT.ofFun (Cert.factor_polyT h g tr hl)⟩ }

end Eight.Level
