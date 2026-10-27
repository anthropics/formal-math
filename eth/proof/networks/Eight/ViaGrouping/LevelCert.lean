/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Eight.ViaGrouping.LevelDefs
public import Eight.ViaGrouping.Bridge
public import Eight.Level.Cert

/-! # The algorithm of one level, on an algorithm for networks in the printed form, has polynomial-time steps

A step of a step machine in this development may be any polynomial-time function. Here: if the
pieces of Lemma 2, «computable in time poly(λ)», are computed in polynomial time (`Eight.StKeeps`)
and the function for Ψ is (`StPsiPoly`), then the row network and the column
network of ι, given as Definition 2(iii) asks (`levelProcs`), have P, P_a and c_{a,b} in unary and
four procedures with polynomial-time steps (`levelProcs_keepsP`); and the algorithm of one level
(`levelAlgP`) has polynomial-time steps if the algorithm for
networks that it calls has (`stLevelKeepsP_of`). The certificates of the loop, of the choice of the
network and of the division are those of proof/networks/Eight/Level/Cert.lean. -/

public section

namespace Eight.ViaGrouping

open Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F ClauseBound.Alg Stepped Eight.SecNetworks Eight.Level

/-- The row network and the column network of ι, given as Definition 2(iii) asks, have P = g³λ, P_a
and c_{a,b} in unary and four procedures with polynomial-time steps, for λ in unary. The test for
membership says yes without looking at the query. -/
theorem levelProcs_keepsP (h : Eight.StKeeps) (g : ℕ) (tr : Bool) {psi : ℕ → ℕ → PsiQ → ℤ} (hp : StPsiPoly psi) (C : Type) [HasSize C] [Enc C] [Carried C] (lam : C → ℕ)
    (R : Stepped (C × IQ) ℤ) (hl : Unary lam) (hR : Nonempty (IsPolyT R)) : KeepsP (levelProcs g tr psi lam R) :=
  keepsP_ofProcs (stNetKeeps_of h g tr C lam R hl hR) ((Unary.const (g ^ 3)).mul (hl.comp (h := fun c : C × ℕ => c.1) PolyT.id'.fst)) ⟨IsPolyT.ofFun (hp C lam hl)⟩

/-- The algorithm of one level has polynomial-time steps if the algorithm for networks has, and if
the pieces and the two functions for Ψ are computed in polynomial time. -/
theorem stLevelKeepsP_of (h : Eight.StKeeps) : StLevelKeepsP := by
  intro g psiR psiC NA hpR hpC hN C _ _ _ lam R hl hR
  obtain ⟨h1⟩ := hN _ _ (levelProcs_keepsP h g false hpR C lam R hl hR)
  obtain ⟨h2⟩ := hN _ _ (levelProcs_keepsP h g true hpC C lam R hl hR)
  have h3 := IsPolyT.ite (M := NA.app (levelProcs g false psiR lam R)) (N := NA.app (levelProcs g true psiC lam R)) (Level.Cert.useRowP_polyT (C := C) h g hl)
  have h4 := IsPolyT.sumRange (M := Stepped.ite (useRowP g lam) (NA.app (levelProcs g false psiR lam R)) (NA.app (levelProcs g true psiC lam R)))
    (Level.Cert.numPat8_polyT g hl)
  have h5 := IsPolyT.ofFun (Level.Cert.div_polyT (C := C) g hl)
  exact ⟨IsPolyT.bind⟩

end Eight.ViaGrouping
