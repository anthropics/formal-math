/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import SparsifyThenCount.Defs
import SparsifyThenCount.CertTop
import UniformInK.Cert.Both
import ClauseBound.Alg.Decode
import ClauseBound.Alg.CertTop
import PaddedDescent.Col.CertG

/-! # The merged function is polynomial-time for every family of thresholds Θ that serves

`stCertBDG : StCertDG → StCertBDG`. The test `VariableBound.useMD`, which chooses between the two
branches, and the exponent `VariableBound.eBD` do not name the thresholds: they are those of
proof/variables/VariableBound. They are proved polynomial-time here (`useMD_polyT`, `eBD_polyT`),
from the test whether every variable occurs (`UniformInK.CertBoth.allOccU_polyT`) and the
certificates of the two exponents.
The certificates of the algorithm for the bound in m are those of
proof/rates/ClauseBound/Alg/CertTop.lean. -/

public section

namespace SparsifyThenCount

open Groundwork Groundwork.Prog PaddedDescent PaddedDescent.F CountKSat CountKSatRate ClauseBound.Alg ClauseBound.TopN ClauseBound.ParityChecks UniformInK UniformInK.CertBoth VariableBound

/-- The test that chooses the algorithm for the bound in m is polynomial-time, if the solver, `pick`
and `slU` are. -/
theorem useMD_polyT {Idx : Type} [Enc Idx] (S : Solver Idx) (hS : S.Poly) {pick : U → U × Idx} {slU : U → U} (hpick : PolyT pick) (hsl : PolyT slU) :
    PolyT (useMD S pick slU) := by
  have heD := eD_polyT S hS hpick hsl
  have heM := (CertTop.stCertM Decode.stCertDecM CertTop.stCertSatK certRebalG Idx S hS pick hpick).2
  have hd : PolyT fmlOf := Decode.stCertDecM.2
  have ha := allOccU_polyT
  obtain ⟨F, hF, hFe⟩ : ∃ F : List Bool → Fml, PolyT F ∧ ∀ x, (fmlOf x).2 = F x := ⟨_, hd.snd, fun _ => rfl⟩
  have e : useMD S pick slU = fun x =>
      allOccU x && decide (1 ≤ (F x).length) && decide (eM S pick x ≤ eD S pick slU x) := by
    funext x
    rw [useMD, hFe]
  rw [e]
  fun_prop

/-- The exponent function of the merged function is polynomial-time, if the solver, `pick` and `slU`
are. -/
theorem eBD_polyT {Idx : Type} [Enc Idx] (S : Solver Idx) (hS : S.Poly) {pick : U → U × Idx} {slU : U → U} (hpick : PolyT pick) (hsl : PolyT slU) :
    PolyT (eBD S pick slU) :=
  PolyT.cond' (useMD_polyT S hS hpick hsl) (CertTop.stCertM Decode.stCertDecM CertTop.stCertSatK certRebalG Idx S hS pick hpick).2 (eD_polyT S hS hpick hsl)

/-- For thresholds that serve, the merged function of (input, pad) and its exponent function of the
input are polynomial-time if the solver, `pick` and `slU` are; given that the algorithm for the
bound in n is (`StCertDG`). -/
theorem stCertBDG (h : StCertDG) : StCertBDG := by
  intro Θ Lc hΘ Idx _ S hS pick slU hpick hsl
  have hADG := h Θ Lc hΘ Idx S hS pick slU hpick hsl
  have hAM := (CertTop.stCertM Decode.stCertDecM CertTop.stCertSatK certRebalG Idx S hS pick hpick).1
  have h2 : PolyT fun p : List Bool × U => useMD S pick slU p.1 := PolyT.comp (useMD_polyT S hS hpick hsl) PolyT.id'.fst
  exact ⟨PolyT.cond' h2 hAM hADG, eBD_polyT S hS hpick hsl⟩

end SparsifyThenCount
