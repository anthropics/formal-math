/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import PaddedDescent.F.CertTop
public import PaddedDescent.F.CertEval

/-! The function `A` of proof/rates/PaddedDescent/F/Prog.lean is polynomial-time (`certA`), given
the certificates of the rebalancing, of the descent through the levels, of
the brute force at the bottom and of the network of marks as hypotheses. -/

@[expose] public section

namespace PaddedDescent.F.CertTop

open Groundwork Groundwork.Prog Groundwork.Prog.Count Groundwork.Sparsify

variable {α : Type} [Enc α]

/-- The function `A` at any width k of the clauses, with the pad, the threshold τ, the schedule S,
the parameters q of the evaluations, the number R of layers (in unary) and the formula φ as
arbitrary functions of a context. -/
theorem A_polyT_aux (k : ℕ) (hV : StCertValF) (hM : StCertMark) (hA : StCertAdm) {S : α → List Lvl × U} {τ R : α → ℕ} {q : α → U × U × U × U}
    {φ : α → Fml} {pad : α → U} (hS : PolyT S) (hp : PolyT pad) (hτ : PolyT τ) (hq : PolyT q) (hR : Unary R) (hφ : PolyT φ) :
    PolyT fun p => bif hasNil (φ p) then false
      else walkF k (pad p) (τ p) (fun ψ => decide (0 < countM k (pad p) (S p) (q p) (R p) ψ)) (rootP (φ p)) :=
  PolyT.cond' (PolyT.comp hasNil_polyT hφ) (PolyT.const false)
    (certWalk k α pad τ (fun p ψ => decide (0 < countM k (pad p) (S p) (q p) (R p) ψ)) (fun p => rootP (φ p)) hp hτ
      (PolyT.decide_ltZ (by fun_prop)
        (CertEval.countM_polyT (pad := fun r : α × PFml => pad r.1) (S := fun r => S r.1) (p := fun r => q r.1) (R := fun r => R r.1)
          (ψ := fun r => r.2) k hV hM hA (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)))
      (polyT_rootP hφ))

/-- The function `A` is polynomial-time, given the certificates of the rebalancing, the descent, the
brute force at the bottom and the network of marks. -/
theorem certA (hR : StCertRebal) (hD : StCertDescend) (hB : StCertBrute) (hM : StCertMark) (hA : StCertAdm) : StCertA := by
  have hn : Unary fun p : List Bool × U => (Decode.dec p.1).1 := nOf_unary.comp (h := fun p : List Bool × U => p.1) (by fun_prop)
  have hdec : PolyT fun p : List Bool × U => decF p.1 := PolyT.comp decF_polyT (by fun_prop)
  have hp : PolyT fun p : List Bool × U => p.2 := by fun_prop
  have hS := schedF_polyT hp (depthOf_unary hn)
  have h := A_polyT_aux 3 (CertEval.certValF hR hD hB) hM hA (PolyT.prodMk hS.fst hS.snd.fst) hp (tauOf_unary hn).poly (markPar_polyT hn)
    (layersOf_unary hn) hdec
  unfold StCertA A
  exact h

end PaddedDescent.F.CertTop
