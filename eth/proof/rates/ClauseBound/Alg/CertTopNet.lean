/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ClauseBound.Alg.TopNet
public import PaddedDescent.F.FuelCert

/-! # Any network on 3K⁸ nodes through a clique solver: polynomial time

The function `valS` of proof/rates/ClauseBound/Alg/TopNet.lean is polynomial-time (`PolyT`) jointly
in the pad, the index of the solver, the bounds Ub and P in unary and the context of the network
(`stCertValS`), if the rebalancing is. -/

public section

namespace ClauseBound.Alg.CertTopNet

open Groundwork Groundwork.Prog PaddedDescent PaddedDescent.F

variable {α : Type} [Enc α]

/-- The label length of the rebalanced instance is given in unary if K, g, Ub and P are. -/
theorem lamS_unary {K g Ub P : α → ℕ} (hK : Unary K) (hg : Unary g) (hU : Unary Ub) (hP : Unary P) :
    Unary fun x => lamS (K x) (g x) (Ub x) (P x) := by
  have hK' : PolyT K := hK.poly
  unfold lamS; fun_prop

/-- The value of a network through a clique solver is polynomial-time if the rebalancing with a
given label length is. -/
theorem stCertValS (hR : StCertRebalG) : StCertValS := by
  intro Idx _ S hS C _ F hF α _ pad i Ub P c hp hi hU hP hc
  have hK : Unary fun x => S.K (i x) := hS.K.comp hi
  have hg : Unary fun x => 3 * S.K (i x) ^ 8 := (Unary.const 3).mul (unary_pow_const hK 8)
  have hl : Unary fun x => lamS (S.K (i x)) (3 * S.K (i x) ^ 8) (Ub x) (P x) := lamS_unary hK hg hU hP
  have h1 := hR C F hF α pad _ _ _ c hp hK hg hl hc
  have h2 : PolyT fun q : α × PInst => S.run (pad q.1, i q.1, q.2) :=
    PolyT.comp hS.run (PolyT.prodMk (PolyT.comp hp PolyT.id'.fst) (PolyT.prodMk (PolyT.comp hi PolyT.id'.fst) PolyT.id'.snd))
  unfold valS
  exact PolyT.optionElim h1 (PolyT.const 0) h2

end ClauseBound.Alg.CertTopNet
