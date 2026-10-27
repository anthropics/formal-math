/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import VariableBound.Top.Defs
import VariableBound.Net.CertEv
import UniformInK.Cert.Top
import ClauseBound.ParityChecks.CertTopOL
import ClauseBound.Alg.Decode

/-! # The exponents of the bound in n and the plan are polynomial-time

This file belongs to Appendix D, the bound in the number n of variables. It is the twin of
proof/sparsification/UniformInK/Cert/Top.lean, whose lemmas on β and on 2^β are used as they are.
The
width k is read from the input, in unary, so every parameter is shown to be given in unary, or to be
polynomial-time, jointly in k, n and s in unary. What differs from the twin: the bounds U, P, B
of Step 3 (`UbD`, `PbD`, `BbD`; in unary by proof/variables/VariableBound/Net/CertEv.lean); the
entries of the networks have up to B = `BbD k n` bits (in
proof/sparsification/UniformInK/Cert/Top.lean B is 0), so the exponent of the networks is
certified for B in unary (`needNetC_polyT`); the exponent for everything else is the formula
`restD`, with the bit lengths of the bounds for the number of objects and for the length of the list
of checks (`restD_polyT`); the plan (`planAtD_polyT`) has three tests. -/

public section

namespace VariableBound.CertTop

open Groundwork Groundwork.Prog PaddedDescent PaddedDescent.F PaddedDescent.F.CertTop PaddedDescent.F.CertEval CountKSatRate CountKSatRate.Cert ClauseBound.Alg ClauseBound.Alg.CertTop
open ClauseBound.TopN ClauseBound.ParityChecks UniformInK UniformInK.CertTop VariableBound.Net VariableBound.Net.CertEv
open ClauseBound.TopN.Cert (lamS_unary)
open ClauseBound.ParityChecks.CertTopOL (LD_polyT)

variable {α : Type} [Enc α]

/-! ### The exponent for everything but the networks -/

section par
variable {k K n s : α → ℕ}

/-- The formula of the exponent for everything but the networks is polynomial-time when every number
in it is. -/
theorem restD_aux {Z₁ Z₂ B z q : α → ℕ} (hk : PolyT k) (hK : PolyT K) (h1 : PolyT Z₁) (h2 : PolyT Z₂) (hB : PolyT B) (hz : PolyT z) (hn : PolyT n) (hq : PolyT q) :
    PolyT fun x => 3 * K x ^ 8 * (3 * K x ^ 8) * 2 * Z₁ x + Z₂ x + (n x / q x + 2) + (B x + 5 * k x + 10 + (k x + 3) * z x) := by
  have h8 : PolyT fun x => 3 * K x ^ 8 := (PolyT.const 3).mul (hK.pow_const 8)
  exact (((((h8.mul h8).mul (PolyT.const 2)).mul h1).add h2).add
    ((PolyT.div hn hq).add (PolyT.const 2))).add (((hB.add ((PolyT.const 5).mul hk)).add (PolyT.const 10)).add ((hk.add (PolyT.const 3)).mul hz))

/-- The exponent for everything but the networks is polynomial-time if k, K, n and s are given in
unary. -/
theorem restD_polyT (hk : Unary k) (hK : Unary K) (hn : Unary n) (hs : Unary s) : PolyT fun x => restD (k x) (K x) (n x) (s x) := by
  have hD := blockU_unary hk hn hs
  have hn' := hn.poly
  unfold restD
  exact restD_aux hk.poly hK.poly (PolyT.size' (objMax_unary hn hD).poly)
    (PolyT.size' (((((PolyT.const 8).mul (((PolyT.const 10).mul hn').add (PolyT.const 1))).mul ((sbMax_unary hD).poly.add (PolyT.const 1))).mul
      ((PolyT.size' (hD.poly.mul hn')).add (PolyT.const 2))).add (PolyT.const 8)))
    (betaU_unary hk hs).poly (PolyT.size' hn') hn' (pow_polyT (PolyT.const 2) hs)

end par

/-! ### The exponent of the networks and the plan -/

section
variable {Idx : Type} [Enc Idx] (S : Solver Idx)

/-- The bound for the bit length of the entries of the rebalanced instance is given in unary if K,
g, P and B are. -/
theorem bitsS_unary {K g P B : α → ℕ} (hK : Unary K) (hg : Unary g) (hP : Unary P) (hB : Unary B) : Unary fun x => bitsS (K x) (g x) (P x) (B x) := by
  have hK' : PolyT K := hK.poly
  unfold bitsS; fun_prop

/-- The exponent of the networks, computed under a bound, is polynomial-time if the solver, the
bound and the index are and U, P and B are given in unary. -/
theorem needNetC_polyT (hP : S.Poly) {b : α → U} {i : α → Idx} {Ub P B : α → ℕ} (hb : PolyT b) (hi : PolyT i) (hU : Unary Ub) (hQ : Unary P) (hB : Unary B) :
    PolyT fun x => needNetC S (b x) (i x) (Ub x) (P x) (B x) := by
  have hK : Unary fun x => S.K (i x) := hP.K.comp hi
  have hK' : PolyT fun x => S.K (i x) := hK.poly
  have hg : Unary fun x => 3 * S.K (i x) ^ 8 := by fun_prop
  have hl : Unary fun x => lamS (S.K (i x)) (3 * S.K (i x) ^ 8) (Ub x) (P x) := lamS_unary hK hg hU hQ
  have hl' := hl.poly
  have hQ' := hQ.poly
  have hbit : Unary fun x => bitsS (S.K (i x)) (3 * S.K (i x) ^ 8) (P x) (B x) := bitsS_unary hK hg hQ hB
  have hn : PolyT fun x => S.needC (b x, i x, List.replicate (lamS (S.K (i x)) (3 * S.K (i x) ^ 8) (Ub x) (P x)) (),
      List.replicate (bitsS (S.K (i x)) (3 * S.K (i x) ^ 8) (P x) (B x)) ()) :=
    PolyT.comp hP.needC (PolyT.prodMk hb (PolyT.prodMk hi (PolyT.prodMk hl hbit)))
  have hv : PolyT fun q : α × ℕ =>
      max (max (3 * S.K (i q.1) ^ 8 * Nat.size (S.K (i q.1))) (P q.1 * (2 * (3 * S.K (i q.1) ^ 8) / S.K (i q.1) + 1)))
        (max ((S.K (i q.1) - 1) * lamS (S.K (i q.1)) (3 * S.K (i q.1) ^ 8) (Ub q.1) (P q.1)) q.2) := by
    have h1 : PolyT fun q : α × ℕ => S.K (i q.1) := PolyT.comp (f := fun x => S.K (i x)) hK' PolyT.id'.fst
    have h2 : PolyT fun q : α × ℕ => lamS (S.K (i q.1)) (3 * S.K (i q.1) ^ 8) (Ub q.1) (P q.1) :=
      PolyT.comp (f := fun x => lamS (S.K (i x)) (3 * S.K (i x) ^ 8) (Ub x) (P x)) hl' PolyT.id'.fst
    have h3 : PolyT fun q : α × ℕ => P q.1 := PolyT.comp (f := P) hQ' PolyT.id'.fst
    exact maxFour_polyT h1 h3 h2 PolyT.id'.snd
  unfold needNetC
  exact PolyT.optionMap hv hn

/-- The plan is polynomial-time if the solver is, k, n and s are given in unary and the index is
polynomial-time. -/
theorem planAtD_polyT (hP : S.Poly) {k n s : α → ℕ} {i : α → Idx} (hk : Unary k) (hn : Unary n) (hi : PolyT i) (hs : Unary s) :
    PolyT fun x => planAtD S (k x) (n x) (i x) (s x) := by
  have hK : Unary fun x => S.K (i x) := hP.K.comp hi
  have hD := blockU_unary hk hn hs
  have hU := UbD_unary hk hK hn hD
  have hQ := PbD_unary hK hn hD
  have hr := restD_polyT hk hK hn hs
  have hnet := needNetC_polyT S hP (b := fun x => List.replicate (n x) ()) hn hi hU hQ (BbD_unary hk hn)
  have hk' : PolyT k := hk.poly
  have hn' : PolyT n := hn.poly
  have hs' : PolyT s := hs.poly
  have hpow := powBetaU_polyT hk hs
  have hc1 : PolyT fun x => decide (s0U (k x) ≤ s x) := by
    unfold s0U
    exact PolyT.decide_le ((PolyT.const 2).mul (PolyT.size' hk')) hs'
  have hc2 : PolyT fun x => decide (2 ^ betaU (k x) (s x) ≤ n x + 1) := PolyT.decide_le hpow (PolyT.add hn' (PolyT.const 1))
  have hc3 : PolyT fun x => decide (29 * LD (2 ^ betaU (k x) (s x)) + 19 ≤ n x) :=
    PolyT.decide_le (((PolyT.const 29).mul (LD_polyT hpow)).add (PolyT.const 19)) hn'
  have hsum : PolyT fun q : α × ℕ => q.2 + restD (k q.1) (S.K (i q.1)) (n q.1) (s q.1) :=
    PolyT.add PolyT.id'.snd (PolyT.comp (f := fun x => restD (k x) (S.K (i x)) (n x) (s x)) hr PolyT.id'.fst)
  have hn2 : PolyT fun q : α × ℕ => n q.1 := PolyT.comp (f := n) hn' PolyT.id'.fst
  have hin : PolyT fun x => (needNetC S (List.replicate (n x) ()) (i x) (UbD (k x) (S.K (i x)) (n x) (blockU (k x) (n x) (s x)))
      (PbD (S.K (i x)) (n x) (blockU (k x) (n x) (s x))) (BbD (k x) (n x))).bind fun v =>
      if v + restD (k x) (S.K (i x)) (n x) (s x) ≤ n x then some (v + restD (k x) (S.K (i x)) (n x) (s x)) else none :=
    PolyT.optionBind (PolyT.ite' (PolyT.decide_le hsum hn2) (PolyT.some' hsum) (PolyT.const none)) hnet
  unfold planAtD
  exact PolyT.ite' (PolyT.decide_and hc1 (PolyT.decide_and hc2 hc3)) hin (PolyT.const none)

end

end VariableBound.CertTop

namespace VariableBound

open Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat CountKSat.Poly PaddedDescent PaddedDescent.F PaddedDescent.F.CertTop PaddedDescent.F.CertEval CountKSatRate CountKSatRate.Cert ClauseBound.Alg ClauseBound.Alg.CertTop
open ClauseBound.TopN ClauseBound.TopN.Cert ClauseBound.ParityChecks UniformInK UniformInK.CertTop VariableBound.CertTop

end VariableBound
