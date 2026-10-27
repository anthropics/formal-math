/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ClauseBound.TopN.Defs
public import ClauseBound.Alg.CertTop
public import CountKSatRate.Cert
import PaddedDescent.F.CertEval

/-! # One evaluation, the parameters and the exponent of the networks are polynomial-time

Lemmas that one evaluation of a sparse formula (`evalV`, with the certificate `StCertAdm` of the
network of marks), the parameters (β, the number of layers, the bounds on shared bits and size,
⌊n^{1/17}⌋, the threshold τ, the label length `lamS`) and the exponent of the networks computed
under a bound (`needNetC`) are polynomial-time or given in unary. -/

public section

namespace ClauseBound.TopN.Cert

open Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat CountKSat.Poly PaddedDescent PaddedDescent.F PaddedDescent.F.CertTop PaddedDescent.F.CertEval CountKSatRate CountKSatRate.Cert ClauseBound.Alg ClauseBound.Alg.CertTop
open PaddedDescent.F.Mark (MCtx Cl cls nProf adm markF placeE)

variable {α : Type} [Enc α]

/-! ### One sparse formula, for any polynomial-time `val` -/

section count

variable {pad gu : α → U} {val : α → MCtx → ℤ} {p : α → U × U × U × U} {R : α → ℕ} {ψ : α → Fml}

/-- One evaluation. -/
theorem evalV_polyT (k : ℕ) (hA : StCertAdm) {Ls : α → List Fml} (hp : PolyT pad) (hg : PolyT gu) (hv : PolyT fun q : α × MCtx => val q.1 q.2) (hq : PolyT p)
    (hL : PolyT Ls) : PolyT fun x => evalV k (pad x) (gu x) (val x) (p x) (Ls x) := by
  have h0 : PolyT fun x => nProf (gu x).length (cls (Ls x)).length (Ls x).length :=
    nProf_polyT (by fun_prop) (PolyT.length (cls_polyT hL)) (by fun_prop)
  have h1 : PolyT fun r : α × ℕ => adm k (gu r.1).length (p r.1).1.length (p r.1).2.1.length (Ls r.1) r.2 :=
    PolyT.comp (g := fun r : α × ℕ => ((gu r.1, (p r.1).1, (p r.1).2.1), Ls r.1, r.2)) (hA k) (by fun_prop)
  have h2 : PolyT fun r : α × ℕ => val r.1 ((gu r.1, (p r.1).1, (p r.1).2.2.1, (p r.1).2.2.2), (Ls r.1, r.2)) :=
    PolyT.comp (g := fun r : α × ℕ => (r.1, ((gu r.1, (p r.1).1, (p r.1).2.2.1, (p r.1).2.2.2), (Ls r.1, r.2)))) hv (by fun_prop)
  unfold evalV
  fun_prop

end count

/-! ### The parameters -/

section par

variable {K n s : α → ℕ}

/-- β is given in unary if s is. -/
@[fun_prop] theorem betaN_unary (k : ℕ) (hs : Unary s) : Unary fun x => betaN k (s x) := by
  unfold betaN; fun_prop

/-- The number of layers is given in unary if s is. -/
@[fun_prop] theorem layersN_unary (k : ℕ) (hs : Unary s) : Unary fun x => layersN k (s x) := by
  unfold layersN; fun_prop

/-- 2^β cut off at n + 1 is given in unary if n and s are. -/
@[fun_prop] theorem blockN_unary (k : ℕ) (hn : Unary n) (hs : Unary s) : Unary fun x => blockN k (n x) (s x) := by
  have h1 : PolyT fun x => 2 ^ betaN k (s x) := pow_polyT (PolyT.const 2) (betaN_unary k hs)
  have h2 : Unary fun x => n x + 1 := by fun_prop
  exact h2.of_le (PolyT.min' h1 h2.poly) fun x => min_le_right _ _

/-- The bound on the shared bits is given in unary. -/
@[fun_prop] theorem UbN_unary (k : ℕ) (hK : Unary K) (hn : Unary n) (hs : Unary s) : Unary fun x => UbN k (K x) (n x) (s x) := by
  have h1 := betaN_unary k hs
  have h2 := layersN_unary k hs
  unfold UbN Ub; fun_prop

/-- The bound on the size is given in unary. -/
@[fun_prop] theorem PbN_unary (k : ℕ) (hK : Unary K) (hn : Unary n) (hs : Unary s) : Unary fun x => PbN k (K x) (n x) (s x) := by
  have h1 := betaN_unary k hs
  have h2 := blockN_unary k hn hs
  have hK' : PolyT K := hK.poly
  unfold PbN Pb Mark.qv; fun_prop

/-- ⌊n^{1/17}⌋ in unary is polynomial-time in n in unary. -/
@[fun_prop] theorem root17_polyT (hn : Unary n) : PolyT fun x => root17 (n x) := by
  have hn' : PolyT n := hn.poly
  unfold root17; fun_prop

/-- The threshold τ = 2^(4s+17) is polynomial-time in s in unary. -/
theorem tauOf_polyT (hs : Unary s) : PolyT fun x => tauOf (s x) := by
  unfold tauOf
  exact pow_polyT (PolyT.const 2) (by fun_prop)

end par

/-! ### The exponent of the networks -/

section
variable {Idx : Type} [Enc Idx] (S : Solver Idx)

/-- The label length of the rebalanced instance is given in unary. -/
theorem lamS_unary {K g Ub P : α → ℕ} (hK : Unary K) (hg : Unary g) (hU : Unary Ub) (hP : Unary P) : Unary fun x => lamS (K x) (g x) (Ub x) (P x) := by
  have hK' : PolyT K := hK.poly
  unfold lamS; fun_prop

/-- The exponent of the networks, computed under a bound. -/
theorem needNetC_polyT (hP : S.Poly) {b : α → U} {i : α → Idx} {Ub P : α → ℕ} (hb : PolyT b) (hi : PolyT i) (hU : Unary Ub) (hQ : Unary P) :
    PolyT fun x => needNetC S (b x) (i x) (Ub x) (P x) 0 := by
  have hK : Unary fun x => S.K (i x) := hP.K.comp hi
  have hK' : PolyT fun x => S.K (i x) := hK.poly
  have hg : Unary fun x => 3 * S.K (i x) ^ 8 := by fun_prop
  have hl : Unary fun x => lamS (S.K (i x)) (3 * S.K (i x) ^ 8) (Ub x) (P x) := lamS_unary hK hg hU hQ
  have hl' := hl.poly
  have hQ' := hQ.poly
  have hbit : Unary fun x => bitsS (S.K (i x)) (3 * S.K (i x) ^ 8) (P x) 0 :=
    PolyT.congr (entry_unary hK hQ) fun x => by
      change List.replicate _ () = List.replicate (bitsS (S.K (i x)) (3 * S.K (i x) ^ 8) (P x) 0) ()
      rw [bitsS, Nat.zero_mul, Nat.zero_mul, Nat.add_zero]
  have hn : PolyT fun x => S.needC (b x, i x, List.replicate (lamS (S.K (i x)) (3 * S.K (i x) ^ 8) (Ub x) (P x)) (),
      List.replicate (bitsS (S.K (i x)) (3 * S.K (i x) ^ 8) (P x) 0) ()) :=
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

end

end ClauseBound.TopN.Cert
