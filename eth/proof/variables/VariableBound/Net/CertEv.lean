/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import VariableBound.Net.Defs
public import ClauseBound.ParityChecks.CertPar
public import PaddedDescent.F.CertEval
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.Ring

/-! # Step 3: one evaluation is polynomial-time

One evaluation (`evD`) is the sum, over the admissible profiles, of the values of their networks,
each computed by the clique solver. For a polynomial-time solver it is polynomial-time (PolyT)
jointly in the width k, n and Δ (given in unary), n̄, M, the
pad, the index of the solver, the flag that chooses between the sums for X and for F of Step 3, and
the data (ψ, 𝓛): `stCertEvD`, the interface statement `StCertEvD`.
The certificates of the value of a network through the solver, of the network of one profile and of
the test «admissible» are hypotheses.

The bounds of «The total» and «The parameters» that do not depend on the formula are given in unary
when k, K, n and Δ are: `UbD_unary`, `PbD_unary`, `BbD_unary`, with `tbMax_unary`, `sbMax_unary`,
`objMax_unary`. P = ⌈2P₀⌉ is the
ceiling of a rational number; with a natural number in the place of s̄ the ceiling disappears
(`PD_natCast`, `PbD_eq`). -/

public section

namespace VariableBound.Net.CertEv

open Groundwork Groundwork.Prog PaddedDescent.F PaddedDescent.F.CertEval ClauseBound.Alg ClauseBound.ParityChecks ClauseBound.ParityChecks.CertLib ClauseBound.ParityChecks.CertPar
open PaddedDescent.F.Mark (qv nProf)
open PaddedDescent.F.Mark.Cert (qv_unary)

variable {α : Type} [Enc α]

/-! ### The bounds in natural numbers -/

/-- P = ⌈2P₀⌉ for a natural number s̄: 2·(⌈n/g⌉(1 + Δ(t̄ + 3)) + ⌈r̄/g⌉·s̄). -/
theorem PD_natCast (g n Δ tb rb sb : ℕ) : PD g n Δ tb rb (sb : ℚ) = 2 * (qv g n * (1 + Δ * (tb + 3)) + qv g rb * sb) := by
  unfold PD P0
  have h : 2 * ((qv g n : ℚ) * (1 + Δ * (tb + 3)) + (qv g rb : ℚ) * sb) = ((2 * (qv g n * (1 + Δ * (tb + 3)) + qv g rb * sb) : ℕ) : ℚ) := by
    push_cast; ring
  rw [h, Nat.ceil_natCast]

/-- The bound P that does not depend on the formula, in natural numbers, with g = 3K⁸. -/
theorem PbD_eq (K n Δ : ℕ) :
    PbD K n Δ = 2 * (qv (3 * K ^ 8) n * (1 + Δ * (tbMax n Δ + 3)) + qv (3 * K ^ 8) (10 * n) * sbMax Δ) :=
  PD_natCast _ _ _ _ _ _

/-! ### The bounds are given in unary -/

/-- The bound for t̄ is given in unary if n and Δ are polynomial-time. -/
theorem tbMax_unary {n Δ : α → ℕ} (hn : PolyT n) (hΔ : PolyT Δ) : Unary fun x => tbMax (n x) (Δ x) :=
  ((clog_unary (hΔ.mul hn)).add ((Unary.const 33).mul (LD_unary hΔ))).add (Unary.const 1)

/-- The bound for s̄ is given in unary if Δ is. -/
theorem sbMax_unary {Δ : α → ℕ} (hΔ : Unary Δ) : Unary fun x => sbMax (Δ x) :=
  ((Unary.const 32).mul hΔ).mul (LD_unary hΔ.poly)

/-- The bound for the number I + m of objects is given in unary if n and Δ are. -/
theorem objMax_unary {n Δ : α → ℕ} (hn : Unary n) (hΔ : Unary Δ) : Unary fun x => objMax (n x) (Δ x) :=
  (((Unary.const 10).mul hn).mul (sbMax_unary hΔ)).add (hΔ.mul hn)

/-- The bound on the total U in «The total» of Step 3, with the logarithms rounded up, is given in
unary if k, K, n and Δ are. -/
theorem UbD_unary {k K n Δ : α → ℕ} (hk : Unary k) (hK : Unary K) (hn : Unary n) (hΔ : Unary Δ) : Unary fun x => UbD (k x) (K x) (n x) (Δ x) :=
  ((((Unary.const 6).mul hk).mul (hn.add (LD_unary hΔ.poly))).add
    ((((Unary.const 28).mul hk).mul hn).mul (clog_unary (((PolyT.const 96).mul hΔ.poly).mul (LD_unary hΔ.poly).poly)))).add
    ((Unary.const 2).mul (unary_pow_const (g_unary hK) 2))

/-- The bound P that does not depend on the formula is given in unary if K, n and Δ are. -/
theorem PbD_unary {K n Δ : α → ℕ} (hK : Unary K) (hn : Unary n) (hΔ : Unary Δ) : Unary fun x => PbD (K x) (n x) (Δ x) :=
  unary_congr ((Unary.const 2).mul
    (((qv_unary (g_unary hK) hn).mul ((Unary.const 1).add (hΔ.mul ((tbMax_unary hn.poly hΔ.poly).add (Unary.const 3))))).add
      ((qv_unary (g_unary hK) ((Unary.const 10).mul hn)).mul (sbMax_unary hΔ)))) fun x => (PbD_eq (K x) (n x) (Δ x)).symm

/-- B = (k + 1)·14n + 1 is given in unary if k and n are. -/
theorem BbD_unary {k n : α → ℕ} (hk : Unary k) (hn : Unary n) : Unary fun x => BbD (k x) (n x) :=
  ((hk.add (Unary.const 1)).mul ((Unary.const 14).mul hn)).add (Unary.const 1)

/-! ### One evaluation -/

/-- The list of the objects is polynomial-time. -/
theorem objs_polyT {D : α → Dat} (hD : PolyT D) : PolyT fun x => objs (D x) := by
  unfold objs; fun_prop

/-- The number of the numbers that are tried as profiles is polynomial-time if g is given in unary
and the data are polynomial-time. -/
theorem nPr_polyT {g : α → ℕ} {D : α → Dat} (hg : Unary g) (hD : PolyT D) : PolyT fun x => nPr (g x) (D x) :=
  nProf_polyT hg (PolyT.length (objs_polyT hD)) (Unary.const 2)

/-- The context of the network of a profile is polynomial-time if g and n are given in unary and the
data, the profile and the flag are polynomial-time. -/
theorem ctx_polyT {g n y : α → ℕ} {D : α → Dat} {fl : α → Bool} (hg : Unary g) (hn : Unary n) (hD : PolyT D) (hy : PolyT y) (hfl : PolyT fl) :
    PolyT fun x => ctx (g x) (n x) (D x) (y x) (fl x) := by
  have h1 : PolyT fun x => rep (g x) := hg
  have h2 : PolyT fun x => rep (n x) := hn
  unfold ctx; fun_prop

end VariableBound.Net.CertEv

namespace VariableBound.Net

open Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg ClauseBound.ParityChecks.CertPar VariableBound.Net.CertEv

/-- `StCertEvD`: one evaluation is polynomial-time jointly in all its arguments, the width k, n and
Δ given in unary, if the solver is polynomial-time; given the certificates of the value of a network
through the solver, of
the network of one profile (condition (iii) of the definition of a network) and of the test
«admissible». -/
theorem CertEv.stCertEvD (hV : StCertValS) (hN : StCertNet) (hA : StCertAdm) : StCertEvD := by
  intro Idx _ S hP α _ k n Δ nb M pad i fl D hk hn hΔ hnb hM hpad hi hfl hD
  have hK : Unary fun x => S.K (i x) := hP.K.comp hi
  have hf : PolyT fun r : α × ℕ => r.1 := PolyT.id'.fst
  have hK' : Unary fun r : α × ℕ => S.K (i r.1) := hK.comp hf
  have h0 : PolyT fun x => nPr (3 * S.K (i x) ^ 8) (D x) := nPr_polyT (g_unary hK) hD
  have h1 : PolyT fun r : α × ℕ => admD (k r.1) (3 * S.K (i r.1) ^ 8) (n r.1) (nb r.1) (M r.1) (D r.1) (fl r.1) r.2 :=
    hA (α × ℕ) _ _ _ _ _ _ _ _ (hk.comp hf).poly (g_unary hK') (hn.comp hf).poly (PolyT.comp hnb hf) (PolyT.comp hM hf) (PolyT.comp hD hf)
      (PolyT.comp hfl hf) PolyT.id'.snd
  have h2 : PolyT fun r : α × ℕ => valS S (pad r.1) (i r.1) (UbD (k r.1) (S.K (i r.1)) (n r.1) (Δ r.1)) (PbD (S.K (i r.1)) (n r.1) (Δ r.1)) netD
      (ctx (3 * S.K (i r.1) ^ 8) (n r.1) (D r.1) r.2 (fl r.1)) :=
    hV Idx S hP DCtx netD hN (α × ℕ) _ _ _ _ _ (PolyT.comp hpad hf) (PolyT.comp hi hf) (UbD_unary (hk.comp hf) hK' (hn.comp hf) (hΔ.comp hf))
      (PbD_unary hK' (hn.comp hf) (hΔ.comp hf)) (ctx_polyT (g_unary hK') (hn.comp hf) (PolyT.comp hD hf) PolyT.id'.snd (PolyT.comp hfl hf))
  unfold evD
  fun_prop

end VariableBound.Net
