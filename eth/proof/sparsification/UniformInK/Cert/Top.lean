/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import UniformInK.Top.Defs
import ClauseBound.ParityChecks.CertTopOL
import ClauseBound.Alg.Decode

/-! # Parameters of the bound in n, given in unary or polynomial-time jointly in the width

Here the width k is read from the input, in unary. The numbers β, 2^β, 2^β cut off at n + 1, the
width cut off at ⌊log₂(n+1)⌋ and 2 to this width are shown to be given
in unary or to be polynomial-time, jointly in k, n and s; and 2 to the width cut off is shown to be
at most n + 1. -/

public section

namespace UniformInK.CertTop

open Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat CountKSat.Poly PaddedDescent PaddedDescent.F PaddedDescent.F.CertTop PaddedDescent.F.CertEval CountKSatRate CountKSatRate.Cert ClauseBound.Alg ClauseBound.Alg.CertTop
open ClauseBound.TopN ClauseBound.TopN.Cert ClauseBound.ParityChecks ClauseBound.ParityChecks.CertTopOL

variable {α : Type} [Enc α]

/-! ### The parameters, jointly in the width -/

section par
variable {k K n s D : α → ℕ}

/-- β is given in unary if k and s are. -/
theorem betaU_unary (hk : Unary k) (hs : Unary s) : Unary fun x => betaU (k x) (s x) := by
  unfold betaU
  exact ((Unary.const 2).mul hk).mul (((Unary.const 4).mul hs).add (Unary.const 17))

/-- 2^β is polynomial-time if k and s are given in unary. -/
theorem powBetaU_polyT (hk : Unary k) (hs : Unary s) : PolyT fun x => 2 ^ betaU (k x) (s x) :=
  pow_polyT (PolyT.const 2) (betaU_unary hk hs)

/-- 2^β cut off at n + 1 is given in unary if k, n and s are. -/
theorem blockU_unary (hk : Unary k) (hn : Unary n) (hs : Unary s) : Unary fun x => blockU (k x) (n x) (s x) := by
  have h2 : Unary fun x => n x + 1 := hn.add (Unary.const 1)
  exact h2.of_le (PolyT.min' (powBetaU_polyT hk hs) h2.poly) fun _ => min_le_right _ _

/-- The width cut off at ⌊log₂(n+1)⌋ is given in unary if k is and n is polynomial-time. -/
theorem kcU_unary (hk : Unary k) (hn : PolyT n) : Unary fun x => kcU (k x) (n x) :=
  hk.of_le (PolyT.min' hk.poly (log_polyT (hn.add (PolyT.const 1)))) fun _ => min_le_left _ _

/-- 2 to the width cut off is at most n + 1. -/
theorem two_pow_kcU_le (k n : ℕ) : 2 ^ kcU k n ≤ n + 1 :=
  (Nat.pow_le_pow_right (by norm_num) (min_le_right _ _)).trans (Nat.pow_log_le_self 2 (by omega))

/-- 2 to the width cut off is given in unary if k and n are. -/
theorem powKcU_unary (hk : Unary k) (hn : Unary n) : Unary fun x => 2 ^ kcU (k x) (n x) :=
  (hn.add (Unary.const 1)).of_le (pow_polyT (PolyT.const 2) (kcU_unary hk hn.poly)) fun _ => two_pow_kcU_le _ _

end par


section
variable {Idx : Type} [Enc Idx] (S : Solver Idx)

end

end UniformInK.CertTop

namespace UniformInK

open Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat CountKSat.Poly PaddedDescent PaddedDescent.F PaddedDescent.F.CertTop PaddedDescent.F.CertEval CountKSatRate CountKSatRate.Cert ClauseBound.Alg ClauseBound.Alg.CertTop
open ClauseBound.TopN ClauseBound.TopN.Cert ClauseBound.ParityChecks ClauseBound.ParityChecks.CertTopOL UniformInK.CertTop

end UniformInK
