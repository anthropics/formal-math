/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import GeneralPieces.Trim.Prog
import PaddedDescent.F.FuelCert

/-! # The values of the pieces are computed in polynomial time

If the programs of P are polynomial-time in the pad and their arguments, so is the program `valF P`
for the values of the pieces (`valF_polyT`). This is
the requirement that one algorithm computes each of them, in the definition of pieces with
parameters (ρ, c) in Appendix A, for the values of the pieces; the loop of `valF` is cut off by the
pad, so
no condition on the pad is needed here. -/

public section

namespace GeneralPieces

open Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg ClauseBound.Gen

namespace Trim

variable {α : Type} [Enc α] {P : PiecesF}

/-- The smaller of two numbers, the second of which is given in unary, is given in unary. -/
theorem unary_min' {f g : α → ℕ} (hf : PolyT f) (hg : Unary g) : Unary fun x => min (f x) (g x) :=
  hg.of_le (PolyT.min' hf hg.poly) fun _ => min_le_right _ _

/-- The number of bits of a factorization of P, with h and λ in unary and the number of the piece in
binary. -/
theorem cap_unary (hP : P.Keeps) {tr : α → Bool} {h lam i : α → ℕ} (ht : PolyT tr) (hh : Unary h) (hl : Unary lam) (hi : PolyT i) :
    Unary fun x => P.cap (tr x) (h x) (lam x) (i x) := by
  simpa using hP.cap.comp (h := fun x => (tr x, List.replicate (h x) (), List.replicate (lam x) (), i x)) (by fun_prop)

end Trim

open Trim

/-- The value of a piece is polynomial-time in the pad, h in unary, the number of the piece in
binary and the four strings. -/
theorem valF_polyT {P : PiecesF} (hP : P.Keeps) : PolyT (valF P) := by
  have ht := hP.top
  have hb := hP.bot
  have hc : Unary fun q : VQ => P.cap q.1.2 q.2.1.1.length q.2.2.1.length q.2.1.2 :=
    cap_unary hP (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
  have hw : PolyT fun p : VQ × ℕ => toWord (P.cap p.1.1.2 p.1.2.1.1.length p.1.2.2.1.length p.1.2.1.2) p.2 :=
    PolyT.toWord' (hc.comp (h := fun p : VQ × ℕ => p.1) (by fun_prop)) (by fun_prop)
  unfold valF
  exact sumF_polyT (PolyT.pow_unary (by fun_prop) hc) (by fun_prop) (by fun_prop)

end GeneralPieces
