/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.RunningTimes.FromClaims.Bounds
public import ThreeSumApsp.TimeClaims.Sec3.Arithmetic

/-!
# From running-time claims to programs: Theorem 5, Corollaries 15 and 16, Theorem 19

Let `M` be a reading of "is solved by a deterministic algorithm in time T".  If the running times of
`M` for a problem are realized on the word RAM (`RealizedWithin`), a claim about `M` with the bound
of an item of the paper gives that item as a statement about programs.  Each theorem asks only for
the problems that its item mentions.  The work is done by `exists_solves`, `exists_solves_pair` and
`solvedAt_of_realized`; what is left here is that the paper's bound is at least 1 on its domain
(`one_le_thinBound`, `add_one_le_splitBound`, `one_le_wantedBound`).
-/

@[expose] public section

open ThreeSumApsp.WordRam
open EndStatement (Instr)

namespace ThreeSumApsp.FromClaims

variable (M : DetTimeModel)

/-- **Theorem 5**, about programs, from the claim about `M`. -/
theorem Theorem5.of_claim
    (hR : ∀ T, M.thinProduct T → RealizedWithin (thinProduct []) (fun x => x.N) (fun x => x.U)
      (fun x => 1 ≤ x.D) fun x => T x.N x.D x.W.length x.U)
    (h : Claim.Theorem_5 M) : Items.Theorem_5 := by
  intro c
  obtain ⟨C, T, hT, hb⟩ := h (c : ℝ)
  refine exists_solves (hR T hT) c (C := C) ?_ ?_ ?_
  · rintro x ⟨-, h4, h18, -, hU⟩
    exact ⟨by omega, le_trans (Nat.one_le_pow _ _ (by omega)) h18, hU⟩
  · rintro x ⟨hk, h4, h18, hw, hU⟩
    exact hb x.N x.D x.W.length x.U hk h4 h18 hw (by rw [hU]; exact (cast_pow_eq _ _).le)
  · rintro x ⟨-, h4, h18, -, -⟩
    exact one_le_thinBound h4 h18

/-- The running times of `M` for the two lopsided triangle problems are realized on the word RAM, on
the instances with entries 0 and 1 and `D ≥ 1`. -/
structure LopRealized : Prop where
  /-- #Lop-AE-SparseTri. -/
  count : ∀ T, M.lopCount T → RealizedWithin lopCount (fun x => x.N) (fun x => x.U)
    (fun x => x.ZeroOne ∧ 1 ≤ x.D) fun x => T x.N x.D x.W.length
  /-- Lop-AE-SparseTri. -/
  detect : ∀ T, M.lopDetect T → RealizedWithin lopDetect (fun x => x.N) (fun x => x.U)
    (fun x => x.ZeroOne ∧ 1 ≤ x.D) fun x => T x.N x.D x.W.length

/-- The two lopsided triangle problems at once.  The entries are 0 and 1, so the magnitude is
`U = 1 = n^0`.  If the running times `Tc` and `Td` are both at most `C X`, where `X ≥ 1`, on the
instances in `dom`, then two programs solve these instances in `O(X)` steps. -/
private theorem exists_solves_lop (hR : LopRealized M) {Tc Td : ℕ → ℕ → ℕ → ℝ}
    (hTc : M.lopCount Tc) (hTd : M.lopDetect Td) {dom : ThinInstance → Prop}
    {X : ThinInstance → ℝ} {C : ℝ}
    (hdom : ∀ x, dom x → x.ZeroOne ∧ x.U = 1 ∧ 1 ≤ x.D ∧ x.D ^ 18 ≤ x.N)
    (hT : ∀ x, dom x → Tc x.N x.D x.W.length ≤ C * X x ∧ Td x.N x.D x.W.length ≤ C * X x)
    (hX : ∀ x, dom x → 1 ≤ X x) :
    ∃ (Pc Pd : List Instr) (b : ℕ) (K : ℝ),
      Solves lopCount Pc b dom (fun x => K * X x) ∧ Solves lopDetect Pd b dom fun x => K * X x := by
  have hdom' : ∀ x : ThinInstance, dom x → (x.ZeroOne ∧ 1 ≤ x.D) ∧ 1 ≤ x.N ∧ x.U = x.N ^ 0 := by
    intro x hx
    obtain ⟨hzero, hU, h1, h18⟩ := hdom x hx
    exact ⟨⟨hzero, h1⟩, le_trans (Nat.one_le_pow _ _ h1) h18, hU.trans (pow_zero _).symm⟩
  exact exists_solves_pair
    (exists_solves_nonneg (hR.count Tc hTc) 0 (C := C) hdom' (fun x hx => (hT x hx).1) hX)
    (exists_solves_nonneg (hR.detect Td hTd) 0 (C := C) hdom' (fun x hx => (hT x hx).2) hX) hX hX

/-- **Corollary 15**, about programs, from the claim about `M`. -/
theorem Corollary15.of_claim (hR : LopRealized M) (h : Claim.Corollary_15_general M) :
    Items.Corollary_15 := by
  obtain ⟨C, Tc, Td, -, hTc, hTd, hb⟩ := h
  refine exists_solves_lop M hR hTc hTd (C := C) ?_ ?_ ?_
  · rintro x ⟨hzero, hU, -, h4, h18⟩
    exact ⟨hzero, hU, by omega, h18⟩
  · rintro x ⟨-, -, hpow, h4, h18⟩
    exact hb x.N x.D x.W.length hpow h4 h18
  · rintro x ⟨-, -, -, h4, h18⟩
    exact (le_add_of_nonneg_left (Nat.cast_nonneg _)).trans (add_one_le_splitBound _ h4 h18)

/-- **Corollary 16**, about programs, from the claim about `M`. -/
theorem Corollary16.of_claim (hR : LopRealized M) (h : Claim.Corollary_16 M) :
    Items.Corollary_16 := by
  obtain ⟨C, Tc, Td, -, hTc, hTd, hb⟩ := h
  refine exists_solves_lop M hR hTc hTd (C := C) (fun _ hx => hx) ?_ ?_
  · rintro x ⟨-, -, h1, h18⟩
    exact hb x.N x.D x.W.length h1 h18
  · rintro x ⟨-, -, h1, h18⟩
    exact one_le_wantedBound h1 h18 _

/-- **Theorem 19**, about programs, from the two claims about `M`. -/
theorem Theorem19.of_claim
    (hR : ∀ T, M.exactTriangle T → Realized EndStatement.ExactTriangle T)
    (hfirst : Claim.Theorem_19_first M) (hsecond : Claim.Theorem_19_second M) :
    Items.Theorem_19 := by
  have hempty : ∀ x : EndStatement.ExactTriangle.Instance 0,
    EndStatement.ExactTriangle.input x = [] :=
    fun _ => rfl
  refine ⟨solvedInTime_of_one_le hempty fun κ hκ => ?_,
    solvedInTime_of_one_le hempty fun κ hκ => ?_,
    solvedInTime_of_one_le hempty fun κ hκ => ?_⟩
  · obtain ⟨C, T, hT, hb⟩ := hfirst κ (by exact_mod_cast hκ)
    exact solvedAt_of_realized T κ (hR T hT) hb
  · obtain ⟨C, T, hT, hb, -⟩ := hsecond κ (by exact_mod_cast hκ)
    exact solvedAt_of_realized T κ (hR T hT) (C := C) (by simpa only [pow_one] using hb)
  · obtain ⟨-, T, hT, -, C, hb⟩ := hsecond κ (by exact_mod_cast hκ)
    exact solvedAt_of_realized T κ (hR T hT) (C := C)
      (by simpa only [pow_zero, mul_one] using hb)

end ThreeSumApsp.FromClaims
