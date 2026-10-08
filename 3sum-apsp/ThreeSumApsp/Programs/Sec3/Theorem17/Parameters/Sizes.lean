/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Lang.Tactics
public import ThreeSumApsp.Spec.Sec3.Theorem17.Parameters

/-!
# The parameters of Theorems 17 and 19, without division and without roots

The proof of Theorem 19 chooses D as "the largest power of four with D ≤ n^{1/18}"
and g := ⌈D^{1/36}⌉, or D := ⌊n^{1/18}⌋ and g := ⌈D^{0.0315}⌉; the reduction of Theorem 17 uses
⌊n²/√D⌋ and quotients rounded up.  The language has neither division nor roots, so all of these are
found by counting up.  A power is compared with a bound without forming a number above the bound
times the base.

* powLt(g, e, t), for g ≥ 1, returns 1 if g^e < t, and 0 if not (`powLt_meets`); what it holds after
  i factors is `capPow g t i`.
* rootCeil(e, t) returns the least g with g^e ≥ t (`rootCeil_meets`).
* The four parameters; 5 and 26 stand for the two routes of Theorem 19, through Theorem 5 and
  through Corollary 26.  d5(n) returns the largest power of four that is at most n^{1/18}, g5(D)
  returns ⌈D^{1/36}⌉, d26(n) returns ⌊n^{1/18}⌋, and g26(D) returns ⌈D^{0.0315}⌉; g5 and g26
  are for D ≥ 1 (`d5_spec`, `g5_spec`, `d26_spec`, `g26_spec`).
* queryCapNat(n, D) returns ⌊n²/√D⌋, and ceilDiv(a, b) returns ⌈a/b⌉ (`queryCapNat_meets`,
  `ceilDiv_meets`).

No routine touches the memory.
-/

@[expose] public section

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## Comparing a power with a bound -/

/-- The powers of g, as long as they are below t: the value stays as it is once it has reached
t. -/
def capPow (g t : ℕ) : ℕ → ℕ
  | 0 => 1
  | i + 1 => if capPow g t i < t then capPow g t i * g else capPow g t i

/-- One more factor. -/
theorem capPow_succ (g t i : ℕ) :
    capPow g t (i + 1) = if capPow g t i < t then capPow g t i * g else capPow g t i := rfl

/-- Below t the value is the power, and a value that has reached t shows that the power has. -/
theorem capPow_spec {g : ℕ} (hg : 1 ≤ g) (t i : ℕ) :
    (capPow g t i < t → capPow g t i = g ^ i) ∧ (t ≤ capPow g t i → t ≤ g ^ i) := by
  induction i with
  | zero => simp [capPow]
  | succ i ih =>
    rw [capPow_succ]
    split_ifs with h
    · rw [ih.1 h, pow_succ]
      exact ⟨fun _ => rfl, fun h' => h'⟩
    · exact ⟨fun h' => absurd h' h,
        fun _ => (ih.2 (not_lt.1 h)).trans (Nat.pow_le_pow_right hg (Nat.le_succ i))⟩

/-- The value is below t exactly if the power is. -/
theorem capPow_lt_iff {g : ℕ} (hg : 1 ≤ g) (t i : ℕ) : capPow g t i < t ↔ g ^ i < t := by
  obtain ⟨hlow, hhigh⟩ := capPow_spec hg t i
  exact ⟨fun h => hlow h ▸ h, fun h => not_le.1 fun hc => absurd (hhigh hc) (not_le.2 h)⟩

namespace PowLt

/-- The local variables of powLt: the arguments g, e, t; the number of factors so far; their
product (Acc). -/
abbrev Base : ℕ := 0
@[inherit_doc Base] abbrev Exp : ℕ := 1
@[inherit_doc Base] abbrev Bound : ℕ := 2
@[inherit_doc Base] abbrev Cnt : ℕ := 3
@[inherit_doc Base] abbrev Acc : ℕ := 4

end PowLt

open PowLt in
/-- powLt(g, e, t). -/
def powLtBody : Stmt :=
  .set Cnt (k 0) ;;
  .set Acc (k 1) ;;
  .while (v Cnt <' v Exp) (
    .ite (v Acc <' v Bound) (.set Acc (v Acc *' v Base)) .skip ;;
    .set Cnt (v Cnt +' k 1)) ;;
  .ite (v Acc <' v Bound) (.set Base (k 1)) (.set Base (k 0))

/-- **powLt**, for g ≥ 1, returns 1 if g^e < t and 0 if not, in at most 16 e + 14 steps.  It forms
no number above t g + e + 1. -/
theorem powLt_meets {μ : ℕ → ℤ} {pPow g e t : ℕ} (hP : P[pPow]? = some powLtBody) (hg : 1 ≤ g)
    (hword : ((t * g + e + 1 : ℕ) : ℤ) ≤ lim.word) :
    Meets lim P pPow d [g, e, t] μ (16 * e + 14) fun r μ' =>
      r = (if g ^ e < t then 1 else 0) ∧ μ' = μ := by
  refine .of_body hP ?_
  push_cast at hword
  have htg : (0 : ℤ) ≤ (t : ℤ) * g := by positivity
  -- cnt := 0; prod := 1
  light_set (0 : ℕ)
  light_set (1 : ℕ)
  -- while cnt < e.  Before round i, cnt = i and prod = capPow g t i.
  refine Ends.next _ (Ends.whileBlock
    (fun i σ => σ = ⟨frame [g, e, t, i, (capPow g t i : ℕ)], μ⟩) e (by simp [capPow]) ?round ?done
    le_rfl) (by simp; omega)
  case round =>
    rintro i _ hi rfl
    rw [capPow_succ]
    generalize capPow g t i = c
    -- if prod < t then prod := prod * g; cnt := cnt + 1
    by_cases hlt : c < t
    · have hmul : (c : ℤ) * g ≤ t * g := by exact_mod_cast Nat.mul_le_mul_right g hlt.le
      have hmul0 : (0 : ℤ) ≤ (c : ℤ) * g := by positivity
      exact ⟨by light_side, by light_side, by light_side [hlt],
        by simp [update_frame_setLocal, hlt]⟩
    · exact ⟨by light_side, by light_side, by simp [abs_le, hlt]; omega,
        by simp [update_frame_setLocal, hlt]⟩
  case done =>
    rintro _ rfl
    have hiff := capPow_lt_iff hg t e
    -- return 1 if prod < t, and 0 if not
    refine ⟨by light_side, by light_side,
      Ends.iteLast (fun h => ?_) (fun h => ?_) (hT := by simp; omega)⟩
    · have hlt : g ^ e < t := hiff.1 (by simpa using h)
      exact Ends.setTo 1 (by simp [hlt]) (hT := by simp; omega)
    · have hlt : ¬ g ^ e < t := fun h' => h (by simpa using hiff.2 h')
      exact Ends.setTo 0 (by simp [hlt]) (hT := by simp; omega)

/-! ## Roots, rounded up -/

namespace RootCeil

/-- The local variables of rootCeil: the arguments e, t; the candidate g; whether g^e < t. -/
abbrev Exp : ℕ := 0
@[inherit_doc Exp] abbrev Bound : ℕ := 1
@[inherit_doc Exp] abbrev Cand : ℕ := 2
@[inherit_doc Exp] abbrev More : ℕ := 3

end RootCeil

open RootCeil in
/-- rootCeil(e, t), over the procedure pPow (powLt). -/
def rootCeilBody (pPow : ℕ) : Stmt :=
  .set Cand (k 1) ;;
  .call pPow [v Cand, v Exp, v Bound] More ;;
  .while (v More =' k 1) (
    .set Cand (v Cand +' k 1) ;;
    .call pPow [v Cand, v Exp, v Bound] More) ;;
  .set Exp (v Cand)

/-- The time of rootCeil. -/
def tRootCeil (e t : ℕ) : ℕ := rootCeil e t * (16 * e + 27)

/-- **rootCeil** returns the least g with g^e ≥ t, for e ≥ 1 and t ≥ 1.  It forms no number above t
times the result plus e + 1. -/
theorem rootCeil_meets {μ : ℕ → ℤ} {pRoot pPow e t : ℕ} (hR : P[pRoot]? = some (rootCeilBody pPow))
    (hP : P[pPow]? = some powLtBody) (he : e ≠ 0) (ht : 1 ≤ t)
    (hword : ((t * rootCeil e t + e + 1 : ℕ) : ℤ) ≤ lim.word) (hd : d < lim.depth) :
    Meets lim P pRoot d [e, t] μ (tRootCeil e t) fun r μ' => r = (rootCeil e t : ℕ) ∧ μ' = μ := by
  refine .of_body hR ?_
  have key : ∀ g, g ^ e < t ↔ g < rootCeil e t := fun g => by
    rw [← not_le, ← not_le, rootCeil_le_iff he ht]
  have hpos : 1 ≤ rootCeil e t := Nat.succ_le_succ (Nat.zero_le _)
  unfold tRootCeil
  generalize rootCeil e t = G at key hpos hword
  obtain ⟨y, rfl⟩ : ∃ y, G = y + 1 := ⟨G - 1, by omega⟩
  have hyt : y + 1 ≤ t * (y + 1) := Nat.le_mul_of_pos_left _ ht
  -- The test of a candidate g ≤ y + 1.
  have test : ∀ g, 1 ≤ g → g ≤ y + 1 → Meets lim P pPow (d + 1) [g, e, t] μ (16 * e + 14)
      fun r μ' => r = (if g < y + 1 then 1 else 0) ∧ μ' = μ := fun g hg hgy => by
    have hle : t * g + e + 1 ≤ t * (y + 1) + e + 1 := by
      have := Nat.mul_le_mul_left t hgy
      omega
    simpa only [key] using powLt_meets hP hg ((Int.ofNat_le.2 hle).trans hword)
  -- cand := 1; more := powLt(cand, e, t)
  light_set (1 : ℕ)
  light_call (test 1 le_rfl hpos) with _ μ' ⟨rfl, hμ⟩
  rw [hμ]
  -- while more = 1.  Before round i, cand = i + 1.
  refine Ends.next _ (Ends.whileConst
    (fun i σ => σ = ⟨frame [e, t, (i + 1 : ℕ), if i + 1 < y + 1 then 1 else 0], μ⟩) y (16 * e + 23)
    (by simp) ?round ?done le_rfl) (by simp; ring_nf; omega)
  case round =>
    rintro i _ hi rfl
    -- cand := cand + 1; more := powLt(cand, e, t)
    refine ⟨by light_side, by simp [hi], Ends.setToThen (i + 1 + 1 : ℕ)
      (Ends.callTo (test (i + 1 + 1) (by omega) (by omega)) ?_)⟩
    rintro _ μ' ⟨rfl, hμ⟩
    simp [hμ]
  case done =>
    rintro _ rfl
    -- return cand
    exact ⟨by light_side, by simp, Ends.setTo (y + 1 : ℕ) (by simp) (hT := by simp; ring_nf; omega)⟩

/-- Rounding a root down is rounding the root of the next number up, minus one. -/
theorem rootCeil_succ {e : ℕ} (he : e ≠ 0) (t : ℕ) : rootCeil e (t + 1) = rootFloor e t + 1 := by
  have h : ∀ g, rootCeil e (t + 1) ≤ g ↔ rootFloor e t + 1 ≤ g := fun g => by
    rw [rootCeil_le_iff he (by omega), Nat.succ_le_iff, Nat.succ_le_iff, ← not_le, ← not_le,
      le_rootFloor_iff he]
  exact le_antisymm ((h _).2 le_rfl) ((h _).1 le_rfl)

/-! ## The four parameters of the proof of Theorem 19 -/

/-- d26(n), over the procedure pRoot (rootCeil): ⌊n^{1/18}⌋.  Local 0 is the argument, local 1 takes
⌈(n + 1)^{1/18}⌉. -/
def d26Body (pRoot : ℕ) : Stmt :=
  .call pRoot [k 18, v 0 +' k 1] 1 ;;
  .set 0 (v 1 -' k 1)

/-- The time of d26. -/
def tD26 (n : ℕ) : ℕ := (paramD₂₆Nat n + 1) * 315 + 10

/-- **d26** returns ⌊n^{1/18}⌋. -/
theorem d26_spec {μ : ℕ → ℤ} {pRoot pPow n : ℕ} (hR : P[pRoot]? = some (rootCeilBody pPow))
    (hP : P[pPow]? = some powLtBody)
    (hword : (((n + 1) * (paramD₂₆Nat n + 1) + 19 : ℕ) : ℤ) ≤ lim.word) (hd : d + 1 < lim.depth) :
    Ends lim P d (d26Body pRoot) ⟨frame [n], μ⟩ (tD26 n) fun σ' =>
      σ'.loc 0 = (paramD₂₆Nat n : ℕ) ∧ σ'.mem = μ := by
  have hroot : rootCeil 18 (n + 1) = paramD₂₆Nat n + 1 := rootCeil_succ (by norm_num) n
  have hn : n + 1 ≤ (n + 1) * (paramD₂₆Nat n + 1) := Nat.le_mul_of_pos_right _ (by omega)
  have hD : paramD₂₆Nat n + 1 ≤ (n + 1) * (paramD₂₆Nat n + 1) := Nat.le_mul_of_pos_left _ (by omega)
  -- root := rootCeil(18, n + 1)
  refine Ends.callToThen (rootCeil_meets (e := 18) (t := n + 1) hR hP (by norm_num) (by omega)
    (by rw [hroot]; exact hword) (by omega)) ?_ (hT := by simp [tD26, tRootCeil, hroot]; omega)
  rintro _ μ' ⟨rfl, hμ⟩
  -- return root - 1
  rw [hroot, hμ]
  exact Ends.setTo (paramD₂₆Nat n) (by simp) (hT := by simp [tD26, tRootCeil, hroot]; omega)

/-- **d26** as a procedure. -/
theorem d26_meets {μ : ℕ → ℤ} {pD26 pRoot pPow n : ℕ} (hD : P[pD26]? = some (d26Body pRoot))
    (hR : P[pRoot]? = some (rootCeilBody pPow)) (hP : P[pPow]? = some powLtBody)
    (hword : (((n + 1) * (paramD₂₆Nat n + 1) + 19 : ℕ) : ℤ) ≤ lim.word) (hd : d + 1 < lim.depth) :
    Meets lim P pD26 d [n] μ (tD26 n) fun r μ' => r = (paramD₂₆Nat n : ℕ) ∧ μ' = μ :=
  Meets.of_body hD (d26_spec hR hP hword hd)

/-- d5(n), over the procedure pD26: the largest power of four that is at most n^{1/18}.  Local 0 is
the argument, local 1 is ⌊n^{1/18}⌋, local 2 the power of four. -/
def d5Body (pD26 : ℕ) : Stmt :=
  .call pD26 [v 0] 1 ;;
  .set 2 (k 1) ;;
  .while (k 4 *' v 2 ≤' v 1) (.set 2 (k 4 *' v 2)) ;;
  .set 0 (v 2)

/-- The time of d5. -/
def tD5 (n : ℕ) : ℕ := tD26 n + 12 * Nat.log 4 (paramD₂₆Nat n) + 15

/-- The test of the loop of d5: 4^(i+1) ≤ y if and only if i < ⌊log₄ y⌋. -/
theorem four_mul_pow_le_iff (y i : ℕ) : 4 * 4 ^ i ≤ y ↔ i < Nat.log 4 y := by
  rcases Nat.eq_zero_or_pos y with rfl | hy
  · simp
  · rw [Nat.mul_comm, ← pow_succ, ← Nat.le_log_iff_pow_le (by norm_num) hy.ne', Nat.succ_le_iff]

/-- **d5** returns the largest power of four that is at most n^{1/18}. -/
theorem d5_spec {μ : ℕ → ℤ} {pD26 pRoot pPow n : ℕ} (hD : P[pD26]? = some (d26Body pRoot))
    (hR : P[pRoot]? = some (rootCeilBody pPow)) (hP : P[pPow]? = some powLtBody)
    (hword : (((n + 1) * (paramD₂₆Nat n + 1) + 19 : ℕ) : ℤ) ≤ lim.word)
    (hword4 : ((4 * (paramD₂₆Nat n + 1) : ℕ) : ℤ) ≤ lim.word) (hd : d + 2 < lim.depth) :
    Ends lim P d (d5Body pD26) ⟨frame [n], μ⟩ (tD5 n) fun σ' =>
      σ'.loc 0 = (paramD₅Nat n : ℕ) ∧ σ'.mem = μ := by
  rw [show paramD₅Nat n = 4 ^ Nat.log 4 (paramD₂₆Nat n) by
    rw [paramD₅Nat, findGreatest_four_pow, paramD₂₆Nat]]
  unfold tD5
  -- root := d26(n)
  light_call (d26_meets hD hR hP hword (by omega)) with _ μ' ⟨rfl, hμ⟩
  rw [hμ]
  have test := four_mul_pow_le_iff (paramD₂₆Nat n)
  generalize paramD₂₆Nat n = y at hword4 test
  generalize Nat.log 4 y = L at test
  -- pow := 1
  light_set (1 : ℕ)
  -- while 4 pow ≤ root: pow := 4 pow.  Before round i, pow = 4^i.
  refine Ends.next _ (Ends.whileBlock (fun i σ => σ = ⟨frame [n, y, (4 ^ i : ℕ)], μ⟩) L (by simp)
    ?round ?done le_rfl)
  case round =>
    rintro i _ hi rfl
    have hle := (test i).2 hi
    rw [pow_succ, Nat.mul_comm]
    generalize 4 ^ i = q at hle
    exact ⟨by light_side, by light_side, by light_side, by simp [update_frame_setLocal]⟩
  case done =>
    rintro _ rfl
    have hnot := mt (test L).1 (lt_irrefl L)
    have hprev : L = 0 ∨ 4 ^ L ≤ y := by
      rcases Nat.eq_zero_or_pos L with h | h
      · exact Or.inl h
      · obtain ⟨i, rfl⟩ : ∃ i, L = i + 1 := ⟨L - 1, by omega⟩
        exact Or.inr (by rw [pow_succ, Nat.mul_comm]; exact (test i).2 (Nat.lt_succ_self i))
    have hsmall : 4 ^ L ≤ y + 1 := by
      rcases hprev with rfl | h
      · simp
      · omega
    generalize 4 ^ L = q at hnot hsmall
    -- return pow
    exact ⟨by light_side, by light_side, Ends.setTo q (by simp)⟩

/-- g5(D), over the procedure pRoot: ⌈D^{1/36}⌉. -/
def g5Body (pRoot : ℕ) : Stmt := .call pRoot [k 36, v 0] 0

/-- The time of g5. -/
def tG5 (D : ℕ) : ℕ := paramG₅Nat D * 603 + 4

/-- **g5** returns ⌈D^{1/36}⌉, for D ≥ 1. -/
theorem g5_spec {μ : ℕ → ℤ} {pRoot pPow D : ℕ} (hR : P[pRoot]? = some (rootCeilBody pPow))
    (hP : P[pPow]? = some powLtBody) (hD : 1 ≤ D)
    (hword : ((D * paramG₅Nat D + 37 : ℕ) : ℤ) ≤ lim.word) (hd : d + 1 < lim.depth) :
    Ends lim P d (g5Body pRoot) ⟨frame [D], μ⟩ (tG5 D) fun σ' =>
      σ'.loc 0 = (paramG₅Nat D : ℕ) ∧ σ'.mem = μ := by
  have hpos : (0 : ℤ) ≤ ((D * paramG₅Nat D : ℕ) : ℤ) := Int.natCast_nonneg _
  rw [Nat.cast_add] at hword
  refine Ends.callTo (rootCeil_meets (e := 36) (t := D) hR hP (by norm_num) hD
    (by exact_mod_cast hword) (by omega)) (fun r μ' h => by simpa [paramG₅Nat] using h)
    (hT := by simp [tG5, tRootCeil, paramG₅Nat]; omega)

/-- g26(D), over the procedure pRoot: ⌈D^{0.0315}⌉, the least g with g^2000 ≥ D^63.  Local 0 is the
argument, local 1 counts the factors, local 2 is their product. -/
def g26Body (pRoot : ℕ) : Stmt :=
  .set 1 (k 0) ;;
  .set 2 (k 1) ;;
  .while (v 1 <' k 63) (
    .set 2 (v 2 *' v 0) ;;
    .set 1 (v 1 +' k 1)) ;;
  .call pRoot [k 2000, v 2] 0

/-- The time of g26. -/
def tG26 (D : ℕ) : ℕ := paramG₂₆Nat D * 32027 + 768

/-- **g26** returns ⌈D^{0.0315}⌉, for D ≥ 1. -/
theorem g26_spec {μ : ℕ → ℤ} {pRoot pPow D : ℕ} (hR : P[pRoot]? = some (rootCeilBody pPow))
    (hP : P[pPow]? = some powLtBody) (hD : 1 ≤ D)
    (hword : ((D ^ 63 * paramG₂₆Nat D + 2001 : ℕ) : ℤ) ≤ lim.word) (hd : d + 1 < lim.depth) :
    Ends lim P d (g26Body pRoot) ⟨frame [D], μ⟩ (tG26 D) fun σ' =>
      σ'.loc 0 = (paramG₂₆Nat D : ℕ) ∧ σ'.mem = μ := by
  have hpos : 1 ≤ paramG₂₆Nat D := Nat.succ_le_succ (Nat.zero_le _)
  have hfits : ((D ^ 63 + 2001 : ℕ) : ℤ) ≤ lim.word := le_trans
    (by exact_mod_cast Nat.add_le_add_right (Nat.le_mul_of_pos_right _ hpos) 2001) hword
  rw [Nat.cast_add] at hfits
  have hpow0 : (0 : ℤ) ≤ ((D ^ 63 : ℕ) : ℤ) := Int.natCast_nonneg _
  unfold tG26
  -- cnt := 0; prod := 1
  light_set (0 : ℕ)
  light_set (1 : ℕ)
  -- while cnt < 63: prod := prod * D; cnt := cnt + 1.  Before round i, prod = D^i.
  refine Ends.next _ (Ends.whileBlock (fun i σ => σ = ⟨frame [D, i, (D ^ i : ℕ)], μ⟩) 63 (by simp)
    ?round ?done le_rfl)
  case round =>
    rintro i _ hi rfl
    have hle : ((D ^ (i + 1) : ℕ) : ℤ) ≤ ((D ^ 63 : ℕ) : ℤ) := by
      exact_mod_cast Nat.pow_le_pow_right hD hi
    have hmul : ((D ^ i : ℕ) : ℤ) * D = ((D ^ (i + 1) : ℕ) : ℤ) := by push_cast; ring
    have hmul0 : (0 : ℤ) ≤ ((D ^ (i + 1) : ℕ) : ℤ) := Int.natCast_nonneg _
    generalize ((D ^ (i + 1) : ℕ) : ℤ) = q' at hle hmul hmul0
    generalize ((D ^ i : ℕ) : ℤ) = q at hmul
    exact ⟨by light_side, by light_side, by light_side [hmul],
      by simp [update_frame_setLocal, hmul]⟩
  case done =>
    rintro _ rfl
    -- return rootCeil(2000, prod)
    exact ⟨by light_side, by light_side,
      Ends.callTo (rootCeil_meets (e := 2000) (t := D ^ 63) hR hP (by norm_num)
        (Nat.one_le_pow _ _ hD) hword (by omega)) (fun r μ' h => by simpa [paramG₂₆Nat] using h)
        (hT := by simp [tRootCeil, paramG₂₆Nat]; omega)⟩

/-! ## ⌊n²/√D⌋ and quotients rounded up -/

/-- queryCapNat(n, D).  Locals 0 and 1 are the arguments, local 2 is n⁴, local 3 the candidate. -/
def queryCapNatBody : Stmt :=
  .set 2 (v 0 *' v 0 *' v 0 *' v 0) ;;
  .set 3 (k 0) ;;
  .while ((v 3 +' k 1) *' (v 3 +' k 1) *' v 1 ≤' v 2) (.set 3 (v 3 +' k 1)) ;;
  .set 0 (v 3)

/-- The time of queryCapNat. -/
def tQueryCapNat (n D : ℕ) : ℕ := 18 * queryCapNat n D + 26

/-- The numbers that the test of queryCapNat forms for a candidate c that is at most the result
C. -/
private theorem queryCapNat_test_bounds {n D C c : ℕ} (hD : 1 ≤ D)
    (hmax : (C + 1) * (C + 1) * D ≤ 4 * n ^ 4 + D) (hc : c ≤ C) :
    (c : ℤ) + 1 ≤ ((c : ℤ) + 1) * ((c : ℤ) + 1) ∧
      ((c : ℤ) + 1) * ((c : ℤ) + 1) ≤ ((c : ℤ) + 1) * ((c : ℤ) + 1) * D ∧
      ((c : ℤ) + 1) * ((c : ℤ) + 1) * D ≤ 4 * ((n ^ 4 : ℕ) : ℤ) + D := by
  have hmono : (c + 1) * (c + 1) * D ≤ (C + 1) * (C + 1) * D :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul (by omega) (by omega))
  exact ⟨by exact_mod_cast Nat.le_mul_of_pos_right (c + 1) (Nat.succ_pos c),
    by exact_mod_cast Nat.le_mul_of_pos_right ((c + 1) * (c + 1)) hD,
    by exact_mod_cast hmono.trans hmax⟩

/-- **queryCapNat** returns ⌊n²/√D⌋, for D ≥ 1. -/
theorem queryCapNat_meets {μ : ℕ → ℤ} {q n D : ℕ} (hP : P[q]? = some queryCapNatBody) (hD : 1 ≤ D)
    (hword : ((4 * n ^ 4 + D + 2 : ℕ) : ℤ) ≤ lim.word) :
    Meets lim P q d [n, D] μ (tQueryCapNat n D) fun r μ' => r = (queryCapNat n D : ℕ) ∧ μ' = μ := by
  refine .of_body hP ?_
  have test : ∀ c : ℕ, c + 1 ≤ queryCapNat n D ↔
      ((c : ℤ) + 1) * ((c : ℤ) + 1) * D ≤ ((n ^ 4 : ℕ) : ℤ) := fun c =>
    (queryCapNat_succ_le_iff hD c).trans (by exact_mod_cast Iff.rfl)
  have bounds := fun c =>
    queryCapNat_test_bounds (c := c) hD (queryCapNat_succ_sq_mul_le (n := n) hD)
  unfold tQueryCapNat
  generalize queryCapNat n D = C at test bounds
  rw [show ((4 * n ^ 4 + D + 2 : ℕ) : ℤ) = 4 * ((n ^ 4 : ℕ) : ℤ) + D + 2 by push_cast; ring]
    at hword
  have hsq : (n : ℤ) * n ≤ ((n ^ 4 : ℕ) : ℤ) := by
    exact_mod_cast (show n * n ≤ n ^ 4 by
      rw [show n ^ 4 = n * n * (n * n) by ring]; exact Nat.le_mul_self (n * n))
  have hcube : (n : ℤ) * n * n ≤ ((n ^ 4 : ℕ) : ℤ) := by
    exact_mod_cast (show n * n * n ≤ n ^ 4 by
      rw [show n ^ 4 = n * n * (n * n) by ring]
      exact Nat.mul_le_mul_left _ (Nat.le_mul_self n))
  have hfour : (n : ℤ) * n * n * n = ((n ^ 4 : ℕ) : ℤ) := by push_cast; ring
  have hsq0 : (0 : ℤ) ≤ (n : ℤ) * n := by positivity
  have hcube0 : (0 : ℤ) ≤ (n : ℤ) * n * n := by positivity
  generalize ((n ^ 4 : ℕ) : ℤ) = N at *
  -- n4 := n⁴; cand := 0
  light_set N using hfour
  light_set (0 : ℕ)
  -- while (cand + 1)² D ≤ n4: cand := cand + 1
  refine Ends.next _ (Ends.whileBlock (fun c σ => σ = ⟨frame [n, D, N, c], μ⟩) C (by simp) ?round
    ?done le_rfl)
  case round =>
    rintro c _ hc rfl
    have hb := bounds c hc.le
    have hle := (test c).1 hc
    exact ⟨by light_side, by light_side, by light_side, by simp [update_frame_setLocal]⟩
  case done =>
    rintro _ rfl
    have hb := bounds C le_rfl
    have hnot := mt (test C).2 (Nat.not_succ_le_self C)
    -- return cand
    exact ⟨by light_side, by light_side, Ends.setTo C (by simp)⟩

/-- ceilDiv(a, b).  Locals 0 and 1 are the arguments, local 2 is the candidate q, local 3 is
q b. -/
def ceilDivBody : Stmt :=
  .set 2 (k 0) ;;
  .set 3 (k 0) ;;
  .while (v 3 <' v 0) (
    .set 3 (v 3 +' v 1) ;;
    .set 2 (v 2 +' k 1)) ;;
  .set 0 (v 2)

/-- The time of ceilDiv. -/
def tCeilDiv (a b : ℕ) : ℕ := 12 * (a ⌈/⌉ b) + 10

/-- **ceilDiv** returns ⌈a/b⌉, for b ≥ 1. -/
theorem ceilDiv_meets {μ : ℕ → ℤ} {q a b : ℕ} (hP : P[q]? = some ceilDivBody) (hb : 1 ≤ b)
    (hword : ((a + b + 1 : ℕ) : ℤ) ≤ lim.word) :
    Meets lim P q d [a, b] μ (tCeilDiv a b) fun r μ' => r = (a ⌈/⌉ b : ℕ) ∧ μ' = μ := by
  refine .of_body hP ?_
  have test : ∀ i, i < a ⌈/⌉ b ↔ i * b < a := fun i => Nat.lt_ceilDiv_iff hb
  unfold tCeilDiv
  generalize a ⌈/⌉ b = q at test
  -- cand := 0; prod := 0
  light_set (0 : ℕ)
  light_set (0 : ℕ)
  -- while prod < a: prod := prod + b; cand := cand + 1.  Before round i, prod = i b.
  refine Ends.next _ (Ends.whileBlock (fun i σ => σ = ⟨frame [a, b, i, (i * b : ℕ)], μ⟩) q (by simp)
    ?round ?done le_rfl)
  case round =>
    rintro i _ hi rfl
    have hlt := (test i).1 hi
    have hle : i ≤ i * b := Nat.le_mul_of_pos_right i hb
    rw [Nat.succ_mul]
    generalize i * b = m at hlt hle
    exact ⟨by light_side, by light_side, by light_side, by simp [update_frame_setLocal]⟩
  case done =>
    rintro _ rfl
    have hnot := mt (test q).2 (lt_irrefl q)
    generalize q * b = m at hnot
    -- return cand
    exact ⟨by light_side, by light_side, Ends.setTo q (by simp)⟩

end Light.Sec3
