/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Lang.Lib.Pass
public import ThreeSumApsp.Lang.Tactics
public import ThreeSumApsp.Programs.Sec4.Theorem30.Contracts

/-!
# The least string with a given number of nines

nineFirst(a, n, lo) writes n - lo zeros and then lo nines into the cells from a: the first string of
the enumeration `Spec.nineStrs n lo hi`.  The two loops that write zeros and then nines up to the
end of the string are also the end of nineNext, so they are a statement of their own, `fillTail`.

Each of the two loops writes one digit again and again while a test holds (`fillRun`,
`Ends.fillRun`).  Together they write the least string from the current position on
(`fillTail_spec`), and `nineFirst_spec` is the case of the position 0.
-/

@[expose] public section

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.Spec

variable {lim : Limits} {P : Program} {d : ℕ}

namespace Nine

/-- The local variables that nineFirst and nineNext share: the address of the string, its length,
the least number of nines, the current position, and the number of nines that are still to be
written.  Local 0 also takes the result. -/
abbrev Str : ℕ := 0
@[inherit_doc Str] abbrev Result : ℕ := 0
@[inherit_doc Str] abbrev Len : ℕ := 1
@[inherit_doc Str] abbrev MinNines : ℕ := 2
@[inherit_doc Str] abbrev Pos : ℕ := 4
@[inherit_doc Str] abbrev Need : ℕ := 10

end Nine

open Nine

/-! ## One digit again and again -/

/-- While the test holds: mem[str + pos] := c; pos := pos + 1. -/
def fillRun (test : Cond) (c : ℕ) : Stmt :=
  .while test (
    .store (v Str +' v Pos) (k c) ;;
    .set Pos (v Pos +' k 1))

/-- The cells that have been written hold the digit. -/
private theorem segN_wrote_const (μ : ℕ → ℤ) (dst c n : ℕ) :
    SegN (wrote μ dst (fun _ => (c : ℤ)) n) dst (List.replicate n c) := fun i hi => by
  rw [wrote_done (by simpa using hi)]
  simp

/-- **The rule for fillRun.**  The test is safe and holds in the first cnt rounds and no longer; it
may depend on the position, not on the memory.  Then the digit c is written into cnt cells.  (A
constant up to 100 fits in a word.) -/
theorem Ends.fillRun (hs : Std lim) {test : Cond} {c a i₀ cnt T : ℕ} {loc μ : ℕ → ℤ}
    {Q : State → Prop} (hc : c ≤ 100) (ha : a + (i₀ + cnt) < lim.space) (hstr : loc Str = a)
    (hpos : loc Pos = i₀)
    (htest : ∀ j ≤ cnt, ∀ μ', test.Safe lim ⟨Function.update loc Pos ((i₀ + j : ℕ) : ℤ), μ'⟩ ∧
      (test.Holds ⟨Function.update loc Pos ((i₀ + j : ℕ) : ℤ), μ'⟩ ↔ j < cnt))
    (done : Q ⟨Function.update loc Pos ((i₀ + cnt : ℕ) : ℤ),
      wrote μ (a + i₀) (fun _ => (c : ℤ)) cnt⟩)
    (hT : cnt * (test.cost + 1 + 9) + (test.cost + 1) ≤ T := by light_time) :
    Ends lim P d (fillRun test c) ⟨loc, μ⟩ T Q := by
  light_facts hs
  refine Ends.whileBlock (fun j σ => σ = ⟨Function.update loc Pos ((i₀ + j : ℕ) : ℤ),
    wrote μ (a + i₀) (fun _ => (c : ℤ)) j⟩) cnt ?start ?round ?done hT
  case start => rw [wrote_zero, Nat.add_zero, ← hpos, Function.update_eq_self]
  case round =>
    rintro j _ hj rfl
    have haddr : ((a : ℤ) + ((i₀ : ℤ) + j)).toNat = a + i₀ + j := by omega
    refine ⟨(htest j hj.le _).1, (htest j hj.le _).2.mpr hj,
      by light_side [hstr], ?_⟩
    rw [← wrote_succ]
    simp [hstr, haddr, add_assoc]
  case done =>
    rintro _ rfl
    exact ⟨(htest cnt le_rfl _).1, fun h => absurd ((htest cnt le_rfl _).2.mp h) (lt_irrefl _),
      done⟩

/-! ## Zeros and then nines up to the end of the string -/

/-- Writes zeros from the current position on as long as more than need cells remain, and nines into
the remaining cells. -/
def fillTail : Stmt :=
  fillRun (v Pos +' v Need <' v Len) 0 ;;
  fillRun (v Pos <' v Len) 9

/-- fillTail writes the least string with need nines into the cells from the position i₀ on. -/
theorem fillTail_spec (hs : Std lim) {μ : ℕ → ℤ} {a n i₀ need : ℕ} (ha : a + n < lim.space)
    (hfit : i₀ + need ≤ n) (loc : ℕ → ℤ) (hstr : loc Str = a) (hlen : loc Len = n)
    (hpos : loc Pos = i₀) (hneed : loc Need = need) :
    Ends lim P d fillTail ⟨loc, μ⟩ (15 * (n - i₀) + 10) fun σ' =>
      σ'.loc = Function.update loc Pos n ∧ SegN σ'.mem (a + i₀) (nineFirst (n - i₀) need) ∧
        SameOutside μ σ'.mem (a + i₀) (n - i₀) := by
  have hw := hs.space_le
  have hmid : i₀ + (n - i₀ - need) = n - need := by omega
  -- zeros while pos + need < len
  refine Ends.next _ (Ends.fillRun hs (a := a) (i₀ := i₀) (cnt := n - i₀ - need) (by norm_num)
    (by omega) hstr hpos
    (fun j hj μ' => by light_side [hlen, hneed]) ?_ (hT := le_rfl)) (by simp; omega)
  -- nines while pos < len
  refine Ends.fillRun hs (a := a) (i₀ := n - need) (cnt := need) (by norm_num) (by omega)
    (by simpa using hstr) (by simp [hmid]) (fun j hj μ' => by simp [hlen]; omega) ?_
    (by simp; omega)
  -- the zeros are kept by the second loop, and both loops stay within the n - i₀ cells
  have hzeros := segN_wrote_const μ (a + i₀) 0 (n - i₀ - need)
  have hsame₀ : SameOutside μ (wrote μ (a + i₀) (fun _ => ((0 : ℕ) : ℤ)) (n - i₀ - need)) (a + i₀)
      (n - i₀ - need) := sameOutside_wrote le_rfl
  generalize wrote μ (a + i₀) (fun _ => ((0 : ℕ) : ℤ)) (n - i₀ - need) = μ₀ at hzeros hsame₀ ⊢
  have hsame₉ : SameOutside μ₀ (wrote μ₀ (a + (n - need)) (fun _ => ((9 : ℕ) : ℤ)) need)
      (a + (n - need)) need := sameOutside_wrote le_rfl
  refine ⟨by simp [Nat.sub_add_cancel (show need ≤ n by omega)], ?_,
    (hsame₀.mono le_rfl (by omega)).trans (hsame₉.mono (by omega) (by omega))⟩
  have hdst : a + i₀ + (List.map (fun x : ℕ => (x : ℤ)) (List.replicate (n - i₀ - need) 0)).length
      = a + (n - need) := by simp; omega
  rw [nineFirst, SegN, List.map_append, seg_append, hdst]
  exact ⟨hzeros.keep, segN_wrote_const _ _ 9 _⟩

/-! ## The least string -/

/-- nineFirst(str, len, minNines): the least string from the position 0 on. -/
def nineFirstBody : Stmt :=
  .set Pos (k 0) ;;
  .set Need (v MinNines) ;;
  fillTail

/-- **nineFirst** writes the least string of n digits with lo nines. -/
theorem nineFirst_spec (hP : P[Proc.nineFirst]? = some nineFirstBody) (hs : Std lim) :
    NineFirstSpec lim P := by
  intro a n lo μ hlo ha
  refine fun d _ => ⟨nineFirstBody, hP, ?_⟩
  have hword := hs.const_le
  unfold tNineFirst
  -- pos := 0; need := minNines
  light_set (0 : ℕ)
  light_set lo
  -- fillTail
  refine (fillTail_spec hs (i₀ := 0) (need := lo) ha (by omega) _ rfl rfl rfl rfl).mono
    (by simp; omega) ?_
  rintro σ' ⟨-, hseg, hsame⟩
  exact ⟨hseg, hsame⟩

end Light.Sec4
