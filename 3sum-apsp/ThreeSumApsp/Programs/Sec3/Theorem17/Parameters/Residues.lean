/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Tasks
public import ThreeSumApsp.Spec.Sec3.Theorem17.Hashing
public import Mathlib.Data.Nat.Size

/-!
# Residues without division

"We reduce the weights modulo a prime p" (proof of Theorem 17).  The language has no division.  The
residue of a number w modulo p is found by greedy subtraction of 2^len p, …, 2p, p, which are kept
in a table.

* bitLen(U) returns the number of binary digits of U, by doubling (`bitLen_spec`).
* dblTable(dst, p, len) writes p, 2p, …, 2^len p to dst (`dblTable_spec`).
* resid(w, dbl, len) returns w mod p, for |w| < 2^len, given the table at dbl (`resid_meets`).  What
  the routine holds after i rounds is `greedyAt p len w i`: it is not negative, below 2^(len+1-i) p,
  and congruent to w (`greedyAt_inv`), so that it ends with the residue (`greedyAt_end`).
* residues(src, dst, m, dbl, len) writes the residues of the m numbers at src to dst, by one call of
  resid for each (`residues_spec`).
-/

@[expose] public section

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## The number of binary digits -/

namespace BitLen

/-- The local variables of bitLen: the argument U, the number of doublings, and the power of two. -/
abbrev Arg : ℕ := 0
@[inherit_doc Arg] abbrev Len : ℕ := 1
@[inherit_doc Arg] abbrev Pow : ℕ := 2

end BitLen

open BitLen in
/-- bitLen(U). -/
def bitLenBody : Stmt :=
  .set Len (k 0) ;;
  .set Pow (k 1) ;;
  .while (v Pow ≤' v Arg) (
    .set Pow (v Pow +' v Pow) ;;
    .set Len (v Len +' k 1)) ;;
  .set Arg (v Len)

/-- The time of bitLen. -/
def tBitLen (U : ℕ) : ℕ := 14 * bitLen U + 12

/-- **bitLen** returns the least len with U < 2^len and changes no cell.  It forms numbers up to
2U + 1. -/
theorem bitLen_spec {μ : ℕ → ℤ} {U : ℕ} (hU : ((2 * U + 2 : ℕ) : ℤ) ≤ lim.word) :
    Ends lim P d bitLenBody ⟨frame [U], μ⟩ (tBitLen U) fun σ' =>
      σ'.loc 0 = (bitLen U : ℕ) ∧ σ'.mem = μ := by
  have hlow : ∀ j, j < bitLen U → 2 ^ j ≤ U := fun j hj => Nat.lt_size.1 hj
  have hup : U < 2 ^ bitLen U := Nat.lt_size_self U
  push_cast at hU
  unfold tBitLen
  generalize bitLen U = n at hlow hup
  -- len := 0; pow := 1
  light_set (0 : ℕ)
  light_set (1 : ℕ)
  -- while pow ≤ U: pow := pow + pow; len := len + 1.  Before round j, len = j and pow = 2^j.
  refine Ends.next _ (Ends.whileBlock (fun j σ => σ = ⟨frame [U, j, (2 ^ j : ℕ)], μ⟩) n
    (by simp) ?round ?done le_rfl)
  case round =>
    rintro j _ hj rfl
    have hpow := hlow j hj
    have hjlt : j < 2 ^ j := Nat.lt_two_pow_self
    have hsucc : 2 ^ (j + 1) = 2 ^ j + 2 ^ j := by ring
    rw [hsucc]
    generalize 2 ^ j = q at hpow hjlt
    exact ⟨by light_side, by light_side, by light_side, by simp [update_frame_setLocal]⟩
  case done =>
    rintro _ rfl
    have hupZ : (U : ℤ) < 2 ^ n := by exact_mod_cast hup
    -- return len
    exact ⟨by light_side, by light_side, Ends.setTo n (by simp)⟩

/-! ## The table of the doubles -/

/-- One more entry of the table. -/
theorem dblList_succ (p len : ℕ) :
    dblList p (len + 1) = dblList p len ++ [((p * 2 ^ (len + 1) : ℕ) : ℤ)] := by
  simp [dblList, List.range_succ]

/-- The table has len + 1 entries. -/
@[simp] theorem length_dblList (p len : ℕ) : (dblList p len).length = len + 1 := by simp [dblList]

/-- Entry j of the table is 2^j p. -/
theorem read_dblList {μ : ℕ → ℤ} {dbl p len j : ℕ} (h : Seg μ dbl (dblList p len)) (hj : j ≤ len) :
    μ (dbl + j) = ((p * 2 ^ j : ℕ) : ℤ) := by
  rw [h j (by simp; omega)]
  simp [dblList]

namespace DblTable

/-- The local variables of dblTable: the arguments dst, p, len; the exponent; the entry. -/
abbrev Dst : ℕ := 0
@[inherit_doc Dst] abbrev Prime : ℕ := 1
@[inherit_doc Dst] abbrev Len : ℕ := 2
@[inherit_doc Dst] abbrev Exp : ℕ := 3
@[inherit_doc Dst] abbrev Entry : ℕ := 4

end DblTable

open DblTable in
/-- dblTable(dst, p, len). -/
def dblTableBody : Stmt :=
  .set Exp (k 0) ;;
  .set Entry (v Prime) ;;
  .store (v Dst) (v Entry) ;;
  .while (v Exp <' v Len) (
    .set Entry (v Entry +' v Entry) ;;
    .set Exp (v Exp +' k 1) ;;
    .store (v Dst +' v Exp) (v Entry))

/-- The time of dblTable. -/
def tDblTable (len : ℕ) : ℕ := 17 * len + 11

/-- The state of dblTable before round j: the entries p, …, 2^j p are written, the last of them is
in a local, and no cell outside the table has changed. -/
def DblInv (μ : ℕ → ℤ) (dst p len j : ℕ) (σ : State) : Prop :=
  ∃ μ', σ = ⟨frame [dst, p, len, j, (p * 2 ^ j : ℕ)], μ'⟩ ∧ Seg μ' dst (dblList p j) ∧
    SameOutside μ μ' dst (len + 1)

/-- **dblTable** writes p, 2p, …, 2^len p and changes nothing else.  It forms numbers up to
2^len p. -/
theorem dblTable_spec {μ : ℕ → ℤ} {dst p len : ℕ} (hw : (lim.space : ℤ) ≤ lim.word)
    (hdst : dst + (len + 1) ≤ lim.space) (hp : ((p * 2 ^ len : ℕ) : ℤ) ≤ lim.word) :
    Ends lim P d dblTableBody ⟨frame [dst, p, len], μ⟩ (tDblTable len) fun σ' =>
      Seg σ'.mem dst (dblList p len) ∧ SameOutside μ σ'.mem dst (len + 1) := by
  have hfits : ∀ j ≤ len, ((p * 2 ^ j : ℕ) : ℤ) ≤ lim.word := fun j hj =>
    le_trans (by exact_mod_cast Nat.mul_le_mul_left p (Nat.pow_le_pow_right (by norm_num) hj)) hp
  unfold tDblTable
  -- exp := 0; entry := p; dst[0] := entry
  light_set (0 : ℕ)
  light_set p
  light_store dst p
  -- while exp < len
  refine Ends.whileBlock (DblInv μ dst p len) len ?start ?round ?done
  case start =>
    refine ⟨Function.update μ dst p, by simp, ?_, SameOutside.refl.update ⟨by omega, by omega⟩ _⟩
    simpa [dblList] using (Seg.nil (μ := μ) (a := dst)).snoc p
  case round =>
    rintro j _ hj ⟨μ', rfl, seg, rest⟩
    have hnext := hfits (j + 1) hj
    have hdouble : p * 2 ^ (j + 1) = p * 2 ^ j + p * 2 ^ j := by ring
    have haddr : ((dst : ℤ) + ((j : ℤ) + 1)).toNat = dst + (dblList p j).length := by
      rw [length_dblList]
      omega
    -- entry := entry + entry; exp := exp + 1; dst[exp] := entry
    refine ⟨by light_side, by light_side, ?_, Function.update μ' (dst + (dblList p j).length)
      ((p * 2 ^ (j + 1) : ℕ) : ℤ), ?_, dblList_succ p j ▸ seg.snoc _,
      rest.update ⟨by omega, by rw [length_dblList]; omega⟩ _⟩
    · rw [hdouble] at hnext
      generalize p * 2 ^ j = q at hnext
      light_side
    · rw [hdouble]
      simp [update_frame_setLocal, haddr]
  case done =>
    rintro _ ⟨μ', rfl, seg, rest⟩
    exact ⟨by light_side, by light_side, seg, rest⟩

/-! ## One residue -/

/-- The number that resid holds after i rounds: it starts from w + 2^len p, and round number i
subtracts 2^(len-i) p if that leaves a number that is not negative. -/
def greedyAt (p len : ℕ) (w : ℤ) : ℕ → ℤ
  | 0 => w + ((p * 2 ^ len : ℕ) : ℤ)
  | i + 1 =>
    if ((p * 2 ^ (len - i) : ℕ) : ℤ) ≤ greedyAt p len w i then
      greedyAt p len w i - ((p * 2 ^ (len - i) : ℕ) : ℤ)
    else greedyAt p len w i

/-- A multiple of p is congruent to 0. -/
private theorem mul_pow_modEq_zero (p j : ℕ) : ((p * 2 ^ j : ℕ) : ℤ) ≡ 0 [ZMOD (p : ℤ)] := by
  rw [Int.modEq_zero_iff_dvd, Nat.cast_mul]
  exact Dvd.intro _ rfl

/-- 2^(j+1) p is twice 2^j p. -/
private theorem cast_mul_pow_succ (p j : ℕ) :
    ((p * 2 ^ (j + 1) : ℕ) : ℤ) = 2 * ((p * 2 ^ j : ℕ) : ℤ) := by
  rw [pow_succ]
  push_cast
  ring

/-- After i rounds the number is not negative, below 2^(len+1-i) p, and congruent to w. -/
theorem greedyAt_inv {p len : ℕ} {w : ℤ} (hp : 1 ≤ p) (hw : |w| < 2 ^ len) : ∀ i, i ≤ len + 1 →
    0 ≤ greedyAt p len w i ∧ greedyAt p len w i < ((p * 2 ^ (len + 1 - i) : ℕ) : ℤ) ∧
      greedyAt p len w i ≡ w [ZMOD (p : ℤ)] := by
  intro i
  induction i with
  | zero =>
    intro _
    obtain ⟨hlow, hhigh⟩ := abs_lt.1 hw
    have hle : (2 : ℤ) ^ len ≤ ((p * 2 ^ len : ℕ) : ℤ) := by
      exact_mod_cast Nat.le_mul_of_pos_left (2 ^ len) hp
    rw [greedyAt, Nat.sub_zero, cast_mul_pow_succ]
    exact ⟨by linarith, by linarith,
      by simpa only [add_zero] using (Int.ModEq.refl w).add (mul_pow_modEq_zero p len)⟩
  | succ i ih =>
    intro hi
    obtain ⟨hlow, hhigh, hmod⟩ := ih (by omega)
    rw [show len + 1 - i = (len - i) + 1 by omega, cast_mul_pow_succ] at hhigh
    rw [show len + 1 - (i + 1) = len - i by omega, greedyAt]
    split_ifs with h
    · exact ⟨by linarith, by linarith,
        by simpa only [sub_zero] using hmod.sub (mul_pow_modEq_zero p (len - i))⟩
    · exact ⟨hlow, by linarith, hmod⟩

/-- Greedy subtraction gives the remainder. -/
theorem greedyAt_end {p len : ℕ} {w : ℤ} (hp : 1 ≤ p) (hw : |w| < 2 ^ len) :
    greedyAt p len w (len + 1) = (resid p w : ℕ) := by
  obtain ⟨hlow, hhigh, hmod⟩ := greedyAt_inv hp hw (len + 1) le_rfl
  rw [Nat.sub_self, pow_zero, mul_one] at hhigh
  rw [resid_cast (by omega), ← Int.emod_eq_of_lt hlow hhigh]
  exact hmod

/-- Every number that resid holds is below 2^(len+1) p. -/
theorem greedyAt_lt {p len : ℕ} {w : ℤ} (hp : 1 ≤ p) (hw : |w| < 2 ^ len) {i : ℕ}
    (hi : i ≤ len + 1) : greedyAt p len w i < ((p * 2 ^ (len + 1) : ℕ) : ℤ) := by
  obtain ⟨-, hhigh, -⟩ := greedyAt_inv hp hw i hi
  exact hhigh.trans_le (by
    exact_mod_cast Nat.mul_le_mul_left p (Nat.pow_le_pow_right (by norm_num) (by omega)))

namespace Resid

/-- The local variables of resid: the arguments w, dbl, len; one more than the next exponent; the
number that is reduced. -/
abbrev Arg : ℕ := 0
@[inherit_doc Arg] abbrev Dbl : ℕ := 1
@[inherit_doc Arg] abbrev Len : ℕ := 2
@[inherit_doc Arg] abbrev Exp : ℕ := 3
@[inherit_doc Arg] abbrev Num : ℕ := 4

end Resid

open Resid in
/-- resid(w, dbl, len). -/
def residBody : Stmt :=
  .set Num (v Arg +' M (v Dbl +' v Len)) ;;
  .set Exp (v Len +' k 1) ;;
  .while (k 0 <' v Exp) (
    .set Exp (v Exp -' k 1) ;;
    .ite (M (v Dbl +' v Exp) ≤' v Num) (.set Num (v Num -' M (v Dbl +' v Exp))) .skip) ;;
  .set Arg (v Num)

/-- The time of resid. -/
def tResid (len : ℕ) : ℕ := 24 * len + 41

/-- **resid** returns w mod p and changes no cell.  It forms numbers up to 2^(len+1) p. -/
theorem resid_meets {μ : ℕ → ℤ} {pResid dbl p len : ℕ} {w : ℤ} (hP : P[pResid]? = some residBody)
    (hw : (lim.space : ℤ) ≤ lim.word) (hp : 1 ≤ p) (hseg : Seg μ dbl (dblList p len))
    (hlt : |w| < 2 ^ len) (hdbl : dbl + (len + 1) ≤ lim.space)
    (hword : ((p * 2 ^ (len + 1) : ℕ) : ℤ) ≤ lim.word) :
    Meets lim P pResid d [w, dbl, len] μ (tResid len) fun r μ' => r = (resid p w : ℕ) ∧ μ' = μ := by
  refine .of_body hP ?_
  have hlow := fun i hi => (greedyAt_inv hp hlt i hi).1
  have hhigh := fun i (hi : i ≤ len + 1) => greedyAt_lt hp hlt hi
  unfold tResid
  -- num := w + dbl[len]; exp := len + 1
  have hlow0 := hlow 0 (by omega)
  have hhigh0 := hhigh 0 (by omega)
  have hfirst : w + μ (dbl + len) = greedyAt p len w 0 := by rw [read_dblList hseg le_rfl, greedyAt]
  light_set (greedyAt p len w 0) using hfirst
  light_set (len + 1 : ℕ)
  -- while 0 < exp.  Before round i, exp = len + 1 - i and num = greedyAt p len w i.
  refine Ends.next _ (Ends.whileBlock
    (fun i σ => σ = ⟨frame [w, dbl, len, (len + 1 - i : ℕ), greedyAt p len w i], μ⟩) (len + 1)
    (by simp) ?round ?done le_rfl) (by simp; omega)
  case round =>
    rintro i _ hi rfl
    have hlowi := hlow i hi.le
    have hhighi := hhigh i hi.le
    have hread := read_dblList hseg (show len - i ≤ len by omega)
    have hexp : ((len + 1 - i : ℕ) : ℤ) - 1 = (len - i : ℕ) := by omega
    have hnext : len + 1 - (i + 1) = len - i := by omega
    have hpos : (0 : ℤ) ≤ ((p * 2 ^ (len - i) : ℕ) : ℤ) := Int.natCast_nonneg _
    rw [hnext, greedyAt]
    generalize greedyAt p len w i = g at hlowi hhighi
    generalize ((p * 2 ^ (len - i) : ℕ) : ℤ) = q at hread hpos
    -- exp := exp - 1; if dbl[exp] ≤ num then num := num - dbl[exp]
    refine ⟨by light_side, by light_side, ?_, ?_⟩
    · simp [Limits.Addr, abs_le, hexp, hread]
      omega
    · by_cases hle : q ≤ g <;> simp [update_frame_setLocal, hexp, hread, hle]
  case done =>
    rintro _ rfl
    -- return num
    exact ⟨by light_side, by light_side,
      Ends.setTo (greedyAt p len w (len + 1)) (by simp [greedyAt_end hp hlt])
      (hT := by simp; omega)⟩

/-! ## The residues of a list -/

namespace Residues

/-- The local variables of residues: the arguments src, dst, m, dbl, len; the counter; the
residue. -/
abbrev Src : ℕ := 0
@[inherit_doc Src] abbrev Dst : ℕ := 1
@[inherit_doc Src] abbrev Num : ℕ := 2
@[inherit_doc Src] abbrev Dbl : ℕ := 3
@[inherit_doc Src] abbrev Len : ℕ := 4
@[inherit_doc Src] abbrev Idx : ℕ := 5
@[inherit_doc Src] abbrev Res : ℕ := 6

end Residues

open Residues in
/-- residues(src, dst, m, dbl, len).  The parameter pResid is the number of the procedure resid in
the program. -/
def residuesBody (pResid : ℕ) : Stmt :=
  .for Idx (v Num) (
    .call pResid [M (v Src +' v Idx), v Dbl, v Len] Res ;;
    .store (v Dst +' v Idx) (v Res))

/-- The time of residues. -/
def tResidues (m len : ℕ) : ℕ := m * (tResid len + 21) + 6

/-- What residues assumes: the table of the doubles of p stands at dbl, and the list l of m numbers
of absolute value at most U < 2^len at src; the m cells at dst lie in the memory and meet
neither. -/
structure ResiduesPre (lim : Limits) (μ : ℕ → ℤ) (src dst m dbl p len U : ℕ) (l : List ℤ) :
    Prop where
  hw : (lim.space : ℤ) ≤ lim.word
  prime : 1 ≤ p
  segDbl : Seg μ dbl (dblList p len)
  segSrc : Seg μ src l
  length : l.length = m
  le : AbsLe l U
  lt : U < 2 ^ len
  spaceDbl : dbl + (len + 1) ≤ lim.space
  spaceSrc : src + m ≤ lim.space
  spaceDst : dst + m ≤ lim.space
  count : m < lim.space
  apartSrc : Apart dst m src m
  apartDbl : Apart dst m dbl (len + 1)
  word : ((p * 2 ^ (len + 1) : ℕ) : ℤ) ≤ lim.word

/-- The state of residues before round i: the first i residues are written, and no cell outside dst
has changed. -/
def ResiduesInv (μ : ℕ → ℤ) (src dst m dbl p len : ℕ) (l : List ℤ) (i : ℕ) (σ : State) : Prop :=
  ∃ (r : ℤ) (μ' : ℕ → ℤ), σ = ⟨frame [src, dst, m, dbl, len, i, r], μ'⟩ ∧
    SegN μ' dst (residList p (l.take i)) ∧ SameOutside μ μ' dst m

/-- One more residue. -/
theorem residList_take_succ (p : ℕ) {l : List ℤ} {i : ℕ} (hi : i < l.length) :
    residList p (l.take (i + 1)) = residList p (l.take i) ++ [resid p l[i]] := by
  rw [residList, residList, List.take_add_one, List.getElem?_eq_getElem hi, List.map_append]
  rfl

open Residues in
/-- **residues** writes the residues of a list and changes nothing else. -/
theorem residues_spec {μ : ℕ → ℤ} {pResid src dst m dbl p len U : ℕ} {l : List ℤ}
    (hP : P[pResid]? = some residBody) (hd : d < lim.depth)
    (pre : ResiduesPre lim μ src dst m dbl p len U l) :
    Ends lim P d (residuesBody pResid) ⟨frame [src, dst, m, dbl, len], μ⟩ (tResidues m len)
      fun σ' => SegN σ'.mem dst (residList p l) ∧ SameOutside μ σ'.mem dst m := by
  obtain ⟨hw, hp, segDbl, segSrc, rfl, hle, hlt, spaceDbl, spaceSrc, spaceDst, hm, apartSrc,
    apartDbl, hword⟩ := pre
  have hltZ : (U : ℤ) < 2 ^ len := by exact_mod_cast hlt
  unfold tResidues
  -- for i < m
  refine Ends.for (ResiduesInv μ src dst l.length dbl p len l) l.length (tResid len + 13)
    ?start ?round ?done ?bound
  case start =>
    exact ⟨0, μ, congrArg (fun loc => (⟨loc, μ⟩ : State))
      ((update_frame_setLocal _ _ _).trans (frame_append_zeros _ 1).symm), Seg.nil, .refl⟩
  case bound =>
    rintro i _ - - ⟨r, μ', rfl, -, -⟩
    simp
  case round =>
    rintro i _ hi - ⟨r, μ', rfl, seg, rest⟩
    have hread : μ' (src + i) = l[i] := (rest _ (by omega)).trans (segSrc.get hi)
    have hlen : (residList p (l.take i)).length = i := by simp [residList]; omega
    -- res := resid(src[i], dbl, len)
    light_call (resid_meets (w := l[i]) hP hw hp
      (segDbl.keep (by light_keep [length_dblList]))
      ((hle.getElem hi).trans_lt hltZ) spaceDbl hword) using hread with _ μ₁ ⟨rfl, rfl⟩
    -- dst[i] := res
    light_store (dst + i) (resid p l[i] : ℕ)
    refine ⟨by simp, resid p l[i],
      Function.update μ₁ (dst + i) (resid p l[i] : ℕ), by simp [update_frame_setLocal], ?_,
      rest.update ⟨by omega, by omega⟩ _⟩
    have hsnoc := seg.snoc (resid p l[i])
    rwa [hlen, ← residList_take_succ p hi] at hsnoc
  case done =>
    rintro _ - ⟨r, μ', rfl, seg, rest⟩
    exact ⟨by simpa using seg, rest⟩

end Light.Sec3
