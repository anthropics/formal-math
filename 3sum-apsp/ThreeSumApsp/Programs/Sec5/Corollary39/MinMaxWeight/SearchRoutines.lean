/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Lang.Lib.PowTable
public import ThreeSumApsp.Programs.Sec3.Theorem21b.MinPlus.Tasks
public import ThreeSumApsp.Spec.Sec5.Corollary39.MaxTriangleSearch

/-!
# Max-Weight Triangle from Exact Triangle: two routines

pw(x, dst) writes the powers of two up to x to dst and returns their number (`pw_meets`).
mask(n, src, r₀, c₀, Big, dst) copies a matrix and adds Big to the entries in the rows below r₀ and
in the columns below c₀ (`mask_meets`).
-/

@[expose] public section

open ThreeSumApsp.Spec

namespace Light.Sec5

open ThreeSumApsp Light.Sec3

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## The powers of two up to x -/

/-- The number of powers of two up to x, for x ≥ 1. -/
def lv (x : ℕ) : ℕ := Nat.log 2 x + 1

/-- The first power of two that is not written is larger than x. -/
theorem lt_two_pow_lv (x : ℕ) : x < 2 ^ lv x := Nat.lt_pow_succ_log_self (by norm_num) _

/-- The first power of two that is not written is at most 2x. -/
theorem two_pow_lv_le {x : ℕ} (hx : 1 ≤ x) : 2 ^ lv x ≤ 2 * x := by
  have := Nat.pow_log_le_self 2 (show x ≠ 0 by omega)
  rw [lv, pow_succ]
  omega

namespace Pw

/-- The locals of pw(x, dst): the bound x (this local also takes the result), the address of the
table, the power, and its exponent. -/
abbrev Bound : ℕ := 0
@[inherit_doc Bound] abbrev Dst : ℕ := 1
@[inherit_doc Bound] abbrev Power : ℕ := 2
@[inherit_doc Bound] abbrev Expo : ℕ := 3

end Pw

open Pw in
/-- pw(x, dst): p := 1; j := 0; while p ≤ x: dst[j] := p; p := 2p; j := j + 1. -/
def pwBody : Stmt :=
  .set Power (k 1) ;;
  .set Expo (k 0) ;;
  .while (v Power ≤' v Bound) (
    .store (v Dst +' v Expo) (v Power) ;;
    .set Power (k 2 *' v Power) ;;
    .set Expo (v Expo +' k 1)) ;;
  .set Bound (v Expo)

/-- **pw** writes the powers of two up to x, returns their number, and changes nothing else. -/
theorem pw_meets {p : ℕ} (hp : P[p]? = some pwBody) {μ : ℕ → ℤ} {x dst : ℕ} (hx : 1 ≤ x)
    (hw : (lim.space : ℤ) ≤ lim.word) (hdst : dst + lv x < lim.space)
    (hword : ((2 * x + 2 : ℕ) : ℤ) ≤ lim.word) :
    Meets lim P p d [(x : ℤ), dst] μ (19 * lv x + 12) fun r μ' =>
      r = lv x ∧ Seg μ' dst (powList 2 (lv x)) ∧ SameOutside μ μ' dst (lv x) := by
  have hlast : (2 : ℤ) ^ lv x ≤ 2 * x := by exact_mod_cast two_pow_lv_le hx
  have hnext : (x : ℤ) < 2 ^ lv x := by exact_mod_cast lt_two_pow_lv x
  refine .of_body hp ?_
  unfold pwBody
  refine Ends.setToThen 1 (Ends.setToThen 0 ?_)
  -- while p ≤ x: before round j, p = 2^j and the first j cells are filled
  refine Ends.next _ (Ends.whileBlock (fun j σ => σ = ⟨frame [(x : ℤ), dst, 2 ^ j, j],
    wrote μ dst (fun t => 2 ^ t) j⟩) (lv x) ?start ?round ?done (hT := le_rfl))
  case start =>
    rw [wrote_zero]
    simp
  case round =>
    rintro j _ hj rfl
    have hpos : (0 : ℤ) < 2 ^ j := by positivity
    have hle : (2 : ℤ) ^ j * 2 ≤ 2 ^ lv x := by
      rw [← pow_succ]
      exact pow_le_pow_right₀ (by norm_num) hj
    refine ⟨by light_side, by simp; omega, by light_side, ?_⟩
    simp [update_frame_setLocal, ← wrote_succ, pow_succ, mul_comm]
  case done =>
    rintro _ rfl
    refine ⟨by light_side, by simp; omega, ?_⟩
    -- the result
    light_set (lv x)
    refine ⟨by simp, fun t ht => ?_, sameOutside_wrote le_rfl⟩
    rw [getElem_powList]
    exact (wrote_done (by simpa using ht)).trans (by simp)

/-! ## Switching off rows and columns -/

namespace Mask

/-- The locals of mask(n, src, r₀, c₀, Big, dst).  The arguments; then the place, its row and its
column, n², and what is added at this place. -/
abbrev Size : ℕ := 0
@[inherit_doc Size] abbrev Src : ℕ := 1
@[inherit_doc Size] abbrev RowLo : ℕ := 2
@[inherit_doc Size] abbrev ColLo : ℕ := 3
@[inherit_doc Size] abbrev Large : ℕ := 4
@[inherit_doc Size] abbrev Dst : ℕ := 5
@[inherit_doc Size] abbrev Place : ℕ := 6
@[inherit_doc Size] abbrev Row : ℕ := 7
@[inherit_doc Size] abbrev Col : ℕ := 8
@[inherit_doc Size] abbrev Cells : ℕ := 9
@[inherit_doc Size] abbrev Add : ℕ := 10

end Mask

open Mask in
/-- What is added: Big in the rows below r₀ and in the columns below c₀, and 0 elsewhere. -/
def maskAdd : Stmt :=
  .ite (v Row <' v RowLo) (.set Add (v Large))
    (.ite (v Col <' v ColLo) (.set Add (v Large)) (.set Add (k 0)))

open Mask in
/-- The entry is written; then the row and the column of the next place. -/
def maskWrite : Stmt :=
  .store (v Dst +' v Place) (M (v Src +' v Place) +' v Add) ;;
  .set Col (v Col +' k 1) ;;
  .ite (v Col =' v Size) (.set Col (k 0) ;; .set Row (v Row +' k 1)) .skip

open Mask in
/-- mask(n, src, r₀, c₀, Big, dst): for all places q < n². -/
def maskBody : Stmt :=
  .set Cells (v Size *' v Size) ;;
  .set Row (k 0) ;;
  .set Col (k 0) ;;
  .for Place (v Cells) (maskAdd ;; maskWrite)

/-- What is added at the place q. -/
def maskAt (n : ℕ) (r₀ c₀ Big : ℤ) (q : ℕ) : ℤ :=
  if ((q / n : ℕ) : ℤ) < r₀ ∨ ((q % n : ℕ) : ℤ) < c₀ then Big else 0

section mask

variable {n src dst : ℕ} {r₀ c₀ Big : ℤ}

/-- **What is added** at the place q. -/
theorem maskAdd_spec (hword : 0 ≤ lim.word) (μ : ℕ → ℤ) (q : ℕ) (a₉ z : ℤ) :
    Ends lim P d maskAdd
      ⟨frame [(n : ℤ), src, r₀, c₀, Big, dst, q, (q / n : ℕ), (q % n : ℕ), a₉, z], μ⟩ 10
      fun σ' => σ' = ⟨frame [(n : ℤ), src, r₀, c₀, Big, dst, q, (q / n : ℕ), (q % n : ℕ), a₉,
        maskAt n r₀ c₀ Big q], μ⟩ := by
  unfold maskAdd maskAt
  refine Ends.iteLast (fun hrow => ?_) fun hrow => Ends.iteLast (fun hcol => ?_) fun hcol => ?_
  · light_set Big
    exact by rw [if_pos (.inl (by simpa using hrow))]; rfl
  · light_set Big
    exact by rw [if_pos (.inr (by simpa using hcol))]; rfl
  · light_set 0
    exact by
      rw [if_neg (not_or.2 ⟨by simpa using hrow, by simpa using hcol⟩)]
      rfl

/-- **The entry is written**, and the row and the column are those of the next place. -/
theorem maskWrite_spec {μ : ℕ → ℤ} {f : ℕ → ℤ} {q : ℕ} {y z : ℤ} (hn : 1 ≤ n) (hq : q < n * n)
    (hw : (lim.space : ℤ) ≤ lim.word) (hsrc : src + n * n ≤ lim.space)
    (hdst : dst + n * n < lim.space) (hread : wrote μ dst f q (src + q) = y) (hf : y + z = f q)
    (hfits : |f q| ≤ lim.word) (a₉ : ℤ) :
    Ends lim P d maskWrite
      ⟨frame [(n : ℤ), src, r₀, c₀, Big, dst, q, (q / n : ℕ), (q % n : ℕ), a₉, z],
        wrote μ dst f q⟩ 24
      fun σ' => σ' = ⟨frame [(n : ℤ), src, r₀, c₀, Big, dst, q, ((q + 1) / n : ℕ),
        ((q + 1) % n : ℕ), a₉, z], wrote μ dst f (q + 1)⟩ := by
  have hmod := Nat.mod_lt q (show 0 < n by omega)
  have hdiv : q / n < n := Nat.div_lt_of_lt_mul hq
  have hnn : n ≤ n * n := Nat.le_mul_of_pos_left _ (by omega)
  have hfits' := abs_le.1 hfits
  have hend := Nat.succ_div_mod_of_eq (n := n) (i := q)
  have hgoes := Nat.succ_div_mod_of_ne (i := q) hn
  generalize (q + 1) / n = row', (q + 1) % n = col', q / n = row, q % n = col at *
  unfold maskWrite
  -- dst[q] := src[q] + what is added
  light_store (dst + q) (f q) using hread, hf
  rw [wrote_succ]
  light_set (col + 1 : ℕ)
  -- if the row has ended, the next row begins
  refine Ends.iteLast (fun hc => ?_) fun hc => ?_
  · obtain ⟨rfl, rfl⟩ := hend (by
      have : (col : ℤ) + 1 = n := by simpa using hc
      omega)
    exact Ends.setToThen 0 (Ends.setTo (row + 1 : ℕ) rfl)
  · obtain ⟨rfl, rfl⟩ := hgoes fun h => hc (by simp; omega)
    exact Ends.skip rfl

/-- **mask** writes the matrix with the rows below r₀ and the columns below c₀ switched off, and
changes nothing else. -/
theorem mask_meets {p : ℕ} (hp : P[p]? = some maskBody) {μ : ℕ → ℤ} {l : List ℤ} (hn : 1 ≤ n)
    (hl : Seg μ src l) (hlen : l.length = n * n) (hw : (lim.space : ℤ) ≤ lim.word)
    (hsrc : src + n * n ≤ lim.space) (hdst : dst + n * n < lim.space)
    (hsep : src + n * n ≤ dst ∨ dst + n * n ≤ src)
    (hb : ∀ x ∈ l, |x| ≤ lim.word ∧ |x + Big| ≤ lim.word) :
    Meets lim P p d [(n : ℤ), src, r₀, c₀, Big, dst] μ (42 * (n * n) + 14) fun _ μ' =>
      Seg μ' dst (maskL n r₀ c₀ Big l) ∧ SameOutside μ μ' dst (n * n) := by
  obtain ⟨f, hf⟩ : ∃ f : ℕ → ℤ, f = fun q => l.getD q 0 + maskAt n r₀ c₀ Big q := ⟨_, rfl⟩
  refine .of_body hp ?_
  unfold maskBody
  refine Ends.setToThen (n * n : ℕ) (Ends.setToThen 0 (Ends.setToThen 0 ?_))
  -- for q < n²: the entries at the places below q are written
  refine Ends.for (fun q σ => ∃ z : ℤ, σ = ⟨frame [(n : ℤ), src, r₀, c₀, Big, dst, q, (q / n : ℕ),
    (q % n : ℕ), (n * n : ℕ), z], wrote μ dst f q⟩) (n * n) 34 ?start ?round ?done ?bound
  case start =>
    exact ⟨0, by rw [update_frame_setLocal, wrote_zero, ← frame_append_zeros _ 1]; simp⟩
  case bound =>
    rintro q _ - - ⟨z, rfl⟩
    simp
  case done =>
    rintro _ - ⟨z, rfl⟩
    refine ⟨fun i hi => ?_, sameOutside_wrote le_rfl⟩
    change wrote μ dst f (n * n) (dst + i) = _
    rw [wrote_done (by simpa using hi), hf]
    simp [maskL, maskAt]
  case round =>
    rintro q _ hq - ⟨z, rfl⟩
    obtain ⟨hx, hxBig⟩ := hb (l.getD q 0) (by
      rw [List.getD_eq_getElem _ _ (hlen ▸ hq)]
      exact List.getElem_mem _)
    refine Ends.next 10 ((maskAdd_spec (by omega) _ q _ z).mono le_rfl ?_)
    rintro _ rfl
    refine (maskWrite_spec (y := l.getD q 0) hn hq hw hsrc hdst
      ((wrote_rest (by omega)).trans (hl.getD (hlen ▸ hq) 0)) (by rw [hf]) ?_ _).mono le_rfl ?_
    · simp only [hf, maskAt]
      split_ifs
      · exact hxBig
      · simpa using hx
    · rintro _ rfl
      exact ⟨by simp, _, by rw [update_frame_setLocal]; rfl⟩

end mask

end Light.Sec5
