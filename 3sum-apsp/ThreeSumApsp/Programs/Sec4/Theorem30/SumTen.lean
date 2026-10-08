/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Lang.Tactics
public import ThreeSumApsp.Programs.Sec4.Theorem30.Contracts

/-!
# The value of a box with stars (proof of Lemma 29, "The values")

"For a box π with e ≥ 1 stars, let ℓ be the highest level at which π has a star.  The leaves of π
are the leaves of the ten strings π[ℓ ← λ] obtained by replacing that star by a term λ, and each of
these strings is again a box, with e - 1 stars. […] Hence we compute val(π) = ∑_λ val(π[ℓ ← λ]) with
ten lookups in the trie, in O(L) operations."  The routine writes the ten digits one after the other
at the position of the star, looks each string up, adds, and puts the star back.  It looks in the
trie of the tile, which is being filled.

Before round j the sum of the first j values has been formed, and the memory differs from the
original one at the position of the star only (`SumTen.Inv`).  `SumTenPre` collects what the
routine assumes.  In a round the string with the digit j at the position of the star stands in the
memory (`segN_set`), so lookup returns its value (`SumTen.round_spec`); `sumTen_spec` is the
specification.
-/

@[expose] public section

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.Spec

namespace SumTen

/-- The local variables of sumTen: the arguments (the base of the trie area, the root of the trie,
the address of the box, its length, the position of the star), the digit that stood at that
position, the digit written, the sum, and a value looked up.  Local 0 also takes the result. -/
abbrev Area : ℕ := 0
@[inherit_doc Area] abbrev Result : ℕ := 0
@[inherit_doc Area] abbrev Root : ℕ := 1
@[inherit_doc Area] abbrev Box : ℕ := 2
@[inherit_doc Area] abbrev Len : ℕ := 3
@[inherit_doc Area] abbrev Star : ℕ := 4
@[inherit_doc Area] abbrev Saved : ℕ := 5
@[inherit_doc Area] abbrev Digit : ℕ := 6
@[inherit_doc Area] abbrev Sum : ℕ := 7
@[inherit_doc Area] abbrev Val : ℕ := 8

end SumTen

open SumTen in
/-- One round: write the digit at the position of the star, look the string up, and add. -/
def sumTenRound : Stmt :=
  .store (v Box +' v Star) (v Digit) ;;
  .call Proc.lookup [v Area, v Root, v Box, v Len] Val ;;
  .set Sum (v Sum +' v Val)

open SumTen in
/-- sumTen(area, root, box, len, star): the sum of the values of the ten strings; the digit at the
position of the star is put back at the end. -/
def sumTenBody : Stmt :=
  .set Saved (M (v Box +' v Star)) ;;
  .set Sum (k 0) ;;
  Stmt.for Digit (k 10) sumTenRound ;;
  .store (v Box +' v Star) (v Saved) ;;
  .set Result (v Sum)

/-- A string with one digit replaced, in the memory. -/
private theorem segN_set {μ μ' : ℕ → ℤ} {a p : ℕ} {l : List ℕ} (h : SegN μ a l)
    (hp : p < l.length) (x : ℕ) (hx : μ' (a + p) = x) (ho : ∀ b, b ≠ a + p → μ' b = μ b) :
    SegN μ' a (l.set p x) := by
  intro i hi
  have hi' : i < l.length := by simpa using hi
  by_cases hip : i = p
  · subst hip
    simp [hx]
  · rw [ho _ (by omega), SegN.getElem h hi']
    simp [List.getElem_set_of_ne (Ne.symm hip)]

namespace SumTen

/-- Before round j: the sum of the first j of the ten values has been formed, and the memory differs
from μ at the position of the star only. -/
def Inv (x : SumTenArgs) (saved : ℕ) (μ : ℕ → ℤ) (j : ℕ) (σ : State) : Prop :=
  ∃ (val : ℤ) (μ' : ℕ → ℤ),
    σ = ⟨frame [x.tr, x.root, x.box, x.l.length, x.p, saved, j, (x.values.take j).sum, val], μ'⟩ ∧
      SameOn (· ≠ x.box + x.p) μ μ'

/-- The time of a round. -/
def tRound (L : ℕ) : ℕ := tLookup L + 15

/-- One round adds the value of the string with the digit j.  The conclusion has the form that the
rule for counting loops asks for: the loop itself then raises the digit. -/
private theorem round_spec {lim : Limits} {P : Program} {d : ℕ} (hLookup : LookupSpec lim P)
    (hs : Std lim) {x : SumTenArgs} {saved j : ℕ} {val : ℤ} {μ μ' : ℕ → ℤ}
    (C : SumTenPre lim μ x) (hdep : d + 1 ≤ lim.depth) (hj : j < 10)
    (hsame : SameOn (· ≠ x.box + x.p) μ μ') :
    Ends lim P d sumTenRound
      ⟨frame [x.tr, x.root, x.box, x.l.length, x.p, saved, j, (x.values.take j).sum, val], μ'⟩
      (tRound x.l.length) fun σ' => σ'.loc Digit = j ∧
        Inv x saved μ (j + 1) { σ' with loc := Function.update σ'.loc Digit ((j : ℤ) + 1) } := by
  have hp := C.star
  have hboxB := C.box_in
  light_facts C hs
  have hsum := C.sums (j + 1) (by omega)
  unfold tRound
  -- mem[box + star] := digit
  light_store (x.box + x.p) j
  have hsame₁ : SameOn (· ≠ x.box + x.p) μ (Function.update μ' (x.box + x.p) j) :=
    hsame.write (by simp) _
  have hdigits : ∀ d ∈ x.l.set x.p j, d < 11 := fun d hd => by
    rcases List.mem_or_eq_of_mem_set hd with h | h
    · exact C.digits d h
    · omega
  -- val := lookup(area, root, box, len)
  light_call (hLookup x.tr x.root x.box x.l.length x.T (x.l.set x.p j) _
    C.area.keep
    (segN_set C.seg hp j (Function.update_self _ _ _) hsame₁) (by simp) hdigits (C.walk j hj)
    C.area_in hboxB _ (by omega)) with _ _ ⟨rfl, rfl⟩
  have hnext : (x.values.take (j + 1)).sum
      = (x.values.take j).sum + trieLookup x.T x.root (x.l.set x.p j) :=
    List.sum_take_map_range_succ (fun d => trieLookup x.T x.root (x.l.set x.p d)) hj
  rw [hnext] at hsum
  -- sum := sum + val
  exact Ends.setTo _ ⟨by simp, _, _, by rw [update_frame_setLocal, hnext]; rfl, hsame₁⟩
    ⟨by simpa using hsum, rfl⟩

end SumTen

open SumTen in
/-- **sumTen** returns the sum of the values of the ten strings, and leaves the memory as it
was. -/
theorem sumTen_spec {lim : Limits} {P : Program} (hP : P[Proc.sumTen]? = some sumTenBody)
    (hLookup : LookupSpec lim P) (hs : Std lim) : SumTenSpec lim P := by
  intro x μ pre d hdep
  refine .of_body hP ?_
  rw [SumTenArgs.vals, ← pre.len]
  have hp := pre.star
  light_facts hs pre
  have hsaved : μ (x.box + x.p) = (x.l[x.p] : ℕ) := pre.seg.getElem hp
  unfold tSumTen
  -- saved := mem[box + star]; sum := 0
  light_set (x.l[x.p] : ℕ) using hsaved
  light_set (0 : ℕ)
  -- for digit < 10
  refine Ends.next _ (Ends.for (Inv x x.l[x.p] μ) 10 (tRound x.l.length) ?start ?round ?done ?bound
    (hT := le_rfl)) (by simp [tRound]; omega)
  case start => exact ⟨0, μ, by rw [update_frame_setLocal, ← frame_append_zeros _ 1]; rfl, .refl⟩
  case bound =>
    rintro j _ - - ⟨val, μ', rfl, -⟩
    simp
    omega
  case round =>
    rintro j _ hj - ⟨val, μ', rfl, hsame⟩
    exact round_spec hLookup hs pre hdep hj hsame
  case done =>
    rintro _ - ⟨val, μ', rfl, hsame⟩
    simp only [tRound]
    -- mem[box + star] := saved
    light_store (x.box + x.p) (x.l[x.p] : ℕ)
    -- return sum
    refine Ends.setTo _ ⟨by rw [List.take_of_length_le (by simp [tenValues])]; rfl,
      funext fun b => ?_⟩ ⟨by simp, rfl⟩
    dsimp only
    by_cases hb : b = x.box + x.p
    · rw [hb, Function.update_self, hsaved]
    · rw [Function.update_of_ne hb, hsame b hb]

end Light.Sec4
