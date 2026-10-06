/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Lang.Lib.Copy
public import ThreeSumApsp.Lang.Tactics
public import ThreeSumApsp.Programs.Sec3.Theorem21a.ChanHe.HostContracts

/-!
# 3SUM from Convolution-3SUM: filling the arrays of the host

Theorem 21(a), after [CH20, Theorem 5.1].  prep(n, V, Λ, m, x, b) fills
those arrays of the memory map `Map` with base b that do not depend on a splitting; the cells for
the three sets and for the doubles are left as they are.  It has five parts.

* prepAddr computes the addresses of the arrays (`prepAddr_runs`).
* prepTables writes the primes up to m and zeros into the count table (`prepTables_ends`).
* prepSorted writes a sorted copy of the input (`prepSorted_ends`).
* prepValues writes the distinct values, how often each occurs, and the binary digits of the labels
  of the values (`prepValues_ends`).
* prepTail writes the block of parameters of the recursive procedure and the cell that holds 0, and
  returns the number of distinct values (`prepTail_ends`).

The sieve and sorting use cells behind the arrays as scratch space.  The arrays are filled in the
order of their addresses, and a part changes no cell below the first array that it fills, except
that prepTail writes the block of parameters at the base.  So what an earlier part has written is
still there at the end (`PrepValues.frontMem`), and the arrays lie as the loop over the splittings
wants them (`FrontMem.of_map`).  `prepBody_ends` puts the five parts together, and `prep_spec` is
the specification.
-/

@[expose] public section

namespace Light.Sec3.ChanHe

open ThreeSumApsp ThreeSumApsp.ChanHe ThreeSumApsp.Spec Finset

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## The program -/

namespace Prep

/-- The locals of prep.  The arguments: n, V, Λ, m, x and the base b.  Then the address of the
primes, the number m², the addresses of the count table, the sorted copy, the values, their
multiplicities, the table of digits, the three sets, the doubles and the cell that holds 0, and the
free pointer behind the arrays.  Then the number of primes, a local for results that are not read,
and the number of distinct values. -/
abbrev Len : ℕ := 0
@[inherit_doc Len] abbrev Bound : ℕ := 1
@[inherit_doc Len] abbrev Digits : ℕ := 2
@[inherit_doc Len] abbrev PrimeBound : ℕ := 3
@[inherit_doc Len] abbrev Src : ℕ := 4
@[inherit_doc Len] abbrev Base : ℕ := 5
@[inherit_doc Len] abbrev Primes : ℕ := 6
@[inherit_doc Len] abbrev Square : ℕ := 7
@[inherit_doc Len] abbrev Count : ℕ := 8
@[inherit_doc Len] abbrev Sorted : ℕ := 9
@[inherit_doc Len] abbrev Val : ℕ := 10
@[inherit_doc Len] abbrev Mul : ℕ := 11
@[inherit_doc Len] abbrev Table : ℕ := 12
@[inherit_doc Len] abbrev Sets : ℕ := 13
@[inherit_doc Len] abbrev Doubles : ℕ := 14
@[inherit_doc Len] abbrev Zero : ℕ := 15
@[inherit_doc Len] abbrev Top : ℕ := 16
@[inherit_doc Len] abbrev NumPrimes : ℕ := 17
@[inherit_doc Len] abbrev Unread : ℕ := 18
@[inherit_doc Len] abbrev NumValues : ℕ := 19

end Prep

open Prep in
/-- The addresses of the arrays. -/
def prepAddr : Stmt :=
  .set Primes (v Base +' k 6) ;;
  .set Square (v PrimeBound *' v PrimeBound) ;;
  .set Count (v Primes +' v PrimeBound) ;;
  .set Sorted (v Count +' v Square) ;;
  .set Val (v Sorted +' v Len) ;;
  .set Mul (v Val +' v Len) ;;
  .set Table (v Mul +' v Len) ;;
  .set Sets (v Table +' v Len *' v Digits) ;;
  .set Doubles (v Sets +' k 3 *' v Len) ;;
  .set Zero (v Doubles +' v Len) ;;
  .set Top (v Zero +' k 1)

open Prep in
/-- The primes, and zeros in the count table. -/
def prepTables (pPrimes pFill : ℕ) : Stmt :=
  .call pPrimes [v PrimeBound, v Primes, v Top] NumPrimes ;;
  .call pFill [v Count, v Square, k 0] Unread

open Prep in
/-- The sorted copy of the input. -/
def prepSorted (pCopy pSort : ℕ) : Stmt :=
  .call pCopy [v Src, v Sorted, v Len] Unread ;;
  .call pSort [v Len, v Sorted, v Top] Unread

open Prep in
/-- The distinct values with their multiplicities, and the binary digits of their labels. -/
def prepValues (pDistinct pBits : ℕ) : Stmt :=
  .call pDistinct [v Len, v Sorted, v Val, v Mul] NumValues ;;
  .call pBits [v NumValues, v Val, v Bound, v Digits, v Table, v Top] Unread

open Prep in
/-- The block of parameters, the cell that holds 0, and the result. -/
def prepTail : Stmt :=
  .store (v Base) (v Bound) ;;
  .store (v Base +' k 1) (v PrimeBound) ;;
  .store (v Base +' k 2) (v Digits) ;;
  .store (v Base +' k 3) (v NumPrimes) ;;
  .store (v Base +' k 4) (v Primes) ;;
  .store (v Base +' k 5) (v Count) ;;
  .store (v Zero) (k 0) ;;
  .set Len (v NumValues)

/-- prep(n, V, Λ, m, x, b), over the procedures pPrimes, pFill, pCopy, pSort, pDistinct, pBits. -/
def prepBody (pPrimes pFill pCopy pSort pDistinct pBits : ℕ) : Stmt :=
  prepAddr ;;
  prepTables pPrimes pFill ;;
  prepSorted pCopy pSort ;;
  prepValues pDistinct pBits ;;
  prepTail

/-- The arguments of prep and the addresses that prepAddr computes, as the list of the locals. -/
abbrev prepFrame (a : Map) (V x : ℕ) : List ℤ :=
  [a.n, V, a.Λ, a.m, x, a.b, a.pr, ((a.m * a.m : ℕ) : ℤ), a.cnt, a.srt, a.val, a.mul, a.bt, a.A,
    a.tw, a.one, a.top]

/-! ## The five parts -/

/-- prepAddr computes the addresses. -/
theorem prepAddr_runs (a : Map) (V x : ℕ) (μ : ℕ → ℤ) (htop : (a.top : ℤ) ≤ lim.word)
    (hword : (6 : ℤ) ≤ lim.word) :
    prepAddr.Runs lim ⟨frame [a.n, V, a.Λ, a.m, x, a.b], μ⟩ (· = ⟨frame (prepFrame a V x), μ⟩) := by
  have hmap := a.layout
  have : (0 : ℤ) ≤ (a.m : ℤ) * a.m := by positivity
  have : (0 : ℤ) ≤ (a.n : ℤ) * a.Λ := by positivity
  exact ⟨by light_side [prepAddr],
    by simp [prepAddr, update_frame_setLocal, prepFrame, Map.top, Map.one, Map.tw, Map.A, Map.bt,
      Map.mul, Map.val, Map.srt, Map.cnt, Map.pr]⟩

/-- What prep may use covers what the sieve needs. -/
private theorem ok_primes {n V Λ m fr : ℕ} (h : (prepNeed n V Λ m).Ok lim fr d) :
    (primesNeed m).Ok lim fr (d + 1) := by
  have : m + 1 ≤ (m + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  refine h.mono ?_ ?_ ?_ <;> simp only [primesNeed, prepNeed] <;> omega

/-- What prep may use covers what sorting needs. -/
private theorem ok_sort {n V Λ m fr : ℕ} (h : (prepNeed n V Λ m).Ok lim fr d) :
    (sortNeed n V).Ok lim fr (d + 1) := by
  refine h.mono ?_ ?_ ?_ <;> simp only [sortNeed, prepNeed] <;> omega

/-- prepTables writes the primes and the zeros, and changes no other cell below the free pointer
behind the arrays. -/
theorem prepTables_ends {pPrimes pFill : ℕ} (hPr : PrimesSpec lim P pPrimes)
    (hFi : P[pFill]? = some fillBody) (a : Map) {V x : ℕ} {μ : ℕ → ℤ}
    (hok : (prepNeed a.n V a.Λ a.m).Ok lim a.top d) :
    Ends lim P d (prepTables pPrimes pFill) ⟨frame (prepFrame a V x), μ⟩
      (10 + tPrimes a.m + (13 * (a.m * a.m) + 6)) fun σ' => ∃ (μ' : ℕ → ℤ) (r : ℤ),
        σ' = ⟨frame (prepFrame a V x ++ [(#(Nat.primesLE a.m) : ℤ), r]), μ'⟩ ∧
        PrimesAt μ' a.pr #(Nat.primesLE a.m) a.m ∧ ZeroAt μ' a.cnt (a.m * a.m) ∧
        SameOn (fun c => c < a.top ∧ Outside a.pr (a.m + a.m * a.m) c) μ μ' := by
  have hmap := a.layout
  have hw := hok.space
  have hcells := hok.cells
  have hword := hok.word
  have hdepth := hok.depth
  simp only [prepNeed] at hcells hword hdepth
  push_cast at hword
  have hnp := Nat.card_primesLE_le a.m
  unfold prepTables
  -- NumPrimes := primes(PrimeBound, Primes, Top)
  light_call (hPr (d + 1) a.top a.m a.pr μ (by omega) (ok_primes hok))
    with _ μ₁ ⟨rfl, hprimes, hkept₁⟩
  -- Unread := fill(Count, Square, 0)
  refine Ends.callTo
    (fill_meets (μ := μ₁) (dst := a.cnt) (n := a.m * a.m) (x := 0) hFi hw (by omega)) ?_
  rintro r μ₂ ⟨hzero, hkept₂⟩
  refine ⟨μ₂, r, rfl,
    ⟨rfl, hprimes.of_sameOutside hkept₂ (.inl (by rw [List.length_map, length_sort]; omega))⟩,
    fun i hi => ?_, hkept₁.then hkept₂ fun c hc => ⟨⟨hc.1, by omega⟩, by omega⟩⟩
  rw [hzero i (by simpa using hi)]
  simp

/-- prepSorted writes a sorted copy of the input, and changes no cell below it. -/
theorem prepSorted_ends {pCopy pSort : ℕ} (hCo : P[pCopy]? = some copyBody)
    (hSo : SortSpec lim P pSort) {a : Map} {V x : ℕ} {X : List ℤ} (C : Prep.Ctx lim d a V x X)
    {μ : ℕ → ℤ} (hseg : Seg μ x X) (np r : ℤ) :
    Ends lim P d (prepSorted pCopy pSort) ⟨frame (prepFrame a V x ++ [np, r]), μ⟩
      (10 + (16 * a.n + 6) + tSort a.n) fun σ' => ∃ (μ' : ℕ → ℤ) (r' : ℤ) (Ls : List ℤ),
        σ' = ⟨frame (prepFrame a V x ++ [np, r']), μ'⟩ ∧ Seg μ' a.srt Ls ∧ Ls.Perm X ∧
        Ls.Pairwise (· ≤ ·) ∧ SameOn (· < a.srt) μ μ' := by
  have hmap := a.layout
  have hlen := C.len
  have hbelow := C.below
  have hw := C.ok.space
  have hcells := C.ok.cells
  have hdepth := C.ok.depth
  simp only [prepNeed] at hcells hdepth
  have htime : tSort X.length = tSort a.n := by rw [hlen]
  unfold prepSorted
  -- Unread := copy(Src, Sorted, Len)
  have hroom : a.srt + X.length ≤ lim.space := by omega
  light_call (copy_meets (μ := μ) (src := x) (dst := a.srt) (n := X.length) hCo hw
    (by omega) hroom (.inl (by omega))) with _ μ₁ ⟨hcells₁, hkept₁⟩
  have hcopy : Seg μ₁ a.srt X := fun i hi => (hcells₁ i hi).trans (hseg i hi)
  -- Unread := sort(Len, Sorted, Top)
  light_call (hSo (d + 1) a.top a.srt V X μ₁ hcopy C.bounded (by omega) (hlen ▸ ok_sort C.ok))
    with r' μ₂ ⟨⟨Ls, hLs, hperm, hsorted⟩, hkept₂⟩
  exact ⟨μ₂, r', Ls, rfl, hLs, hperm, hsorted,
    hkept₁.then hkept₂ fun c hc => ⟨by omega, by omega, by omega⟩⟩

/-- The labels for V have `Lam V` binary digits. -/
private theorem two_mul_lt_two_pow_Lam (V : ℕ) : 2 * V < 2 ^ Lam V :=
  Nat.lt_pow_succ_log_self (by norm_num) _

/-- `2 ^ Lam V` is at most twice as large as it has to be. -/
private theorem two_pow_Lam_le {V : ℕ} (hV : 1 ≤ V) : 2 ^ Lam V ≤ 4 * V + 4 := by
  have := Nat.pow_log_le_self 2 (x := 2 * V) (by omega)
  rw [Lam, pow_succ]
  omega

/-- The time of bits grows with the number of elements. -/
private theorem tBits_mono {len len' : ℕ} (h : len ≤ len') (Λ : ℕ) : tBits len Λ ≤ tBits len' Λ :=
  Nat.add_le_add_right (Nat.add_le_add_right (Nat.mul_le_mul_right _ h) _) _

/-- What distinct assumes holds when the three regions stand one after the other. -/
private theorem Distinct.Ctx.of_consecutive {μ : ℕ → ℤ} {s val mul : ℕ} {L : List ℤ}
    (hsorted : L.Pairwise (· ≤ ·)) (hseg : Seg μ s L) (hval : s + L.length ≤ val)
    (hmul : val + L.length ≤ mul) (hspace : mul + L.length ≤ lim.space)
    (hw : (lim.space : ℤ) ≤ lim.word) (hword : (2 * L.length + 8 : ℤ) ≤ lim.word) :
    Distinct.Ctx lim μ s val mul L where
  sorted := hsorted
  seg := hseg
  apartVal := .inl hval
  apartMul := .inl (by omega)
  apart := .inl hmul
  spaceSrc := by omega
  spaceVal := by omega
  spaceMul := hspace
  space_le := hw
  word := hword

/-- What prepValues leaves in the memory: the distinct values D of the input X, how often each
occurs, and the binary digits of their labels. -/
structure PrepValues (μ : ℕ → ℤ) (a : Map) (V : ℕ) (X D C : List ℤ) : Prop where
  /-- D lists the distinct values, and C how often each occurs. -/
  values : Values a.n X D C
  /-- The values have absolute value at most V. -/
  bounded : AbsLe D V
  /-- The values stand at val. -/
  segVal : Seg μ a.val D
  /-- Their multiplicities stand at mul. -/
  segMul : Seg μ a.mul C
  /-- The binary digits of their labels stand at bt. -/
  segTable : Seg μ a.bt (bitTable V a.Λ D)

/-- prepValues writes the distinct values, their multiplicities and the binary digits, and changes
no cell below them. -/
theorem prepValues_ends {pDistinct pBits : ℕ} (hDi : DistinctSpec lim P pDistinct)
    (hBi : BitsSpec lim P pBits) {a : Map} {V x : ℕ} {X Ls : List ℤ} (C : Prep.Ctx lim d a V x X)
    {μ : ℕ → ℤ} (hLs : Seg μ a.srt Ls) (hperm : Ls.Perm X) (hsorted : Ls.Pairwise (· ≤ ·))
    (np r : ℤ) :
    Ends lim P d (prepValues pDistinct pBits) ⟨frame (prepFrame a V x ++ [np, r]), μ⟩
      (14 + tDistinct a.n + tBits a.n a.Λ) fun σ' => ∃ (μ' : ℕ → ℤ) (r' : ℤ) (D M : List ℤ),
        σ' = ⟨frame (prepFrame a V x ++ [np, r', D.length]), μ'⟩ ∧ PrepValues μ' a V X D M ∧
        SameOn (· < a.val) μ μ' := by
  have hmap := a.layout
  have hlen : Ls.length = a.n := hperm.length_eq.trans C.len
  have hLsV : AbsLe Ls V := fun e he => C.bounded e (hperm.mem_iff.1 he)
  have hw := C.ok.space
  have hcells := C.ok.cells
  have hword := C.ok.word
  have hdepth := C.ok.depth
  simp only [prepNeed] at hcells hword hdepth
  push_cast at hword
  have : (0 : ℤ) ≤ ((a.m : ℤ) + 1) ^ 2 := by positivity
  have htime : tDistinct Ls.length = tDistinct a.n := by rw [hlen]
  unfold prepValues
  -- NumValues := distinct(Len, Sorted, Val, Mul)
  have hctx : Distinct.Ctx lim μ a.srt a.val a.mul Ls :=
    .of_consecutive hsorted hLs (by omega) (by omega) (show a.mul + Ls.length ≤ _ by omega) hw
      (by omega)
  light_call (hDi (d + 1) a.srt a.val a.mul Ls μ hctx)
    with _ μ₁ ⟨⟨D, rfl, hDn, hDv, hsegD, hsegM⟩, hkept₁⟩
  have hvalues := Values.of_perm C.len hperm hDn hDv
  have hDle := hvalues.length_le
  have hrows := Nat.mul_le_mul_right a.Λ hDle
  have hDV : AbsLe D V := fun e he =>
    hLsV e (List.mem_toFinset.1 (hDv ▸ List.mem_toFinset.2 he))
  have htime' := tBits_mono hDle a.Λ
  -- Unread := bits(NumValues, Val, Bound, Digits, Table, Top)
  have hapart : Apart a.val D.length a.bt (D.length * a.Λ) := .inl (by omega)
  have hctx' : Bits.Ctx lim μ₁ a.val V a.Λ a.bt D :=
    ⟨hDV, C.digits ▸ two_mul_lt_two_pow_Lam V, C.digits ▸ two_pow_Lam_le C.bound_pos, hsegD,
      hapart, by omega, by omega, hw, by omega⟩
  light_call (hBi (d + 1) a.top a.val a.bt V a.Λ D μ₁ hctx') with r' μ₂ ⟨hsegB, hkept₂⟩
  exact ⟨μ₂, r', D, _, rfl, ⟨hvalues, hDV, hsegD.of_sameOutside hkept₂ (.inl (by omega)),
    hsegM.of_sameOutside hkept₂ (.inl (by simp; omega)), hsegB⟩,
    hkept₁.then hkept₂ fun c hc => ⟨⟨by omega, by omega⟩, by omega⟩⟩

/-- prepTail writes the block of parameters and the cell that holds 0, and returns the number of
distinct values. -/
theorem prepTail_ends (a : Map) {V x np nd : ℕ} {μ : ℕ → ℤ} (r : ℤ) (htop : a.top ≤ lim.space)
    (hw : (lim.space : ℤ) ≤ lim.word) (hword : (5 : ℤ) ≤ lim.word) :
    Ends lim P d prepTail ⟨frame (prepFrame a V x ++ [(np : ℤ), r, nd]), μ⟩ 33 fun σ' =>
      σ'.loc 0 = nd ∧ CtxAt σ'.mem a.cx V a.m a.Λ np a.pr a.cnt ∧ σ'.mem a.one = 0 ∧
      SameOn (fun c => Outside a.b 6 c ∧ c ≠ a.one) μ σ'.mem := by
  have hmap := a.layout
  unfold prepTail
  -- mem[Base], …, mem[Base + 5] := Bound, PrimeBound, Digits, NumPrimes, Primes, Count
  light_store a.b V
  light_store (a.b + 1) a.m
  light_store (a.b + 2) a.Λ
  light_store (a.b + 3) np
  light_store (a.b + 4) a.pr
  light_store (a.b + 5) a.cnt
  -- mem[Zero] := 0 ; Len := NumValues
  light_store a.one 0
  light_set nd
  refine ⟨rfl, ?_, by simp, ?_⟩
  · have hbase : a.b ≠ a.one := by omega
    have hone : ∀ i < 6, a.b + i ≠ a.one := fun i hi => by omega
    simp [CtxAt, seg_cons, Map.cx, Nat.add_assoc, hbase, hone]
  · rintro c ⟨hoff, hone⟩
    simp only [Function.update_apply]
    split_ifs <;> first | rfl | omega

/-! ## The whole routine -/

/-- The arrays of the map lie as the loop over the splittings wants them. -/
theorem FrontMem.of_map (a : Map) {μ : ℕ → ℤ} {V : ℕ} {D : List ℤ} (hle : D.length ≤ a.n)
    (hnodup : D.Nodup) (hbdd : AbsLe D V) (hval : Seg μ a.val D)
    (htable : Seg μ a.bt (bitTable V a.Λ D))
    (hctx : CtxAt μ a.cx V a.m a.Λ #(Nat.primesLE a.m) a.pr a.cnt)
    (hprimes : PrimesAt μ a.pr #(Nat.primesLE a.m) a.m) (hzero : ZeroAt μ a.cnt (a.m * a.m)) :
    FrontMem μ (a.front V D) := by
  have hmap := a.layout
  have hnp := Nat.card_primesLE_le a.m
  have hrows := Nat.mul_le_mul_right a.Λ hle
  exact {
    lenD := rfl
    nd_le := hle
    nodup := hnodup
    bdd := fun e he => hbdd e (List.mem_toFinset.1 he)
    segVal := hval
    segBt := htable
    ctx := hctx
    primes := hprimes
    zero := hzero
    belowVal := by dsimp only [Map.front]; omega
    belowBt := by dsimp only [Map.front]; omega
    belowCx := by dsimp only [Map.front]; omega
    belowPr := by dsimp only [Map.front]; omega
    belowCnt := by dsimp only [Map.front]; omega
    belowA := by dsimp only [Map.front]; omega
    apartVal := .inr (by dsimp only [Map.front]; omega)
    apartBt := .inr (by dsimp only [Map.front]; omega)
    apartCx := .inr (by dsimp only [Map.front]; omega)
    apartPr := .inr (by dsimp only [Map.front]; omega)
    apartCnt := .inr (by dsimp only [Map.front]; omega)
    cntVal := .inr (by dsimp only [Map.front]; omega)
    cntCx := .inl (by dsimp only [Map.front]; omega)
    cntPr := .inl (by dsimp only [Map.front]; omega) }

/-- What the earlier parts have written is still there after prepTail. -/
theorem PrepValues.frontMem {a : Map} {V : ℕ} {X D M : List ℤ} {μ₁ μ₃ μ₄ : ℕ → ℤ}
    (h : PrepValues μ₃ a V X D M) (hprimes : PrimesAt μ₁ a.pr #(Nat.primesLE a.m) a.m)
    (hzero : ZeroAt μ₁ a.cnt (a.m * a.m)) (hlate : SameOn (· < a.srt) μ₁ μ₃)
    (hctx : CtxAt μ₄ a.cx V a.m a.Λ #(Nat.primesLE a.m) a.pr a.cnt)
    (htail : SameOn (fun c => Outside a.b 6 c ∧ c ≠ a.one) μ₃ μ₄) :
    Seg μ₄ a.mul M ∧ FrontMem μ₄ (a.front V D) := by
  have hmap := a.layout
  have hle := h.values.length_le
  have hrows := Nat.mul_le_mul_right a.Λ hle
  have hlenM : M.length = D.length := by rw [h.values.counts, List.length_map]
  have hlenT := length_bitTable V a.Λ D
  have hnp := Nat.card_primesLE_le a.m
  have htables : SameOn (fun c => a.pr ≤ c ∧ c < a.srt) μ₁ μ₄ :=
    hlate.then htail fun c hc => ⟨hc.2, by omega, by omega⟩
  refine ⟨h.segMul.of_sameOn htail fun i hi => ⟨by omega, by omega⟩,
    .of_map a hle h.values.nodup h.bounded
      (h.segVal.of_sameOn htail fun i hi => ⟨by omega, by omega⟩)
      (h.segTable.of_sameOn htail fun i hi => ⟨by omega, by omega⟩) hctx
      ⟨rfl, hprimes.2.of_sameOn htables fun i hi => ?_⟩
      fun i hi => (htables _ ⟨by omega, by omega⟩).trans (hzero i hi)⟩
  rw [List.length_map, length_sort] at hi
  exact ⟨by omega, by omega⟩

/-- The five parts one after the other. -/
theorem prepBody_ends {pPrimes pFill pCopy pSort pDistinct pBits : ℕ}
    (hPr : PrimesSpec lim P pPrimes) (hFi : P[pFill]? = some fillBody)
    (hCo : P[pCopy]? = some copyBody) (hSo : SortSpec lim P pSort)
    (hDi : DistinctSpec lim P pDistinct) (hBi : BitsSpec lim P pBits) {a : Map} {V x : ℕ}
    {X : List ℤ} (C : Prep.Ctx lim d a V x X) {μ : ℕ → ℤ} (hseg : Seg μ x X) :
    Ends lim P d (prepBody pPrimes pFill pCopy pSort pDistinct pBits)
      ⟨frame [a.n, V, a.Λ, a.m, x, a.b], μ⟩ (tPrep a.n a.Λ a.m) fun σ' =>
      (∃ D M : List ℤ, σ'.loc 0 = (D.length : ℤ) ∧ Values a.n X D M ∧ Seg σ'.mem a.mul M ∧
        σ'.mem a.one = 0 ∧ FrontMem σ'.mem (a.front V D)) ∧ Kept μ σ'.mem a.b := by
  have hmap := a.layout
  have hw := C.ok.space
  have hcells := C.ok.cells
  have hword := C.ok.word
  light_facts C
  simp only [prepNeed] at hcells hword
  push_cast at hword
  have : (0 : ℤ) ≤ ((a.m : ℤ) + 1) ^ 2 := by positivity
  unfold tPrep prepBody
  -- prepAddr
  refine Ends.next _ (Ends.block ((prepAddr_runs a V x μ (by omega) (by omega)).mono ?_) le_rfl)
    (by simp [prepAddr])
  rintro _ rfl
  -- prepTables
  refine Ends.next _ ((prepTables_ends hPr hFi a C.ok).mono le_rfl ?_) (by simp [prepAddr]; omega)
  rintro _ ⟨μ₁, r₁, rfl, hprimes, hzero, hkept₁⟩
  -- prepSorted
  refine Ends.next _ ((prepSorted_ends hCo hSo C
    (hseg.of_sameOn hkept₁ fun i hi => ⟨by omega, by omega⟩) _ r₁).mono le_rfl ?_)
    (by simp [prepAddr]; omega)
  rintro _ ⟨μ₂, r₂, Ls, rfl, hLs, hperm, hsorted, hkept₂⟩
  -- prepValues
  refine Ends.next _ ((prepValues_ends hDi hBi C hLs hperm hsorted _ r₂).mono le_rfl ?_)
    (by simp [prepAddr]; omega)
  rintro _ ⟨μ₃, r₃, D, M, rfl, hvals, hkept₃⟩
  -- prepTail
  refine (prepTail_ends a r₃ (by omega) hw (by omega)).mono (by simp [prepAddr]; omega) ?_
  rintro ⟨_, μ₄⟩ ⟨hres, hctx, hone, hkept₄⟩
  have hlate : SameOn (· < a.srt) μ₁ μ₃ := hkept₂.then hkept₃ fun c hc => ⟨hc, by omega⟩
  obtain ⟨hmul, hfront⟩ := hvals.frontMem hprimes hzero hlate hctx hkept₄
  exact ⟨⟨D, M, hres, hvals.values, hmul, hone, hfront⟩,
    (hkept₁.then hlate fun c hc => ⟨⟨by omega, by omega⟩, by omega⟩).then hkept₄
      fun c hc => ⟨hc, by omega, by omega⟩⟩

/-- **prep** meets its specification. -/
theorem prep_spec {p pPrimes pFill pCopy pSort pDistinct pBits : ℕ}
    (hP : P[p]? = some (prepBody pPrimes pFill pCopy pSort pDistinct pBits))
    (hPr : PrimesSpec lim P pPrimes) (hFi : P[pFill]? = some fillBody)
    (hCo : P[pCopy]? = some copyBody) (hSo : SortSpec lim P pSort)
    (hDi : DistinctSpec lim P pDistinct) (hBi : BitsSpec lim P pBits) : PrepSpec lim P p :=
  fun _ _ _ _ _ _ C hseg => Meets.of_body hP (prepBody_ends hPr hFi hCo hSo hDi hBi C hseg)

end Light.Sec3.ChanHe
