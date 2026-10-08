/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Lang.Lib.ArrayAt
public import ThreeSumApsp.Lang.Lib.Pass
public import ThreeSumApsp.Lang.Tactics
public import ThreeSumApsp.Spec.Sec3.Theorem17.Cyclic

/-!
# Vectors: sums, differences, and the product in ℤ[x]/(x^p - 1)

The proof of Theorem 17 computes with matrices over the ring ℤ[x]/(x^p - 1); an element of the ring
is a vector of p integers, and a ring operation takes "O(p²) word operations".

* vlin(dst, a, b, n, s): dst[i] := a[i] + s b[i] for i < n, with s = 1 or s = -1; dst may be the
  segment a itself (accumulation).  It is one pass (`vlin_spec`), and what it writes is `vadd` or
  `vsub` (`vlinList_one`, `vlinList_neg_one`).
* cconv(dst, a, b, p): dst := the cyclic convolution of a and b.  The inner loop adds up the p terms
  of one entry (`cconvEntry_spec`), the outer loop stores the p entries (`cconv_spec`).  The partial
  sums stay below p α β if the entries of a and b are bounded by α and β (`abs_convPartialSum_le`).
-/

@[expose] public section

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## Sums and differences -/

namespace Vlin

/-- The local variables of vlin: the arguments dst, a, b, n, s, and the counter. -/
abbrev Dst : ℕ := 0
@[inherit_doc Dst] abbrev ArgA : ℕ := 1
@[inherit_doc Dst] abbrev ArgB : ℕ := 2
@[inherit_doc Dst] abbrev Len : ℕ := 3
@[inherit_doc Dst] abbrev Sign : ℕ := 4
@[inherit_doc Dst] abbrev Idx : ℕ := 5

end Vlin

open Vlin in
/-- vlin(dst, a, b, n, s): for i < n: dst[i] := a[i] + s b[i]. -/
def vlinBody : Stmt :=
  pass Idx (v Len) (v Dst) (M (v ArgA +' v Idx) +' v Sign *' M (v ArgB +' v Idx))

/-- The list that vlin writes. -/
def vlinList (s : ℤ) (A B : List ℤ) : List ℤ := List.zipWith (fun x y => x + s * y) A B

/-- With s = 1 it is the sum. -/
theorem vlinList_one (A B : List ℤ) : vlinList 1 A B = vadd A B := by
  simp [vlinList, vadd]

/-- With s = -1 it is the difference. -/
theorem vlinList_neg_one (A B : List ℤ) : vlinList (-1) A B = vsub A B := by
  unfold vlinList vsub
  congr 1
  funext x y
  ring

/-- Entry j of that list. -/
def vlinAt (s : ℤ) (A B : List ℤ) (j : ℕ) : ℤ := A.getD j 0 + s * B.getD j 0

/-- What vlin assumes: the lists A and B of n numbers of absolute value at most V stand at a and b;
the n cells at dst lie in the memory, do not meet b, and are the cells at a or do not meet them. -/
structure VlinPre (lim : Limits) (μ : ℕ → ℤ) (dst a b n : ℕ) (s V : ℤ) (A B : List ℤ) : Prop where
  opA : ArrayAt μ a A n V lim.space
  opB : ArrayAt μ b B n V lim.space
  sign : |s| ≤ 1
  word : 2 * V ≤ lim.word := by light_arith
  space : dst + n ≤ lim.space := by light_arith
  apartA : dst = a ∨ dst + n ≤ a ∨ a + n ≤ dst := by light_arith
  apartB : dst + n ≤ b ∨ b + n ≤ dst := by light_arith

open Vlin in
/-- **vlin** writes a + s b to dst and changes nothing else, in at most 23 n + 6 steps. -/
theorem vlin_spec {μ : ℕ → ℤ} {dst a b n : ℕ} {s V : ℤ} {A B : List ℤ}
    (hw : (lim.space : ℤ) ≤ lim.word) (pre : VlinPre lim μ dst a b n s V A B) :
    Ends lim P d vlinBody ⟨frame [dst, a, b, n, s], μ⟩ (23 * n + 6) fun σ' =>
      Seg σ'.mem dst (vlinList s A B) ∧ SameOutside μ σ'.mem dst n := by
  light_facts pre pre.opA pre.opB
  refine Ends.pass (x := Len) (y := Dst) (dst := dst) (n := n) (vlinAt s A B) ?round ?done hw
    pre.space rfl rfl
  case round =>
    intro j hj
    -- The two cells that round j reads have not been written yet.
    have hreadA : wrote μ dst (vlinAt s A B) j (a + j) = A.getD j 0 :=
      (wrote_rest (by omega)).trans (pre.opA.read hj)
    have hreadB : wrote μ dst (vlinAt s A B) j (b + j) = B.getD j 0 :=
      (wrote_rest (by omega)).trans (pre.opB.read hj)
    have hx : |A.getD j 0| ≤ V := pre.opA.read hj ▸ pre.opA.abs_read_le hj
    have hy : |B.getD j 0| ≤ V := pre.opB.read hj ▸ pre.opB.abs_read_le hj
    have hsy : |s * B.getD j 0| ≤ V := by
      rw [abs_mul]
      exact (mul_le_of_le_one_left (abs_nonneg _) pre.sign).trans hy
    rw [abs_le] at hx hsy
    rw [vlinAt]
    generalize A.getD j 0 = x at hreadA hx
    generalize B.getD j 0 = y at hreadB hsy
    simp [Limits.Addr, abs_le, hreadA, hreadB, -abs_mul]
    omega
  case done =>
    refine ⟨fun i hi => ?_, sameOutside_wrote (j := n) le_rfl⟩
    have hi' : i < n := by
      simp only [vlinList, List.length_zipWith] at hi
      omega
    change wrote μ dst (vlinAt s A B) n (dst + i) = _
    simp only [vlinList, List.getElem_zipWith]
    rw [wrote_done hi', vlinAt, List.getD_eq_getElem _ _ (by omega),
      List.getD_eq_getElem _ _ (by omega)]

/-- **vlin** as a procedure. -/
theorem vlin_meets {μ : ℕ → ℤ} {pVlin dst a b n : ℕ} {s V : ℤ} {A B : List ℤ}
    (hP : P[pVlin]? = some vlinBody) (hw : (lim.space : ℤ) ≤ lim.word)
    (pre : VlinPre lim μ dst a b n s V A B) :
    Meets lim P pVlin d [dst, a, b, n, s] μ (23 * n + 6) fun _ μ' =>
      Seg μ' dst (vlinList s A B) ∧ SameOutside μ μ' dst n :=
  Meets.of_body hP (vlin_spec hw pre)

/-! ## The product -/

/-- A term of the convolution. -/
def convTerm (p : ℕ) (A B : List ℤ) (r i : ℕ) : ℤ :=
  A.getD i 0 * B.getD (if i ≤ r then r - i else r + p - i) 0

/-- The sum of the first j terms of entry r of the convolution. -/
def convPartialSum (p : ℕ) (A B : List ℤ) (r j : ℕ) : ℤ :=
    ((List.range j).map (convTerm p A B r)).sum

/-- One more term. -/
theorem convPartialSum_succ (p : ℕ) (A B : List ℤ) (r j : ℕ) :
    convPartialSum p A B r (j + 1) = convPartialSum p A B r j + convTerm p A B r j :=
  List.sum_range_succ _ _

/-- The convolution is the list of these sums. -/
theorem cconv_eq_map_convPartialSum (p : ℕ) (A B : List ℤ) :
    cconv p A B = (List.range p).map fun r => convPartialSum p A B r p := rfl

section bounds

variable {p : ℕ} {A B : List ℤ} {α β : ℤ}

/-- A term is at most α β in absolute value. -/
theorem abs_convTerm_le (leA : AbsLe A α) (leB : AbsLe B β) (hα : 0 ≤ α) (hβ : 0 ≤ β) (r i : ℕ) :
    |convTerm p A B r i| ≤ α * β := by
  rw [convTerm, abs_mul]
  exact mul_le_mul (AbsLe.abs_getD_le hα leA _) (AbsLe.abs_getD_le hβ leB _) (abs_nonneg _) hα

/-- A sum of j terms is at most j α β in absolute value. -/
theorem abs_convPartialSum_le (leA : AbsLe A α) (leB : AbsLe B β) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (r j : ℕ) :
    |convPartialSum p A B r j| ≤ j * (α * β) := by
  simpa [convPartialSum] using List.abs_sum_map_le (List.range j) (convTerm p A B r)
    fun i _ => abs_convTerm_le leA leB hα hβ r i

end bounds

namespace Cconv

/-- The local variables of cconv: the arguments dst, a, b, p; the number r of the entry; the number
i of the term; the sum (Acc); the index into b. -/
abbrev Dst : ℕ := 0
@[inherit_doc Dst] abbrev ArgA : ℕ := 1
@[inherit_doc Dst] abbrev ArgB : ℕ := 2
@[inherit_doc Dst] abbrev Len : ℕ := 3
@[inherit_doc Dst] abbrev Row : ℕ := 4
@[inherit_doc Dst] abbrev Idx : ℕ := 5
@[inherit_doc Dst] abbrev Acc : ℕ := 6
@[inherit_doc Dst] abbrev Jdx : ℕ := 7

end Cconv

open Cconv in
/-- One term: j := r - i or r + p - i; sum := sum + a[i] b[j]. -/
def cconvTerm : Stmt :=
  .ite (v Idx ≤' v Row) (.set Jdx (v Row -' v Idx)) (.set Jdx (v Row +' v Len -' v Idx)) ;;
  .set Acc (v Acc +' M (v ArgA +' v Idx) *' M (v ArgB +' v Jdx))

open Cconv in
/-- One entry: sum := the entry number r of the convolution. -/
def cconvEntry : Stmt :=
  .set Acc (k 0) ;;
  .for Idx (v Len) cconvTerm

open Cconv in
/-- cconv(dst, a, b, p): for r < p: dst[r] := the entry number r. -/
def cconvBody : Stmt :=
  .for Row (v Len) (cconvEntry ;; .store (v Dst +' v Row) (v Acc))

/-- What the inner loop of cconv assumes: the lists A and B of p numbers, bounded by α and β, stand
at a and b, and p α β fits in a word. -/
structure CconvPre (lim : Limits) (μ : ℕ → ℤ) (a b p : ℕ) (α β : ℤ) (A B : List ℤ) : Prop where
  opA : ArrayAt μ a A p α lim.space
  opB : ArrayAt μ b B p β lim.space
  word : p * (α * β) ≤ lim.word
  nonnegA : 0 ≤ α := by light_arith
  nonnegB : 0 ≤ β := by light_arith
  room : 2 * p < lim.space := by light_arith

section cconv

variable {μ : ℕ → ℤ} {dst a b p r : ℕ} {α β : ℤ} {A B : List ℤ}

open Cconv in
/-- **One term of cconv.** -/
theorem cconvTerm_spec (hw : (lim.space : ℤ) ≤ lim.word) (pre : CconvPre lim μ a b p α β A B)
    (hr : r < p) {i : ℕ} (hi : i < p) (t : ℤ) :
    Ends lim P d cconvTerm ⟨frame [dst, a, b, p, r, i, convPartialSum p A B r i, t], μ⟩ 24 fun σ' =>
      ∃ t', σ' = ⟨frame [dst, a, b, p, r, i, convPartialSum p A B r (i + 1), t'], μ⟩ := by
  obtain ⟨opA, opB, hword, hα, hβ, room⟩ := pre
  light_facts opA opB
  have hreadA : μ (a + i) = A.getD i 0 := opA.read hi
  have hterm := abs_le.1 (abs_convTerm_le (p := p) opA.bound opB.bound hα hβ r i)
  have hsum := abs_le.1 (abs_convPartialSum_le (p := p) opA.bound opB.bound hα hβ r (i + 1))
  have hfits : ((i + 1 : ℕ) : ℤ) * (α * β) ≤ lim.word :=
    (mul_le_mul_of_nonneg_right (by exact_mod_cast hi) (mul_nonneg hα hβ)).trans hword
  have hone : α * β ≤ ((i + 1 : ℕ) : ℤ) * (α * β) :=
    le_mul_of_one_le_left (mul_nonneg hα hβ) (by push_cast; omega)
  rw [convPartialSum_succ] at hsum ⊢
  -- sum := sum + a[i] b[j], once j is the index of the term
  have add : ∀ j : ℕ, j < p → convTerm p A B r i = A.getD i 0 * B.getD j 0 →
      Ends lim P d (.set Acc (v Acc +' M (v ArgA +' v Idx) *' M (v ArgB +' v Jdx)))
        ⟨frame [dst, a, b, p, r, i, convPartialSum p A B r i, j], μ⟩ 12 fun σ' => ∃ t',
          σ' = ⟨frame [dst, a, b, p, r, i, convPartialSum p A B r i + convTerm p A B r i, t'],
            μ⟩ := by
    intro j hj hc
    have hreadB : μ (b + j) = B.getD j 0 := opB.read hj
    rw [hc] at hterm hsum ⊢
    generalize A.getD i 0 = x at hreadA hterm hsum
    generalize B.getD j 0 = y at hreadB hterm hsum
    exact Ends.setTo _ ⟨j, rfl⟩ (by light_side [hreadA, hreadB])
  -- if i ≤ r then j := r - i else j := r + p - i
  refine Ends.next 12 (Ends.iteLast (fun hc => ?_) fun hc => ?_)
  · have hir : i ≤ r := by simpa using hc
    exact Ends.setTo (r - i : ℕ) (add _ (by omega) (by rw [convTerm, if_pos hir]))
  · have hir : ¬ i ≤ r := by simpa using hc
    exact Ends.setTo (r + p - i : ℕ) (add _ (by omega) (by rw [convTerm, if_neg hir]))

open Cconv in
/-- **One entry of cconv**, in at most 32 p + 8 steps. -/
theorem cconvEntry_spec (hw : (lim.space : ℤ) ≤ lim.word) (pre : CconvPre lim μ a b p α β A B)
    (hr : r < p) (i₀ s₀ t₀ : ℤ) :
    Ends lim P d cconvEntry ⟨frame [dst, a, b, p, r, i₀, s₀, t₀], μ⟩ (32 * p + 8) fun σ' =>
      ∃ t, σ' = ⟨frame [dst, a, b, p, r, p, convPartialSum p A B r p, t], μ⟩ := by
  have room := pre.room
  -- sum := 0
  light_set 0
  -- for i < p: one term
  refine Ends.for (fun i σ => ∃ t, σ = ⟨frame [dst, a, b, p, r, i, convPartialSum p A B r i, t], μ⟩)
      p 24
    ⟨t₀, by simp [update_frame_setLocal, convPartialSum]⟩ ?round ?done ?bound
  case bound =>
    rintro i _ - - ⟨t, rfl⟩
    simp
  case round =>
    rintro i _ hi - ⟨t, rfl⟩
    refine (cconvTerm_spec hw pre hr hi t).mono le_rfl ?_
    rintro _ ⟨t', rfl⟩
    exact ⟨by simp, t', by simp [update_frame_setLocal]⟩
  case done => exact fun _ _ h => h

open Cconv in
/-- The state of cconv before round r: the first r entries are written, and no cell outside dst has
changed. -/
def CconvInv (μ : ℕ → ℤ) (dst a b p : ℕ) (A B : List ℤ) (r : ℕ) (σ : State) : Prop :=
  ∃ (i s t : ℤ) (μ' : ℕ → ℤ), σ = ⟨frame [dst, a, b, p, r, i, s, t], μ'⟩ ∧
    (∀ e < r, μ' (dst + e) = convPartialSum p A B e p) ∧ SameOutside μ μ' dst p

open Cconv in
/-- **cconv** writes the cyclic convolution to dst and changes nothing else, in at most
32 p² + 21 p + 6 steps. -/
theorem cconv_spec (hw : (lim.space : ℤ) ≤ lim.word) (pre : CconvPre lim μ a b p α β A B)
    (spaceDst : dst + p ≤ lim.space) (apartA : dst + p ≤ a ∨ a + p ≤ dst)
    (apartB : dst + p ≤ b ∨ b + p ≤ dst) :
    Ends lim P d cconvBody ⟨frame [dst, a, b, p], μ⟩ (32 * p * p + 21 * p + 6) fun σ' =>
      Seg σ'.mem dst (cconv p A B) ∧ SameOutside μ σ'.mem dst p := by
  have room := pre.room
  -- for r < p
  refine Ends.for (CconvInv μ dst a b p A B) p (32 * p + 13) ?start ?round ?done ?bound
  case start =>
    exact ⟨0, 0, 0, μ, congrArg (fun loc => (⟨loc, μ⟩ : State))
      ((update_frame_setLocal _ _ _).trans (frame_append_zeros _ 3).symm),
      fun e he => absurd he (by omega), .refl⟩
  case bound =>
    rintro r _ - - ⟨i, s, t, μ', rfl, -, -⟩
    simp
  case round =>
    rintro r _ hr - ⟨i, s, t, μ', rfl, filled, rest⟩
    have pre' : CconvPre lim μ' a b p α β A B :=
      { pre with
        opA := pre.opA.keep, opB := pre.opB.keep }
    -- sum := the entry number r
    light_piece (cconvEntry_spec hw pre' hr i s t) with _ ⟨t', rfl⟩
    -- dst[r] := sum
    light_store (dst + r) (convPartialSum p A B r p)
    refine ⟨by simp, p, convPartialSum p A B r p, t',
      Function.update μ' (dst + r) (convPartialSum p A B r p), by simp [update_frame_setLocal],
      fun e he => ?_, rest.update ⟨by omega, by omega⟩ _⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 he with he | rfl
    · exact (Function.update_of_ne (by omega) _ _).trans (filled e he)
    · exact Function.update_self ..
  case done =>
    rintro _ - ⟨i, s, t, μ', rfl, filled, rest⟩
    refine ⟨fun e he => ?_, rest⟩
    have he' : e < p := by simpa [cconv_eq_map_convPartialSum] using he
    simpa [cconv_eq_map_convPartialSum] using filled e he'

/-- **cconv** as a procedure. -/
theorem cconv_meets {pCconv : ℕ} (hP : P[pCconv]? = some cconvBody)
    (hw : (lim.space : ℤ) ≤ lim.word) (pre : CconvPre lim μ a b p α β A B)
    (spaceDst : dst + p ≤ lim.space := by light_arith)
    (apartA : dst + p ≤ a ∨ a + p ≤ dst := by light_arith)
    (apartB : dst + p ≤ b ∨ b + p ≤ dst := by light_arith) :
    Meets lim P pCconv d [dst, a, b, p] μ (32 * p * p + 21 * p + 6) fun _ μ' =>
      Seg μ' dst (cconv p A B) ∧ SameOutside μ μ' dst p :=
  Meets.of_body hP (cconv_spec hw pre spaceDst apartA apartB)

end cconv

end Light.Sec3
