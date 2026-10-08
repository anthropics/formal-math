/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Lang.Lib.Copy
public import ThreeSumApsp.Lang.Lib.CountSort
public import ThreeSumApsp.Util.StablePass

/-!
# One pass of a radix sort on a list of indices

The pass sorts the list of indices at perm stably by a key that is read through the index: countSort
writes the sorted list into the w cells after the list, and copy brings it back.  What countSort
leaves is the result of a stable pass on lists (`exists_stablePass`), and `radixPass_ends` puts the
two calls together.  The pass is used with different expressions for the place of the keys, so these
are parameters.
-/

@[expose] public section

open ThreeSumApsp

namespace Light

variable {lim : Limits} {P : Program} {d : ℕ}

/-- What countSort leaves at dst is a list, and it is the result of a stable pass. -/
theorem exists_stablePass {μ' : ℕ → ℤ} {dst : ℕ} {π : List ℕ} {kd : ℕ → ℕ}
    (h : ∀ j (hj : j < π.length), μ' (dst + sortPos (keyAt kd π) π.length j) = (π[j] : ℤ)) :
    ∃ π', IsStablePass kd π π' ∧ SegN μ' dst π' := by
  refine ⟨(readSeg μ' dst π.length).map Int.toNat, ⟨by simp, fun j hj => ?_⟩, fun q hq => ?_⟩
  · have hp := sortPos_lt (keyAt kd π) hj
    rw [List.getD_eq_getElem _ _ (by simpa using hp)]
    simp [h j hj]
  · have hq' : q < π.length := by simpa using hq
    obtain ⟨j, hj, rfl⟩ := exists_sortPos_eq (keyAt kd π) hq'
    simp [h j hj]

namespace RadixPass

/-- The local variables that the pass uses: w, perm, and a local that takes the results of the two
calls, which are not used. -/
abbrev Num : ℕ := 0
@[inherit_doc Num] abbrev Perm : ℕ := 5
@[inherit_doc Num] abbrev Unused : ℕ := 7

/-- The pass: procedure pc is countSort, procedure pp is copy. -/
def _root_.Light.radixPass (pc pp : ℕ) (ekey estride eoff enb ecnt : Expr) : Stmt :=
  .call pc [v Num, v Perm, v Perm +' v Num, ekey, estride, eoff, enb, ecnt] Unused ;;
  .call pp [v Perm +' v Num, v Perm, v Num] Unused

/-- Where the data of a pass lie. -/
structure Args where
  /-- the number of indices -/
  w : ℕ
  /-- where the list of indices stands; the w cells after it are scratch space -/
  perm : ℕ
  /-- the key of the index i is in the cell key + i · stride + off -/
  key : ℕ
  /-- see key -/
  stride : ℕ
  /-- see key -/
  off : ℕ
  /-- all keys are below nb -/
  nb : ℕ
  /-- nb + 1 cells for the counters -/
  cnt : ℕ
  /-- only the R cells from perm on may change -/
  R : ℕ

/-- The arguments of the call of countSort. -/
abbrev Args.sort (A : Args) : CountSort.Args :=
  ⟨A.w, A.perm, A.perm + A.w, A.key, A.stride, A.off, A.nb, A.cnt⟩

end RadixPass

/-- What a pass assumes: the list π of indices below w stands at perm, the keys lie before the list,
and the counters after the list and its scratch space, within the R cells that may change. -/
structure RadixPass.Pre (lim : Limits) (μ : ℕ → ℤ) (A : RadixPass.Args) (π : List ℕ)
    (kd : ℕ → ℕ) : Prop where
  hw : (lim.space : ℤ) ≤ lim.word
  len : π.length = A.w
  lt : ∀ i ∈ π, i < A.w
  seg : SegN μ A.perm π
  keyBefore : ∀ i < A.w, A.key + i * A.stride + A.off < A.perm
  keys : ∀ i < A.w, μ (A.key + i * A.stride + A.off) = kd i
  keyLt : ∀ i < A.w, kd i < A.nb
  cntAfter : A.perm + 2 * A.w ≤ A.cnt
  cntIn : A.cnt + (A.nb + 1) ≤ A.perm + A.R
  space : A.perm + A.R ≤ lim.space

/-- What a pass achieves: the list at perm is the result of a stable pass by the key kd, cnt[t] is
the number of indices with a key below t, and only the R cells from perm on have changed. -/
structure RadixPass.Post (μ : ℕ → ℤ) (A : RadixPass.Args) (π : List ℕ) (kd : ℕ → ℕ)
    (μ' : ℕ → ℤ) : Prop where
  same : SameOutside μ μ' A.perm A.R
  starts : ∀ t ≤ A.nb, μ' (A.cnt + t) = cntLt (keyAt kd π) t A.w
  sorted : ∃ π', IsStablePass kd π π' ∧ SegN μ' A.perm π'

variable {μ : ℕ → ℤ} {A : RadixPass.Args} {π : List ℕ} {kd : ℕ → ℕ}

/-- What countSort assumes holds for the pass: the items are the list at perm, and they go to the w
cells after it. -/
theorem RadixPass.Pre.sort (pre : RadixPass.Pre lim μ A π kd) :
    CountSort.Pre lim μ A.sort (fun j => π.getD j 0) (keyAt kd π) := by
  obtain ⟨hw, len, lt, seg, keyBefore, keys, keyLt, cntAfter, cntIn, space⟩ := pre
  have hit : ∀ i < A.w, π.getD i 0 < A.w := fun i hi => by
    rw [List.getD_eq_getElem _ _ (by omega)]; exact lt _ (List.getElem_mem _)
  have hbefore : ∀ i < A.w, A.key + π.getD i 0 * A.stride + A.off < A.perm :=
    fun i hi => keyBefore _ (hit i hi)
  exact
    { hw := hw
      srcB := by dsimp only; omega
      dstB := by dsimp only; omega
      cntB := by dsimp only; omega
      items := fun i hi => seg.read (by dsimp only at hi; omega)
      keyB := fun i hi => (hbefore i hi).trans_le (by omega)
      keys := fun i hi => keys _ (hit i hi)
      keyLt := fun i hi => keyLt _ (hit i hi)
      srcDst := Or.inl le_rfl
      srcCnt := Or.inl (by dsimp only; omega)
      dstCnt := Or.inl (by dsimp only; omega)
      keyDst := fun i hi => Or.inl ((hbefore i hi).trans_le (by dsimp only; omega))
      keyCnt := fun i hi => Or.inl ((hbefore i hi).trans_le (by dsimp only; omega)) }

/-- The memory after countSort (μ₁) and after the copy (μ₂). -/
theorem RadixPass.Post.of_sorted_copied {μ₁ μ₂ : ℕ → ℤ} (pre : RadixPass.Pre lim μ A π kd)
    (sorted : CountSort.Post μ A.sort (fun j => π.getD j 0) (keyAt kd π) μ₁)
    (copied : ∀ i < A.w, μ₂ (A.perm + i) = μ₁ (A.perm + A.w + i))
    (same₂ : SameOutside μ₁ μ₂ A.perm A.w) : RadixPass.Post μ A π kd μ₂ := by
  obtain ⟨placed, starts, (same₁ : SameOutside2 μ μ₁ (A.perm + A.w) A.w A.cnt (A.nb + 1))⟩ := sorted
  dsimp only at placed starts
  have len := pre.len
  light_facts pre
  refine ⟨fun b hb => (same₂ b (by omega)).trans (same₁ b ⟨by omega, by omega⟩),
    fun t ht => (same₂ (A.cnt + t) (by omega)).trans (starts t ht), ?_⟩
  -- What stands after the list is the result of a stable pass, and it has been copied back.
  obtain ⟨π', stable, seg⟩ := exists_stablePass (μ' := μ₁) (dst := A.perm + A.w) (π := π)
    fun j hj => by rw [len, placed j (by omega), List.getD_eq_getElem _ _ hj]
  have len' : π'.length = π.length := stable.1
  refine ⟨π', stable, fun i hi => ?_⟩
  rw [← seg i hi]
  exact copied i (by simpa [len', len] using hi)

/-- **pass**: the list π of indices at perm is replaced by the result of a stable pass by the key
kd.  The five expressions give the place of the keys, the number of buckets and the place of the
counters.  Of the local variables only `Unused` changes. -/
theorem radixPass_ends {pc pp T : ℕ} {ekey estride eoff enb ecnt : Expr} {loc : ℕ → ℤ}
    (hpc : P[pc]? = some countSortBody) (hpp : P[pp]? = some copyBody)
    (pre : RadixPass.Pre lim μ A π kd)
    (hlen : loc RadixPass.Num = A.w := by light_side)
    (hperm : loc RadixPass.Perm = A.perm := by light_side)
    (hkey : ekey.Gives lim ⟨loc, μ⟩ A.key := by light_side)
    (hstride : estride.Gives lim ⟨loc, μ⟩ A.stride := by light_side)
    (hoff : eoff.Gives lim ⟨loc, μ⟩ A.off := by light_side)
    (hnb : enb.Gives lim ⟨loc, μ⟩ A.nb := by light_side)
    (hcnt : ecnt.Gives lim ⟨loc, μ⟩ A.cnt := by light_side)
    (hd : d < lim.depth := by omega)
    (hT : 84 * A.w + 58 * A.nb + 72 +
      (ekey.cost + estride.cost + eoff.cost + enb.cost + ecnt.cost) ≤ T := by light_time) :
    Ends lim P d (radixPass pc pp ekey estride eoff enb ecnt) ⟨loc, μ⟩ T fun σ' =>
      (∃ r, σ'.loc = Function.update loc RadixPass.Unused r) ∧ RadixPass.Post μ A π kd σ'.mem := by
  have hw := pre.hw
  light_facts pre
  -- countSort(w, perm, perm + w, key, stride, off, nb, cnt)
  refine Ends.callThen (countSort_meets hpc pre.sort) ?_
    (by simp [abs_le, hlen, hperm, hkey.1, hkey.2, hstride.1, hstride.2, hoff.1, hoff.2, hnb.1,
      hnb.2, hcnt.1, hcnt.2]; omega) hd (by simp; omega)
  intro _ μ₁ sorted
  -- copy(perm + w, perm, w)
  refine Ends.callLast (copy_meets (src := A.perm + A.w) (dst := A.perm) (n := A.w) hpp hw
    (hsrc := by omega) (hdst := by omega) (hsep := Or.inr le_rfl)) ?_
    (by light_side [hlen, hperm]) hd (by simp; omega)
  rintro r μ₂ ⟨copied, same₂⟩
  exact ⟨⟨r, by simp⟩, .of_sorted_copied pre sorted copied same₂⟩

end Light
