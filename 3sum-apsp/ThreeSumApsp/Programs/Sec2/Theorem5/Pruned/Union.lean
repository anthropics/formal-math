/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec2.Theorem5.Contracts

/-!
# The merge of two lists (Section 2.4.4: "a union of slices is a merge")

union(pa, na, pb, nb, pc) writes the merge of the list of na numbers at pa and the list of nb
numbers at pb to pc, a number that heads both lists being taken once, and returns its length.  The
program follows Spec.mergeUnion step by step.

union_entry shows that a call does this in at most 70 (na + nb + 1) steps and changes no cell
outside the output.  Both loops keep UnionInv.  What writing one number does to the data is
union_emit.  The three bodies are unionBoth_ends, unionLeft_ends and unionRight_ends, and
union_entry treats the two loops.
-/

@[expose] public section

namespace Light.Sec2

open ThreeSumApsp

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## The program -/

namespace UnionLocal

/-- The first list, A in the comments of the proofs. -/
abbrev ListA : ℕ := 0
/-- The length na of the first list. -/
abbrev LenA : ℕ := 1
/-- The second list, B in the comments of the proofs. -/
abbrev ListB : ℕ := 2
/-- The length nb of the second list. -/
abbrev LenB : ℕ := 3
/-- Where the merge is written, C in the comments of the proofs. -/
abbrev Dest : ℕ := 4
/-- The number i of entries taken from the first list. -/
abbrev TakenA : ℕ := 5
/-- The number j of entries taken from the second list. -/
abbrev TakenB : ℕ := 6
/-- The number len of entries written. -/
abbrev Written : ℕ := 7
/-- The head a of what is left of the first list. -/
abbrev HeadA : ℕ := 8
/-- The head b of what is left of the second list. -/
abbrev HeadB : ℕ := 9

end UnionLocal

open UnionLocal

/-- Both lists have a head: the smaller one is written and its list advances; if they are equal, the
number is written once and both lists advance. -/
def unionBoth : Stmt :=
  .set HeadA (M (v ListA +' v TakenA)) ;;
  .set HeadB (M (v ListB +' v TakenB)) ;;
  .ite (v HeadA <' v HeadB) (
    .store (v Dest +' v Written) (v HeadA) ;; .set TakenA (v TakenA +' k 1) ;;
      .set Written (v Written +' k 1)) (
    .ite (v HeadB <' v HeadA) (
      .store (v Dest +' v Written) (v HeadB) ;; .set TakenB (v TakenB +' k 1) ;;
        .set Written (v Written +' k 1)) (
      .store (v Dest +' v Written) (v HeadA) ;; .set TakenA (v TakenA +' k 1) ;;
        .set TakenB (v TakenB +' k 1) ;; .set Written (v Written +' k 1)))

/-- The head of the first list is written. -/
def unionLeft : Stmt :=
  .store (v Dest +' v Written) (M (v ListA +' v TakenA)) ;; .set TakenA (v TakenA +' k 1) ;;
    .set Written (v Written +' k 1)

/-- The head of the second list is written. -/
def unionRight : Stmt :=
  .store (v Dest +' v Written) (M (v ListB +' v TakenB)) ;; .set TakenB (v TakenB +' k 1) ;;
    .set Written (v Written +' k 1)

/-- union(pa, na, pb, nb, pc); it returns len. -/
def unionBody : Stmt :=
  .while (v TakenA <' v LenA) (.ite (v TakenB <' v LenB) unionBoth unionLeft) ;;
  .while (v TakenB <' v LenB) unionRight ;;
  .set 0 (v Written)

/-! ## The invariant -/

/-- What union assumes: the two lists lie below the output, and the output fits in the memory. -/
structure UnionPre (lim : Limits) (μ : ℕ → ℤ) (pa pb pc : ℕ) (la lb : List ℕ) : Prop where
  listA : SegN μ pa la
  listB : SegN μ pb lb
  belowA : pa + la.length ≤ pc
  belowB : pb + lb.length ≤ pc
  room : pc + (la.length + lb.length) ≤ lim.space

/-- What both loops keep: i and j numbers of the two lists have been taken; the list done has been
written to pc; together with the merge of what is left it is the merge of the two lists; no cell
outside the output has changed. -/
structure UnionInv (μ μ' : ℕ → ℤ) (pc : ℕ) (la lb : List ℕ) (i j : ℕ) (done : List ℕ) : Prop where
  hi : i ≤ la.length
  hj : j ≤ lb.length
  len_le : done.length ≤ i + j
  merged : done ++ Spec.mergeUnion (la.drop i) (lb.drop j) = Spec.mergeUnion la lb
  written : SegN μ' pc done
  rest : SameOutside μ μ' pc (la.length + lb.length)

/-- The state of the two loops. -/
abbrev unionState (pa pb pc : ℕ) (la lb : List ℕ) (i j len : ℕ) (a b : ℤ) (μ' : ℕ → ℤ) : State :=
  ⟨frame [pa, la.length, pb, lb.length, pc, i, j, len, a, b], μ'⟩

/-- The invariant of both loops.  In the second loop the first list is used up: i₀ = la.length. -/
def UnionLoop (μ : ℕ → ℤ) (pa pb pc : ℕ) (la lb : List ℕ) (i₀ : ℕ) (σ : State) : Prop :=
  ∃ (i j : ℕ) (done : List ℕ) (a b : ℤ) (μ' : ℕ → ℤ), i₀ ≤ i ∧
    σ = unionState pa pb pc la lb i j done.length a b μ' ∧ UnionInv μ μ' pc la lb i j done

/-- What is still to be taken. -/
def unionRest (la lb : List ℕ) (σ : State) : ℕ :=
  (la.length - (σ.loc TakenA).toNat) + (lb.length - (σ.loc TakenB).toNat)

/-- What a round that starts in σ achieves: the invariant holds again, and less is left. -/
def UnionNext (μ : ℕ → ℤ) (pa pb pc : ℕ) (la lb : List ℕ) (i₀ : ℕ) (σ σ' : State) : Prop :=
  UnionLoop μ pa pb pc la lb i₀ σ' ∧ unionRest la lb σ' < unionRest la lb σ

variable {μ μ' : ℕ → ℤ} {pa pb pc : ℕ} {la lb : List ℕ} {i j : ℕ} {done : List ℕ}

/-- The merge with the empty list. -/
theorem mergeUnion_nil_right (l : List ℕ) : Spec.mergeUnion l [] = l := by
  cases l <;> simp [Spec.mergeUnion]

/-- The first list lies outside the output, so it can be read at any time. -/
theorem UnionPre.readA (pre : UnionPre lim μ pa pb pc la lb) (inv : UnionInv μ μ' pc la lb i j done)
    (h : i < la.length) : μ' (pa + i) = (la[i] : ℕ) := by
  have := pre.belowA
  exact (inv.rest _ (Or.inl (by omega))).trans (pre.listA.getElem h)

/-- The second list lies outside the output, so it can be read at any time. -/
theorem UnionPre.readB (pre : UnionPre lim μ pa pb pc la lb) (inv : UnionInv μ μ' pc la lb i j done)
    (h : j < lb.length) : μ' (pb + j) = (lb[j] : ℕ) := by
  have := pre.belowB
  exact (inv.rest _ (Or.inl (by omega))).trans (pre.listB.getElem h)

/-- **One number is written.**  If x heads the merge of what is left, and what is left afterwards
starts at i' and j', then after writing x the invariant holds again, and less is left. -/
theorem union_emit (inv : UnionInv μ μ' pc la lb i j done) (a b a' b' : ℤ) {i₀ i' j' x : ℕ}
    (h₀ : i₀ ≤ i') (hi' : i' ≤ la.length) (hj' : j' ≤ lb.length) (hsum : i + j < i' + j')
    (hu : Spec.mergeUnion (la.drop i) (lb.drop j)
      = x :: Spec.mergeUnion (la.drop i') (lb.drop j')) :
    UnionNext μ pa pb pc la lb i₀ (unionState pa pb pc la lb i j done.length a b μ')
      (unionState pa pb pc la lb i' j' (done ++ [x]).length a' b'
        (Function.update μ' (pc + done.length) x)) := by
  light_facts inv
  refine ⟨⟨i', j', done ++ [x], a', b', _, h₀, rfl, hi', hj', by simp; omega, ?_,
    inv.written.snoc x, inv.rest.update ⟨by omega, by omega⟩ _⟩, ?_⟩
  · rw [← inv.merged, hu]
    simp
  · simp [unionRest]
    omega

/-! ## The three bodies -/

/-- Both lists have a head. -/
theorem unionBoth_ends (std : Std lim) (pre : UnionPre lim μ pa pb pc la lb)
    (inv : UnionInv μ μ' pc la lb i j done) (hi : i < la.length) (hj : j < lb.length) (a b : ℤ) :
    Ends lim P d unionBoth (unionState pa pb pc la lb i j done.length a b μ') 36
      (UnionNext μ pa pb pc la lb 0 (unionState pa pb pc la lb i j done.length a b μ')) := by
  light_facts std pre inv
  have hA := pre.readA inv hi
  have hB := pre.readB inv hj
  have da := List.drop_eq_getElem_cons hi
  have db := List.drop_eq_getElem_cons hj
  -- a := A[i]; b := B[j]
  light_set (la[i] : ℕ) using hA
  light_set (lb[j] : ℕ) using hB
  -- if a < b
  refine Ends.iteLast (fun hab => ?_) (fun hab => ?_)
  · replace hab : la[i] < lb[j] := by simpa using hab
    -- C[len] := a; i := i + 1; len := len + 1
    light_store (pc + done.length) (la[i] : ℕ)
    light_set (i + 1 : ℕ)
    light_set ((done ++ [la[i]]).length : ℕ)
    exact union_emit inv _ _ _ _ (Nat.zero_le _) (by omega) hj.le (by omega)
      (by rw [da, db, Spec.mergeUnion, if_pos hab])
  replace hab : ¬ la[i] < lb[j] := by simpa using hab
  -- else if b < a
  refine Ends.iteLast (fun hba => ?_) (fun hba => ?_)
  · replace hba : lb[j] < la[i] := by simpa using hba
    -- C[len] := b; j := j + 1; len := len + 1
    light_store (pc + done.length) (lb[j] : ℕ)
    light_set (j + 1 : ℕ)
    light_set ((done ++ [lb[j]]).length : ℕ)
    exact union_emit inv _ _ _ _ (Nat.zero_le _) hi.le (by omega) (by omega)
      (by rw [db, da, Spec.mergeUnion, if_neg hab, if_pos hba, ← da])
  · replace hba : ¬ lb[j] < la[i] := by simpa using hba
    -- else C[len] := a; i := i + 1; j := j + 1; len := len + 1
    light_store (pc + done.length) (la[i] : ℕ)
    light_set (i + 1 : ℕ)
    light_set (j + 1 : ℕ)
    light_set ((done ++ [la[i]]).length : ℕ)
    exact union_emit inv _ _ _ _ (Nat.zero_le _) (by omega) (by omega) (by omega)
      (by rw [da, db, Spec.mergeUnion, if_neg hab, if_neg hba])

/-- The second list is used up. -/
theorem unionLeft_ends (std : Std lim) (pre : UnionPre lim μ pa pb pc la lb)
    (inv : UnionInv μ μ' pc la lb i lb.length done) (hi : i < la.length) (a b : ℤ) :
    Ends lim P d unionLeft (unionState pa pb pc la lb i lb.length done.length a b μ') 36
      (UnionNext μ pa pb pc la lb 0
        (unionState pa pb pc la lb i lb.length done.length a b μ')) := by
  light_facts std pre inv
  have hA := pre.readA inv hi
  -- C[len] := A[i]; i := i + 1; len := len + 1
  light_store (pc + done.length) (la[i] : ℕ) using hA
  light_set (i + 1 : ℕ)
  light_set ((done ++ [la[i]]).length : ℕ)
  exact union_emit inv _ _ _ _ (Nat.zero_le _) (by omega) le_rfl (by omega)
    (by rw [List.drop_length, mergeUnion_nil_right, mergeUnion_nil_right,
      List.drop_eq_getElem_cons hi])

/-- The first list is used up. -/
theorem unionRight_ends (std : Std lim) (pre : UnionPre lim μ pa pb pc la lb)
    (inv : UnionInv μ μ' pc la lb la.length j done) (hj : j < lb.length) (a b : ℤ) :
    Ends lim P d unionRight (unionState pa pb pc la lb la.length j done.length a b μ') 16
      (UnionNext μ pa pb pc la lb la.length
        (unionState pa pb pc la lb la.length j done.length a b μ')) := by
  light_facts std pre inv
  have hB := pre.readB inv hj
  -- C[len] := B[j]; j := j + 1; len := len + 1
  light_store (pc + done.length) (lb[j] : ℕ) using hB
  light_set (j + 1 : ℕ)
  light_set ((done ++ [lb[j]]).length : ℕ)
  exact union_emit inv _ _ _ _ le_rfl le_rfl (by omega) (by omega)
    (by rw [List.drop_length, List.drop_eq_getElem_cons hj]; simp [Spec.mergeUnion])

/-! ## The procedure -/

/-- **union**: a call writes the merge of the two lists to pc, returns its length and changes no
cell outside the output, in at most 70 (na + nb + 1) steps. -/
theorem union_entry (std : Std lim) (hP : P[pUnion]? = some unionBody) {c : ℕ} (hc : 70 ≤ c) :
    UnionSpec lim P c := by
  intro pa pb pc la lb μ hsa hsb hpa hpb hsp d hd
  have pre : UnionPre lim μ pa pb pc la lb := ⟨hsa, hsb, hpa, hpb, hsp⟩
  refine .mono_const (.of_body hP ?_) hc
  refine Ends.seq ((la.length + lb.length) * 44 + 4) (lb.length * 20 + 6) ?_ (by omega)
  -- while i < na
  refine Ends.whileVariant (UnionLoop μ pa pb pc la lb 0) (unionRest la lb) 40 ?start
    (fun _ _ => ⟨trivial, trivial⟩) ?round ?next (by simp [unionRest])
  case start =>
    exact ⟨0, 0, [], 0, 0, μ, le_rfl, by rw [unionState, ← frame_append_zeros _ 5]; rfl, by omega,
      by omega, by simp, by simp, by simp [SegN], .refl⟩
  case round =>
    rintro _ ⟨i, j, done, a, b, μ', -, rfl, inv⟩ hi
    replace hi : i < la.length := by simpa using hi
    -- if j < nb
    refine Ends.iteLast (fun hj => ?_) (fun hj => ?_)
    · exact unionBoth_ends std pre inv hi (by simpa using hj) a b
    · obtain rfl : j = lb.length := le_antisymm inv.hj (by simpa using hj)
      exact unionLeft_ends std pre inv hi a b
  case next =>
    rintro _ ⟨i, j, done, a, b, μ', -, rfl, inv⟩ hi
    obtain rfl : i = la.length := le_antisymm inv.hi (by simpa using hi)
    -- while j < nb
    refine Ends.seq (lb.length * 20 + 4) 2 ?_ (by omega)
    refine Ends.whileVariant (UnionLoop μ pa pb pc la lb la.length) (unionRest la lb) 16
      ⟨_, j, done, a, b, μ', le_rfl, rfl, inv⟩ (fun _ _ => ⟨trivial, trivial⟩) ?round ?done
      (by simp [unionRest])
    case round =>
      rintro _ ⟨i, j, done, a, b, μ', hi, rfl, inv⟩ hj
      obtain rfl : i = la.length := le_antisymm inv.hi hi
      exact unionRight_ends std pre inv (by simpa using hj) a b
    case done =>
      rintro _ ⟨i, j, done, a, b, μ', hi, rfl, inv⟩ hj
      obtain rfl : i = la.length := le_antisymm inv.hi hi
      obtain rfl : j = lb.length := le_antisymm inv.hj (by simpa using hj)
      obtain rfl : done = Spec.mergeUnion la lb := by simpa [Spec.mergeUnion] using inv.merged
      -- return len
      light_set ((Spec.mergeUnion la lb).length : ℕ)
      exact ⟨by simp, inv.written, inv.rest⟩

end Light.Sec2
