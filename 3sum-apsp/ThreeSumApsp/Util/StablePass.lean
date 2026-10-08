/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Util.CountingSort
public import Mathlib.Data.List.GetD

/-!
# One stable pass of a radix sort, on lists

A stable counting sort moves the item at place `j` of a list `π` to place `sortPos kf n j`, where
`n` is the length of `π` and `kf j = keyAt kd π j` is the key of that item (`IsStablePass`).  The
new list is a rearrangement of `π` (`IsStablePass.perm`), and if `π` was sorted by `g`, the new list
is sorted by the pair (key, `g`) (`IsStablePass.sorted`).  This is the step of a radix sort that
starts with the least significant digit.
-/

@[expose] public section

namespace ThreeSumApsp

variable {π π' : List ℕ} {kd g : ℕ → ℕ} {B : ℕ}

/-- The keys of the items of a list, by place. -/
def keyAt (kd : ℕ → ℕ) (π : List ℕ) (j : ℕ) : ℕ := kd (π.getD j 0)

/-- The key at a place of the list. -/
theorem keyAt_eq (kd : ℕ → ℕ) {j : ℕ} (hj : j < π.length) : keyAt kd π j = kd π[j] := by
  rw [keyAt, List.getD_eq_getElem _ _ hj]

/-- `π'` is the result of a stable pass on `π` by the key `kd`: it is as long as `π`, and the item
at place `j` of `π` stands at place `sortPos … j` of `π'`. -/
def IsStablePass (kd : ℕ → ℕ) (π π' : List ℕ) : Prop :=
  π'.length = π.length ∧
    ∀ j (hj : j < π.length), π'.getD (sortPos (keyAt kd π) π.length j) 0 = π[j]

/-- A stable pass rearranges the list: the places `sortPos … j` are a permutation of the places. -/
theorem IsStablePass.perm (h : IsStablePass kd π π') : π'.Perm π := by
  obtain ⟨hlen, hplace⟩ := h
  let f : Fin π.length → Fin π.length := fun j =>
    ⟨sortPos (keyAt kd π) π.length j, sortPos_lt _ j.2⟩
  have hinj : Function.Injective f := fun a b hab =>
    Fin.ext (eq_of_sortPos_eq a.2 b.2 (by simpa [f] using congrArg Fin.val hab))
  let σ : Equiv.Perm (Fin π.length) := Equiv.ofBijective f (Finite.injective_iff_bijective.1 hinj)
  have hold : π = List.ofFn fun j : Fin π.length => π[j] := by simp
  have hnew : π' = List.ofFn fun q : Fin π.length => π'.getD q 0 := by
    apply List.ext_getElem
    · simp [hlen]
    · intro i hi _
      simp [List.getElem?_eq_getElem hi]
  have hmove : (fun j : Fin π.length => π[j]) = (fun q : Fin π.length => π'.getD q 0) ∘ σ :=
    funext fun j => (hplace j j.2).symm
  rw [hnew]
  conv_rhs => rw [hold, hmove]
  exact (Equiv.Perm.ofFn_comp_perm σ _).symm

/-- After a stable pass by `kd` on a list sorted by `g`, the list is sorted by `kd · B + g`, if
`g < B`. -/
theorem IsStablePass.sorted (h : IsStablePass kd π π') (hg : ∀ i ∈ π, g i < B)
    (hs : (π.map g).Pairwise (· ≤ ·)) :
    (π'.map fun i => kd i * B + g i).Pairwise (· ≤ ·) := by
  obtain ⟨hlen, hplace⟩ := h
  rw [List.pairwise_iff_getElem]
  intro a b ha hb hab
  simp only [List.length_map] at ha hb
  simp only [List.getElem_map]
  -- The items at the places `a < b` of `π'` come from the places `i` and `j` of `π`.
  obtain ⟨i, hi, hia⟩ := exists_sortPos_eq (keyAt kd π) (hlen ▸ ha)
  obtain ⟨j, hj, hjb⟩ := exists_sortPos_eq (keyAt kd π) (hlen ▸ hb)
  rw [show π'[a] = π[i] by rw [← hplace i hi, hia, List.getD_eq_getElem _ _ ha],
    show π'[b] = π[j] by rw [← hplace j hj, hjb, List.getD_eq_getElem _ _ hb]]
  -- So the key of `π[i]` is smaller, or the keys are equal and `i < j`.
  have hlt : sortPos (keyAt kd π) π.length i < sortPos (keyAt kd π) π.length j := by omega
  rw [sortPos_lt_sortPos_iff hi hj, keyAt_eq kd hi, keyAt_eq kd hj] at hlt
  rcases hlt with hlt | ⟨heq, hij⟩
  · have hgi := hg _ (List.getElem_mem hi)
    have hmul : (kd π[i] + 1) * B ≤ kd π[j] * B := Nat.mul_le_mul_right B hlt
    rw [Nat.add_mul, Nat.one_mul] at hmul
    omega
  · rw [heq]
    have hgij := (List.pairwise_iff_getElem.1 hs) i j (by simpa using hi) (by simpa using hj) hij
    simp only [List.getElem_map] at hgij
    omega

/-- The number of places with a key below `s` is the number of items with a key below `s`. -/
theorem cntLt_keyAt (kd : ℕ → ℕ) (π : List ℕ) (s : ℕ) :
    cntLt (keyAt kd π) s π.length = π.countP fun i => decide (kd i < s) := by
  induction π using List.reverseRecOn with
  | nil => simp
  | append_singleton l x ih =>
    have hfirst : cntLt (keyAt kd (l ++ [x])) s l.length = cntLt (keyAt kd l) s l.length :=
      cntLt_congr s fun i hi => by rw [keyAt, keyAt, List.getD_append _ _ _ _ hi]
    have hlast : keyAt kd (l ++ [x]) l.length = kd x := by simp [keyAt]
    rw [List.length_append, List.length_singleton, cntLt_succ_right, hfirst, ih,
      List.countP_append, hlast]
    by_cases hx : kd x < s <;> simp [hx]

end ThreeSumApsp
