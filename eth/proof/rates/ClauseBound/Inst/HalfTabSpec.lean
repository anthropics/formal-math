/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ClauseBound.Inst.HalfTab
public import ClauseBound.Boson.Size
public import PaddedDescent.F.LenList

/-! # The matrices of the operators as tables: correctness

If the list of monomials is in order (`FlatOK`), all parts are at most W and the pad is long enough,
then the tables of proof/rates/ClauseBound/Inst/HalfTab.lean hold the matrices they are meant to
hold;
for the table of a[·], the matrices of the operators a[r], this is `tabOp_rep`, with `padOp` as a
sufficient length of the pad. -/

public section

namespace ClauseBound.Inst.Half

open Finset Groundwork PaddedDescent.F ClauseBound.Inst.Rec ClauseBound.Boson

/-! ### Tables and look-ups -/

/-- The entry number i·(length of M) + j of a table with rows L and columns M. -/
theorem getD_flatMap_map {γ δ : Type} (M : List δ) (f : γ → δ → ℤ) : ∀ (L : List γ) (i j : ℕ) (hi : i < L.length) (hj : j < M.length),
    (L.flatMap fun x => M.map fun y => f x y).getD (i * M.length + j) 0 = f L[i] M[j] := by
  intro L
  induction L with
  | nil => intro i j hi; simp at hi
  | cons x L ih =>
    intro i j hi hj
    rw [List.flatMap_cons]
    cases i with
    | zero =>
      rw [Nat.zero_mul, Nat.zero_add, List.getD_append _ _ _ _ (by simpa using hj), List.getD_eq_getElem _ _ (by simpa using hj)]
      simp
    | succ i =>
      have hi' : i < L.length := by simpa using hi
      rw [List.getD_append_right _ _ _ _ (by rw [List.length_map]; nlinarith)]
      have : (i + 1) * M.length + j - (M.map fun y => f x y).length = i * M.length + j := by
        rw [List.length_map, Nat.succ_mul]; omega
      rw [this, ih i j hi' hj]
      simp

/-- Looking up in the table of a function gives its value. -/
theorem lookT_tab {flat : List (List ℕ)} (f : List ℕ → List ℕ → ℤ) {π σ : List ℕ} (hπ : π ∈ flat) (hσ : σ ∈ flat) :
    lookT flat (tab flat f) π σ = f π σ := by
  have h1 := List.idxOf_lt_length_iff.2 hπ
  have h2 := List.idxOf_lt_length_iff.2 hσ
  rw [lookT, tab, getD_flatMap_map flat f flat _ _ h1 h2, List.getElem_idxOf h1, List.getElem_idxOf h2]

/-- The table of a function holds a family of matrices if the function has their entries. -/
theorem rep_tab {flat : List (List ℕ)} {f : List ℕ → List ℕ → ℤ} {F : ℤ → Ker}
    (h : ∀ π ∈ flat, ∀ σ ∈ flat, f π σ = F ((π.sum : ℤ) - σ.sum) π σ) : Rep flat (tab flat f) F :=
  fun π hπ σ hσ => (lookT_tab f hπ hσ).trans (h π hπ σ hσ)

/-- A table has (length of the list)² entries. -/
theorem length_tab (flat : List (List ℕ)) (f : List ℕ → List ℕ → ℤ) : (tab flat f).length = flat.length ^ 2 := by
  simp [tab, List.length_flatMap, sq]

/-- The length of the word of an integer of absolute value at most 2^B. -/
theorem len_int_le {z : ℤ} {B : ℕ} (h : |z| ≤ 2 ^ B) : len z ≤ 3 * B + 8 := by
  have h1 : z.natAbs < 2 ^ (B + 1) := by
    have : (z.natAbs : ℤ) ≤ 2 ^ B := by rwa [Int.natCast_natAbs]
    have h2 : z.natAbs ≤ 2 ^ B := by exact_mod_cast this
    have h3 : 2 ^ B < 2 ^ (B + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  have h2 : Nat.size z.natAbs ≤ B + 1 := Nat.size_le.2 h1
  rw [len_int]
  omega

/-- The length of the word of a table with entries of absolute value at most 2^B. -/
theorem len_tab_le {flat : List (List ℕ)} {f : List ℕ → List ℕ → ℤ} {B : ℕ} (h : ∀ π ∈ flat, ∀ σ ∈ flat, |f π σ| ≤ 2 ^ B) :
    len (tab flat f) ≤ flat.length ^ 2 * (3 * B + 10) + 2 := by
  rw [← length_tab flat f]
  refine Lists.len_list_le _ _ fun z hz => ?_
  obtain ⟨π, hπ, hz⟩ := List.mem_flatMap.1 hz
  obtain ⟨σ, hσ, rfl⟩ := List.mem_map.1 hz
  have := len_int_le (h π hπ σ hσ)
  omega

/-! ### One round -/

/-- The coefficient of the series of t_n. -/
theorem betF_eq {W n : ℕ} (hn : n ≤ W) (r : ℤ) : betF W n r = bet n r := by
  rw [betF, bet, min_eq_left hn, chooseZ_eq]

/-- A sum over the distinct members of a list. -/
theorem sum_toFinset_coe (π : List ℕ) (g : ℕ → ℤ) : ∑ l ∈ (π : Multiset ℕ).toFinset, g l = (π.dedup.map g).sum := by
  rw [Finset.sum_eq_multiset_sum, Multiset.toFinset_val, Multiset.coe_dedup, Multiset.map_coe, Multiset.sum_coe]

/-- One round: the entries of the normally ordered product with the series of t_n. -/
theorem nopE_eq {W n : ℕ} {flat : List (List ℕ)} {T : List ℤ} {F : ℤ → Ker} (hf : FlatOK W flat) (hn : n ≤ W) (hT : Rep flat T F) {π σ : List ℕ}
    (hπ : π ∈ flat) (hσ : σ ∈ flat) : nopE W n flat T π σ = nop n F ((π.sum : ℤ) - σ.sum) π σ := by
  rw [nopE, nop, sum_toFinset_coe, sum_toFinset_coe]
  congr 1
  · refine congrArg List.sum (List.map_congr_left fun l hl => ?_)
    have hl' : l ∈ π := List.mem_dedup.1 hl
    have hs : ((π.erase l).sum : ℤ) - σ.sum = (π.sum : ℤ) - σ.sum - l := by
      have := List.sum_erase hl'
      push_cast [← this]
      ring
    rw [betF_eq hn, hT _ (hf.erase π hπ l hl') σ hσ, hs, cre, if_pos (Multiset.mem_coe.2 hl'), Multiset.coe_erase]
  · refine congrArg List.sum (List.map_congr_left fun k hk => ?_)
    have hk' : k ∈ σ := List.mem_dedup.1 hk
    have hs : (π.sum : ℤ) - (σ.erase k).sum = (π.sum : ℤ) - σ.sum + k := by
      have := List.sum_erase hk'
      push_cast [← this]
      ring
    rw [betF_eq hn, hT π hπ _ (hf.erase σ hσ k hk'), hs, ann, Multiset.coe_count, Multiset.coe_erase]

/-! ### The tables -/

/-- The table of the identity. -/
theorem oneT_rep {W : ℕ} {flat : List (List ℕ)} (hf : FlatOK W flat) : Rep flat (oneT flat) (op []) := by
  refine rep_tab fun π hπ σ hσ => ?_
  by_cases h : π = σ
  · subst h
    simp [op, one]
  · have h' : (π : Multiset ℕ) ≠ σ := fun e => h (hf.inj π hπ σ hσ e)
    rw [if_neg h, op]
    split_ifs
    · simp [one, h']
    · rfl

theorem tabOp_nil (pad : U) (W : ℕ) (flat : List (List ℕ)) : tabOp pad W flat [] = cap pad [] (oneT flat) := rfl

/-- The table of (n :: a)[·] is made from that of a[·] by one round. -/
theorem tabOp_cons (pad : U) (W : ℕ) (flat : List (List ℕ)) (n : ℕ) (a : List ℕ) :
    tabOp pad W flat (n :: a) = cap pad [] (tab flat (nopE W n flat (tabOp pad W flat a))) := by
  simp [tabOp, List.reverse_cons, List.foldl_append]

/-- The sufficient length of the pad grows with the number of parts. -/
theorem padOp_mono (W Δ : ℕ) {L L' : ℕ} (h : L ≤ L') : padOp W Δ L ≤ padOp W Δ L' := by
  unfold padOp
  gcongr

/-- The table of a[·] holds the matrices of a[r]. -/
theorem tabOp_rep {pad : U} {W : ℕ} {flat : List (List ℕ)} {a : List ℕ} (hW : 1 ≤ W) (hf : FlatOK W flat) (ha : ∀ n ∈ a, n ≤ W)
    (hp : padOp W flat.length a.length ≤ pad.length) : Rep flat (tabOp pad W flat a) (op a) := by
  induction a with
  | nil =>
    have hlen : len (oneT flat) ≤ pad.length := by
      refine (len_tab_le (B := 0) fun π _ σ _ => ?_).trans (by simpa [padOp] using hp)
      split_ifs <;> simp
    rw [tabOp_nil, cap_eq hlen]
    exact oneT_rep hf
  | cons n a ih =>
    have ih' := ih (fun x hx => ha x (by simp [hx])) ((padOp_mono W _ (by simp)).trans hp)
    have hE : ∀ π ∈ flat, ∀ σ ∈ flat, nopE W n flat (tabOp pad W flat a) π σ = op (n :: a) ((π.sum : ℤ) - σ.sum) π σ :=
      fun π hπ σ hσ => nopE_eq hf (ha n (by simp)) ih' hπ hσ
    have hlen : len (tab flat (nopE W n flat (tabOp pad W flat a))) ≤ pad.length := by
      refine (len_tab_le (B := (4 * W + 1) * (n :: a).length) fun π hπ σ hσ => ?_).trans hp
      rw [hE π hπ σ hσ]
      exact abs_op_le hW (n :: a) ha _ (by simpa using hf.sum_le π hπ) (by simpa using hf.sum_le σ hσ)
    rw [tabOp_cons, cap_eq hlen]
    exact rep_tab hE

end ClauseBound.Inst.Half
