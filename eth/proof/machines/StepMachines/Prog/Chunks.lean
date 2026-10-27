/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Groundwork.Net.Defs
public import Mathlib.Data.List.Basic
public import Mathlib.Data.List.TakeDrop
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Vector
public import Mathlib.Data.List.FinRange
public import Mathlib.Data.List.Nodup
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith

/-! Words (List Bool), counters, and cutting a word into chunks of given lengths.
sum_toWord: a sum over y < 2^ℓ of G(the ℓ-bit word of y) is the sum of G over all words of length ℓ.
sum_cut: a sum over all words of length Σ c i of F(the chunks) is the sum of F over all tuples of
words. -/

namespace Groundwork

open Finset

/-- The ℓ-bit word of y, lowest bit first. -/
@[expose] public def toWord : ℕ → ℕ → List Bool
  | 0, _ => []
  | ℓ + 1, y => decide (y % 2 = 1) :: toWord ℓ (y / 2)

/-- The number written by a word, lowest bit first. -/
@[expose] public def ofWord : List Bool → ℕ
  | [] => 0
  | b :: w => b.toNat + 2 * ofWord w

@[simp] public theorem length_toWord (ℓ y : ℕ) : (toWord ℓ y).length = ℓ := by
  induction ℓ generalizing y with
  | zero => rfl
  | succ ℓ ih => simp [toWord, ih]

public theorem ofWord_lt (w : List Bool) : ofWord w < 2 ^ w.length := by
  induction w with
  | nil => simp [ofWord]
  | cons b w ih =>
    have : b.toNat ≤ 1 := Bool.toNat_le b
    simp only [ofWord, List.length_cons, pow_succ]
    omega

public theorem ofWord_toWord {ℓ y : ℕ} (h : y < 2 ^ ℓ) : ofWord (toWord ℓ y) = y := by
  induction ℓ generalizing y with
  | zero => simp only [pow_zero] at h; simp only [toWord, ofWord]; omega
  | succ ℓ ih =>
    have h2 : y / 2 < 2 ^ ℓ := by rw [pow_succ] at h; omega
    simp only [toWord, ofWord, ih h2]
    rcases Nat.mod_two_eq_zero_or_one y with h' | h' <;> simp [h'] <;> omega

public theorem toWord_ofWord (w : List Bool) : toWord w.length (ofWord w) = w := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    have h1 : (b.toNat + 2 * ofWord w) / 2 = ofWord w := by
      have : b.toNat ≤ 1 := Bool.toNat_le b
      omega
    simp only [List.length_cons, toWord, ofWord, h1, ih]
    cases b <;> simp

/-- All words of length ℓ. -/
@[expose] public def words (ℓ : ℕ) : Finset (List Bool) := (range (2 ^ ℓ)).image (toWord ℓ)

@[simp] public theorem mem_words {ℓ : ℕ} {w : List Bool} : w ∈ words ℓ ↔ w.length = ℓ := by
  simp only [words, mem_image, mem_range]
  constructor
  · rintro ⟨y, _, rfl⟩; simp
  · rintro rfl; exact ⟨ofWord w, ofWord_lt w, toWord_ofWord w⟩

public theorem toWord_injOn (ℓ : ℕ) : Set.InjOn (toWord ℓ) (range (2 ^ ℓ) : Finset ℕ) := by
  intro y hy y' hy' h
  rw [← ofWord_toWord (mem_range.1 hy), h, ofWord_toWord (mem_range.1 hy')]

public theorem card_words (ℓ : ℕ) : #(words ℓ) = 2 ^ ℓ := by
  rw [words, card_image_of_injOn (toWord_injOn ℓ), card_range]

/-- A sum over the counter y < 2^ℓ is a sum over all words of length ℓ. -/
public theorem sum_toWord {X : Type*} [AddCommMonoid X] (ℓ : ℕ) (G : List Bool → X) :
    ∑ y ∈ range (2 ^ ℓ), G (toWord ℓ y) = ∑ w ∈ words ℓ, G w :=
  (sum_image (toWord_injOn ℓ)).symm

/-! ### Cutting a word into chunks -/

/-- The chunks of lengths c₁, c₂, … of a word, as a list. -/
@[expose] public def chunks : List ℕ → List Bool → List (List Bool)
  | [], _ => []
  | c :: cs, w => w.take c :: chunks cs (w.drop c)

section cut

variable {ι : Type*} [DecidableEq ι]

/-- The chunks of a word, as a function: the indices in the list e get chunks of lengths c i, in
this order;
all other indices get d. -/
@[expose] public def cut (c : ι → ℕ) (d : List Bool) : List ι → List Bool → ι → List Bool
  | [], _ => fun _ => d
  | i :: e, w => Function.update (cut c d e (w.drop (c i))) i (w.take (c i))

/-- The inverse of cut: the words t i, i in e, one after the other. -/
@[expose] public def glue (e : List ι) (t : ι → List Bool) : List Bool := (e.map t).flatten

public theorem cut_eq_getD (c : ι → ℕ) (d : List Bool) (e : List ι) (w : List Bool) (i : ι) :
    cut c d e w i = (chunks (e.map c) w).getD (e.idxOf i) d := by
  induction e generalizing w with
  | nil => rfl
  | cons j e ih =>
    by_cases h : j = i
    · subst h; simp [cut, chunks]
    · rw [List.idxOf_cons_ne _ h]
      simp [cut, chunks, Function.update_of_ne (Ne.symm h), ih]

/-- cut_eq_getD for any lawful ==, such as the one of a product type. -/
public theorem cut_eq_getD_beq [BEq ι] [LawfulBEq ι] (c : ι → ℕ) (d : List Bool) (e : List ι) (w : List Bool)
    (i : ι) : cut c d e w i = (chunks (e.map c) w).getD (e.idxOf i) d := by
  induction e generalizing w with
  | nil => rfl
  | cons j e ih =>
    by_cases h : j = i
    · subst h; simp [cut, chunks]
    · have h' : (j == i) = false := by simpa using h
      simp [cut, chunks, List.idxOf_cons, h', Function.update_of_ne (Ne.symm h), ih]

public theorem cut_of_notMem (c : ι → ℕ) (d : List Bool) (e : List ι) (w : List Bool) {i : ι} (h : i ∉ e) :
    cut c d e w i = d := by
  induction e generalizing w with
  | nil => rfl
  | cons j e ih =>
    rw [List.mem_cons, not_or] at h
    rw [cut, Function.update_of_ne h.1, ih _ h.2]

public theorem length_cut (c : ι → ℕ) (d : List Bool) (e : List ι) (w : List Bool) (hw : w.length = (e.map c).sum)
    {i : ι} (h : i ∈ e) : (cut c d e w i).length = c i := by
  induction e generalizing w with
  | nil => simp at h
  | cons j e ih =>
    simp only [List.map_cons, List.sum_cons] at hw
    by_cases hji : i = j
    · subst hji; simp only [cut, Function.update_self, List.length_take]; omega
    · rw [cut, Function.update_of_ne hji]
      exact ih _ (by rw [List.length_drop]; omega) ((List.mem_cons.1 h).resolve_left hji)

public theorem length_cut_of_le (c : ι → ℕ) (d : List Bool) (e : List ι) (w : List Bool)
    (hw : (e.map c).sum ≤ w.length) {i : ι} (h : i ∈ e) : (cut c d e w i).length = c i := by
  induction e generalizing w with
  | nil => simp at h
  | cons j e ih =>
    simp only [List.map_cons, List.sum_cons] at hw
    by_cases hji : i = j
    · subst hji; simp only [cut, Function.update_self, List.length_take]; omega
    · rw [cut, Function.update_of_ne hji]
      exact ih _ (by rw [List.length_drop]; omega) ((List.mem_cons.1 h).resolve_left hji)

omit [DecidableEq ι] in
public theorem glue_congr (e : List ι) {t t' : ι → List Bool} (h : ∀ i ∈ e, t i = t' i) : glue e t = glue e t' := by
  unfold glue; rw [List.map_congr_left h]

public theorem glue_cut (c : ι → ℕ) (d : List Bool) (e : List ι) (he : e.Nodup) (w : List Bool)
    (hw : w.length = (e.map c).sum) : glue e (cut c d e w) = w := by
  induction e generalizing w with
  | nil => simp only [List.map_nil, List.sum_nil, List.length_eq_zero_iff] at hw; simp [glue, hw]
  | cons j e ih =>
    simp only [List.map_cons, List.sum_cons] at hw
    rw [List.nodup_cons] at he
    have h1 : glue e (cut c d (j :: e) w) = glue e (cut c d e (w.drop (c j))) :=
      glue_congr e fun i hi => by
        rw [cut, Function.update_of_ne]
        rintro rfl; exact he.1 hi
    have h2 : glue (j :: e) (cut c d (j :: e) w) = cut c d (j :: e) w j ++ glue e (cut c d (j :: e) w) := by
      simp [glue]
    rw [h2, h1, ih he.2 _ (by rw [List.length_drop]; omega), cut, Function.update_self, List.take_append_drop]

omit [DecidableEq ι] in
public theorem length_glue (c : ι → ℕ) (e : List ι) (t : ι → List Bool) (h : ∀ i ∈ e, (t i).length = c i) :
    (glue e t).length = (e.map c).sum := by
  induction e with
  | nil => rfl
  | cons j e ih =>
    have h2 : glue (j :: e) t = t j ++ glue e t := by simp [glue]
    rw [h2, List.length_append, h j List.mem_cons_self, ih fun i hi => h i (List.mem_cons_of_mem _ hi)]
    simp

public theorem cut_glue (c : ι → ℕ) (d : List Bool) (e : List ι) (he : e.Nodup) (t : ι → List Bool)
    (h : ∀ i ∈ e, (t i).length = c i) (h' : ∀ i, i ∉ e → t i = d) : cut c d e (glue e t) = t := by
  induction e generalizing t with
  | nil => funext i; exact (h' i (by simp)).symm
  | cons j e ih =>
    rw [List.nodup_cons] at he
    have h2 : glue (j :: e) t = t j ++ glue e t := by simp [glue]
    have h3 : glue e t = glue e (Function.update t j d) :=
      glue_congr e fun i hi => by
        rw [Function.update_of_ne]
        rintro rfl; exact he.1 hi
    have hj := h j List.mem_cons_self
    have h4 := ih he.2 (Function.update t j d)
      (fun i hi => by
        rw [Function.update_of_ne (by rintro rfl; exact he.1 hi)]
        exact h i (List.mem_cons_of_mem _ hi))
      (fun i hi => by
        by_cases hij : i = j
        · subst hij; simp
        · rw [Function.update_of_ne hij]; exact h' i (by simp [hij, hi]))
    rw [cut, h2, ← hj, List.drop_left, List.take_left, h3, h4, Function.update_idem, Function.update_eq_self]

/-- A sum over all words of length Σ c i of F(the chunks) is the sum of F over all tuples of words.
e lists the indices i with P i, each once. -/
public theorem sum_cut {X : Type*} [AddCommMonoid X] [Fintype ι] (P : ι → Prop) [DecidablePred P] (e : List ι)
    (he : e.Nodup) (hP : ∀ i, i ∈ e ↔ P i) (c : ι → ℕ) (d : List Bool) (F : (ι → List Bool) → X) :
    ∑ w ∈ words (e.map c).sum, F (cut c d e w) = ∑ t ∈ tuples P (fun i => words (c i)) d, F t := by
  have hm : ∀ t : ι → List Bool, t ∈ tuples P (fun i => words (c i)) d ↔
      (∀ i ∈ e, (t i).length = c i) ∧ ∀ i, i ∉ e → t i = d := by
    intro t
    simp only [tuples, Fintype.mem_piFinset]
    constructor
    · intro h
      refine ⟨fun i hi => ?_, fun i hi => ?_⟩
      · have := h i; rw [if_pos ((hP i).1 hi)] at this; exact mem_words.1 this
      · have := h i; rw [if_neg (fun hp => hi ((hP i).2 hp))] at this; exact mem_singleton.1 this
    · rintro ⟨h1, h2⟩ i
      by_cases hp : P i
      · rw [if_pos hp]; exact mem_words.2 (h1 i ((hP i).2 hp))
      · rw [if_neg hp]; exact mem_singleton.2 (h2 i fun hi => hp ((hP i).1 hi))
  refine sum_nbij' (cut c d e) (glue e) ?_ ?_ ?_ ?_ fun _ _ => rfl
  · intro w hw
    exact (hm _).2 ⟨fun i hi => length_cut c d e w (mem_words.1 hw) hi, fun i hi => cut_of_notMem c d e w hi⟩
  · intro t ht
    exact mem_words.2 (length_glue c e t ((hm t).1 ht).1)
  · intro w hw
    exact glue_cut c d e he w (mem_words.1 hw)
  · intro t ht
    exact cut_glue c d e he t ((hm t).1 ht).1 ((hm t).1 ht).2

/-- sum_toWord followed by sum_cut: a sum over the counter y < 2^(Σ c i) of F(the chunks of the word
of y) is the sum
of F over all tuples of words. -/
public theorem sum_cut_toWord {X : Type*} [AddCommMonoid X] [Fintype ι] (P : ι → Prop) [DecidablePred P]
    (e : List ι) (he : e.Nodup) (hP : ∀ i, i ∈ e ↔ P i) (c : ι → ℕ) (d : List Bool)
    (F : (ι → List Bool) → X) :
    ∑ y ∈ range (2 ^ (e.map c).sum), F (cut c d e (toWord (e.map c).sum y))
      = ∑ t ∈ tuples P (fun i => words (c i)) d, F t := by
  rw [sum_toWord _ fun w => F (cut c d e w), sum_cut P e he hP]

/-! ### Chunks of equal length, found by position -/

/-- The j-th block of ℓ bits of a word. -/
@[expose] public def block (ℓ j : ℕ) (w : List Bool) : List Bool := (w.drop (j * ℓ)).take ℓ

public theorem length_block {ℓ j : ℕ} {w : List Bool} (h : (j + 1) * ℓ ≤ w.length) : (block ℓ j w).length = ℓ := by
  rw [block, List.length_take, List.length_drop]
  rw [Nat.succ_mul] at h
  omega

public theorem getD_chunks_replicate (ℓ r j : ℕ) (w d : List Bool) (hj : j < r) :
    (chunks (List.replicate r ℓ) w).getD j d = block ℓ j w := by
  induction r generalizing j w with
  | zero => omega
  | succ r ih =>
    rw [List.replicate_succ, chunks]
    cases j with
    | zero => simp [block]
    | succ j =>
      rw [List.getD_cons_succ, ih j _ (by omega), block, block, List.drop_drop]
      congr 2; ring

/-- A sum over all words of r·ℓ bits of F(the blocks) is the sum of F over all tuples of words of ℓ
bits.
pos numbers the indices i with P i by 0, …, r-1. -/
public theorem sum_blocks {X : Type*} [AddCommMonoid X] [Fintype ι] (P : ι → Prop) [DecidablePred P]
    (pos : ι → ℕ) (r ℓ : ℕ) (hinj : ∀ i i', P i → P i' → pos i = pos i' → i = i') (hlt : ∀ i, P i → pos i < r)
    (hsurj : ∀ j < r, ∃ i, P i ∧ pos i = j) (d : List Bool) (F : (ι → List Bool) → X) :
    ∑ w ∈ words (r * ℓ), F (fun i => if P i then block ℓ (pos i) w else d)
      = ∑ t ∈ tuples P (fun _ => words ℓ) d, F t := by
  choose inv hinv using hsurj
  let e : List ι := (List.finRange r).map fun j : Fin r => inv j.1 j.2
  have hlen : e.length = r := by simp [e]
  have he : e.Nodup := by
    refine (List.nodup_finRange r).map fun (j j' : Fin r) h => ?_
    have h1 := (hinv j.1 j.2).2
    have h2 := (hinv j'.1 j'.2).2
    change inv j.1 j.2 = inv j'.1 j'.2 at h
    rw [h] at h1
    exact Fin.ext (h1.symm.trans h2)
  have hget : ∀ i (hi : P i), e[pos i]'(by rw [hlen]; exact hlt i hi) = i := by
    intro i hi
    simp only [e, List.getElem_map, List.getElem_finRange]
    exact hinj _ _ (hinv _ _).1 hi (hinv _ _).2
  have hP : ∀ i, i ∈ e ↔ P i := by
    intro i
    constructor
    · intro h
      obtain ⟨j, _, rfl⟩ := List.mem_map.1 h
      exact (hinv j.1 j.2).1
    · intro hi
      rw [← hget i hi]; exact List.getElem_mem _
  have hidx : ∀ i, P i → e.idxOf i = pos i := by
    intro i hi
    have := he.idxOf_getElem (pos i) (by rw [hlen]; exact hlt i hi)
    rwa [hget i hi] at this
  have hmap : e.map (fun _ => ℓ) = List.replicate r ℓ := by rw [List.map_const', hlen]
  have hsum : (e.map fun _ => ℓ).sum = r * ℓ := by rw [hmap]; simp
  rw [← sum_cut P e he hP (fun _ => ℓ) d F, hsum]
  refine sum_congr rfl fun w _ => congrArg F (funext fun i => ?_)
  by_cases hi : P i
  · rw [if_pos hi, cut_eq_getD, hmap, hidx i hi, getD_chunks_replicate _ _ _ _ _ (hlt i hi)]
  · rw [if_neg hi, cut_of_notMem _ _ _ _ fun h => hi ((hP i).1 h)]

end cut

/-! ### Numbering the pairs a < b < K -/

/-- The number of the pair a < b: pairs are listed by b, then by a. -/
@[expose] public def tri (a b : ℕ) : ℕ := b * (b - 1) / 2 + a

theorem tri_zero_succ (b : ℕ) : tri 0 (b + 1) = tri 0 b + b := by
  have : (b + 1) * (b + 1 - 1) = b * (b - 1) + 2 * b := by
    cases b with
    | zero => rfl
    | succ b => simp only [Nat.add_sub_cancel]; ring
  simp only [tri, this, add_zero]
  rw [Nat.add_mul_div_left _ _ (by omega)]

theorem tri_zero_mono {b b' : ℕ} (h : b ≤ b') : tri 0 b ≤ tri 0 b' := by
  simp only [tri, add_zero]
  exact Nat.div_le_div_right (Nat.mul_le_mul h (by omega))

theorem tri_eq (a b : ℕ) : tri a b = tri 0 b + a := by simp [tri]

public theorem tri_lt {a b K : ℕ} (hab : a < b) (hb : b < K) : tri a b < K * (K - 1) / 2 := by
  have h1 := tri_zero_succ b
  have h2 := tri_zero_mono (show b + 1 ≤ K from hb)
  have h3 : tri 0 K = K * (K - 1) / 2 := by simp [tri]
  rw [tri_eq]; omega

public theorem tri_inj {a b a' b' : ℕ} (hab : a < b) (hab' : a' < b') (h : tri a b = tri a' b') :
    a = a' ∧ b = b' := by
  rw [tri_eq a b, tri_eq a' b'] at h
  rcases lt_trichotomy b b' with hb | hb | hb
  · have h1 := tri_zero_succ b
    have h2 := tri_zero_mono (show b + 1 ≤ b' from hb)
    omega
  · subst hb; exact ⟨by omega, rfl⟩
  · have h1 := tri_zero_succ b'
    have h2 := tri_zero_mono (show b' + 1 ≤ b from hb)
    omega

public theorem tri_surj {K j : ℕ} (h : j < K * (K - 1) / 2) : ∃ a b, a < b ∧ b < K ∧ tri a b = j := by
  have h3 : ∀ K, tri 0 K = K * (K - 1) / 2 := fun K => by simp [tri]
  rw [← h3] at h
  induction K with
  | zero => simp [tri] at h
  | succ K ih =>
    rw [tri_zero_succ] at h
    by_cases hj : j < tri 0 K
    · obtain ⟨a, b, h1, h2, h3⟩ := ih hj
      exact ⟨a, b, h1, by omega, h3⟩
    · exact ⟨j - tri 0 K, K, by omega, by omega, by rw [tri_eq]; omega⟩

/-- A sum over all words of K(K-1)/2 · ℓ bits is a sum over all labellings of the pairs a < b in Fin
K. -/
public theorem sum_blocks_pairs {X : Type*} [AddCommMonoid X] (K ℓ : ℕ) (d : List Bool)
    (F : (Fin K × Fin K → List Bool) → X) :
    ∑ w ∈ words (K * (K - 1) / 2 * ℓ), F (fun p => if p.1 < p.2 then block ℓ (tri p.1 p.2) w else d)
      = ∑ t ∈ tuples (fun p : Fin K × Fin K => p.1 < p.2) (fun _ => words ℓ) d, F t := by
  refine sum_blocks (fun p : Fin K × Fin K => p.1 < p.2) (fun p => tri p.1 p.2) _ ℓ ?_ ?_ ?_ d F
  · intro p p' hp hp' h
    obtain ⟨h1, h2⟩ := tri_inj hp hp' h
    exact Prod.ext (Fin.ext h1) (Fin.ext h2)
  · intro p hp
    exact tri_lt hp p.2.2
  · intro j hj
    obtain ⟨a, b, h1, h2, h3⟩ := tri_surj hj
    exact ⟨(⟨a, by omega⟩, ⟨b, h2⟩), h1, h3⟩

end Groundwork
