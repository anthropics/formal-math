/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Coding.Defs
import all StepMachines.Prog.CountNet
import Mathlib.Data.List.ProdSigma

/-! # Occurrences and places

Section 6: «An occurrence is a pair o = (E, ω) of a clause E ∈ Φ and a literal ω ∈ E, that is, one
position of one clause.» Lean's network (`Groundwork.Prog.Count.wordNet`) numbers PLACES: 3 for each
clause, whether or not a literal stands there. The occurrence (e, j) stands at the place 3e + j
(`place`).
For clauses of at most 3 literals this map is increasing for the reading order and goes onto the
places with a literal. So it carries «the pairs {o₁,o₂}, {o₂,o₃}, … of consecutive occurrences are
the equality tests» (`Coding.tests`) to Lean's links (`linkB`): `mem_tests_iff`.
The file begins with five small facts: a product of increasing lists is increasing in the order of
the dictionary; two increasing lists with the same members are equal; in an increasing list the
order of the positions is the order of the values; two bit strings with the same bits are equal; and
e / μ = a exactly if e lies in the a-th block of μ numbers. `import all StepMachines.Prog.CountNet`
gives access to `slotsOf_eq`, which is not public. -/

public section

namespace Coding

open Groundwork Groundwork.Prog Groundwork.Prog.Count

/-! ### Lists -/

/-- The order of the dictionary on pairs of numbers. -/
@[expose] def lexLt (p q : ℕ × ℕ) : Prop := p.1 < q.1 ∨ (p.1 = q.1 ∧ p.2 < q.2)

/-- The product of two lists that are increasing for r₁ and r₂ is increasing for the order of the
dictionary. -/
theorem pairwise_product {α β : Type} {r₁ : α → α → Prop} {r₂ : β → β → Prop} {l₁ : List α} {l₂ : List β} (h₁ : l₁.Pairwise r₁) (h₂ : l₂.Pairwise r₂) :
    (l₁ ×ˢ l₂).Pairwise fun p q => r₁ p.1 q.1 ∨ (p.1 = q.1 ∧ r₂ p.2 q.2) := by
  induction l₁ with
  | nil => exact List.Pairwise.nil
  | cons x l ih =>
    rw [List.product_cons, List.pairwise_append]
    obtain ⟨hx, hl⟩ := List.pairwise_cons.1 h₁
    refine ⟨List.pairwise_map.2 (h₂.imp fun h => Or.inr ⟨rfl, h⟩), ih hl, ?_⟩
    intro p hp q hq
    obtain ⟨y, -, rfl⟩ := List.mem_map.1 hp
    obtain ⟨q1, q2⟩ := q
    exact Or.inl (hx q1 (List.mem_product.1 hq).1)

/-- Two lists of pairs of numbers that are increasing in the order of the dictionary and have the
same members are equal. -/
theorem eq_of_lex {l₁ l₂ : List (ℕ × ℕ)} (h₁ : l₁.Pairwise lexLt) (h₂ : l₂.Pairwise lexLt) (h : ∀ q, q ∈ l₁ ↔ q ∈ l₂) : l₁ = l₂ := by
  have irr : ∀ {a b : ℕ × ℕ}, lexLt a b → a ≠ b := by
    intro a b hab e
    subst e
    unfold lexLt at hab
    omega
  refine List.Perm.eq_of_pairwise (fun a b _ _ hab hba => ?_) h₁ h₂ ((List.perm_ext_iff_of_nodup (h₁.imp irr) (h₂.imp irr)).2 h)
  unfold lexLt at hab hba
  omega

/-- In a list along which f increases, the order of the positions is the order of the values of f. -/
theorem idxOf_lt_iff {α : Type} [BEq α] [LawfulBEq α] {f : α → ℕ} {l : List α} (hl : l.Pairwise fun x y => f x < f y) {x y : α} (hx : x ∈ l) (hy : y ∈ l) :
    l.idxOf x < l.idxOf y ↔ f x < f y := by
  have key : ∀ {x y : α}, x ∈ l → y ∈ l → l.idxOf x < l.idxOf y → f x < f y := by
    intro x y hx hy h
    have hx' := List.idxOf_lt_length_of_mem hx
    have hy' := List.idxOf_lt_length_of_mem hy
    have h2 := List.pairwise_iff_getElem.1 hl _ _ hx' hy' h
    rwa [List.getElem_idxOf hx', List.getElem_idxOf hy'] at h2
  refine ⟨key hx hy, fun h => ?_⟩
  by_contra hn
  rcases Nat.lt_or_eq_of_le (not_lt.1 hn) with h' | h'
  · have := key hy hx h'
    omega
  · have e : y = x := (List.idxOf_inj hy).1 h'
    subst e
    omega

/-- Two bit strings of the same length with the same bits are equal. -/
theorem ext_getD {l l' : List Bool} (hl : l.length = l'.length) (h : ∀ i < l.length, l.getD i false = l'.getD i false) : l = l' :=
  List.ext_getElem hl fun i h1 h2 => by simpa [List.getD_eq_getElem?_getD, h1, h2] using h i h1

/-- e lies in the a-th block of μ numbers. -/
theorem div_eq_iff_block {μ e a : ℕ} (hμ : 0 < μ) : e / μ = a ↔ a * μ ≤ e ∧ e < a * μ + μ := by
  constructor
  · rintro rfl
    exact ⟨Nat.div_mul_le_self e μ, Nat.lt_div_mul_add hμ⟩
  · rintro ⟨h1, h2⟩
    exact Nat.div_eq_of_lt_le h1 (by rw [Nat.succ_mul]; exact h2)

/-! ### Occurrences -/

variable {g : ℕ} {Φ : Fml}

/-- The place of an occurrence: 3 places for each clause. -/
@[expose] def place (o : ℕ × ℕ) : ℕ := o.1 * 3 + o.2

/-- The place of the pair (i / 3, i % 3) is i. -/
theorem place_div_mod (i : ℕ) : place (i / 3, i % 3) = i := by simp only [place]; omega

/-- Beyond the last clause, Φ.getD e [] is the empty list. -/
theorem getD_nil_of_le {e : ℕ} (h : Φ.length ≤ e) : Φ.getD e [] = [] := by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]; rfl

/-- Every clause, and the empty list beyond the last clause, has at most 3 literals. -/
theorem length_getD_le (h3 : ∀ C ∈ Φ, C.length ≤ 3) (e : ℕ) : (Φ.getD e []).length ≤ 3 := by
  rw [List.getD_eq_getElem?_getD]
  cases h : Φ[e]? with
  | none => simp
  | some C => simpa using h3 C (List.mem_of_getElem? h)

/-- (e, j) is an occurrence in the clauses number e₀, …, e₀ + r − 1 if e is one of these numbers and
j is a position of clause e. -/
theorem mem_occIn {e₀ r : ℕ} {o : ℕ × ℕ} : o ∈ occIn Φ e₀ r ↔ e₀ ≤ o.1 ∧ o.1 < e₀ + r ∧ o.2 < (Φ.getD o.1 []).length := by
  obtain ⟨e, j⟩ := o
  simp only [occIn, List.mem_flatMap, List.mem_range'_1, List.mem_map, List.mem_range, Prod.mk.injEq]
  constructor
  · rintro ⟨e', ⟨h1, h2⟩, j', hj, rfl, rfl⟩
    exact ⟨h1, h2, hj⟩
  · rintro ⟨h1, h2, hj⟩
    exact ⟨e, ⟨h1, h2⟩, j, hj, rfl, rfl⟩

/-- (e, j) is an occurrence in Φ if j is a position of clause e. -/
theorem mem_occAll {o : ℕ × ℕ} : o ∈ occAll Φ ↔ o.2 < (Φ.getD o.1 []).length := by
  rw [occAll, mem_occIn]
  refine ⟨fun h => h.2.2, fun h => ⟨Nat.zero_le _, ?_, h⟩⟩
  by_contra hn
  rw [getD_nil_of_le (by omega)] at h
  simp at h

/-- The clause of an occurrence is one of the clauses of Φ. -/
theorem fst_lt_of_mem_occAll {o : ℕ × ℕ} (h : o ∈ occAll Φ) : o.1 < Φ.length := by
  have := (mem_occIn.1 h).2.1
  omega

/-- The reading order of the occurrences is the order of their places. -/
theorem pairwise_occIn (h3 : ∀ C ∈ Φ, C.length ≤ 3) (e₀ r : ℕ) : (occIn Φ e₀ r).Pairwise fun o o' => place o < place o' := by
  induction r generalizing e₀ with
  | zero => simp [occIn]
  | succ r ih =>
    have e : occIn Φ e₀ (r + 1) = ((List.range (Φ.getD e₀ []).length).map fun j => (e₀, j)) ++ occIn Φ (e₀ + 1) r := by
      simp only [occIn, List.range'_succ, List.flatMap_cons]
    rw [e, List.pairwise_append]
    refine ⟨List.pairwise_map.2 (List.pairwise_lt_range.imp fun h => by simp only [place]; omega), ih (e₀ + 1), ?_⟩
    intro o ho o' ho'
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 ho
    have h1 := length_getD_le h3 e₀
    have h2 := (mem_occIn.1 ho').1
    have h4 := List.mem_range.1 hj
    simp only [place]
    omega

/-- No occurrence is listed twice. -/
theorem nodup_occIn (h3 : ∀ C ∈ Φ, C.length ≤ 3) (e₀ r : ℕ) : (occIn Φ e₀ r).Nodup :=
  (pairwise_occIn h3 e₀ r).imp fun {a b} h e => by subst e; omega

/-! ### Literals at places -/

/-- What stands at place i: the literal of the occurrence (i / 3, i % 3), if this is one. -/
theorem litAt_eq (i : ℕ) : litAt 3 Φ i = if i % 3 < (Φ.getD (i / 3) []).length then some (litOf Φ (i / 3, i % 3)) else none := by
  unfold litAt litOf
  generalize Φ.getD (i / 3) [] = C
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  split_ifs with h
  · rw [List.getElem?_eq_getElem h]; rfl
  · rw [List.getElem?_eq_none (not_lt.1 h)]; rfl

/-- At the place of an occurrence stands its literal. -/
theorem litAt_place (h3 : ∀ C ∈ Φ, C.length ≤ 3) {o : ℕ × ℕ} (ho : o ∈ occAll Φ) : litAt 3 Φ (place o) = some (litOf Φ o) := by
  have h1 := mem_occAll.1 ho
  have h2 := length_getD_le h3 o.1
  have e1 : place o / 3 = o.1 := by simp only [place]; omega
  have e2 : place o % 3 = o.2 := by simp only [place]; omega
  rw [litAt_eq, e1, e2, if_pos h1]

/-- At the place of an occurrence stands the variable of its literal. -/
theorem varAt_place (h3 : ∀ C ∈ Φ, C.length ≤ 3) {o : ℕ × ℕ} (ho : o ∈ occAll Φ) : varAt 3 Φ (place o) = some (litOf Φ o).1 := by
  rw [varAt, litAt_place h3 ho]; rfl

/-- A place with a variable is the place of an occurrence. -/
theorem mem_occAll_of_varAt {i v : ℕ} (h : varAt 3 Φ i = some v) : (i / 3, i % 3) ∈ occAll Φ := by
  rw [mem_occAll]
  by_contra hn
  rw [varAt, litAt_eq, if_neg hn] at h
  simp at h

/-- The place of an occurrence is one of the 3m places of Φ. -/
theorem place_lt (h3 : ∀ C ∈ Φ, C.length ≤ 3) {o : ℕ × ℕ} (ho : o ∈ occAll Φ) : place o < Φ.length * 3 := by
  have h1 := mem_occAll.1 ho
  have h2 := length_getD_le h3 o.1
  have h4 := fst_lt_of_mem_occAll ho
  simp only [place]
  omega

/-! ### Tests and links -/

/-- Lean's link between two places, in words. -/
theorem linkB_iff_places (i i' : ℕ) : linkB 3 Φ i i' = true ↔ i < i' ∧ (varAt 3 Φ i).isSome = true ∧ varAt 3 Φ i = varAt 3 Φ i' ∧
    ∀ t < Φ.length * 3, ¬ (i < t ∧ t < i' ∧ varAt 3 Φ t = varAt 3 Φ i) := by
  simp only [linkB, slotsOf_eq, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range, Bool.not_eq_true', Bool.eq_false_iff, ne_eq, beq_iff_eq, and_assoc]

/-- «the pairs {o₁,o₂}, {o₂,o₃}, … of consecutive occurrences are the equality tests» (Section 6):
(o, o') is a test exactly if Lean's network has a link from the place of o to the place of o'. -/
theorem mem_tests_iff (h3 : ∀ C ∈ Φ, C.length ≤ 3) {o o' : ℕ × ℕ} : (o, o') ∈ tests Φ ↔ o ∈ occAll Φ ∧ o' ∈ occAll Φ ∧ linkB 3 Φ (place o) (place o') = true := by
  have hp : (occAll Φ).Pairwise fun o o' => place o < place o' := pairwise_occIn h3 0 Φ.length
  simp only [tests, List.mem_filter, List.mem_product, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.not_eq_true', Bool.eq_false_iff, ne_eq, and_assoc]
  refine and_congr_right fun ho => and_congr_right fun ho' => ?_
  rw [linkB_iff_places, varAt_place h3 ho, varAt_place h3 ho', idxOf_lt_iff hp ho ho']
  simp only [Option.isSome_some, true_and, Option.some.injEq]
  refine and_congr_right fun _ => and_congr_right fun _ => ⟨fun H t _ ht => ?_, fun H o'' ho'' ht => ?_⟩
  · have hm := mem_occAll_of_varAt ht.2.2
    refine H _ hm ?_
    rw [idxOf_lt_iff hp ho hm, idxOf_lt_iff hp hm ho', place_div_mod]
    have hv := varAt_place h3 hm
    rw [place_div_mod, ht.2.2] at hv
    exact ⟨ht.1, ht.2.1, (Option.some.inj hv).symm⟩
  · rw [idxOf_lt_iff hp ho ho'', idxOf_lt_iff hp ho'' ho'] at ht
    exact H _ (place_lt h3 ho'') ⟨ht.1, ht.2.1, by rw [varAt_place h3 ho'', ht.2.2]⟩

end Coding
