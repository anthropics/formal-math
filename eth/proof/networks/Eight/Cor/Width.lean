/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Eight.Cor.WidthDefs
import Mathlib.Tactic

/-! # Section 7, proof of Corollary 6: the width reduction keeps the number of satisfying assignments (proofs)

Proofs of the four statements of `WidthDefs.lean`: `stForced`, `stRestrict`, `stExtend`, `stWidth`.
The paper gives the reason in one sentence («The number is preserved if each new variable is forced
… to equal the disjunction of the two literals that it replaces»); spelled out:
* `holds_forced`: the three clauses say y = l₁ ∨ l₂.
* Downwards (`splitClause_sound`, `splitAll_sound`): from y ∨ l₃ ∨ … and ¬y ∨ l₁ ∨ l₂ follows l₁ ∨
  l₂ ∨ l₃ ∨ …; this needs nothing about y.
* Upwards (`splitClause_extend`, `splitAll_extend`): give y the value of l₁ ∨ l₂. This needs that
  the fresh variables differ from each other and occur nowhere in the formula.
* Only one way (`splitClause_unique`, `splitAll_unique`): the value of y is determined by those of
  l₁ and l₂, which are variables of the formula or fresh variables set earlier. This needs that no
  fresh variable is left unused.
* Sizes: `splitAll_width`, `length_splitAll` (exactly m + 3N clauses before repetitions are struck
  out), `numFresh_le`.
All of this is for any type of variables. The last section takes V = Fin (n + N) and counts:
restriction to x₀ … xₙ₋₁ is a bijection between the satisfying assignments of the image and those of
φ (`numSat_widthReduce`). -/

public section

namespace Eight.Width

open Sat3 (Lit CNF)

variable {V : Type}

/-! ### Satisfaction -/

theorem holds_nil (a : V → Bool) : Holds a [] := by simp [Holds]

theorem holds_cons {a : V → Bool} {C : List (V × Bool)} {φ : List (List (V × Bool))} :
    Holds a (C :: φ) ↔ (∃ l ∈ C, a l.1 = l.2) ∧ Holds a φ := by simp [Holds]

theorem holds_append {a : V → Bool} {φ ψ : List (List (V × Bool))} : Holds a (φ ++ ψ) ↔ Holds a φ ∧ Holds a ψ := by
  simp [Holds, or_imp, forall_and]

/-- Two assignments that agree on the variables of a formula satisfy it or not together. -/
theorem holds_congr {a b : V → Bool} {φ : List (List (V × Bool))} (h : ∀ C ∈ φ, ∀ l ∈ C, a l.1 = b l.1) :
    Holds a φ ↔ Holds b φ := by
  constructor
  · intro ha C hC
    obtain ⟨l, hl, e⟩ := ha C hC
    exact ⟨l, hl, by rw [← h C hC l hl]; exact e⟩
  · intro hb C hC
    obtain ⟨l, hl, e⟩ := hb C hC
    exact ⟨l, hl, by rw [h C hC l hl]; exact e⟩

/-- The three clauses say y = l₁ ∨ l₂. -/
theorem holds_forced (a : V → Bool) (y : V) (l₁ l₂ : V × Bool) :
    Holds a (forced y l₁ l₂) ↔ (a y = true ↔ a l₁.1 = l₁.2 ∨ a l₂.1 = l₂.2) := by
  obtain ⟨v₁, s₁⟩ := l₁
  obtain ⟨v₂, s₂⟩ := l₂
  simp only [Holds, forced, neg, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, exists_eq_or_imp,
    exists_eq_left]
  generalize a y = p
  generalize a v₁ = q₁
  generalize a v₂ = q₂
  cases p <;> cases q₁ <;> cases q₂ <;> cases s₁ <;> cases s₂ <;> simp

/-- `StForced`. -/
theorem stForced : StForced := fun _ a y l₁ l₂ => ⟨holds_forced a y l₁ l₂, by simp [forced]⟩

/-! ### One clause -/

theorem splitClause_step (y : V) (ys : List V) (l₁ l₂ l₃ l₄ : V × Bool) (r : List (V × Bool)) :
    splitClause (y :: ys) (l₁ :: l₂ :: l₃ :: l₄ :: r) = forced y l₁ l₂ ++ splitClause ys ((y, true) :: l₃ :: l₄ :: r) := rfl

theorem splitClause_nil (C : List (V × Bool)) : splitClause [] C = [C] := by simp [splitClause]

theorem splitClause_short (ys : List V) {C : List (V × Bool)} (h : C.length ≤ 3) : splitClause ys C = [C] := by
  match ys, C, h with
  | [], _, _ => exact splitClause_nil _
  | _ :: _, [], _ => rfl
  | _ :: _, [_], _ => rfl
  | _ :: _, [_, _], _ => rfl
  | _ :: _, [_, _, _], _ => rfl
  | _ :: _, _ :: _ :: _ :: _ :: _, h => simp at h; omega

theorem exists_four {C : List (V × Bool)} (h : ¬ C.length ≤ 3) : ∃ l₁ l₂ l₃ l₄ r, C = l₁ :: l₂ :: l₃ :: l₄ :: r := by
  match C, h with
  | l₁ :: l₂ :: l₃ :: l₄ :: r, _ => exact ⟨l₁, l₂, l₃, l₄, r, rfl⟩
  | [], h | [_], h | [_, _], h | [_, _, _], h => simp at h

/-- An assignment that satisfies the clauses made from C satisfies C. (No condition on the variables
ys.) -/
theorem splitClause_sound (a : V → Bool) : ∀ (ys : List V) (C : List (V × Bool)),
    Holds a (splitClause ys C) → ∃ l ∈ C, a l.1 = l.2
  | [], C, h => by
    rw [splitClause_nil] at h
    exact h C (by simp)
  | y :: ys, C, h => by
    by_cases hC : C.length ≤ 3
    · rw [splitClause_short _ hC] at h
      exact h C (by simp)
    · obtain ⟨l₁, l₂, l₃, l₄, r, rfl⟩ := exists_four hC
      rw [splitClause_step, holds_append, holds_forced] at h
      obtain ⟨l, hl, e⟩ := splitClause_sound a ys _ h.2
      rcases List.mem_cons.1 hl with rfl | hl
      · rcases h.1.1 e with e | e
        · exact ⟨l₁, by simp, e⟩
        · exact ⟨l₂, by simp, e⟩
      · exact ⟨l, by simp only [List.mem_cons] at hl ⊢; tauto, e⟩

/-- A variable of a clause made from C is one of ys or a variable of C. -/
theorem splitClause_vars : ∀ (ys : List V) (C : List (V × Bool)), ∀ D ∈ splitClause ys C, ∀ l ∈ D,
    l.1 ∈ ys ∨ ∃ l' ∈ C, l'.1 = l.1
  | [], C, D, hD, l, hl => by
    rw [splitClause_nil] at hD
    obtain rfl : D = C := by simpa using hD
    exact Or.inr ⟨l, hl, rfl⟩
  | y :: ys, C, D, hD, l, hl => by
    by_cases hC : C.length ≤ 3
    · rw [splitClause_short _ hC] at hD
      obtain rfl : D = C := by simpa using hD
      exact Or.inr ⟨l, hl, rfl⟩
    · obtain ⟨l₁, l₂, l₃, l₄, r, rfl⟩ := exists_four hC
      rw [splitClause_step, List.mem_append] at hD
      rcases hD with hD | hD
      · simp only [forced, neg, List.mem_cons, List.not_mem_nil, or_false] at hD
        rcases hD with rfl | rfl | rfl <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hl <;>
          rcases hl with rfl | rfl | rfl <;> simp
      · rcases splitClause_vars ys _ D hD l hl with h | ⟨l', hl', e⟩
        · exact Or.inl (List.mem_cons_of_mem _ h)
        · rcases List.mem_cons.1 hl' with rfl | hl'
          · exact Or.inl (by simp [← e])
          · exact Or.inr ⟨l', by simp only [List.mem_cons] at hl' ⊢; tauto, e⟩

/-- An assignment that satisfies C can be changed on the fresh variables ys so that it satisfies the
clauses made from C. -/
theorem splitClause_extend : ∀ (ys : List V) (C : List (V × Bool)) (a : V → Bool), ys.Nodup → (∀ l ∈ C, l.1 ∉ ys) →
    (∃ l ∈ C, a l.1 = l.2) → ∃ b : V → Bool, (∀ v, v ∉ ys → b v = a v) ∧ Holds b (splitClause ys C)
  | [], C, a, _, _, h => ⟨a, fun _ _ => rfl, by rw [splitClause_nil]; simpa [Holds] using h⟩
  | y :: ys, C, a, hn, hf, h => by
    classical
    by_cases hC : C.length ≤ 3
    · exact ⟨a, fun _ _ => rfl, by rw [splitClause_short _ hC]; simpa [Holds] using h⟩
    · obtain ⟨l₁, l₂, l₃, l₄, r, rfl⟩ := exists_four hC
      obtain ⟨hy, hn⟩ := List.nodup_cons.1 hn
      have hne : ∀ l ∈ l₁ :: l₂ :: l₃ :: l₄ :: r, l.1 ≠ y := fun l hl e => hf l hl (by simp [e])
      have hnm : ∀ l ∈ l₁ :: l₂ :: l₃ :: l₄ :: r, l.1 ∉ ys := fun l hl e => hf l hl (List.mem_cons_of_mem _ e)
      let a' : V → Bool := Function.update a y (decide (a l₁.1 = l₁.2 ∨ a l₂.1 = l₂.2))
      have ha' : ∀ l ∈ l₁ :: l₂ :: l₃ :: l₄ :: r, a' l.1 = a l.1 := fun l hl => Function.update_of_ne (hne l hl) _ _
      have hay : a' y = decide (a l₁.1 = l₁.2 ∨ a l₂.1 = l₂.2) := Function.update_self _ _ _
      obtain ⟨b, hb, hH⟩ := splitClause_extend ys ((y, true) :: l₃ :: l₄ :: r) a' hn
        (by
          intro l hl
          rcases List.mem_cons.1 hl with rfl | hl
          · exact hy
          · exact hnm l (by simp only [List.mem_cons] at hl ⊢; tauto))
        (by
          obtain ⟨l, hl, e⟩ := h
          by_cases h12 : a l₁.1 = l₁.2 ∨ a l₂.1 = l₂.2
          · exact ⟨(y, true), by simp, by simp [hay, h12]⟩
          · have hl' : l ∈ l₃ :: l₄ :: r := by
              simp only [List.mem_cons] at hl ⊢
              rcases hl with rfl | rfl | hl
              · exact absurd (Or.inl e) h12
              · exact absurd (Or.inr e) h12
              · exact hl
            exact ⟨l, List.mem_cons_of_mem _ hl', by rw [ha' l hl]; exact e⟩)
      refine ⟨b, fun v hv => ?_, ?_⟩
      · rw [hb v fun h => hv (List.mem_cons_of_mem _ h)]
        exact Function.update_of_ne (fun e => hv (by simp [e])) _ _
      · rw [splitClause_step, holds_append, holds_forced]
        refine ⟨?_, hH⟩
        rw [hb y hy, hb _ (hnm l₁ (by simp)), hb _ (hnm l₂ (by simp)), ha' l₁ (by simp), ha' l₂ (by simp), hay]
        simp

/-- Two assignments that satisfy the clauses made from C and agree on the variables of C agree on
the fresh variables, if all of these are used. -/
theorem splitClause_unique (b b' : V → Bool) : ∀ (ys : List V) (C : List (V × Bool)), ys.length ≤ C.length - 3 →
    (∀ l ∈ C, b l.1 = b' l.1) → Holds b (splitClause ys C) → Holds b' (splitClause ys C) → ∀ y ∈ ys, b y = b' y
  | [], _, _, _, _, _, y, hy => by simp at hy
  | y :: ys, C, hlen, hag, h, h', z, hz => by
    have hC : ¬ C.length ≤ 3 := by simp at hlen; omega
    obtain ⟨l₁, l₂, l₃, l₄, r, rfl⟩ := exists_four hC
    rw [splitClause_step, holds_append, holds_forced] at h h'
    have hy : b y = b' y := by
      have e : (b y = true ↔ b' y = true) := by
        rw [h.1, h'.1, hag l₁ (by simp), hag l₂ (by simp)]
      cases hb : b y <;> cases hb' : b' y <;> simp_all
    rcases List.mem_cons.1 hz with rfl | hz
    · exact hy
    · refine splitClause_unique b b' ys _ (by simp at hlen ⊢; omega) ?_ h.2 h'.2 z hz
      intro l hl
      rcases List.mem_cons.1 hl with rfl | hl
      · exact hy
      · exact hag l (by simp only [List.mem_cons] at hl ⊢; tauto)

/-- With enough fresh variables every clause made from C has at most 3 literals. -/
theorem splitClause_width : ∀ (ys : List V) (C : List (V × Bool)), C.length - 3 ≤ ys.length →
    ∀ D ∈ splitClause ys C, D.length ≤ 3
  | [], C, h, D, hD => by
    rw [splitClause_nil] at hD
    obtain rfl : D = C := by simpa using hD
    simp at h; omega
  | y :: ys, C, h, D, hD => by
    by_cases hC : C.length ≤ 3
    · rw [splitClause_short _ hC] at hD
      obtain rfl : D = C := by simpa using hD
      exact hC
    · obtain ⟨l₁, l₂, l₃, l₄, r, rfl⟩ := exists_four hC
      rw [splitClause_step, List.mem_append] at hD
      rcases hD with hD | hD
      · exact (stForced V (fun _ => true) y l₁ l₂).2 D hD
      · exact splitClause_width ys _ (by simp at h ⊢; omega) D hD

/-- The number of clauses made from C: 1, and 3 for each fresh variable that is used. -/
theorem length_splitClause : ∀ (ys : List V) (C : List (V × Bool)),
    (splitClause ys C).length = 1 + 3 * min ys.length (C.length - 3)
  | [], C => by rw [splitClause_nil]; simp
  | y :: ys, C => by
    by_cases hC : C.length ≤ 3
    · rw [splitClause_short _ hC]; simp; omega
    · obtain ⟨l₁, l₂, l₃, l₄, r, rfl⟩ := exists_four hC
      rw [splitClause_step, List.length_append, length_splitClause ys]
      simp [forced]; omega

/-! ### All clauses -/

theorem splitAll_cons (ys : List V) (C : List (V × Bool)) (φ : List (List (V × Bool))) :
    splitAll ys (C :: φ) = splitClause (ys.take (C.length - 3)) C ++ splitAll (ys.drop (C.length - 3)) φ := rfl

theorem numFresh_cons (C : List (V × Bool)) (φ : List (List (V × Bool))) :
    numFresh (C :: φ) = (C.length - 3) + numFresh φ := by simp [numFresh]

/-- An assignment that satisfies the image satisfies the formula. (No condition on the variables
ys.) -/
theorem splitAll_sound (a : V → Bool) : ∀ (φ : List (List (V × Bool))) (ys : List V), Holds a (splitAll ys φ) → Holds a φ
  | [], _, _ => holds_nil a
  | C :: φ, ys, h => by
    rw [splitAll_cons, holds_append] at h
    exact holds_cons.2 ⟨splitClause_sound a _ C h.1, splitAll_sound a φ _ h.2⟩

/-- An assignment that satisfies the formula can be changed on the fresh variables so that it
satisfies the image. -/
theorem splitAll_extend : ∀ (φ : List (List (V × Bool))) (ys : List V) (a : V → Bool), ys.Nodup →
    (∀ C ∈ φ, ∀ l ∈ C, l.1 ∉ ys) → Holds a φ → ∃ b : V → Bool, (∀ v, v ∉ ys → b v = a v) ∧ Holds b (splitAll ys φ)
  | [], _, a, _, _, _ => ⟨a, fun _ _ => rfl, holds_nil a⟩
  | C :: φ, ys, a, hn, hf, h => by
    obtain ⟨hC, hφ⟩ := holds_cons.1 h
    have hsub : (ys.take (C.length - 3)).Sublist ys := List.take_sublist _ _
    have hsub' : (ys.drop (C.length - 3)).Sublist ys := List.drop_sublist _ _
    obtain ⟨b₁, hb₁, hH₁⟩ := splitClause_extend (ys.take (C.length - 3)) C a (hn.sublist hsub)
      (fun l hl hm => hf C (by simp) l hl (hsub.subset hm)) hC
    have hφ₁ : Holds b₁ φ := (holds_congr fun D hD l hl =>
      hb₁ l.1 fun hm => hf D (List.mem_cons_of_mem _ hD) l hl (hsub.subset hm)).2 hφ
    obtain ⟨b₂, hb₂, hH₂⟩ := splitAll_extend φ (ys.drop (C.length - 3)) b₁ (hn.sublist hsub')
      (fun D hD l hl hm => hf D (List.mem_cons_of_mem _ hD) l hl (hsub'.subset hm)) hφ₁
    refine ⟨b₂, fun v hv => ?_, ?_⟩
    · rw [hb₂ v fun hm => hv (hsub'.subset hm), hb₁ v fun hm => hv (hsub.subset hm)]
    · rw [splitAll_cons, holds_append]
      refine ⟨(holds_congr fun D hD l hl => hb₂ l.1 fun hm => ?_).2 hH₁, hH₂⟩
      rcases splitClause_vars _ C D hD l hl with h1 | ⟨l', hl', e⟩
      · exact List.disjoint_take_drop hn le_rfl h1 hm
      · exact hf C (by simp) l' hl' (e ▸ hsub'.subset hm)

/-- Two assignments that satisfy the image and agree on the variables of the formula agree on the
fresh variables, if all of these are used. -/
theorem splitAll_unique (b b' : V → Bool) : ∀ (φ : List (List (V × Bool))) (ys : List V), ys.length ≤ numFresh φ →
    (∀ C ∈ φ, ∀ l ∈ C, b l.1 = b' l.1) → Holds b (splitAll ys φ) → Holds b' (splitAll ys φ) → ∀ y ∈ ys, b y = b' y
  | [], ys, hlen, _, _, _, y, hy => by
    obtain rfl : ys = [] := List.length_eq_zero_iff.1 (by simpa [numFresh] using hlen)
    simp at hy
  | C :: φ, ys, hlen, hag, h, h', y, hy => by
    rw [splitAll_cons, holds_append] at h h'
    rw [numFresh_cons] at hlen
    rw [← List.take_append_drop (C.length - 3) ys, List.mem_append] at hy
    rcases hy with hy | hy
    · exact splitClause_unique b b' _ C (by simp) (hag C (by simp)) h.1 h'.1 y hy
    · exact splitAll_unique b b' φ _ (by simp; omega) (fun D hD => hag D (List.mem_cons_of_mem _ hD)) h.2 h'.2 y hy

/-- With enough fresh variables every clause of the image has at most 3 literals. -/
theorem splitAll_width : ∀ (φ : List (List (V × Bool))) (ys : List V), numFresh φ ≤ ys.length →
    ∀ D ∈ splitAll ys φ, D.length ≤ 3
  | [], _, _, D, hD => by simp [splitAll] at hD
  | C :: φ, ys, hlen, D, hD => by
    rw [numFresh_cons] at hlen
    rw [splitAll_cons, List.mem_append] at hD
    rcases hD with hD | hD
    · exact splitClause_width _ C (by simp; omega) D hD
    · exact splitAll_width φ _ (by simp; omega) D hD

/-- With enough fresh variables the image, before repetitions are struck out, has exactly m + 3N
clauses: m the number of clauses of the formula, N the number of fresh variables. -/
theorem length_splitAll : ∀ (φ : List (List (V × Bool))) (ys : List V), numFresh φ ≤ ys.length →
    (splitAll ys φ).length = φ.length + 3 * numFresh φ
  | [], _, _ => by simp [splitAll, numFresh]
  | C :: φ, ys, hlen => by
    rw [numFresh_cons] at hlen
    rw [splitAll_cons, List.length_append, length_splitClause, length_splitAll φ _ (by simp; omega), numFresh_cons]
    simp; omega

/-- At most k − 3 fresh variables for each clause of a k-CNF. -/
theorem numFresh_le (k : ℕ) : ∀ φ : List (List (V × Bool)), (∀ C ∈ φ, C.length ≤ k) → numFresh φ ≤ (k - 3) * φ.length
  | [], _ => by simp [numFresh]
  | C :: φ, h => by
    have h1 := h C (by simp)
    have h2 := numFresh_le k φ fun D hD => h D (List.mem_cons_of_mem _ hD)
    rw [numFresh_cons, List.length_cons, Nat.mul_succ]
    omega

/-! ### Formulas on x₀ … xₙ₋₁ -/

section fin

variable {n : ℕ}

/-- The fresh variables xₙ … x_{n+N−1}. -/
@[expose] def freshFin (n N : ℕ) : List (Fin (n + N)) := (List.finRange N).map (Fin.natAdd n)

/-- The formula, read as a formula on n + N variables. -/
@[expose] def lift (N : ℕ) (φ : CNF n) : CNF (n + N) := φ.map fun C => C.map fun l => (Fin.castAdd N l.1, l.2)

theorem widthReduce_eq (φ : CNF n) : widthReduce φ = (splitAll (freshFin n (numFresh φ)) (lift (numFresh φ) φ)).dedup := rfl

theorem holds_dedup {W : Type} [DecidableEq W] {a : W → Bool} {φ : List (List (W × Bool))} : Holds a φ.dedup ↔ Holds a φ := by
  simp [Holds]

theorem holds_lift (N : ℕ) (φ : CNF n) (b : Fin (n + N) → Bool) : Holds b (lift N φ) ↔ Holds (fun i => b (Fin.castAdd N i)) φ := by
  simp [Holds, lift]

theorem numFresh_lift (N : ℕ) (φ : CNF n) : numFresh (lift N φ) = numFresh φ := by
  simp [numFresh, lift, Function.comp_def]

theorem length_freshFin (n N : ℕ) : (freshFin n N).length = N := by simp [freshFin]

theorem nodup_freshFin (n N : ℕ) : (freshFin n N).Nodup :=
  (List.nodup_finRange N).map (Fin.natAdd_injective N n)

theorem natAdd_mem_freshFin (n N : ℕ) (j : Fin N) : Fin.natAdd n j ∈ freshFin n N := by simp [freshFin]

theorem castAdd_notMem_freshFin (n N : ℕ) (i : Fin n) : Fin.castAdd N i ∉ freshFin n N := by
  simp only [freshFin, List.mem_map, not_exists, not_and]
  intro j _ e
  have := congrArg Fin.val e
  simp at this
  omega

theorem lift_fresh (N : ℕ) (φ : CNF n) : ∀ C ∈ lift N φ, ∀ l ∈ C, l.1 ∉ freshFin n N := by
  intro C hC l hl
  simp only [lift, List.mem_map] at hC
  obtain ⟨C', _, rfl⟩ := hC
  obtain ⟨l', _, rfl⟩ := List.mem_map.1 hl
  exact castAdd_notMem_freshFin n N l'.1

/-- `StRestrict`. -/
theorem stRestrict : StRestrict := fun _ φ b h =>
  (holds_lift _ φ b).1 (splitAll_sound b _ _ (holds_dedup.1 h))

/-- `StExtend`. -/
theorem stExtend : StExtend := by
  intro n φ a ha
  have ha' : Holds (Fin.append a fun _ : Fin (numFresh φ) => false) (lift (numFresh φ) φ) := by
    rw [holds_lift]
    simpa using ha
  obtain ⟨b, hb, hH⟩ := splitAll_extend _ _ _ (nodup_freshFin n (numFresh φ)) (lift_fresh _ φ) ha'
  refine ⟨b, ⟨holds_dedup.2 hH, fun i => ?_⟩, ?_⟩
  · rw [hb _ (castAdd_notMem_freshFin n _ i)]
    simp
  · rintro b' ⟨hH', hb'⟩
    have hold : ∀ i, b' (Fin.castAdd (numFresh φ) i) = b (Fin.castAdd (numFresh φ) i) := by
      intro i
      rw [hb' i, hb _ (castAdd_notMem_freshFin n _ i)]
      simp
    funext v
    refine Fin.addCases hold (fun j => ?_) v
    refine splitAll_unique b' b (lift _ φ) (freshFin n _) (by rw [length_freshFin, numFresh_lift]) ?_ (holds_dedup.1 hH') hH _
      (natAdd_mem_freshFin n _ j)
    intro C hC l hl
    simp only [lift, List.mem_map] at hC
    obtain ⟨C', _, rfl⟩ := hC
    obtain ⟨l', _, rfl⟩ := List.mem_map.1 hl
    exact hold l'.1

/-- The number of satisfying assignments is kept. -/
theorem numSat_widthReduce (φ : CNF n) : SatK.numSat (widthReduce φ) = SatK.numSat φ := by
  unfold SatK.numSat
  refine Finset.card_bij (fun b _ i => b (Fin.castAdd (numFresh φ) i)) ?_ ?_ ?_
  · intro b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
    exact stRestrict n φ b hb
  · intro b hb b' hb' e
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb hb'
    exact (stExtend n φ _ (stRestrict n φ b hb)).unique ⟨hb, fun _ => rfl⟩ ⟨hb', fun i => (congrFun e i).symm⟩
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
    obtain ⟨b, ⟨hb, e⟩, _⟩ := stExtend n φ a ha
    exact ⟨b, by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hb, funext e⟩

/-- `StWidth`. -/
theorem stWidth : StWidth := by
  intro n φ
  refine ⟨⟨fun C hC => ?_, List.nodup_dedup _⟩, numSat_widthReduce φ, fun k hk => ?_⟩
  · exact splitAll_width (lift _ φ) (freshFin n _) (by rw [length_freshFin, numFresh_lift]) C (List.mem_dedup.1 hC)
  · have h1 := numFresh_le k φ hk
    refine ⟨h1, ?_⟩
    calc (widthReduce φ).length ≤ (splitAll (freshFin n (numFresh φ)) (lift (numFresh φ) φ)).length :=
          (List.dedup_sublist _).length_le
      _ = φ.length + 3 * numFresh φ := by
          rw [length_splitAll _ _ (by rw [length_freshFin, numFresh_lift]), numFresh_lift]
          simp [lift]
      _ ≤ φ.length + 3 * ((k - 3) * φ.length) := by omega

end fin

end Eight.Width
