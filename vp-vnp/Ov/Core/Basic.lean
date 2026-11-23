/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Ov.Core.Tensor

/-!
# Restrictions and sums of restrictions: the basic calculus

Paper: the subsection "Tensors". `Restr s t` says that s is a restriction of t, and `SumRestr s b` that s
is covered by the b k. Restriction is reflexive and
transitive and compatible with products, powers, products of families and `push` (giving legs to
parties); sums of restrictions can be substituted in one another and multiplied, and are compatible
with the same operations.
-/

set_option linter.unusedSectionVars false

namespace Ov

open Finset

namespace Ten

variable {K : Type} [Field K] {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-! ### Values of the constructions -/

@[simp] theorem one_val (x : ∀ p, (1 : Ten K I).ι p) : (1 : Ten K I).val x = 1 := rfl

theorem mul_val (s t : Ten K I) (x : ∀ p, (s * t).ι p) :
    (s * t).val x = s.val (fun p => (x p).1) * t.val (fun p => (x p).2) := rfl

theorem prod_val {κ : Type} [Fintype κ] [DecidableEq κ] (b : κ → Ten K I)
    (x : ∀ p, (prod b).ι p) : (prod b).val x = ∏ k, (b k).val (fun p => x p k) := rfl

theorem push_val (π : J → I) (t : Ten K J) (x : ∀ q, (push π t).ι q) :
    (push π t).val x = t.val (fun j => x (π j) ⟨j, rfl⟩) := rfl

theorem unit_val (r : ℕ) (x : J → Fin r) :
    (unit K J r).val x = if ∀ i j, x i = x j then 1 else 0 := rfl

/-- The k-th power is the product of k equal tensors. -/
theorem kpow_eq_prod (t : Ten K I) (k : ℕ) : kpow t k = prod (fun _ : Fin k => t) := rfl

/-- The same legs with another array. -/
def withVal (t : Ten K I) (v : (∀ p, t.ι p) → K) : Ten K I where
  ι := t.ι
  val := v

@[simp] theorem withVal_val (t : Ten K I) (v : (∀ p, t.ι p) → K) : (t.withVal v).val = v := rfl

/-! ### Local maps applied to arrays -/

/-- Local maps L applied to an array f; this is `app` for plain index sets in the place of the legs of
tensors. -/
def appG {α β : I → Type} [∀ p, Fintype (β p)] (L : ∀ p, α p → β p → K)
    (f : (∀ p, β p) → K) (x : ∀ p, α p) : K :=
  ∑ y, (∏ p, L p (x p) (y p)) * f y

theorem app_eq_appG {s t : Ten K I} (L : Loc s t) (x : ∀ p, s.ι p) : app L x = appG L t.val x := rfl

/-- Local maps compose. -/
theorem appG_comp {α β γ : I → Type} [∀ p, Fintype (β p)] [∀ p, Fintype (γ p)]
    (L : ∀ p, α p → β p → K) (M : ∀ p, β p → γ p → K) (f : (∀ p, γ p) → K) (x : ∀ p, α p) :
    appG L (appG M f) x = appG (fun p a c => ∑ b, L p a b * M p b c) f x := by
  simp only [appG, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [Fintype.prod_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.prod_mul_distrib, mul_assoc]

/-- Local maps applied to a sum. -/
theorem appG_sum {α β : I → Type} [∀ p, Fintype (β p)] {κ : Type} [Fintype κ]
    (L : ∀ p, α p → β p → K) (f : κ → (∀ p, β p) → K) (x : ∀ p, α p) :
    appG L (fun y => ∑ k, f k y) x = ∑ k, appG L (f k) x := by
  simp only [appG, Finset.mul_sum]
  rw [Finset.sum_comm]

/-- Local maps applied to a product of two arrays. -/
theorem appG_mul {α β α' β' : I → Type} [∀ p, Fintype (β p)] [∀ p, Fintype (β' p)]
    (L : ∀ p, α p → β p → K) (L' : ∀ p, α' p → β' p → K)
    (f : (∀ p, β p) → K) (g : (∀ p, β' p) → K) (x : ∀ p, α p × α' p) :
    appG (β := fun p => β p × β' p) (fun p a b => L p a.1 b.1 * L' p a.2 b.2)
      (fun y => f (fun p => (y p).1) * g (fun p => (y p).2)) x =
    appG L f (fun p => (x p).1) * appG L' g (fun p => (x p).2) := by
  simp only [appG]
  rw [Finset.sum_mul_sum, ← Fintype.sum_prod_type']
  refine Fintype.sum_equiv
    ⟨fun y => (fun p => (y p).1, fun p => (y p).2), fun z p => (z.1 p, z.2 p),
      fun _ => rfl, fun _ => rfl⟩ _ _ fun y => ?_
  simp only [Equiv.coe_fn_mk, Finset.prod_mul_distrib]
  ring

/-- Local maps applied to a product of a family of arrays. -/
theorem appG_prod {κ : Type} [Fintype κ] [DecidableEq κ] {α β : κ → I → Type}
    [∀ k p, Fintype (β k p)] (L : ∀ k p, α k p → β k p → K) (f : ∀ k, (∀ p, β k p) → K)
    (x : ∀ p k, α k p) :
    appG (β := fun p => ∀ k, β k p) (fun p a b => ∏ k, L k p (a k) (b k))
      (fun y => ∏ k, f k (fun p => y p k)) x =
    ∏ k, appG (L k) (f k) (fun p => x p k) := by
  simp only [appG]
  rw [Fintype.prod_sum]
  refine Fintype.sum_equiv (Equiv.piComm _) _ _ fun y => ?_
  rw [Finset.prod_mul_distrib, Finset.prod_comm]
  rfl

/-- The index tuples of the legs sorted by their parties correspond to the index tuples of all
legs. -/
def pushEquiv (π : J → I) (β : J → Type) :
    (∀ q, ∀ j : {j : J // π j = q}, β j.1) ≃ (∀ j, β j) where
  toFun y j := y (π j) ⟨j, rfl⟩
  invFun z _ j := z j.1
  left_inv y := by
    funext q j
    obtain ⟨j, rfl⟩ := j
    rfl
  right_inv _ := rfl

/-- Local maps applied to an array whose legs are sorted by parties. -/
theorem appG_push (π : J → I) {α β : J → Type} [∀ j, Fintype (β j)]
    (L : ∀ j, α j → β j → K) (f : (∀ j, β j) → K) (x : ∀ q, ∀ j : {j : J // π j = q}, α j.1) :
    appG (β := fun q => ∀ j : {j : J // π j = q}, β j.1)
      (fun q a b => ∏ j : {j : J // π j = q}, L j.1 (a j) (b j))
      (fun y => f (fun j => y (π j) ⟨j, rfl⟩)) x =
    appG L f (fun j => x (π j) ⟨j, rfl⟩) := by
  simp only [appG]
  refine Fintype.sum_equiv (pushEquiv π β) _ _ fun y => ?_
  congr 1
  rw [← Fintype.prod_fiberwise π]
  refine Finset.prod_congr rfl fun q _ => Finset.prod_congr rfl fun j _ => ?_
  obtain ⟨j, rfl⟩ := j
  rfl

/-- Local maps whose matrices have at most one entry that is not 0 in each row: the row a of the
matrix of p has the entry w p a in the column g p a. -/
theorem appG_map {α β : I → Type} [∀ p, Fintype (β p)] [∀ p, DecidableEq (β p)]
    (w : ∀ p, α p → K) (g : ∀ p, α p → β p) (f : (∀ p, β p) → K) (x : ∀ p, α p) :
    appG (fun p a b => if b = g p a then w p a else 0) f x =
      (∏ p, w p (x p)) * f (fun p => g p (x p)) := by
  unfold appG
  rw [Finset.sum_eq_single (fun p => g p (x p))]
  · simp
  · intro y _ hy
    obtain ⟨p, hp⟩ := Function.ne_iff.1 hy
    rw [Finset.prod_eq_zero (Finset.mem_univ p), zero_mul]
    exact if_neg hp
  · intro h
    exact absurd (Finset.mem_univ _) h

/-! ### Restrictions -/

/-- A tensor is a restriction of itself. -/
theorem Restr.refl (t : Ten K I) : Restr t t :=
  ⟨fun _ a b => if b = a then 1 else 0, fun x => by
    rw [app_eq_appG]
    exact ((appG_map (fun p _ => (1 : K)) (fun p a => a) t.val x).trans (by simp)).symm⟩

/-- A restriction of a restriction is a restriction. -/
theorem Restr.trans {s t u : Ten K I} (h : Restr s t) (h' : Restr t u) : Restr s u := by
  obtain ⟨L, hL⟩ := h
  obtain ⟨M, hM⟩ := h'
  refine ⟨fun p a c => ∑ b, L p a b * M p b c, fun x => ?_⟩
  rw [hL, app_eq_appG, app_eq_appG, ← appG_comp]
  congr 1
  funext y
  exact hM y

/-- Products of restrictions. -/
theorem Restr.mul {s t s' t' : Ten K I} (h : Restr s s') (h' : Restr t t') :
    Restr (s * t) (s' * t') := by
  obtain ⟨L, hL⟩ := h
  obtain ⟨M, hM⟩ := h'
  refine ⟨fun p a b => L p a.1 b.1 * M p a.2 b.2, fun x => ?_⟩
  rw [mul_val, hL, hM]
  exact (appG_mul L M s'.val t'.val x).symm

/-- Products of a family of restrictions. -/
theorem Restr.prod {κ : Type} [Fintype κ] [DecidableEq κ] {a b : κ → Ten K I}
    (h : ∀ k, Restr (a k) (b k)) : Restr (Ten.prod a) (Ten.prod b) := by
  choose L hL using h
  refine ⟨fun p x y => ∏ k, L k p (x k) (y k), fun x => ?_⟩
  rw [prod_val]
  exact (Finset.prod_congr rfl fun k _ => hL k _).trans
    (appG_prod (α := fun k p => (a k).ι p) (β := fun k p => (b k).ι p) L
      (fun k => (b k).val) x).symm

/-- Restrictions stay restrictions if the legs are given to other parties. -/
theorem Restr.push (π : J → I) {s t : Ten K J} (h : Restr s t) :
    Restr (push π s) (push π t) := by
  obtain ⟨L, hL⟩ := h
  refine ⟨fun q a b => ∏ j : {j : J // π j = q}, L j.1 (a j) (b j), fun x => ?_⟩
  rw [push_val, hL]
  exact (appG_push π L t.val x).symm

/-- If the entry of s at x is a product of local factors times the entry of t at g(x), where g acts
leg by leg, then s is a restriction of t. -/
theorem Restr.of_map {s t : Ten K I} (w : ∀ p, s.ι p → K) (g : ∀ p, s.ι p → t.ι p)
    (h : ∀ x, s.val x = (∏ p, w p (x p)) * t.val (fun p => g p (x p))) : Restr s t :=
  ⟨fun p a b => if b = g p a then w p a else 0, fun x => by
    rw [h, app_eq_appG]; exact (appG_map w g t.val x).symm⟩

/-- If the entry of s at x is the entry of t at g(x), where g acts leg by leg, then s is a
restriction of t. -/
theorem Restr.of_map' {s t : Ten K I} (g : ∀ p, s.ι p → t.ι p)
    (h : ∀ x, s.val x = t.val (fun p => g p (x p))) : Restr s t :=
  Restr.of_map (fun _ _ => 1) g (by simpa using h)

/-- 1 is a restriction of every tensor with an entry that is not 0, if there is a party. -/
theorem Restr.one_le [Nonempty I] {t : Ten K I} {y : ∀ p, t.ι p} (h : t.val y ≠ 0) :
    Restr 1 t := by
  classical
  let p₀ : I := Classical.arbitrary I
  refine Restr.of_map (fun p _ => if p = p₀ then (t.val y)⁻¹ else 1) (fun p _ => y p) fun x => ?_
  rw [Finset.prod_ite_eq' Finset.univ p₀]
  simp [h]

/-! ### Sums of restrictions -/

section Sum

variable {κ κ' : Type} [Fintype κ] [Fintype κ']

/-- s is a sum of restrictions of the b k if and only if its array is a sum of arrays, the k-th
of which is a restriction of b k. -/
theorem sumRestr_iff {s : Ten K I} {b : κ → Ten K I} :
    SumRestr s b ↔ ∃ v : κ → (∀ p, s.ι p) → K,
      (∀ x, s.val x = ∑ k, v k x) ∧ ∀ k, Restr (s.withVal (v k)) (b k) := by
  constructor
  · rintro ⟨L, hL⟩
    exact ⟨fun k x => appG (L k) (b k).val x, hL, fun k => ⟨L k, fun x => rfl⟩⟩
  · rintro ⟨v, hv, h⟩
    choose L hL using h
    exact ⟨L, fun x => (hv x).trans (Finset.sum_congr rfl fun k _ => hL k x)⟩

/-- If the array of s is the sum of the arrays v k, then s is a sum of restrictions of the tensors
with these arrays. -/
theorem SumRestr.of_withVal (s : Ten K I) (v : κ → (∀ p, s.ι p) → K)
    (h : ∀ x, s.val x = ∑ k, v k x) : SumRestr s (fun k => s.withVal (v k)) :=
  sumRestr_iff.2 ⟨v, h, fun _ => Restr.refl _⟩

/-- A restriction is a sum of restrictions with one term. -/
theorem Restr.sumRestr {s t : Ten K I} (h : Restr s t) : SumRestr s (fun _ : Unit => t) := by
  obtain ⟨L, hL⟩ := h
  exact ⟨fun _ => L, fun x => by simpa using hL x⟩

/-- A tensor whose array is 0 is a sum of restrictions of the empty family. -/
theorem SumRestr.of_zero [IsEmpty κ] {s : Ten K I} (h : ∀ x, s.val x = 0) (b : κ → Ten K I) :
    SumRestr s b :=
  ⟨fun k => isEmptyElim k, fun x => by simp [h]⟩

/-- A sum of restrictions of tensors that are themselves sums of restrictions is a sum of restrictions
(covers are transitive). -/
theorem SumRestr.bind {μ : κ → Type} [∀ k, Fintype (μ k)] {s : Ten K I} {b : κ → Ten K I}
    {c : ∀ k, μ k → Ten K I} (h : SumRestr s b) (h' : ∀ k, SumRestr (b k) (c k)) :
    SumRestr s (fun x : Σ k, μ k => c x.1 x.2) := by
  obtain ⟨L, hL⟩ := h
  choose M hM using h'
  refine ⟨fun x p a d => ∑ b, L x.1 p a b * M x.1 x.2 p b d, fun x => ?_⟩
  rw [hL, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun k _ => ?_
  have e : (b k).val = fun y => ∑ m, appG (M k m) (c k m).val y := funext fun y => hM k y
  rw [app_eq_appG, e, appG_sum]
  exact Finset.sum_congr rfl fun m _ => appG_comp _ _ _ _

/-- A restriction of a sum of restrictions is a sum of restrictions of the same tensors. -/
theorem Restr.trans_sum {s t : Ten K I} {b : κ → Ten K I} (h : Restr s t) (h' : SumRestr t b) :
    SumRestr s b := by
  obtain ⟨L, hL⟩ := h
  obtain ⟨M, hM⟩ := h'
  refine ⟨fun k p a d => ∑ b, L p a b * M k p b d, fun x => ?_⟩
  have e : t.val = fun y => ∑ k, appG (M k) (b k).val y := funext fun y => hM y
  rw [hL, app_eq_appG, e, appG_sum]
  exact Finset.sum_congr rfl fun m _ => appG_comp _ _ _ _

/-- In a sum of restrictions every term may be replaced by a tensor of which it is a restriction. -/
theorem SumRestr.mono {s : Ten K I} {b c : κ → Ten K I} (h : SumRestr s b)
    (h' : ∀ k, Restr (b k) (c k)) : SumRestr s c := by
  obtain ⟨v, hv, h⟩ := sumRestr_iff.1 h
  exact sumRestr_iff.2 ⟨v, hv, fun k => (h k).trans (h' k)⟩

/-- The terms of a sum of restrictions may be renamed. -/
theorem SumRestr.reindex {s : Ten K I} {b : κ → Ten K I} (h : SumRestr s b) (e : κ' ≃ κ) :
    SumRestr s (fun k => b (e k)) := by
  obtain ⟨L, hL⟩ := h
  exact ⟨fun k => L (e k), fun x => (hL x).trans (Fintype.sum_equiv e _ _ fun _ => rfl).symm⟩

/-- The product of two sums of restrictions is a sum of restrictions of the products of two terms. -/
theorem SumRestr.mul {s t : Ten K I} {b : κ → Ten K I} {c : κ' → Ten K I} (h : SumRestr s b)
    (h' : SumRestr t c) : SumRestr (s * t) (fun k : κ × κ' => b k.1 * c k.2) := by
  obtain ⟨L, hL⟩ := h
  obtain ⟨M, hM⟩ := h'
  refine ⟨fun k p x y => L k.1 p x.1 y.1 * M k.2 p x.2 y.2, fun x => ?_⟩
  rw [mul_val, hL, hM, Finset.sum_mul_sum, ← Fintype.sum_prod_type']
  exact Finset.sum_congr rfl fun k _ => (appG_mul (L k.1) (M k.2) (b k.1).val (c k.2).val x).symm

/-- A sum of restrictions stays one if the legs are given to other parties. -/
theorem SumRestr.push (π : J → I) {s : Ten K J} {b : κ → Ten K J} (h : SumRestr s b) :
    SumRestr (push π s) (fun k => Ten.push π (b k)) := by
  obtain ⟨L, hL⟩ := h
  refine ⟨fun k q x y => ∏ j : {j : J // π j = q}, L k j.1 (x j) (y j), fun x => ?_⟩
  rw [push_val, hL]
  exact Finset.sum_congr rfl fun k _ => (appG_push π (L k) (b k).val x).symm

end Sum

end Ten

end Ov
