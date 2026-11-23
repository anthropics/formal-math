/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Ov.Core.Equi

/-!
# Networks

A tensor that is the value of a network is a restriction of the product of the wires on the edges of the
network, wherever its vertices are placed. The paper uses special cases: in Lemma lem:exponents, that ⟨q⟩_uw
is a restriction of ⟨q⟩_uv ⟨q⟩_vw, and the same for trees; and Lemma lem:hubs. The statements are about
functions, not graphs: a vertex v has a table T v, a function of all labels, which is *local*: it depends
only on the labels of the edges at v and on the indices held by the party of v.
-/

set_option linter.unusedSectionVars false

namespace Ov

open Finset

namespace Ten

variable {K : Type} [Field K] {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
variable {V : Type} [Fintype V] [DecidableEq V]

/-- Contraction with one tensor. The legs of t are at vertices (the leg l at ρ l), every vertex v is
placed at the party ξ v and has a local table T v: it depends only on the legs of s that are held by
the party ξ v and on the legs of t at v. If s is the sum over all labels of the legs of t of the
product of the tables and of t, then s is a restriction of t, with the legs at their places. -/
theorem Restr.of_contract {L : Type} [Fintype L] [DecidableEq L] (π : J → I) (ξ : V → I)
    (ρ : L → V) (s : Ten K J) (t : Ten K L) (T : V → (∀ j, s.ι j) → (∀ l, t.ι l) → K)
    (hT : ∀ v x x' y y', (∀ j, π j = ξ v → x j = x' j) → (∀ l, ρ l = v → y l = y' l) →
      T v x y = T v x' y')
    (h : ∀ x, s.val x = ∑ y, (∏ v, T v x y) * t.val y) :
    Restr (Ten.push π s) (Ten.push (fun l => ξ (ρ l)) t) := by
  classical
  rcases isEmpty_or_nonempty (∀ j, s.ι j) with hs | ⟨⟨x₀⟩⟩
  · exact ⟨fun _ _ _ => 0, fun x => (hs.false fun j => x (π j) ⟨j, rfl⟩).elim⟩
  rcases isEmpty_or_nonempty (∀ l, t.ι l) with ht | ⟨⟨y₀⟩⟩
  · refine ⟨fun _ _ _ => 0, fun x => ?_⟩
    rw [push_val, h, Finset.univ_eq_empty, Finset.sum_empty]
    have : IsEmpty (∀ q, (Ten.push (fun l => ξ (ρ l)) t).ι q) :=
      ⟨fun y => ht.false fun l => y (ξ (ρ l)) ⟨l, rfl⟩⟩
    rw [app, Finset.univ_eq_empty, Finset.sum_empty]
  let ex : ∀ q, (∀ j : {j : J // π j = q}, s.ι j.1) → ∀ j, s.ι j :=
    fun q a j => if hj : π j = q then a ⟨j, hj⟩ else x₀ j
  let ey : ∀ q, (∀ l : {l : L // ξ (ρ l) = q}, t.ι l.1) → ∀ l, t.ι l :=
    fun q b l => if hl : ξ (ρ l) = q then b ⟨l, hl⟩ else y₀ l
  refine ⟨fun q a b => ∏ v : {v : V // ξ v = q}, T v.1 (ex q a) (ey q b), fun x => ?_⟩
  rw [push_val, h, app_eq_appG, appG]
  symm
  refine Fintype.sum_equiv (pushEquiv (fun l => ξ (ρ l)) t.ι) _ _ fun y => ?_
  congr 1
  rw [← Fintype.prod_fiberwise ξ]
  refine Finset.prod_congr rfl fun q _ => Finset.prod_congr rfl fun v _ => ?_
  obtain ⟨v, rfl⟩ := v
  refine hT v _ _ _ _ (fun j hj => ?_) (fun l hl => ?_)
  · have : ex (ξ v) (x (ξ v)) j = x (ξ v) ⟨j, hj⟩ := dif_pos hj
    rw [this]
    clear this
    revert hj
    generalize ξ v = q
    rintro rfl
    rfl
  · subst hl
    exact dif_pos rfl

section Outer

variable {κ : Type} [Fintype κ] [DecidableEq κ] {M : κ → Type} [∀ k, Fintype (M k)]
  [∀ k, DecidableEq (M k)]

/-- The product of tensors with separate legs. -/
def outer (t : ∀ k, Ten K (M k)) : Ten K (Σ k, M k) where
  ι l := (t l.1).ι l.2
  val y := ∏ k, (t k).val fun m => y ⟨k, m⟩

theorem outer_val (t : ∀ k, Ten K (M k)) (y : ∀ l, (outer t).ι l) :
    (outer t).val y = ∏ k, (t k).val fun m => y ⟨k, m⟩ := rfl

/-- Giving the legs of a product with separate legs to parties. -/
theorem Equi.push_outer (π : (Σ k, M k) → I) (t : ∀ k, Ten K (M k)) :
    Equi (Ten.push π (outer t)) (Ten.prod fun k => Ten.push (fun m => π ⟨k, m⟩) (t k)) :=
  Equi.of_equiv
    (fun _ => ⟨fun y k j => y ⟨⟨k, j.1⟩, j.2⟩, fun z l => z l.1.1 ⟨l.1.2, l.2⟩,
      fun _ => rfl, fun _ => rfl⟩)
    fun _ => rfl

end Outer

section Two

variable {L L' : Type} [Fintype L] [DecidableEq L] [Fintype L'] [DecidableEq L']

/-- The product of two tensors with separate legs. -/
def outer₂ (s : Ten K L) (t : Ten K L') : Ten K (L ⊕ L') where
  ι l := Sum.elim s.ι t.ι l
  fin l := match l with
    | Sum.inl l => s.fin l
    | Sum.inr l => t.fin l
  dec l := match l with
    | Sum.inl l => s.dec l
    | Sum.inr l => t.dec l
  val y := s.val (fun l => y (Sum.inl l)) * t.val (fun l => y (Sum.inr l))

/-- Giving the legs of a product of two tensors with separate legs to parties. -/
theorem Equi.push_outer₂ (π : L ⊕ L' → I) (s : Ten K L) (t : Ten K L') :
    Equi (Ten.push π (outer₂ s t))
      (Ten.push (fun l => π (Sum.inl l)) s * Ten.push (fun l => π (Sum.inr l)) t) :=
  Equi.of_equiv
    (fun q => ⟨fun y => (fun l => y ⟨Sum.inl l.1, l.2⟩, fun l => y ⟨Sum.inr l.1, l.2⟩),
      fun z l => match l with
        | ⟨Sum.inl l, h⟩ => z.1 ⟨l, h⟩
        | ⟨Sum.inr l, h⟩ => z.2 ⟨l, h⟩,
      fun y => by funext l; obtain ⟨l | l, h⟩ := l <;> rfl, fun z => rfl⟩)
    fun _ => rfl

end Two

/-- A sum over pairs of labels that must be equal. -/
theorem sum_unit_two {E : Type} [Fintype E] [DecidableEq E] (n : E → ℕ)
    (g : (∀ e, Fin 2 → Fin (n e)) → K) :
    ∑ z : ∀ e, Fin 2 → Fin (n e), g z * ∏ e, (unit K (Fin 2) (n e)).val (z e) =
      ∑ l : ∀ e, Fin (n e), g fun e _ => l e := by
  symm
  refine Finset.sum_of_injOn (fun l e _ => l e) (fun l _ l' _ h => ?_) (fun _ _ => by simp)
    (fun z _ hz => ?_) (fun l _ => ?_)
  · funext e
    exact congr_fun (congr_fun h e) 0
  · have : ∃ e, ¬ ∀ i j, z e i = z e j := by
      by_contra hcon
      push Not at hcon
      exact hz ⟨fun e => z e 0, by simp, funext fun e => funext fun i => hcon e 0 i⟩
    obtain ⟨e, he⟩ := this
    rw [Finset.prod_eq_zero (Finset.mem_univ e), mul_zero]
    exact if_neg he
  · rw [Finset.prod_eq_one, mul_one]
    intro e _
    exact if_pos fun _ _ => rfl

/-- **Networks.** The vertices v are placed at the parties ξ v, the legs j of s are held
by the parties π j. There are edges e with labels in Λ e and ends a e, b e, and tensors t k with
their legs m at the vertices ρ k m. Each vertex has a local table T v: it depends only on the legs of
s held by the party ξ v, on the labels of the edges at v, and on the legs of the t k at v. If s is
the sum over all labels of the product of the tables and of the t k, then s is a restriction of the
product of the edges and of the t k, all at their places. -/
theorem Restr.of_network {E κ : Type} [Fintype E] [DecidableEq E] [Fintype κ] [DecidableEq κ]
    {M : κ → Type} [∀ k, Fintype (M k)] [∀ k, DecidableEq (M k)]
    (π : J → I) (ξ : V → I) (s : Ten K J) (Λ : E → Type) [∀ e, Fintype (Λ e)] (a b : E → V)
    (t : ∀ k, Ten K (M k)) (ρ : ∀ k, M k → V)
    (T : V → (∀ j, s.ι j) → (∀ e, Λ e) → (∀ k m, (t k).ι m) → K)
    (hT : ∀ v x x' l l' y y', (∀ j, π j = ξ v → x j = x' j) →
      (∀ e, a e = v ∨ b e = v → l e = l' e) → (∀ k m, ρ k m = v → y k m = y' k m) →
      T v x l y = T v x' l' y')
    (h : ∀ x, s.val x = ∑ l : ∀ e, Λ e, ∑ y : ∀ k m, (t k).ι m,
      (∏ v, T v x l y) * ∏ k, (t k).val (y k)) :
    Restr (Ten.push π s)
      (Ten.prod (fun e => wire K (Fintype.card (Λ e)) (ξ (a e)) (ξ (b e))) *
        Ten.prod (fun k => Ten.push (fun m => ξ (ρ k m)) (t k))) := by
  classical
  let n : E → ℕ := fun e => Fintype.card (Λ e)
  let eq : ∀ e, Fin (n e) ≃ Λ e := fun e => (Fintype.equivFin (Λ e)).symm
  let U : Ten K (Σ _ : E, Fin 2) := outer fun e => unit K (Fin 2) (n e)
  let ρ' : (Σ _ : E, Fin 2) ⊕ (Σ k, M k) → V :=
    Sum.elim (fun l => ![a l.1, b l.1] l.2) (fun l => ρ l.1 l.2)
  let T' : V → (∀ j, s.ι j) → (∀ l, (outer₂ U (outer t)).ι l) → K := fun v x y =>
    T v x (fun e => eq e (if a e = v then y (Sum.inl ⟨e, 0⟩) else y (Sum.inl ⟨e, 1⟩)))
      (fun k m => y (Sum.inr ⟨k, m⟩))
  have key : Restr (Ten.push π s) (Ten.push (fun l => ξ (ρ' l)) (outer₂ U (outer t))) := by
    refine Restr.of_contract π ξ ρ' s (outer₂ U (outer t)) T' (fun v x x' y y' hx hy => ?_)
      fun x => ?_
    · refine hT v _ _ _ _ _ _ hx (fun e he => ?_) fun k m hm => hy (Sum.inr ⟨k, m⟩) hm
      by_cases ha : a e = v
      · simp only [ha]
        exact congr_arg (eq e) (hy (Sum.inl ⟨e, 0⟩) ha)
      · simp only [ha]
        exact congr_arg (eq e) (hy (Sum.inl ⟨e, 1⟩) (he.resolve_left ha))
    · rw [h]
      let Φ : (∀ l, (outer₂ U (outer t)).ι l) ≃
          (∀ e, Fin 2 → Fin (n e)) × (∀ k m, (t k).ι m) :=
        ⟨fun y => (fun e i => y (Sum.inl ⟨e, i⟩), fun k m => y (Sum.inr ⟨k, m⟩)),
          fun z l => match l with
            | Sum.inl l => z.1 l.1 l.2
            | Sum.inr l => z.2 l.1 l.2,
          fun y => by funext l; rcases l with l | l <;> rfl, fun z => rfl⟩
      let g : (∀ e, Fin 2 → Fin (n e)) → (∀ k m, (t k).ι m) → K := fun z y =>
        (∏ v, T v x (fun e => eq e (if a e = v then z e 0 else z e 1)) y) *
          ∏ k, (t k).val (y k)
      have e1 : ∑ y, (∏ v, T' v x y) * (outer₂ U (outer t)).val y =
          ∑ z : (∀ e, Fin 2 → Fin (n e)) × (∀ k m, (t k).ι m),
            g z.1 z.2 * ∏ e, (unit K (Fin 2) (n e)).val (z.1 e) := by
        refine Fintype.sum_equiv Φ _ _ fun y => ?_
        show (∏ v, T' v x y) * ((∏ e, (unit K (Fin 2) (n e)).val ((Φ y).1 e)) *
          ∏ k, (t k).val ((Φ y).2 k)) = (∏ v, T' v x y) * (∏ k, (t k).val ((Φ y).2 k)) *
            ∏ e, (unit K (Fin 2) (n e)).val ((Φ y).1 e)
        ring
      have e2 : ∀ y : ∀ k m, (t k).ι m,
          ∑ z : ∀ e, Fin 2 → Fin (n e), g z y * ∏ e, (unit K (Fin 2) (n e)).val (z e) =
            ∑ l : ∀ e, Λ e, (∏ v, T v x l y) * ∏ k, (t k).val (y k) := by
        intro y
        rw [sum_unit_two n fun z => g z y]
        refine Fintype.sum_equiv (Equiv.piCongrRight eq) _ _ fun l => ?_
        simp only [g, ite_self]
        rfl
      rw [e1, Fintype.sum_prod_type_right, Finset.sum_comm]
      exact Finset.sum_congr rfl fun y _ => (e2 y).symm
  refine key.trans ((Equi.push_outer₂ _ U (outer t)).1.trans (Restr.mul ?_ ?_))
  · refine (Equi.push_outer (fun l : Σ _ : E, Fin 2 => ξ (ρ' (Sum.inl l))) _).1.trans
      (Restr.prod fun e => ?_)
    have : (fun m => ξ (ρ' (Sum.inl ⟨e, m⟩))) = ![ξ (a e), ξ (b e)] := by
      funext m
      fin_cases m <;> rfl
    rw [this]
    exact Restr.refl _
  · exact (Equi.push_outer (fun l : Σ k, M k => ξ (ρ' (Sum.inr l))) t).1

/-- Networks without other tensors: if s is the sum over all labels of the edges of the product of
local tables, then s is a restriction of the product of the wires on the edges, at their places. -/
theorem Restr.of_edges {E : Type} [Fintype E] [DecidableEq E]
    (π : J → I) (ξ : V → I) (s : Ten K J) (Λ : E → Type) [∀ e, Fintype (Λ e)] (a b : E → V)
    (T : V → (∀ j, s.ι j) → (∀ e, Λ e) → K)
    (hT : ∀ v x x' l l', (∀ j, π j = ξ v → x j = x' j) →
      (∀ e, a e = v ∨ b e = v → l e = l' e) → T v x l = T v x' l')
    (h : ∀ x, s.val x = ∑ l : ∀ e, Λ e, ∏ v, T v x l) :
    Restr (Ten.push π s) (Ten.prod fun e => wire K (Fintype.card (Λ e)) (ξ (a e)) (ξ (b e))) := by
  have := Restr.of_network (κ := Empty) (M := fun _ => Empty) π ξ s Λ a b
    (fun k => k.elim) (fun k => k.elim) (fun v x l _ => T v x l)
    (fun v x x' l l' _ _ hx hl _ => hT v x x' l l' hx hl)
    (fun x => by rw [h]; refine Finset.sum_congr rfl fun l _ => ?_
                 rw [Fintype.sum_unique]; simp)
  exact this.trans (((Equi.refl _).mul (Equi.prod_empty _)).trans (Equi.mul_one _)).1

end Ten

end Ov
