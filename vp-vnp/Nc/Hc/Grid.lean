/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Hc.Segments
import Nc.WidePerm

/-!
# Grid completeness of the permanent and of the Hamiltonian cycle polynomial

A sum over two families of bits of products of weights, one for every incidence, is a Hamiltonian cycle polynomial
with affine entries, in every characteristic. For every incidence there are seven segments and ten gadgets.
-/

namespace Nc

open Finset MvPolynomial

namespace Hc

/-- The segments of a grid: one for every bit of the two families; for every incidence the one that chooses the
weight, one for each of the two sides and one for each of the four pairs of bits; and some for padding. -/
inductive Seg (N V K P : Type) where
  | var (a : V)
  | row (b : K)
  | edge (n : N)
  | left (n : N)
  | right (n : N)
  | tab (n : N) (t : Bool × Bool)
  | pad (p : P)
  deriving DecidableEq

variable {N V K P : Type}

/-- The segments as a disjoint union. -/
def Seg.equivSum : Seg N V K P ≃ V ⊕ K ⊕ N ⊕ N ⊕ N ⊕ (N × Bool × Bool) ⊕ P where
  toFun
    | .var a => .inl a
    | .row b => .inr (.inl b)
    | .edge n => .inr (.inr (.inl n))
    | .left n => .inr (.inr (.inr (.inl n)))
    | .right n => .inr (.inr (.inr (.inr (.inl n))))
    | .tab n t => .inr (.inr (.inr (.inr (.inr (.inl (n, t))))))
    | .pad p => .inr (.inr (.inr (.inr (.inr (.inr p)))))
  invFun
    | .inl a => .var a
    | .inr (.inl b) => .row b
    | .inr (.inr (.inl n)) => .edge n
    | .inr (.inr (.inr (.inl n))) => .left n
    | .inr (.inr (.inr (.inr (.inl n)))) => .right n
    | .inr (.inr (.inr (.inr (.inr (.inl (n, t)))))) => .tab n t
    | .inr (.inr (.inr (.inr (.inr (.inr p))))) => .pad p
  left_inv := by rintro (_ | _ | _ | _ | _ | _ | _) <;> rfl
  right_inv := by rintro (_ | _ | _ | _ | _ | _ | _) <;> rfl

instance [Fintype N] [Fintype V] [Fintype K] [Fintype P] : Fintype (Seg N V K P) :=
  Fintype.ofEquiv _ Seg.equivSum.symm

/-- The options of a segment. -/
abbrev Opt : Seg N V K P → Type
  | .var _ => Bool
  | .row _ => Bool
  | .edge _ => Bool × Bool
  | .left _ => Option Bool
  | .right _ => Option Bool
  | .tab _ _ => Bool
  | .pad _ => Unit

instance (i : Seg N V K P) : Fintype (Opt i) := by cases i <;> infer_instance

instance (i : Seg N V K P) : DecidableEq (Opt i) := by cases i <;> infer_instance

/-- The ten gadgets of an incidence. -/
abbrev Gad (N : Type) : Type := N × ((Bool × Bool) ⊕ Option Bool ⊕ Option Bool)

/-- The two options of every gadget. -/
def gridPort (v : N → V) (w : N → K) : Gad N × Bool → Σ i : Seg N V K P, Opt i
  | ((n, .inl t), true) => ⟨.edge n, t⟩
  | ((n, .inl t), false) => ⟨.tab n t, false⟩
  | ((n, .inr (.inl o)), true) => ⟨.left n, o⟩
  | ((n, .inr (.inl (some b))), false) => ⟨.tab n (true, b), false⟩
  | ((n, .inr (.inl none)), false) => ⟨.var (v n), true⟩
  | ((n, .inr (.inr o)), true) => ⟨.right n, o⟩
  | ((n, .inr (.inr (some b))), false) => ⟨.tab n (b, true), false⟩
  | ((n, .inr (.inr none)), false) => ⟨.row (w n), true⟩

/-- The row of segments of a grid. -/
def gridRow (v : N → V) (w : N → K) (next : Equiv.Perm (Seg N V K P)) :
    Row (Opt (N := N) (V := V) (K := K) (P := P)) (Gad N) where
  next := next
  port := gridPort v w

/-- The selection that belongs to two families of bits. -/
def choice (v : N → V) (w : N → K) (x : V → Bool) (r : K → Bool) : ∀ i : Seg N V K P, Opt i
  | .var a => x a
  | .row b => r b
  | .edge n => (x (v n), r (w n))
  | .left n => if x (v n) then some (r (w n)) else none
  | .right n => if r (w n) then some (x (v n)) else none
  | .tab n t => decide (t = (x (v n), r (w n)))
  | .pad _ => ()

/-- The weights of the options: only the choices at the incidences carry one. -/
def gridWeight {R : Type*} [One R] (W : N → Bool → Bool → R) : ∀ i : Seg N V K P, Opt i → R
  | .edge n, t => W n t.1 t.2
  | _, _ => 1

variable {v : N → V} {w : N → K} {next : Equiv.Perm (Seg N V K P)}

/-- The three kinds of gadgets at one incidence. -/
theorem choice_cases : (∀ (t : Bool × Bool) (a c : Bool), (a, c) = t ↔ ¬decide (t = (a, c)) = false) ∧
    (∀ a c : Bool, (if a then some c else none) = none ↔ ¬a = true) ∧
    (∀ a c b : Bool, (if a then some c else none) = some b ↔ ¬decide ((true, b) = (a, c)) = false) ∧
    ∀ a c b : Bool, (if a then some c else none) = some b ↔ ¬decide ((b, true) = (c, a)) = false := by
  decide

/-- The selection of two families of bits uses every gadget exactly once. -/
theorem valid_choice (x : V → Bool) (r : K → Bool) : (gridRow v w next).Valid (choice v w x r) := by
  obtain ⟨h1, h2, h3, h4⟩ := choice_cases
  rintro ⟨n, t | (_ | b) | (_ | b)⟩
  exacts [h1 t _ _, h2 _ _, h3 _ _ b, h2 _ _, h4 _ _ b]

/-- The pair chosen at an incidence is the pair of the bits of its two ends. -/
theorem incidence_cases : ∀ (e : Bool × Bool) (l h : Option Bool) (a c : Bool),
    (∀ b, l = some b ↔ e = (true, b)) → (l = none ↔ a = false) →
    (∀ b, h = some b ↔ e = (b, true)) → (h = none ↔ c = false) →
      e = (a, c) ∧ l = (if a then some c else none) ∧ h = (if c then some a else none) := by
  decide

/-- The selections that use every gadget exactly once are those of the
pairs of families of bits. -/
theorem eq_choice_of_valid {J : ∀ i : Seg N V K P, Opt i} (h : (gridRow v w next).Valid J) :
    J = choice v w (fun a => J (.var a)) (fun b => J (.row b)) := by
  have key : ∀ n, J (.edge n) = (J (.var (v n)), J (.row (w n))) ∧
      J (.left n) = (if J (.var (v n)) then some (J (.row (w n))) else none) ∧
      J (.right n) = (if J (.row (w n)) then some (J (.var (v n))) else none) ∧
      ∀ t, J (.tab n t) = decide (t = J (.edge n)) := by
    intro n
    have ht : ∀ t, J (.edge n) = t ↔ ¬ J (.tab n t) = false := fun t => h (n, .inl t)
    have hl : ∀ b, J (.left n) = some b ↔ ¬ J (.tab n (true, b)) = false := fun b => h (n, .inr (.inl (some b)))
    have hr : ∀ b, J (.right n) = some b ↔ ¬ J (.tab n (b, true)) = false := fun b => h (n, .inr (.inr (some b)))
    have hl0 : J (.left n) = none ↔ ¬ J (.var (v n)) = true := h (n, .inr (.inl none))
    have hr0 : J (.right n) = none ↔ ¬ J (.row (w n)) = true := h (n, .inr (.inr none))
    obtain ⟨he, h1, h2⟩ := incidence_cases _ _ _ _ _ (fun b => (hl b).trans (ht _).symm)
      (hl0.trans Bool.eq_false_iff.symm) (fun b => (hr b).trans (ht _).symm) (hr0.trans Bool.eq_false_iff.symm)
    refine ⟨he, h1, h2, fun t => ?_⟩
    rw [Bool.eq_iff_iff, decide_eq_true_iff, eq_comm (a := t), ht t, Bool.not_eq_false]
  funext i
  rcases i with a | b | n | n | n | ⟨n, t⟩ | p
  · rfl
  · rfl
  · exact (key n).1
  · exact (key n).2.1
  · exact (key n).2.2.1
  · exact ((key n).2.2.2 t).trans (by rw [(key n).1]; rfl)
  · rfl

/-- Every option of a grid, except at most one in its segment, runs through a gadget. -/
theorem gridRow_noParallel (hv : Function.Surjective v) (hw : Function.Surjective w) :
    (gridRow v w next).NoParallel := by
  intro i o o' h h'
  rcases i with a | b | n | n | n | ⟨n, t⟩ | p
  · obtain ⟨n, rfl⟩ := hv a
    cases o <;> cases o' <;> first | rfl | exact absurd rfl (h ((n, .inr (.inl none)), false)) |
      exact absurd rfl (h' ((n, .inr (.inl none)), false))
  · obtain ⟨n, rfl⟩ := hw b
    cases o <;> cases o' <;> first | rfl | exact absurd rfl (h ((n, .inr (.inr none)), false)) |
      exact absurd rfl (h' ((n, .inr (.inr none)), false))
  · exact absurd rfl (h ((n, .inl o), true))
  · exact absurd rfl (h ((n, .inr (.inl o)), true))
  · exact absurd rfl (h ((n, .inr (.inr o)), true))
  · cases o <;> cases o' <;> first | rfl | exact absurd rfl (h ((n, .inl t), false)) |
      exact absurd rfl (h' ((n, .inl t), false))
  · rfl

variable [Fintype N] [DecidableEq N] [Fintype V] [DecidableEq V] [Fintype K] [DecidableEq K]
  [Fintype P] [DecidableEq P]

/-- Over every commutative semiring, a sum over two families of bits of
products of weights, one for every incidence, is the sum over the cycles through all vertices of the grid graph. -/
theorem hcSum_grid {R : Type*} [CommSemiring R] (hv : Function.Surjective v) (hw : Function.Surjective w)
    (hnext : next.IsCycleOn Set.univ) (W : N → Bool → Bool → R) :
    hcSum ((gridRow v w next).weight (gridWeight W)) =
      ∑ x : V → Bool, ∑ r : K → Bool, ∏ n, W n (x (v n)) (r (w n)) := by
  classical
  rw [Row.hcSum_weight (T := gridRow v w next) hnext (gridRow_noParallel hv hw), ← Fintype.sum_prod_type']
  symm
  refine Finset.sum_bij' (fun p _ => choice v w p.1 p.2) (fun J _ => (fun a => J (.var a), fun b => J (.row b)))
    (fun p _ => mem_filter.2 ⟨mem_univ _, valid_choice _ _⟩) (fun _ _ => mem_univ _) (fun _ _ => rfl)
    (fun J hJ => (eq_choice_of_valid (mem_filter.1 hJ).2).symm) fun p _ => ?_
  refine Fintype.prod_of_injective Seg.edge (fun a b h => Seg.edge.inj h) _ _ (fun i hi => ?_) fun n => rfl
  rcases i with _ | _ | n | _ | _ | _ | _ <;> first | rfl | exact absurd ⟨n, rfl⟩ hi

omit [DecidableEq N] [DecidableEq V] [DecidableEq K] [DecidableEq P] in
/-- The number of vertices of a grid. -/
theorem card_gridVtx :
    Fintype.card (Vtx (Seg N V K P) (Gad N)) =
      Fintype.card V + Fintype.card K + 37 * Fintype.card N + Fintype.card P := by
  rw [Vtx.card_eq, Fintype.card_congr (Seg.equivSum (N := N) (V := V) (K := K) (P := P))]
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_bool, Fintype.card_option]
  ring

/-- Renaming the points does not change the sum over the cycles. -/
theorem hcSum_equiv {R : Type*} [CommSemiring R] {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B]
    [DecidableEq B] (e : A ≃ B) (M : B → B → R) : hcSum (fun a a' => M (e a) (e a')) = hcSum M := by
  classical
  unfold hcSum
  refine Finset.sum_equiv e.permCongr (fun σ => ?_) fun σ _ => ?_
  · simp only [mem_filter, mem_univ, true_and]
    have hz : ∀ (m : ℤ) a, (e.permCongr σ ^ m) (e a) = e ((σ ^ m) a) := by
      intro m a
      have h : e.permCongr σ ^ m = e.permCongr (σ ^ m) := (map_zpow e.permCongrHom σ m).symm
      rw [h, Equiv.permCongr_apply, Equiv.symm_apply_apply]
    constructor
    · refine fun h => ⟨Set.bijOn_univ.2 (Equiv.bijective _), fun a _ b _ => ?_⟩
      obtain ⟨m, hm⟩ := h.2 (Set.mem_univ (e.symm a)) (Set.mem_univ (e.symm b))
      refine ⟨m, ?_⟩
      have := hz m (e.symm a)
      rwa [hm, Equiv.apply_symm_apply, Equiv.apply_symm_apply] at this
    · refine fun h => ⟨Set.bijOn_univ.2 (Equiv.bijective _), fun a _ b _ => ?_⟩
      obtain ⟨m, hm⟩ := h.2 (Set.mem_univ (e a)) (Set.mem_univ (e b))
      exact ⟨m, e.injective ((hz m a).symm.trans hm)⟩
  · exact Fintype.prod_equiv e _ _ fun a => by rw [Equiv.permCongr_apply, Equiv.symm_apply_apply]

/-- Substitution in the Hamiltonian cycle polynomial gives the sum over the cycles. -/
theorem aeval_genHC {F A : Type} [Field F] {m : ℕ} (M : Fin m × Fin m → MvPolynomial A F) :
    aeval M (genHC F m) = hcSum fun i j => M (i, j) := by
  classical
  unfold genHC hcSum
  simp only [map_sum, map_prod, aeval_X]

end Hc

end Nc
