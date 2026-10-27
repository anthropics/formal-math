/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import GraphProblems.Interfaces
import SparsifyWidthK.Thresholds

/-! # Corollary 7: the tree that shortens the long clauses of Dominating Set

The formula of Dominating Set has one clause of positive literals for every vertex, and its width is
not bounded. The tree of `stepD w` branches on a clause C with more than w literals, with H its
first w variables: in the light child C is replaced by H, in the heavy child the variables of H are
false and are deleted from all open clauses. This file proves `StShortens`:

* an assignment that satisfies a node satisfies exactly one of its two children, the light one if it
  makes a variable of H true (`sat_light`, `sat_heavy`, `cntS_step`), so the numbers of the
  leaves add up to the number of the root (`sum_leaves`);
* a light step removes an open clause, of which there are n at the root, and a heavy step removes w
  variables from the open clauses, in which at most n variables occur; so a path has at most n light
  steps and at
  most n/w heavy steps (the invariant `Inv`, `inv_root`, `inv_step`);
* so the tree has at most Σ_{j ≤ n/w} C(Ln, j) leaves for every L ≥ 2, which is at most 2^{εn} for a
  suitable w (from `proof/sparsification/SparsifyWidthK/Thresholds.lean`). -/

namespace GraphProblems.DomTree

open Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat Finset

/-! ### Which assignments satisfy a node -/

variable {n : ℕ} {a : Fin n → Bool}

/-- The assignment a makes a variable of the list D true. -/
def Hit (a : Fin n → Bool) (D : List ℕ) : Prop := ∃ u ∈ D, ext a u = true

/-- The assignment a makes a literal of every clause of ψ true. -/
def Sat (a : Fin n → Bool) (ψ : Fml) : Prop := ∀ C ∈ ψ, ∃ l ∈ C, ext a l.1 = l.2

theorem sat_append {ψ φ : Fml} : Sat a (ψ ++ φ) ↔ Sat a ψ ∧ Sat a φ := List.forall_mem_append

theorem sat_cons {C : List (ℕ × Bool)} {ψ : Fml} : Sat a (C :: ψ) ↔ (∃ l ∈ C, ext a l.1 = l.2) ∧ Sat a ψ := List.forall_mem_cons

theorem posC_iff {D : List ℕ} : (∃ l ∈ posC D, ext a l.1 = l.2) ↔ Hit a D := by
  simp [posC, Hit]

theorem sat_map_posC {O : List (List ℕ)} : Sat a (O.map posC) ↔ ∀ D ∈ O, Hit a D := by
  simp only [Sat, List.forall_mem_map, posC_iff]

theorem sat_units {H : List ℕ} : Sat a (H.map fun u => [(u, false)]) ↔ ¬Hit a H := by
  simp [Sat, Hit]

/-- The light child: the node, and a variable of H is true. -/
theorem sat_light {O : List (List ℕ)} {F : Fml} {C : List ℕ} (w : ℕ) :
    Sat a ((O.filter fun D => D != C).map posC ++ (posC (C.take w) :: F)) ↔ Sat a (O.map posC ++ F) ∧ Hit a (C.take w) := by
  rw [sat_append, sat_cons, sat_append, sat_map_posC, sat_map_posC, posC_iff]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨⟨fun D hD => ?_, h3⟩, h2⟩
    by_cases hDC : D = C
    · subst hDC
      obtain ⟨u, hu, hv⟩ := h2
      exact ⟨u, List.mem_of_mem_take hu, hv⟩
    · exact h1 D (List.mem_filter.2 ⟨hD, by simpa using hDC⟩)
  · rintro ⟨⟨h1, h3⟩, h2⟩
    exact ⟨fun D hD => h1 D (List.mem_of_mem_filter hD), h2, h3⟩

/-- The heavy child: the node, and no variable of H is true. -/
theorem sat_heavy {O : List (List ℕ)} {F : Fml} {H : List ℕ} :
    Sat a ((O.map fun D => D.filter fun u => !H.contains u).map posC ++ ((H.map fun u => [(u, false)]) ++ F)) ↔
      Sat a (O.map posC ++ F) ∧ ¬Hit a H := by
  rw [sat_append, sat_append, sat_append, sat_map_posC, sat_map_posC, sat_units]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨⟨fun D hD => ?_, h3⟩, h2⟩
    obtain ⟨u, hu, hv⟩ := h1 _ (List.mem_map_of_mem hD)
    exact ⟨u, List.mem_of_mem_filter hu, hv⟩
  · rintro ⟨⟨h1, h3⟩, h2⟩
    refine ⟨fun D' hD' => ?_, h2, h3⟩
    obtain ⟨D, hD, rfl⟩ := List.mem_map.1 hD'
    obtain ⟨u, hu, hv⟩ := h1 D hD
    refine ⟨u, List.mem_filter.2 ⟨hu, ?_⟩, hv⟩
    have : u ∉ H := fun hH => h2 ⟨u, hH, hv⟩
    simpa using this

/-! ### The two children of a node -/

/-- What `stepD` returns. -/
theorem stepD_some {w : ℕ} {x l h : DNode} (e : stepD w x = some (l, h)) :
    ∃ C ∈ x.2.1, w < C.length ∧
      l = (x.1, (x.2.1.filter fun D => D != C, posC (C.take w) :: x.2.2)) ∧
      h = (x.1, (x.2.1.map fun D => D.filter fun u => !(C.take w).contains u, ((C.take w).map fun u => [(u, false)]) ++ x.2.2)) := by
  unfold stepD at e
  obtain ⟨C, hC, e'⟩ := Option.map_eq_some_iff.1 e
  have h1 := List.find?_some hC
  have h2 := List.mem_of_find?_eq_some hC
  rw [Prod.mk.injEq] at e'
  exact ⟨C, h2, by simpa using h1, e'.1.symm, e'.2.symm⟩

/-- A set that is cut in two by a property Q. -/
theorem card_filter_split {α : Type} [Fintype α] (P Pl Ph Q : α → Prop) [DecidablePred P] [DecidablePred Pl] [DecidablePred Ph]
    (hl : ∀ a, Pl a ↔ P a ∧ Q a) (hh : ∀ a, Ph a ↔ P a ∧ ¬Q a) :
    #(univ.filter P) = #(univ.filter Pl) + #(univ.filter Ph) := by
  classical
  rw [← card_filter_add_card_filter_not (s := univ.filter P) Q, filter_filter, filter_filter]
  congr 1 <;> exact congrArg _ (filter_congr fun a _ => by simp [hl, hh])

/-- The number of a node is the sum of the numbers of its two children. -/
theorem cntS_step {w : ℕ} {x l h : DNode} (e : stepD w x = some (l, h)) (n s : ℕ) :
    cntS n s (leafD x).2.2 = cntS n s (leafD l).2.2 + cntS n s (leafD h).2.2 := by
  obtain ⟨C, -, -, rfl, rfl⟩ := stepD_some e
  unfold cntS
  refine card_filter_split _ _ _ (fun a => Hit a (C.take w)) (fun a => ?_) (fun a => ?_)
  · have := sat_light (a := a) (O := x.2.1) (F := x.2.2) (C := C) w
    unfold Sat at this
    simp only [leafD]
    tauto
  · have := sat_heavy (a := a) (O := x.2.1) (F := x.2.2) (H := C.take w)
    unfold Sat at this
    simp only [leafD]
    tauto

/-- A number that is the sum of the numbers of the two children is the sum of the numbers of the
leaves. -/
theorem sum_leaves {σ : Type} (step : σ → Option (σ × σ)) (f : σ → ℕ) (hf : ∀ s l h, step s = some (l, h) → f s = f l + f h)
    (k : ℕ) (s : σ) : f s = ((leaves step k s).map f).sum := by
  induction k generalizing s with
  | zero => simp [leaves]
  | succ k ih =>
    rw [leaves]
    split
    · simp
    · rename_i l h h0
      rw [hf s l h h0, ih l, ih h, List.map_append, List.sum_append]

/-! ### The invariant -/

/-- The node x lies at depth p of the tree and t variables have been set to false; a counts the
light steps, so that p ≤ a + t, and V holds the variables that may still occur in the open clauses. -/
def Inv (n s w : ℕ) (x : DNode) (p t : ℕ) : Prop :=
  x.1 = (List.replicate n (), s) ∧ ∃ (a : ℕ) (V : Finset ℕ), a + x.2.1.length ≤ n ∧ p ≤ a + t ∧ t + #V ≤ n ∧ (∀ u ∈ V, u < n) ∧
    (∀ D ∈ x.2.1, D.Nodup ∧ ∀ u ∈ D, u ∈ V) ∧ x.2.2.length ≤ a + t ∧ Shaped w n x.2.2

theorem inv_bound {n s w : ℕ} (x : DNode) (p t : ℕ) (h : Inv n s w x p t) : p ≤ 2 * n ∧ t ≤ n := by
  obtain ⟨-, a, V, h1, h2, h3, -⟩ := h
  omega

theorem inv_root (n s w : ℕ) (m : List Bool) : Inv n s w (rootD (List.replicate n (), s, m)) 0 0 := by
  refine ⟨rfl, 0, range n, by simp [rootD, nbhd], le_rfl, by simp, fun u hu => mem_range.1 hu, ?_, by simp [rootD], by simp [rootD, Shaped]⟩
  intro D hD
  simp only [rootD, nbhd, List.length_replicate, List.mem_map, List.mem_range] at hD
  obtain ⟨v, hv, rfl⟩ := hD
  refine ⟨List.nodup_cons.2 ⟨by simp, List.nodup_range.filter _⟩, fun u hu => ?_⟩
  rcases List.mem_cons.1 hu with rfl | hu
  · exact mem_range.2 hv
  · exact mem_range.2 (List.mem_range.1 (List.mem_of_mem_filter hu))

theorem inv_step {n s w : ℕ} (hw : 1 ≤ w) (x : DNode) (p t : ℕ) (l h : DNode) (hG : Inv n s w x p t) (e : stepD w x = some (l, h)) :
    Inv n s w l (p + 1) t ∧ Inv n s w h (p + 1) (t + w) := by
  obtain ⟨C, hC, hwC, rfl, rfl⟩ := stepD_some e
  obtain ⟨hx, a, V, h1, h2, h3, h4, h5, h6, h7⟩ := hG
  have hlen : (C.take w).length = w := by rw [List.length_take]; omega
  have hHV : ∀ u ∈ C.take w, u ∈ V := fun u hu => (h5 C hC).2 u (List.mem_of_mem_take hu)
  constructor
  · refine ⟨hx, a + 1, V, ?_, by omega, h3, h4, fun D hD => h5 D (List.mem_of_mem_filter hD), by simp only [List.length_cons]; omega, ?_⟩
    · have : (x.2.1.filter fun D => D != C).length < x.2.1.length :=
        List.length_filter_lt_length_iff_exists.2 ⟨C, hC, by simp⟩
      simp only
      omega
    · intro B hB
      rcases List.mem_cons.1 hB with rfl | hB
      · refine ⟨by simp [posC], fun q hq => ?_⟩
        obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hq
        exact h4 u (hHV u hu)
      · exact h7 B hB
  · refine ⟨hx, a, V \ (C.take w).toFinset, by simpa using h1, by omega, ?_, fun u hu => h4 u (mem_sdiff.1 hu).1, ?_, ?_, ?_⟩
    · have hsub : (C.take w).toFinset ⊆ V := fun u hu => hHV u (List.mem_toFinset.1 hu)
      have hc := card_sdiff_add_card_eq_card hsub
      have hn : #(C.take w).toFinset = w := by
        rw [List.toFinset_card_of_nodup ((h5 C hC).1.sublist (List.take_sublist w C)), hlen]
      omega
    · intro D' hD'
      obtain ⟨D, hD, rfl⟩ := List.mem_map.1 hD'
      refine ⟨(h5 D hD).1.filter _, fun u hu => ?_⟩
      obtain ⟨hu1, hu2⟩ := List.mem_filter.1 hu
      exact mem_sdiff.2 ⟨(h5 D hD).2 u hu1, by simpa using hu2⟩
    · simp only [List.length_append, List.length_map, hlen]
      omega
    · intro B hB
      rcases List.mem_append.1 hB with hB | hB
      · obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hB
        exact ⟨by simpa using hw, fun q hq => by
          obtain rfl : q = (u, false) := by simpa using hq
          exact h4 u (hHV u hu)⟩
      · exact h7 B hB

/-- What the invariant says on the size of a node. -/
theorem inv_size {n s w : ℕ} {x : DNode} {p t : ℕ} (h : Inv n s w x p t) :
    x.1 = (List.replicate n (), s) ∧ x.2.1.length ≤ n ∧ (∀ D ∈ x.2.1, D.length ≤ n ∧ ∀ u ∈ D, u < n) ∧ x.2.2.length ≤ 2 * n ∧
      Shaped w n x.2.2 ∧ x.2.1.length + x.2.2.length ≤ 3 * n := by
  obtain ⟨hx, a, V, h1, h2, h3, h4, h5, h6, h7⟩ := h
  refine ⟨hx, by omega, fun D hD => ⟨?_, fun u hu => h4 u ((h5 D hD).2 u hu)⟩, by omega, h7, by omega⟩
  have hc : #D.toFinset ≤ #V := card_le_card fun u hu => (h5 D hD).2 u (List.mem_toFinset.1 hu)
  rw [List.toFinset_card_of_nodup (h5 D hD).1] at hc
  omega

end GraphProblems.DomTree

namespace GraphProblems

open Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat Finset DomTree

/-- For every ε > 0 some width w ≥ 1 works. -/
public theorem stShortens : StShortens := by
  intro ε hε
  obtain ⟨w, -, hw4, hw⟩ := WidthK.Thresholds.exists_tau 1 0 hε
  have hw1 : 1 ≤ w := by omega
  refine ⟨w, hw1, fun n s m => ?_⟩
  set L : ℕ := WidthK.bsum w 1 with hL
  have hL2 : 2 ≤ L := WidthK.Thresholds.two_le_bsum w 1
  have hb : ∀ x p t, Inv n s w x p t → p ≤ 2 * n ∧ t ≤ n := inv_bound
  have hs : ∀ x p t l h, Inv n s w x p t → stepD w x = some (l, h) → Inv n s w l (p + 1) t ∧ Inv n s w h (p + 1) (t + w) :=
    inv_step hw1
  have h0 := inv_root n s w m
  refine ⟨?_, fun x hx => ?_, ?_, fun i => ?_⟩
  · have h1 := length_leaves_le hb hs (2 * n) (L * n) (1 * n / w) _ 0 0 h0 (by nlinarith)
      (by have := Nat.lt_mul_div_succ n (show 0 < w by omega); rw [Nat.mul_comm] at this; simpa using this)
    have h2 := WidthK.Thresholds.sum_choose_le_two_rpow hw1 (show 1 ≤ L by omega) (by simpa using hw) n
    exact le_trans (by exact_mod_cast h1) h2
  · have hn := step_eq_none_of_mem_leaves hb hs (2 * n) _ 0 0 h0 (by omega) x hx
    obtain ⟨p', t', hG⟩ := exists_of_mem_leaves hs (2 * n) _ 0 0 h0 x hx
    obtain ⟨g1, g2, g3, g4, g5, g6⟩ := inv_size hG
    refine ⟨hn, g1, ?_, by simpa [leafD] using g6⟩
    have hshort : ∀ D ∈ x.2.1, D.length ≤ w := by
      unfold stepD at hn
      have := List.find?_eq_none.1 (Option.map_eq_none_iff.1 hn)
      intro D hD
      simpa using this D hD
    intro B hB
    rcases List.mem_append.1 hB with hB | hB
    · obtain ⟨D, hD, rfl⟩ := List.mem_map.1 hB
      refine ⟨by simpa [posC] using hshort D hD, fun q hq => ?_⟩
      obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hq
      exact (g3 D hD).2 u hu
    · exact g5 B hB
  · have h1 := sum_leaves (stepD w) (fun x => cntS n s (leafD x).2.2) (fun x l h e => cntS_step e n s) (2 * n)
      (rootD (List.replicate n (), s, m))
    rw [← h1]
    simp [leafD, rootD, domF]
  · obtain ⟨h1, h2⟩ := stack_bound hb hs _ 0 0 h0 i
    refine ⟨h1, fun x hx => ?_⟩
    obtain ⟨p', t', hG⟩ := h2 x hx
    obtain ⟨g1, g2, g3, g4, g5, -⟩ := inv_size hG
    exact ⟨g1, g2, g3, g4, g5⟩

end GraphProblems
