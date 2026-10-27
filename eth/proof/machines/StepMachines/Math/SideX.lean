/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import StepMachines.Math.SideNet

/-! The weights and the factors of the network `sideN`, in explicit form: what the procedures have
to compute. `sideN` is
the network of one term Z_ι of the expansion in the proof of Proposition 3 (Section 5), with all
rows or all columns (the parts) merged, that is, the row or the column network there; its states and
labels are words of bits. -/

@[expose] public section

namespace Groundwork.Grid

open Finset

/-- The weight of the part a at a state z: the product of the tensor entries of its g nodes (0
unless the slot of a node
for itself is all zeros), times the tests that the two ends of every edge inside a agree. -/
theorem sideN_W (g : ℕ) (tr : Bool) (n : ℕ) (Rm : Inst (Fin (g * g)) (List Bool)) (y : ℕ) (a : Fin g) {z : List Bool}
    (hz : z.length = g ^ 3 * n) :
    (sideN g tr n Rm y).W a z =
      (∏ i : Fin g, if (he g n z i (node g tr a i)).all (!·) = true then
          Rm ((gridE g tr).symm (a, i)) (fun u => if u = (gridE g tr).symm (a, i) then [] else he g n z i u)
        else 0) *
      ∏ q ∈ pairs (Fin g), if he g n z q.1 (node g tr a q.2) = he g n z q.2 (node g tr a q.1) then 1 else 0 := by
  have hn : ∀ i : Fin g, node g tr a i < g * g := fun i => node_lt tr a.2 i.2
  change rowW (sideR g tr n Rm) a ((stC g tr n).dec z) = _
  unfold rowW
  congr 1
  · refine prod_congr rfl fun i _ => ?_
    have h := sideR_nodeC g tr n Rm (a, i) (wn := block (g * g * n) i z) (length_block (by
      rw [hz, show g ^ 3 * n = g * (g * g * n) by ring]
      exact Nat.mul_le_mul_right _ i.2))
    rw [gridE_symm_val] at h
    exact h
  · refine prod_congr rfl fun q _ => if_congr ?_ rfl rfl
    rw [stC_dec, stC_dec]
    exact bitsOf_inj (length_he hz q.1.2 (hn q.2)) (length_he hz q.2.2 (hn q.1))

/-- The chunk of the rectangle number κ in the label θ of the parts a, b; the first g * n bits of θ
belong to the g edges
between nodes of equal number. -/
def sideChunk (g : ℕ) (tr : Bool) (n y a b : ℕ) (θ : List Bool) (κ : ℕ) : List Bool :=
  chunkAt (rectLen g tr n y (tri (min a b) (max a b))) κ (θ.drop (g * n))

/-- The factor of the rectangle on the nodes number i < i' of the parts a, b, on the side of a: z is
the state of a and
θ the label. -/
def sideItem (g : ℕ) (tr : Bool) (n y a b : ℕ) (z θ : List Bool) (i i' : ℕ) : ℤ :=
  cutW tr (decide (a < b)) (rectDig g tr n y (tri (min a b) (max a b)) (tri i i'))
    (he g n z i (node g tr b i')) (he g n z i' (node g tr b i)) (sideChunk g tr n y a b θ (tri i i'))

section core

variable {g n : ℕ}

theorem block_take (m : ℕ) {i r : ℕ} (hi : i < r) (θ : List Bool) : block m i (θ.take (r * m)) = block m i θ := by
  have h : (i + 1) * m ≤ r * m := Nat.mul_le_mul_right _ hi
  rw [Nat.succ_mul] at h
  rw [block, block, List.drop_take, List.take_take, min_eq_left (by omega)]

theorem sideCl_D (tr : Bool) (R : Inst (Fin g × Fin g) (Bits n)) (y : ℕ) {a b : Fin g} (hab : a < b) :
    (sideCl g tr n R y a b).D = ((vC g n).prod (rectsC g tr n y a b)).D := by
  unfold sideCl
  rw [dif_pos hab]
  rfl

theorem sideCl_dec (tr : Bool) (R : Inst (Fin g × Fin g) (Bits n)) (y : ℕ) {a b : Fin g} (hab : a < b) :
    (sideCl g tr n R y a b).dec = ((vC g n).prod (rectsC g tr n y a b)).dec := by
  unfold sideCl
  rw [dif_pos hab]
  rfl

/-- Both factors of two parts a < b at once: o is the other part, top says which of the two parts of
the cuts is taken. -/
theorem side_core (tr top : Bool) (R : Inst (Fin g × Fin g) (Bits n)) (y : ℕ) {a b : Fin g} (hab : a < b) (o : Fin g)
    {z θ : List Bool} (hz : z.length = g ^ 3 * n)
    (hθ : θ.length = g * n + ∑ κ ∈ range (c2 g), rectLen g tr n y (tri a b) κ) :
    (if θ ∈ (sideCl g tr n R y a b).D then
      (∏ i : Fin g, if (stC g tr n).dec z i (o, i) = ((sideCl g tr n R y a b).dec θ).1 i then (1 : ℤ) else 0) *
      ∏ k : Fin g × Fin g with k.1 < k.2,
        if top = true then
          (sideCuts g tr n y ((a, b), k)).top ((stC g tr n).dec z k.1 (o, k.2)) ((stC g tr n).dec z k.2 (o, k.1))
            (((sideCl g tr n R y a b).dec θ).2 k)
        else
          (sideCuts g tr n y ((a, b), k)).bot ((stC g tr n).dec z k.1 (o, k.2)) ((stC g tr n).dec z k.2 (o, k.1))
            (((sideCl g tr n R y a b).dec θ).2 k)
      else 0) =
      (∏ i : Fin g, if he g n z i (node g tr o i) = block n i θ then 1 else 0) *
      ∏ k : Fin g × Fin g with k.1 < k.2,
        cutW tr top (rectDig g tr n y (tri a b) (tri k.1 k.2)) (he g n z k.1 (node g tr o k.2))
          (he g n z k.2 (node g tr o k.1)) (chunkAt (rectLen g tr n y (tri a b)) (tri k.1 k.2) (θ.drop (g * n))) := by
  have hdrop : (θ.drop (g * n)).length = ∑ κ ∈ range (c2 g), rectLen g tr n y (tri a b) κ := by
    rw [List.length_drop, hθ]; omega
  have hhe : ∀ x i : Fin g, (he g n z x (node g tr o i)).length = n := fun x i =>
    length_he hz x.2 (node_lt tr o.2 i.2)
  have hmem : θ ∈ (sideCl g tr n R y a b).D ↔ ∀ k ∈ (univ.filter fun k : Fin g × Fin g => k.1 < k.2),
      chunkAt (rectLen g tr n y (tri a b)) (tri k.1 k.2) (θ.drop (g * n)) ∈
        (rectC g tr n y (tri a b) (tri k.1 k.2)).D := by
    rw [sideCl_D tr R y hab]
    change θ ∈ (words _).filter _ ↔ _
    rw [mem_filter, mem_words, vC_full, mem_words]
    constructor
    · rintro ⟨_, _, h⟩ k hk
      exact (mem_filter.1 h).2 k (mem_filter.1 hk).2
    · intro h
      exact ⟨hθ, by rw [List.length_take, hθ]; omega,
        mem_filter.2 ⟨mem_words.2 hdrop, fun k hk => h k (mem_filter.2 ⟨mem_univ _, hk⟩)⟩⟩
  have h1 : ∀ i : Fin g, (if (stC g tr n).dec z i (o, i) = ((sideCl g tr n R y a b).dec θ).1 i then (1 : ℤ) else 0) =
      if he g n z i (node g tr o i) = block n i θ then 1 else 0 := fun i => by
    rw [sideCl_dec tr R y hab, stC_dec]
    change (if bitsOf n (he g n z i (node g tr o i)) = bitsOf n (block n i (θ.take (g * n))) then (1 : ℤ) else 0) = _
    rw [block_take _ i.2]
    exact if_congr (bitsOf_inj (hhe i i)
      (length_block (by rw [hθ]; exact (Nat.mul_le_mul_right _ i.2).trans (Nat.le_add_right _ _)))) rfl rfl
  have h2 : ∀ k ∈ (univ.filter fun k : Fin g × Fin g => k.1 < k.2),
      cutW tr top (rectDig g tr n y (tri a b) (tri k.1 k.2)) (he g n z k.1 (node g tr o k.2))
          (he g n z k.2 (node g tr o k.1)) (chunkAt (rectLen g tr n y (tri a b)) (tri k.1 k.2) (θ.drop (g * n))) =
        if chunkAt (rectLen g tr n y (tri a b)) (tri k.1 k.2) (θ.drop (g * n)) ∈
            (rectC g tr n y (tri a b) (tri k.1 k.2)).D then
          if top = true then
            (sideCuts g tr n y ((a, b), k)).top ((stC g tr n).dec z k.1 (o, k.2)) ((stC g tr n).dec z k.2 (o, k.1))
              (((sideCl g tr n R y a b).dec θ).2 k)
          else
            (sideCuts g tr n y ((a, b), k)).bot ((stC g tr n).dec z k.1 (o, k.2)) ((stC g tr n).dec z k.2 (o, k.1))
              (((sideCl g tr n R y a b).dec θ).2 k)
        else 0 := fun k hk => by
    have hk' := (mem_filter.1 hk).2
    have hd : ((sideCl g tr n R y a b).dec θ).2 k =
        (rectC g tr n y (tri a b) (tri k.1 k.2)).dec
          (chunkAt (rectLen g tr n y (tri a b)) (tri k.1 k.2) (θ.drop (g * n))) := by
      rw [sideCl_dec tr R y hab]
      change (if k.1 < k.2 then _ else _) = _
      rw [if_pos hk']
    rw [cutW_eq tr top (n := n) (i := rectDig g tr n y (tri a b) (tri k.1 k.2)) (hhe k.1 k.2)
      (length_chunkAt _ (mem_range.1 ((tri_bijOn g).mapsTo hk')) hdrop), hd, stC_dec, stC_dec]
    rfl
  simp only [h1]
  by_cases h : θ ∈ (sideCl g tr n R y a b).D
  · rw [if_pos h]
    congr 1
    exact prod_congr rfl fun k hk => by rw [h2 k hk, if_pos (hmem.1 h k hk)]
  · rw [if_neg h]
    obtain ⟨k, hk, hnk⟩ : ∃ k ∈ (univ.filter fun k : Fin g × Fin g => k.1 < k.2),
        chunkAt (rectLen g tr n y (tri a b)) (tri k.1 k.2) (θ.drop (g * n)) ∉
          (rectC g tr n y (tri a b) (tri k.1 k.2)).D := by
      by_contra hh
      push Not at hh
      exact h (hmem.2 hh)
    rw [prod_eq_zero hk (by rw [h2 k hk, if_neg hnk]), mul_zero]

end core

/-- The factor of the parts a ≠ b on the side of a: the tests on the g edges between nodes of equal
number, times the
factors `sideItem` of the rectangles. -/
theorem sideN_f (g : ℕ) (tr : Bool) (n : ℕ) (Rm : Inst (Fin (g * g)) (List Bool)) (y : ℕ) {a b : Fin g} (hab : a ≠ b)
    {z θ : List Bool} (hz : z.length = g ^ 3 * n) (hθ : θ.length = sideCap g tr n y a b) :
    (sideN g tr n Rm y).f a b z θ =
      (∏ i : Fin g, if he g n z i (node g tr b i) = block n i θ then 1 else 0) *
      ∏ k : Fin g × Fin g with k.1 < k.2, sideItem g tr n y a b z θ k.1 k.2 := by
  have e : (sideN g tr n Rm y).f a b z θ =
      if θ ∈ (sideCl g tr n (sideR g tr n Rm) y (min a b) (max a b)).D then
        (sideNet g tr n (sideR g tr n Rm) y).f a b ((stC g tr n).dec z)
          ((sideCl g tr n (sideR g tr n Rm) y (min a b) (max a b)).dec θ) else 0 := rfl
  unfold sideCap at hθ
  simp only [sideItem, sideChunk]
  rcases lt_or_gt_of_ne hab with h | h
  · have h' : (a : ℕ) < b := h
    rw [min_eq_left h'.le, max_eq_right h'.le] at hθ
    simp only [min_eq_left h'.le, max_eq_right h'.le, decide_eq_true h']
    rw [← side_core tr true (sideR g tr n Rm) y h b hz hθ, e, min_eq_left h.le, max_eq_right h.le]
    have e' : ∀ θ', (sideNet g tr n (sideR g tr n Rm) y).f a b ((stC g tr n).dec z) θ' =
        rowTop (sideCuts g tr n y) a b ((stC g tr n).dec z) θ' := fun θ' => if_pos h
    rw [e']
    rfl
  · have h' : (b : ℕ) < a := h
    rw [min_eq_right h'.le, max_eq_left h'.le] at hθ
    simp only [min_eq_right h'.le, max_eq_left h'.le, decide_eq_false (not_lt.2 h'.le)]
    rw [← side_core tr false (sideR g tr n Rm) y h b hz hθ, e, min_eq_right h.le, max_eq_left h.le]
    have e' : ∀ θ', (sideNet g tr n (sideR g tr n Rm) y).f a b ((stC g tr n).dec z) θ' =
        rowBot (sideCuts g tr n y) b a ((stC g tr n).dec z) θ' := fun θ' => if_neg (not_lt.2 h.le)
    rw [e']
    rfl

end Groundwork.Grid
