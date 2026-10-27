/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import CountedRecursion.SolverDefs
public import CountedRecursion.Within
import Mathlib.Tactic

/-! # The stages of the solver

The solver at a level ℓ + 1 (`levelSolver`, SolverDefs.lean) runs its stages one after the other.
Here each stage is run against ANY oracle O and prices w, of which only what the stage asks is
assumed; nothing is said yet of the pieces or of the networks.
* `askInt_within`, `askList_within`: one query.
* `capsLoop_within`: «the numbers … c^row_i, c^col_i are computed once»: one query for each i in the
  list.
* `sumAndDivide_within`: «adding one Z_ι», for all ι; then «computing d^{|ℛ|} and dividing by it».
* `levelSolver_within`: all stages. The cost is 2ℓ + 5 + 2|𝓘| own steps, 2|𝓘| + 2 queries to the
  pieces, and the cost of `sumAndDivide`, which is the cost of the patterns, one step more for each
  pattern, and 2 steps more. -/

public section

namespace ExplicitCost

open Finset Groundwork QueryMachines Printed

variable {Q α : Type}

/-- One query, read as an integer. -/
theorem askInt_within [HasSize α] {h : α → Q} {O : Q → Option Ans} {w : Q → ℕ} {a : α} {v : Ans} (hv : O (h a) = some v) : (askInt h).Within O w a (w (h a)) (max (size a) (size v) + 1) (asInt v) :=
  mapOut_within (query_within hv)

/-- One query, read as a list. -/
theorem askList_within [HasSize α] {h : α → Q} {O : Q → Option Ans} {w : Q → ℕ} {a : α} {v : Ans} (hv : O (h a) = some v) : (askList h).Within O w a (w (h a)) (max (size a) (size v) + 1) (asList v) :=
  mapOut_within (query_within hv)

/-! ### Numbers and lists -/

/-- The size of a number grows with the number. -/
theorem size_le_of_le {m n : ℕ} (h : m ≤ n) : size m ≤ size n := Nat.succ_le_succ (Nat.size_le_size h)

/-- A number n has size at most n + 1. -/
theorem size_le_succ (n : ℕ) : size n ≤ n + 1 := Nat.succ_le_succ (Nat.size_le.2 Nat.lt_two_pow_self)

/-- An element is not larger than the list. -/
theorem size_mem_le [HasSize α] {l : List α} {x : α} (h : x ∈ l) : size x ≤ size l := by
  induction l with
  | nil => cases h
  | cons y l ih =>
    simp only [size_list, List.map_cons, List.sum_cons] at ih ⊢
    rcases List.mem_cons.1 h with rfl | h
    · omega
    · have := ih h
      omega

/-- A list has at most as many elements as its size. -/
theorem length_lt_size [HasSize α] (l : List α) : l.length < size l := by
  induction l with
  | nil => simp [size_list]
  | cons y l ih =>
    simp only [size_list, List.map_cons, List.sum_cons, List.length_cons] at ih ⊢
    omega

/-- The first k elements are not larger than the list. -/
theorem size_take_le [HasSize α] (l : List α) (k : ℕ) : size (l.take k) ≤ size l := by
  conv_rhs => rw [← List.take_append_drop k l]
  simp only [size_list, List.map_append, List.sum_append]
  omega

/-- The first k elements, read off by their places. -/
theorem map_range_getD (l : List α) (d : α) {k : ℕ} (hk : k ≤ l.length) : (List.range k).map (fun j => l.getD j d) = l.take k := by
  apply List.ext_getElem
  · simp [hk]
  · intro i h1 h2
    have h3 : i < l.length := by
      simp only [List.length_map, List.length_range] at h1
      omega
    simp [List.getElem?_eq_getElem h3]

/-- The loop that appends one number in each round makes the list of the numbers. -/
theorem foldl_append_toNat (v : ℕ → ℤ) (k : ℕ) : (List.range k).foldl (fun (acc : List ℕ) y => acc ++ [(v y).toNat]) [] = (List.range k).map fun y => (v y).toNat := by
  induction k with
  | zero => rfl
  | succ k ih => rw [List.range_succ, List.foldl_append, ih, List.map_append]; rfl

/-! ### The stages -/

/-- «The numbers … c^row_i, c^col_i are computed once»: if the oracle answers the question for the
element number j of the list by the number at the place j of `caps`, at the price t, the loop
returns `caps` within |𝓘|·(t + 1) operations. -/
theorem capsLoop_within {σ : Type} [HasSize σ] {tr : Bool} {lamU : σ → List Unit} {idx : σ → List ℤ} {O : SolQuery → Option Ans} {w : SolQuery → ℕ} {s : σ} (caps : List ℕ) (t : ℕ) (hlen : caps.length = (idx s).length)
    (hO : ∀ j < (idx s).length, O (Sum.inr (Sum.inr (lamU s, .inr (.inr (.inl (tr, (idx s).getD j 0)))))) = some (.inl (caps.getD j 0 : ℤ)))
    (hw : ∀ q, w (Sum.inr (Sum.inr (lamU s, q))) = t) :
    (capsLoop tr lamU idx).Within O w s ((idx s).length * (t + 1)) (2 * size s + 2 * size (idx s).length + 2 * size caps + 3) caps := by
  have r := foldRange_within (N := fun s : σ => (idx s).length) (M := askInt fun v : σ × ℕ => (Sum.inr (Sum.inr (lamU v.1, .inr (.inr (.inl (tr, (idx v.1).getD v.2 0))))) : SolQuery))
    (g := fun (acc : List ℕ) _ (b : ℤ) => acc ++ [b.toNat]) (c₀ := fun _ => []) (O := O) (w := w) (a := s) (fun _ => t) (fun j => (caps.getD j 0 : ℤ)) (size caps) (size s + size (idx s).length + size caps + 2)
    (fun j hj => by
      have h1 := askInt_within (h := fun v : σ × ℕ => (Sum.inr (Sum.inr (lamU v.1, .inr (.inr (.inl (tr, (idx v.1).getD v.2 0))))) : SolQuery)) (w := w) (a := (s, j)) (hO j hj)
      refine h1.mono (hw _).le ?_
      have h2 : size j ≤ size (idx s).length := size_le_of_le (Nat.le_of_lt hj)
      have h3 : size (caps.getD j 0) ≤ size caps := by
        rw [List.getD_eq_getElem _ _ (hlen ▸ hj)]
        exact size_mem_le (List.getElem_mem _)
      simp only [size_prod, size_inl, size_int, size_nat, Int.natAbs_natCast] at h2 h3 ⊢
      omega)
    (fun k hk => by
      rw [foldl_append_toNat]
      simp only [Int.toNat_natCast]
      rw [map_range_getD caps 0 (hlen ▸ hk)]
      exact size_take_le _ _)
  rw [foldl_append_toNat] at r
  simp only [Int.toNat_natCast] at r
  rw [map_range_getD caps 0 hlen.ge, ← hlen, List.take_length, hlen] at r
  refine r.mono ?_ ?_
  · rw [Finset.sum_const, card_range, smul_eq_mul]
  · omega

/-- «adding one Z_ι», for all ι; then «computing d^{|ℛ|} and dividing by it»: if the pattern number
y costs T₀ and has the value v y, |v y| ≤ V, the whole costs |𝓘|^{|ℛ|}·(T₀ + 1) + 2 operations. -/
theorem sumAndDivide_within {c : ℕ} {O : SolQuery → Option Ans} {w : SolQuery → ℕ} {r : Ready} (T₀ Sm V : ℕ) (v : ℕ → ℤ) (hM : ∀ y < nPatterns r, (patternValue c).Within O w (r, y) T₀ Sm (v y))
    (hV : ∀ y < nPatterns r, (v y).natAbs ≤ V) :
    (sumAndDivide c).Within O w r (nPatterns r * (T₀ + 1) + 2) (2 * size r + size (nPatterns r) + size (nPatterns r * V) + Sm + 3) ((∑ y ∈ range (nPatterns r), v y) / (((rD r).toNat ^ rRect r : ℕ) : ℤ)) := by
  have h1 := sumRange_within (N := nPatterns) (M := patternValue c) (fun _ => T₀) v V Sm hM hV
  have h2 := lift_within (Q := SolQuery) (A := Ans) (O := O) (w := w) (Stepped.ofFun_runs (fun p : Ready × ℤ => p.2 / (((rD p.1).toNat ^ rRect p.1 : ℕ) : ℤ)) (r, ∑ y ∈ range (nPatterns r), v y))
  refine (bind_within h1 h2).mono ?_ ?_
  · rw [Finset.sum_const, card_range, smul_eq_mul]
  · have h3 : (∑ y ∈ range (nPatterns r), v y).natAbs ≤ nPatterns r * V := Stepped.natAbs_sum_le v V _ fun y hy => hV y hy
    have h4 : ((∑ y ∈ range (nPatterns r), v y) / (((rD r).toNat ^ rRect r : ℕ) : ℤ)).natAbs ≤ nPatterns r * V := (Int.natAbs_ediv_le_natAbs _ _).trans h3
    have h5 := Nat.size_le_size h3
    have h6 := Nat.size_le_size h4
    simp only [size_prod, size_int, size_nat] at h5 h6 ⊢
    omega

/-- **All stages.** The oracle answers the question for 𝓘 by the list I, that for d by d, those for
c^row_i and c^col_i by the numbers of the lists c₀ and c₁, each at the price t; the numbers K and g
are written by the loop on states of size at most S₁; and the last stage, on what has been computed,
costs T₆ on states of size at most S₆. -/
theorem levelSolver_within {c x₀ : ℕ} {O : SolQuery → Option Ans} {w : SolQuery → ℕ} {h : Head} {l S₁ : ℕ} {nums : List Unit × List Unit} (hN : (numbersM x₀).Runs h.1.tail (2 * l) S₁ nums) (I : List ℤ) (d : ℤ) (c₀ c₁ : List ℕ) (t : ℕ)
    (hI : O (Sum.inr (Sum.inr (h.2.1, .inr (.inl ())))) = some (.inr I)) (hd : O (Sum.inr (Sum.inr (h.2.1, .inl ()))) = some (.inl d)) (hl₀ : c₀.length = I.length) (hl₁ : c₁.length = I.length)
    (h₀ : ∀ j < I.length, O (Sum.inr (Sum.inr (h.2.1, .inr (.inr (.inl (false, I.getD j 0)))))) = some (.inl (c₀.getD j 0 : ℤ)))
    (h₁ : ∀ j < I.length, O (Sum.inr (Sum.inr (h.2.1, .inr (.inr (.inl (true, I.getD j 0)))))) = some (.inl (c₁.getD j 0 : ℤ)))
    (hw : ∀ q, w (Sum.inr (Sum.inr (h.2.1, q))) = t) {T₆ S₆ : ℕ} {Z : ℤ} (h₆ : (sumAndDivide c).Within O w (((((h, nums), I), d), c₀), c₁) T₆ S₆ Z) :
    (levelSolver c x₀).Within O w h (2 * l + 5 + 2 * I.length + (2 * I.length + 2) * t + T₆) (S₁ + 8 * size (((((h, nums), I), d), c₀), c₁) + S₆ + 10) Z := by
  have r₁ := lift_within (Q := SolQuery) (A := Ans) (O := O) (w := w) (Stepped.mapIn_runs (f := fun a : Head => a.1.tail) (a := h) hN)
  have r₂ := askList_within (h := fun s : Stage₁ => (Sum.inr (Sum.inr (s.1.2.1, .inr (.inl ()))) : SolQuery)) (w := w) (a := (h, nums)) hI
  have r₃ := askInt_within (h := fun s : Stage₂ => (Sum.inr (Sum.inr (s.1.1.2.1, .inl ())) : SolQuery)) (w := w) (a := ((h, nums), I)) hd
  have r₄ := capsLoop_within (tr := false) (lamU := fun s : Stage₃ => s.1.1.1.2.1) (idx := fun s : Stage₃ => s.1.2) (O := O) (w := w) (s := (((h, nums), I), d)) c₀ t hl₀ h₀ hw
  have r₅ := capsLoop_within (tr := true) (lamU := fun s : Stage₄ => s.1.1.1.1.2.1) (idx := fun s : Stage₄ => s.1.1.2) (O := O) (w := w) (s := ((((h, nums), I), d), c₀)) c₁ t hl₁ h₁ hw
  have hn : size I.length ≤ size I := by
    have h1 := length_lt_size I
    have h2 := size_le_succ I.length
    omega
  refine (bind_within r₁ (bind_within r₂ (bind_within r₃ (bind_within r₄ (bind_within r₅ h₆))))).mono ?_ ?_
  · rw [hw, hw]
    ring_nf
    omega
  · simp only [size_prod, size_inl, size_inr, asInt, asList] at hn ⊢
    omega

end ExplicitCost
