/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import StepMachines.Prog.Stepped
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Data.List.Range

/-! Loops over y < N a (N a possibly huge, y a binary natural): fold, sum, product, «first». -/

namespace Groundwork.Stepped

open Finset

variable {α β γ : Type}

/-- The first point of the loop over y < N a. -/
@[expose] public def rangeStart (N : α → ℕ) (a : α) : Option (α × ℕ) := if 0 < N a then some (a, 0) else none

/-- The next point of the loop over y < N a. -/
@[expose] public def rangeNext (N : α → ℕ) (x : α × ℕ) : Option (α × ℕ) :=
  if x.2 + 1 < N x.1 then some (x.1, x.2 + 1) else none

/-- g, seeing only the counter of the point. -/
@[expose] public def rangeG (g : γ → ℕ → β → γ) (c : γ) (x : α × ℕ) (b : β) : γ := g c x.2 b

/-- The loop over y = 0, 1, …, N a - 1; the body sees (a, y). -/
@[expose] public def foldRange [HasSize α] [HasSize γ] (N : α → ℕ) (M : Stepped (α × ℕ) β) (g : γ → ℕ → β → γ)
    (c₀ : α → γ) : Stepped α γ :=
  foldWhile (rangeStart N) (rangeNext N) M (rangeG g) c₀

theorem orbit_range (N : α → ℕ) (a : α) (k y : ℕ) (h : y + k = N a) :
    Orbit (rangeNext N) (if y < N a then some (a, y) else none) ((List.range' y k).map fun y => (a, y)) := by
  induction k generalizing y with
  | zero => rw [if_neg (by omega)]; exact .nil
  | succ k ih =>
    rw [if_pos (by omega), List.range'_succ, List.map_cons]
    exact .cons (ih (y + 1) (by omega))

theorem sum_map_range (f : ℕ → ℕ) (n : ℕ) : ((List.range n).map f).sum = ∑ y ∈ range n, f y := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, sum_range_succ]; simp

public theorem foldl_range_succ (f : γ → ℕ → γ) (c : γ) (k : ℕ) :
    (List.range (k + 1)).foldl f c = f ((List.range k).foldl f c) k := by
  simp [List.range_succ]

/-- The body takes t y steps on (a, y) and returns v y. Steps of the loop: Σ_{y < N a} (t y + 1).
Result: the fold of g
over y = 0, …, N a - 1. Sc bounds the size of the accumulator, Sm the size inside the body. -/
public theorem foldRange_runs [HasSize α] [HasSize γ] {N : α → ℕ} {M : Stepped (α × ℕ) β} {g : γ → ℕ → β → γ}
    {c₀ : α → γ} {a : α} (t : ℕ → ℕ) (v : ℕ → β) (Sc Sm : ℕ) (hM : ∀ y < N a, M.Runs (a, y) (t y) Sm (v y))
    (hc : ∀ k ≤ N a, size ((List.range k).foldl (fun c y => g c y (v y)) (c₀ a)) ≤ Sc) :
    (foldRange N M g c₀).Runs a (∑ y ∈ range (N a), (t y + 1)) (size a + size (N a) + (Sc + Sm) + 1)
      ((List.range (N a)).foldl (fun c y => g c y (v y)) (c₀ a)) := by
  have ho := orbit_range N a (N a) 0 (by omega)
  rw [← List.range_eq_range'] at ho
  have := foldWhile_runs (start := rangeStart N) (M := M)
    (g := rangeG g) (c₀ := c₀) ho (fun x => t x.2) (fun x => v x.2)
    (size a + size (N a)) Sc Sm
    (by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
      exact hM y (List.mem_range.1 hy))
    (by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
      have := Nat.size_le_size (List.mem_range.1 hy).le
      simp only [size_prod, size_nat]; omega)
    (by
      intro l hl
      rw [List.prefix_iff_eq_take] at hl
      rw [hl, ← List.map_take, List.take_range, List.foldl_map]
      exact hc _ (min_le_right _ _))
  rw [List.map_map, List.foldl_map] at this
  rw [← sum_map_range]
  exact this

/-! ### Sum -/

/-- The accumulator of a sum. -/
@[expose] public def addG (c : ℤ) (_ : ℕ) (b : ℤ) : ℤ := c + b

/-- The start of a sum. -/
@[expose] public def zeroC (_ : α) : ℤ := 0

/-- Σ_{y < N a} M(a, y). -/
@[expose] public def sumRange [HasSize α] (N : α → ℕ) (M : Stepped (α × ℕ) ℤ) : Stepped α ℤ :=
  foldRange N M addG zeroC

theorem foldl_add (v : ℕ → ℤ) (k : ℕ) :
    (List.range k).foldl (fun c y => c + v y) 0 = ∑ y ∈ range k, v y := by
  induction k with
  | zero => rfl
  | succ k ih => rw [foldl_range_succ, ih, sum_range_succ]

public theorem natAbs_sum_le (v : ℕ → ℤ) (V k : ℕ) (h : ∀ y < k, (v y).natAbs ≤ V) :
    (∑ y ∈ range k, v y).natAbs ≤ k * V := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ]
    have h1 := ih fun y hy => h y (by omega)
    have h2 := h k (by omega)
    have h3 := Int.natAbs_add_le (∑ y ∈ range k, v y) (v k)
    rw [Nat.succ_mul]; omega

/-- Steps: Σ_{y < N a} (t y + 1). Result: Σ_{y < N a} v y. V bounds every |v y|. -/
public theorem sumRange_runs [HasSize α] {N : α → ℕ} {M : Stepped (α × ℕ) ℤ} {a : α} (t : ℕ → ℕ) (v : ℕ → ℤ)
    (V Sm : ℕ) (hM : ∀ y < N a, M.Runs (a, y) (t y) Sm (v y)) (hV : ∀ y < N a, (v y).natAbs ≤ V) :
    (sumRange N M).Runs a (∑ y ∈ range (N a), (t y + 1)) (size a + size (N a) + (size (N a * V) + Sm) + 1)
      (∑ y ∈ range (N a), v y) := by
  rw [← foldl_add]
  refine foldRange_runs t v _ Sm hM fun k hk => ?_
  rw [show List.foldl (fun c y => addG c y (v y)) (zeroC a) (List.range k) = ∑ y ∈ range k, v y from foldl_add v k]
  have h1 := natAbs_sum_le v V k fun y hy => hV y (by omega)
  have h2 := Nat.size_le_size (h1.trans (Nat.mul_le_mul_right V hk))
  simp only [size_int, size_nat]; omega

/-! ### Product -/

/-- The accumulator of a product. -/
@[expose] public def mulG (c : ℤ) (_ : ℕ) (b : ℤ) : ℤ := c * b

/-- The start of a product. -/
@[expose] public def oneC (_ : α) : ℤ := 1

/-- ∏_{y < N a} M(a, y). -/
@[expose] public def prodRange [HasSize α] (N : α → ℕ) (M : Stepped (α × ℕ) ℤ) : Stepped α ℤ :=
  foldRange N M mulG oneC

theorem foldl_mul (v : ℕ → ℤ) (k : ℕ) :
    (List.range k).foldl (fun c y => c * v y) 1 = ∏ y ∈ range k, v y := by
  induction k with
  | zero => rfl
  | succ k ih => rw [foldl_range_succ, ih, prod_range_succ]

public theorem natAbs_prod_le (v : ℕ → ℤ) (V k : ℕ) (h : ∀ y < k, (v y).natAbs ≤ V) :
    (∏ y ∈ range k, v y).natAbs ≤ V ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [prod_range_succ, Int.natAbs_mul, pow_succ]
    exact Nat.mul_le_mul (ih fun y hy => h y (by omega)) (h k (by omega))

/-- Steps: Σ_{y < N a} (t y + 1). Result: ∏_{y < N a} v y. V ≥ 1 bounds every |v y|. -/
public theorem prodRange_runs [HasSize α] {N : α → ℕ} {M : Stepped (α × ℕ) ℤ} {a : α} (t : ℕ → ℕ) (v : ℕ → ℤ)
    (V Sm : ℕ) (hV1 : 1 ≤ V) (hM : ∀ y < N a, M.Runs (a, y) (t y) Sm (v y))
    (hV : ∀ y < N a, (v y).natAbs ≤ V) :
    (prodRange N M).Runs a (∑ y ∈ range (N a), (t y + 1)) (size a + size (N a) + (size (V ^ N a) + Sm) + 1)
      (∏ y ∈ range (N a), v y) := by
  rw [← foldl_mul]
  refine foldRange_runs t v _ Sm hM fun k hk => ?_
  rw [show List.foldl (fun c y => mulG c y (v y)) (oneC a) (List.range k) = ∏ y ∈ range k, v y from foldl_mul v k]
  have h1 := natAbs_prod_le v V k fun y hy => hV y (by omega)
  have h2 := Nat.size_le_size (h1.trans (Nat.pow_le_pow_right hV1 hk))
  simp only [size_int, size_nat]; omega

/-! ### «The first index whose result passes the test» -/

/-- The accumulator of «first». -/
@[expose] public def firstG (p : β → Bool) (c : Option ℕ) (y : ℕ) (b : β) : Option ℕ :=
  match c with | some i => some i | none => if p b then some y else none

/-- The start of «first». -/
@[expose] public def noneC (_ : α) : Option ℕ := none

/-- The least y < N a such that p holds of M(a, y), if there is one. -/
@[expose] public def firstRange [HasSize α] (N : α → ℕ) (M : Stepped (α × ℕ) β) (p : β → Bool) :
    Stepped α (Option ℕ) :=
  foldRange N M (firstG p) noneC

theorem foldl_first (q : ℕ → Bool) (k : ℕ) :
    (List.range k).foldl (fun c y => match c with | some i => some i | none => if q y then some y else none)
      none = (List.range k).find? q := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [foldl_range_succ, ih, List.range_succ, List.find?_append]
    cases (List.range k).find? q with
    | some i => rfl
    | none => by_cases h : q k <;> simp [h]

/-- Steps: Σ_{y < N a} (t y + 1); the loop does not stop early. Result: the least y < N a such that
p holds of v y. -/
public theorem firstRange_runs [HasSize α] {N : α → ℕ} {M : Stepped (α × ℕ) β} {p : β → Bool} {a : α}
    (t : ℕ → ℕ) (v : ℕ → β) (Sm : ℕ) (hM : ∀ y < N a, M.Runs (a, y) (t y) Sm (v y)) :
    (firstRange N M p).Runs a (∑ y ∈ range (N a), (t y + 1))
      (size a + size (N a) + (size (N a) + 1 + Sm) + 1) ((List.range (N a)).find? fun y => p (v y)) := by
  rw [← foldl_first fun y => p (v y)]
  refine foldRange_runs t v _ Sm hM fun k hk => ?_
  rw [show List.foldl (fun c y => firstG p c y (v y)) (noneC a) (List.range k)
    = (List.range k).find? fun y => p (v y) from foldl_first (fun y => p (v y)) k]
  cases h : (List.range k).find? fun y => p (v y) with
  | none => simp only [size_none]; omega
  | some i =>
    have hi := List.mem_range.1 (List.mem_of_find?_eq_some h)
    have := Nat.size_le_size (hi.le.trans hk)
    simp only [size_some, size_nat]; omega

end Groundwork.Stepped
