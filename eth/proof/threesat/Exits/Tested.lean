/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Exits.Defs

/-! # The points that are met, the leaves that are tested

Facts on the two list functions of proof/threesat/Exits/Defs.lean, with no machine in them.
`tested v ls` is the part of ls up to and including the first entry that passes v; `met f stop c xs`
is the part of xs that a loop sees which halts as soon as its accumulator passes `stop`.
For the two loops of Algorithm 1 that are left early, the loop over the formulas of line 2, in its
deciding form that stops at the first Φ with Count(Φ) > 0, and line 10 («try all groupings into K_ℓ
groups until one is good»), `met` is `tested`: `met_or` and `met_first`.
The rest says how `tested` behaves on a list put together from two, on a range of numbers, and under
a choice `sel` of the entries on which the test is run at all. -/

public section

namespace Exits

open Groundwork Groundwork.Stepped

variable {α β γ τ ν : Type}

/-! ### `tested` -/

/-- Nothing is tested in the empty list. -/
theorem tested_nil (v : ν → Bool) : tested v [] = [] := by simp [tested]

/-- If the first entry passes, it alone is tested: «if … then return». -/
theorem tested_cons_of_pass {v : ν → Bool} {x : ν} (h : v x = true) (l : List ν) : tested v (x :: l) = [x] := by simp [tested, List.findIdx_cons, h]

/-- If the first entry fails, the search goes on behind it. -/
theorem tested_cons_of_fail {v : ν → Bool} {x : ν} (h : v x = false) (l : List ν) : tested v (x :: l) = x :: tested v l := by simp [tested, List.findIdx_cons, h]

/-- A single entry is tested, whatever the outcome. -/
theorem tested_singleton (v : ν → Bool) (x : ν) : tested v [x] = [x] := by cases h : v x <;> simp [tested, List.findIdx_cons, h]

/-- What is tested lies in the list. -/
theorem mem_of_mem_tested {v : ν → Bool} {l : List ν} {x : ν} (h : x ∈ tested v l) : x ∈ l := List.mem_of_mem_take h

/-- If no entry passes, all are tested. -/
theorem tested_of_fail {v : ν → Bool} {l : List ν} (h : l.any v = false) : tested v l = l := by
  induction l with
  | nil => exact tested_nil v
  | cons x l ih =>
    rw [List.any_cons, Bool.or_eq_false_iff] at h
    rw [tested_cons_of_fail h.1, ih h.2]

/-- If an entry of the first list passes, nothing of the second list is tested. -/
theorem tested_append_of_pass {v : ν → Bool} {A : List ν} (h : A.any v = true) (B : List ν) : tested v (A ++ B) = tested v A := by
  induction A with
  | nil => simp at h
  | cons x A ih =>
    cases hx : v x with
    | true => rw [List.cons_append, tested_cons_of_pass hx, tested_cons_of_pass hx]
    | false =>
      rw [List.any_cons, hx, Bool.false_or] at h
      rw [List.cons_append, tested_cons_of_fail hx, tested_cons_of_fail hx, ih h]

/-- If no entry of the first list passes, all of it is tested and the search goes on in the second
list. -/
theorem tested_append_of_fail {v : ν → Bool} {A : List ν} (h : A.any v = false) (B : List ν) : tested v (A ++ B) = A ++ tested v B := by
  induction A with
  | nil => rfl
  | cons x A ih =>
    rw [List.any_cons, Bool.or_eq_false_iff] at h
    rw [List.cons_append, tested_cons_of_fail h.1, ih h.2, List.cons_append]

/-- Some tested entry passes if and only if some entry passes. -/
theorem any_tested (v : ν → Bool) (l : List ν) : (tested v l).any v = l.any v := by
  induction l with
  | nil => rw [tested_nil]
  | cons x l ih =>
    cases hx : v x with
    | true => rw [tested_cons_of_pass hx]; simp [hx]
    | false => rw [tested_cons_of_fail hx, List.any_cons, List.any_cons, ih]

/-- The search does not go beyond the range. -/
theorem reach_le (q : ℕ → Bool) (n : ℕ) : reach q n ≤ n := by
  unfold reach
  cases h : (List.range n).find? q with
  | none => exact le_rfl
  | some i => exact List.mem_range.1 (List.mem_of_find?_eq_some h)

/-- In the range 0, …, n − 1 the numbers below `reach` are tested: «try all … until one is good». -/
theorem tested_range (q : ℕ → Bool) (n : ℕ) : tested q (List.range n) = List.range (reach q n) := by
  unfold tested reach
  rw [List.take_range]
  congr 1
  cases h : (List.range n).find? q with
  | none =>
    rw [List.find?_eq_none] at h
    rw [List.findIdx_eq_length_of_false (fun x hx => by simpa using h x hx), List.length_range]
    change min (n + 1) n = n
    omega
  | some i =>
    rw [List.find?_range_eq_some] at h
    obtain ⟨h1, h2, h3⟩ := h
    have hi := List.mem_range.1 h2
    rw [(List.findIdx_eq (p := q) (xs := List.range n) (i := i) (by simpa using hi)).2 ⟨by simpa using h1, fun j hj => by simpa using h3 j hj⟩]
    change min (i + 1) n = i + 1
    omega

/-! ### The test is run only on the entries that `sel` picks -/

section sel

variable (sel : τ → Option ν) (v : ν → Bool) (w : τ → Bool) (hw : ∀ x, w x = ((sel x).map v).getD false)
include hw

/-- Some entry passes w if and only if some picked entry passes v. -/
theorem any_filterMap_sel (xs : List τ) : (xs.filterMap sel).any v = xs.any w := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases h : sel x with
    | none => rw [List.filterMap_cons_none h, ih, List.any_cons, hw x, h]; rfl
    | some y => rw [List.filterMap_cons_some h, List.any_cons, ih, List.any_cons, hw x, h]; rfl

/-- The picked entries among those tested by w are the picked entries tested by v. -/
theorem filterMap_tested (xs : List τ) : (tested w xs).filterMap sel = tested v (xs.filterMap sel) := by
  induction xs with
  | nil => simp [tested_nil]
  | cons x xs ih =>
    cases h : sel x with
    | none =>
      have hx : w x = false := by rw [hw x, h]; rfl
      rw [tested_cons_of_fail hx, List.filterMap_cons_none h, List.filterMap_cons_none h, ih]
    | some y =>
      cases hy : v y with
      | true =>
        have hx : w x = true := by rw [hw x, h]; exact hy
        rw [tested_cons_of_pass hx, List.filterMap_cons_some h, List.filterMap_cons_some h, tested_cons_of_pass hy]; rfl
      | false =>
        have hx : w x = false := by rw [hw x, h]; exact hy
        rw [tested_cons_of_fail hx, List.filterMap_cons_some h, List.filterMap_cons_some h, tested_cons_of_fail hy, ih]

end sel

/-! ### `met` -/

/-- No point is met on the empty orbit. -/
theorem met_nil (f : γ → τ → γ) (stop : γ → Bool) (c : γ) : met f stop c [] = [] := by simp [met]

/-- If the accumulator passes `stop` after the first round, the loop is left. -/
theorem met_cons_of_stop {f : γ → τ → γ} {stop : γ → Bool} {c : γ} {x : τ} (h : stop (f c x) = true) (xs : List τ) : met f stop c (x :: xs) = [x] := by simp [met, h]

/-- If it does not, the loop goes on with the new accumulator. -/
theorem met_cons_of_go {f : γ → τ → γ} {stop : γ → Bool} {c : γ} {x : τ} (h : stop (f c x) = false) (xs : List τ) : met f stop c (x :: xs) = x :: met f stop (f c x) xs := by simp [met, h]

/-- The loop of «if … then return»: the accumulator says whether some point has passed so far, and
the loop is left as soon as it says yes. The points met are those tested. -/
theorem met_or (w : τ → Bool) (xs : List τ) : met (fun c x => c || w x) id false xs = tested w xs := by
  induction xs with
  | nil => rw [tested_nil, met_nil]
  | cons x xs ih =>
    cases hx : w x with
    | true => rw [tested_cons_of_pass hx]; exact met_cons_of_stop (by simp [hx]) xs
    | false =>
      have e : met (fun c x => c || w x) id false (x :: xs) = x :: met (fun c x => c || w x) id (false || w x) xs := met_cons_of_go (by simp [hx]) xs
      rw [e, hx, tested_cons_of_fail hx]
      exact congrArg (x :: ·) ih

/-- The result of that loop. -/
theorem foldl_or (w : τ → Bool) (xs : List τ) (c : Bool) : xs.foldl (fun c x => c || w x) c = (c || xs.any w) := by
  induction xs generalizing c with
  | nil => simp
  | cons x xs ih => rw [List.foldl_cons, ih, List.any_cons, Bool.or_assoc]

/-- The loop of «try all … until one is good»: the accumulator holds the first good number, if one
has been seen, and the loop is left as soon as it holds one. The points met are those tested. -/
theorem met_first (p : β → Bool) (v : ℕ → β) (a : α) (l : List ℕ) :
    met (fun c (x : α × ℕ) => rangeG (firstG p) c x (v x.2)) Option.isSome none (l.map fun y => (a, y)) = (tested (fun y => p (v y)) l).map fun y => (a, y) := by
  induction l with
  | nil => rw [tested_nil]; exact met_nil _ _ _
  | cons y l ih =>
    cases hy : p (v y) with
    | true =>
      rw [tested_cons_of_pass (v := fun y => p (v y)) (x := y) hy, List.map_cons]
      exact met_cons_of_stop (by simp [rangeG, firstG, hy]) _
    | false =>
      have e : rangeG (firstG p) none (a, y) (v y) = none := by simp [rangeG, firstG, hy]
      have e2 : met (fun c (x : α × ℕ) => rangeG (firstG p) c x (v x.2)) Option.isSome none ((a, y) :: l.map fun y => (a, y))
          = (a, y) :: met (fun c (x : α × ℕ) => rangeG (firstG p) c x (v x.2)) Option.isSome (rangeG (firstG p) none (a, y) (v y)) (l.map fun y => (a, y)) :=
        met_cons_of_go (by simp [rangeG, firstG, hy]) _
      rw [tested_cons_of_fail (v := fun y => p (v y)) (x := y) hy, List.map_cons, List.map_cons, e2, e, ih]

/-- The result of that loop: the first good number of the whole list. -/
theorem foldl_first_tested (p : β → Bool) (v : ℕ → β) (l : List ℕ) :
    (tested (fun y => p (v y)) l).foldl (fun c y => firstG p c y (v y)) none = l.find? fun y => p (v y) := by
  induction l with
  | nil => rw [tested_nil]; rfl
  | cons y l ih =>
    cases hy : p (v y) with
    | true => rw [tested_cons_of_pass (v := fun y => p (v y)) (x := y) hy]; simp [firstG, hy]
    | false =>
      rw [tested_cons_of_fail (v := fun y => p (v y)) (x := y) hy, List.foldl_cons, show firstG p none y (v y) = none by simp [firstG, hy], ih]
      simp [hy]

end Exits
