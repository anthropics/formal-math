/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import RecursionToBound.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.ByContra

/-! # The numbers of Step 5 in natural numbers and lists

The definitions of proof/variables/RecursionToBound/Defs.lean follow Step 5 of Appendix D: ε =
min(a/b, 1) is rational, α = ⌈2(k−1)²·ε⁻¹·⌈log₂(32(k−1)²/ε)⌉⌉ (the paper has no ceilings), the
occurrence bound is a finite sum
and Δ is a finite supremum. A certificate of polynomial time needs them from natural numbers and
lists; this file proves the equalities, **for ALL arguments** (also k = 0, a = 0, b = 0): Theorem D (a)
needs all inputs.

* `epsOf_eq`: ε = min(a, b)/b. (For b = 0 both sides are 0, by Mathlib's convention x/0 = 0.)
* `ceil_natCast_div`: ⌈m/p⌉ = ⌊(m + p − 1)/p⌋ =: `ceilDiv m p`, for all natural numbers m and p.
  (For p = 0 both sides are 0.)
* `alphaC_epsOf`: α = `alphaN k r` = ⌈2·s·b·L / min(a, b)⌉ with L = `logN k r` = ⌈log₂ ⌈32·s·b /
  min(a, b)⌉⌉ and s = `sqPred k` = (k − 1)², which is 1 for k = 0 because the subtraction is that of
  rational numbers.
* `ceil_epsOf_mul`: ⌈ε·n⌉ = ⌈min(a, b)·n / b⌉.
* `occBound_eq`, `DeltaOf_eq`, `widthOr3F_eq`: the sum, the supremum and the width as functions of
  lists.
* `foldr_bind_max`: the maximum of a list of numbers of which some may be missing, computed from the
  right as in `needOutputsC`, is missing if one of them is, and else is the maximum of the list. -/

public section

namespace RecursionToBound

open Finset SparsificationLemma

/-! ### Fractions -/

/-- (k − 1)² as a natural number, where the subtraction is that of integers: 1 for k = 0. -/
@[expose] def sqPred (k : ℕ) : ℕ := (k - 1) * (k - 1) + (1 - k)

/-- m/p rounded up; 0 for p = 0. -/
@[expose] def ceilDiv (m p : ℕ) : ℕ := (m + p - 1) / p

/-- ⌈log₂ x⌉ for x = 32(k−1)²/ε and ε = min(a/b, 1), r = (a, b). -/
@[expose] def logN (k : ℕ) (r : ℕ × ℕ) : ℕ := Nat.clog 2 (ceilDiv (32 * sqPred k * r.2) (min r.1 r.2))

/-- α = ⌈2(k−1)²·ε⁻¹·⌈log₂ x⌉⌉ for ε = min(a/b, 1), r = (a, b). -/
@[expose] def alphaN (k : ℕ) (r : ℕ × ℕ) : ℕ := ceilDiv (2 * sqPred k * r.2 * logN k r) (min r.1 r.2)

/-- The ceiling of a quotient of natural numbers, for all m and p. -/
theorem ceil_natCast_div (m p : ℕ) : ⌈(m : ℚ) / (p : ℚ)⌉₊ = ceilDiv m p := by
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · simp [ceilDiv]
  · have hp' : (0 : ℚ) < p := by exact_mod_cast hp
    obtain ⟨d, hd⟩ : ∃ d, d = (m + p - 1) / p := ⟨_, rfl⟩
    have h1 : m ≤ d * p := by
      have h2 := Nat.div_add_mod (m + p - 1) p
      have h3 := Nat.mod_lt (m + p - 1) hp
      rw [← hd] at h2
      rw [Nat.mul_comm]
      omega
    rw [ceilDiv, ← hd]
    refine le_antisymm (Nat.ceil_le.2 ((div_le_iff₀ hp').2 (by exact_mod_cast h1))) ?_
    have h4 : (m : ℚ) ≤ (⌈(m : ℚ) / (p : ℚ)⌉₊ : ℚ) * p := (div_le_iff₀ hp').1 (Nat.le_ceil _)
    have h5 : m ≤ ⌈(m : ℚ) / (p : ℚ)⌉₊ * p := by exact_mod_cast h4
    rw [hd]
    refine Nat.lt_succ_iff.1 ((Nat.div_lt_iff_lt_mul hp).2 ?_)
    rw [Nat.succ_mul]
    omega

/-- ε = min(a/b, 1) = min(a, b)/b, for all a and b. -/
theorem epsOf_eq (r : ℕ × ℕ) : epsOf r = ((min r.1 r.2 : ℕ) : ℚ) / (r.2 : ℚ) := by
  rcases Nat.eq_zero_or_pos r.2 with h | h
  · simp [epsOf, h]
  · have h' : (0 : ℚ) < r.2 := by exact_mod_cast h
    rw [epsOf, Nat.cast_min, ← min_div_div_right h'.le, div_self h'.ne']

/-- (k − 1)², computed in the rational numbers, is `sqPred k`. -/
theorem sqPred_cast (k : ℕ) : ((k : ℚ) - 1) ^ 2 = ((sqPred k : ℕ) : ℚ) := by
  cases k with
  | zero => simp [sqPred]
  | succ k =>
    have e : sqPred (k + 1) = k * k := by
      rw [sqPred, Nat.add_sub_cancel, Nat.sub_eq_zero_of_le (by omega), Nat.add_zero]
    rw [e]
    push_cast
    ring

/-- ⌈log₂ x⌉ of the thresholds, without fractions. -/
theorem logC_epsOf (k : ℕ) (r : ℕ × ℕ) : Cal.logC k (epsOf r) = logN k r := by
  have e : (32 : ℚ) * ((sqPred k : ℕ) : ℚ) * (r.2 : ℚ) = ((32 * sqPred k * r.2 : ℕ) : ℚ) := by push_cast; ring
  rw [Cal.logC, Cal.xC, epsOf_eq, sqPred_cast, div_div_eq_mul_div, e, ceil_natCast_div, logN]

/-- **α of the thresholds, without fractions**: `Cal.alphaC k (epsOf r)` = ⌈2·(k−1)²·b·L / min(a,
b)⌉, for all k and r = (a, b). -/
theorem alphaC_epsOf (k : ℕ) (r : ℕ × ℕ) : Cal.alphaC k (epsOf r) = alphaN k r := by
  have e : (2 : ℚ) * ((sqPred k : ℕ) : ℚ) * (r.2 : ℚ) * ((logN k r : ℕ) : ℚ) = ((2 * sqPred k * r.2 * logN k r : ℕ) : ℚ) := by push_cast; ring
  rw [Cal.alphaC, logC_epsOf, epsOf_eq, sqPred_cast, div_div_eq_mul_div, div_mul_eq_mul_div, e, ceil_natCast_div, alphaN]

/-- **⌈ε·n⌉ without fractions**: ⌈min(a, b)·n / b⌉, for all r = (a, b) and n. -/
theorem ceil_epsOf_mul (r : ℕ × ℕ) (n : ℕ) : ⌈epsOf r * (n : ℚ)⌉₊ = ceilDiv (min r.1 r.2 * n) r.2 := by
  have e : ((min r.1 r.2 : ℕ) : ℚ) * (n : ℚ) = ((min r.1 r.2 * n : ℕ) : ℚ) := by push_cast; ring
  rw [epsOf_eq, div_mul_eq_mul_div, e, ceil_natCast_div]

/-! ### Finite sets as lists -/

/-- A sum over the numbers below k is the sum of a list. -/
theorem sum_range_eq_list (f : ℕ → ℕ) (k : ℕ) : ∑ j ∈ range k, f j = ((List.range k).map f).sum := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Finset.sum_range_succ, ih, List.range_succ, List.map_append, List.sum_append, List.map_singleton, List.sum_singleton]

/-- The bound on the occurrences as the sum of a list. -/
theorem occBound_eq (k : ℕ) (r : ℕ × ℕ) : occBound k r = 2 * ((List.range k).map (thresholds k r)).sum + 2 := by
  rw [occBound, sum_range_eq_list]

/-- A supremum over the members of a list is the maximum of a list. -/
theorem sup_toFinset_eq (f : ℕ → ℕ) (l : List ℕ) : l.toFinset.sup f = (l.map f).foldr max 0 := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.toFinset_cons, Finset.sup_insert, ih, List.map_cons, List.foldr_cons]

/-- The Δ of a formula as the maximum of a list. -/
theorem DeltaOf_eq (n : ℕ) (Φ : Groundwork.Sparsify.PFml) : SparsificationLemma.StepSparsify.DeltaOf n Φ = max 2 (((List.range n).map (occN Φ)).foldr max 0) := by
  rw [SparsificationLemma.StepSparsify.DeltaOf, ← List.toFinset_range, sup_toFinset_eq]

/-- The width of Step 5 as the maximum of a list. -/
theorem widthOr3F_eq (ψ : Groundwork.Prog.Fml) : widthOr3F ψ = max 3 ((ψ.map List.length).foldr max 0) := by
  rw [widthOr3F, SparsificationLemma.StepSparsify.widthOf, List.foldr_map]

/-! ### The maximum of numbers that may be missing -/

/-- The maximum computed from the right, where every number may be missing: it is missing if one of
the numbers is, and else it is the maximum of the list. -/
theorem foldr_bind_max (f : ℕ → Option ℕ) (l : List ℕ) :
    l.foldr (fun a o => o.bind fun v => (f a).map (max v)) (some 0) =
      if l.all (fun a => (f a).isSome) then some ((l.map fun a => (f a).getD 0).foldr max 0) else none := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.foldr_cons, ih]
    by_cases hc : l.all (fun a => (f a).isSome) = true <;> cases h : f a <;> simp [hc, h, max_comm]

/-- If every number is there, so is the maximum. -/
theorem foldr_bind_max_of_some {f : ℕ → Option ℕ} {g : ℕ → ℕ} {l : List ℕ} (h : ∀ a ∈ l, f a = some (g a)) :
    l.foldr (fun a o => o.bind fun v => (f a).map (max v)) (some 0) = some ((l.map g).foldr max 0) := by
  rw [foldr_bind_max, if_pos (List.all_eq_true.2 fun a ha => by rw [h a ha]; rfl)]
  congr 2
  exact List.map_congr_left fun a ha => by rw [h a ha]; rfl

/-- The maximum is missing only if one of the numbers is. -/
theorem exists_none_of_foldr_bind_max {f : ℕ → Option ℕ} {l : List ℕ} (h : l.foldr (fun a o => o.bind fun v => (f a).map (max v)) (some 0) = none) :
    ∃ a ∈ l, f a = none := by
  rw [foldr_bind_max] at h
  by_contra hc
  rw [if_pos (List.all_eq_true.2 fun a ha => ?_)] at h
  · exact Option.some_ne_none _ h
  · exact Option.isSome_iff_ne_none.2 fun hn => hc ⟨a, ha, hn⟩

/-- If the maximum is there, so is every number. -/
theorem isSome_of_foldr_bind_max {f : ℕ → Option ℕ} {l : List ℕ} {v : ℕ} (h : l.foldr (fun a o => o.bind fun v => (f a).map (max v)) (some 0) = some v) :
    ∀ a ∈ l, (f a).isSome = true := by
  rw [foldr_bind_max] at h
  split_ifs at h with hc
  exact List.all_eq_true.1 hc

end RecursionToBound
