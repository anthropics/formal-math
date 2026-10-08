/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Spec.Sec3.Problems

/-!
# Finding a negative triangle by halving

[VW18, Lemma 4.1], one of the reductions behind Theorem 21(b): an algorithm that
decides whether a graph has a negative triangle also finds one.  The search keeps three offsets and
a side length `h` such that the `h × h × h` sub-instance at these offsets has a negative triangle
(`NegAt`), and replaces `h` by `⌈h/2⌉`.

* The sub-instance is an instance of its own, made of three blocks of the matrices (`subMat`,
  `hasNegativeTriangle_subMat_iff`), so the decision algorithm can be asked about it.
* Each of the three ranges `[o, o + h)` is covered by its two halves `[o, o + ⌈h/2⌉)` and
  `[o + h - ⌈h/2⌉, o + h)`, which overlap in one place if `h` is odd.  So one of the eight triples
  of halves (`octants`) has a negative triangle (`NegAt.split`).
* At side length 1 the sub-instance is the triangle (`NegAt.triangle`).
* The side lengths `⌈n/2⌉, ⌈⌈n/2⌉/2⌉, …, 1` that the search goes through (`halvingChain`) add up to
  at most `2n` (`sum_halvingChain_le`).
-/

@[expose] public section

namespace ThreeSumApsp.Spec

/-! ## Sub-instances -/

/-- The sub-instance on the vertices `a0 + a`, `b0 + b`, `c0 + c` with `a, b, c < h` has a negative
triangle. -/
def NegAt (n : ℕ) (AB BC AC : List ℤ) (a0 b0 c0 h : ℕ) : Prop :=
  ∃ a < h, ∃ b < h, ∃ c < h,
    entry n AB (a0 + a) (b0 + b) + entry n BC (b0 + b) (c0 + c) +
      entry n AC (a0 + a) (c0 + c) < 0

/-- A negative triangle of an instance read from three lists, with the vertices as numbers. -/
private theorem hasNegativeTriangle_triOf_iff (h : ℕ) (AB BC AC : List ℤ) :
    (triOf h AB BC AC).HasNegativeTriangle ↔ ∃ a < h, ∃ b < h, ∃ c < h,
      entry h AB a b + entry h BC b c + entry h AC a c < 0 :=
  ⟨fun ⟨a, b, c, hS⟩ => ⟨a, a.2, b, b.2, c, c.2, hS⟩,
    fun ⟨a, ha, b, hb, c, hc, hS⟩ => ⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩, hS⟩⟩

/-- The instance made of the three blocks has a negative triangle if and only if the sub-instance
has one. -/
theorem hasNegativeTriangle_subMat_iff (n : ℕ) (AB BC AC : List ℤ) (a0 b0 c0 h : ℕ) :
    (triOf h (subMat n h a0 b0 AB) (subMat n h b0 c0 BC)
      (subMat n h a0 c0 AC)).HasNegativeTriangle ↔ NegAt n AB BC AC a0 b0 c0 h := by
  rw [hasNegativeTriangle_triOf_iff, NegAt]
  constructor <;> rintro ⟨a, ha, b, hb, c, hc, hS⟩ <;> refine ⟨a, ha, b, hb, c, hc, ?_⟩ <;>
    simpa only [entry_subMat ha hb, entry_subMat hb hc, entry_subMat ha hc] using hS

/-- The whole instance is the sub-instance at the offsets 0 with side `n`. -/
theorem hasNegativeTriangle_iff_negAt (n : ℕ) (AB BC AC : List ℤ) :
    (triOf n AB BC AC).HasNegativeTriangle ↔ NegAt n AB BC AC 0 0 0 n := by
  simp only [hasNegativeTriangle_triOf_iff, NegAt, Nat.zero_add]

/-- A sub-instance of side 1 that has a negative triangle is a negative triangle. -/
theorem NegAt.triangle {n : ℕ} {AB BC AC : List ℤ} {a0 b0 c0 : ℕ}
    (h : NegAt n AB BC AC a0 b0 c0 1) (ha : a0 < n) (hb : b0 < n) (hc : c0 < n) :
    (triOf n AB BC AC).S ⟨a0, ha⟩ ⟨b0, hb⟩ ⟨c0, hc⟩ < 0 := by
  obtain ⟨a, ha', b, hb', c, hc', hS⟩ := h
  obtain rfl : a = 0 := by omega
  obtain rfl : b = 0 := by omega
  obtain rfl : c = 0 := by omega
  simpa only [TriangleInstance.S, triOf, Nat.add_zero] using hS

/-! ## The step of the search -/

/-- The eight triples of halves: 0 stands for the lower half of a range and 1 for the upper
half. -/
def octants : List (ℕ × ℕ × ℕ) :=
  [(0, 0, 0), (0, 0, 1), (0, 1, 0), (0, 1, 1), (1, 0, 0), (1, 0, 1), (1, 1, 0), (1, 1, 1)]

/-- The entries of an octant are 0 or 1. -/
theorem le_one_of_mem_octants {t : ℕ × ℕ × ℕ} (ht : t ∈ octants) :
    t.1 ≤ 1 ∧ t.2.1 ≤ 1 ∧ t.2.2 ≤ 1 := by
  simp only [octants, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

/-- A number below `h` lies in the lower or in the upper half of `[0, h)`. -/
private theorem exists_half {h h' a : ℕ} (ha : a < h) (hle : h' ≤ h) (hhalf : h ≤ 2 * h') :
    ∃ x a', (x = 0 ∨ x = 1) ∧ a' < h' ∧ a = x * (h - h') + a' := by
  by_cases hlow : a < h'
  · exact ⟨0, a, Or.inl rfl, hlow, by simp⟩
  · exact ⟨1, a - (h - h'), Or.inr rfl, by omega, by omega⟩

/-- **The step of the search.**  If the sub-instance of side `h` has a negative triangle and
`h/2 ≤ h' ≤ h`, then so has one of the eight sub-instances of side `h'` made of lower and upper
halves. -/
theorem NegAt.split {n : ℕ} {AB BC AC : List ℤ} {a0 b0 c0 h h' : ℕ}
    (hn : NegAt n AB BC AC a0 b0 c0 h) (hle : h' ≤ h) (hhalf : h ≤ 2 * h') :
    ∃ t ∈ octants, NegAt n AB BC AC (a0 + t.1 * (h - h')) (b0 + t.2.1 * (h - h'))
      (c0 + t.2.2 * (h - h')) h' := by
  obtain ⟨a, ha, b, hb, c, hc, hS⟩ := hn
  obtain ⟨x, a', hx, ha', rfl⟩ := exists_half ha hle hhalf
  obtain ⟨y, b', hy, hb', rfl⟩ := exists_half hb hle hhalf
  obtain ⟨z, c', hz, hc', rfl⟩ := exists_half hc hle hhalf
  refine ⟨(x, y, z), ?_, a', ha', b', hb', c', hc', ?_⟩
  · rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> rcases hz with rfl | rfl <;>
      simp [octants]
  · simpa only [Nat.add_assoc] using hS

/-! ## The chain of side lengths -/

/-- The side lengths after `n`: `⌈n/2⌉`, then `⌈⌈n/2⌉/2⌉`, and so on down to 1.  Empty for `n ≤ 1`.
-/
def halvingChain (n : ℕ) : List ℕ :=
  if 2 ≤ n then (n + 1) / 2 :: halvingChain ((n + 1) / 2) else []
termination_by n
decreasing_by omega

/-- The chain is empty for `n ≤ 1`. -/
theorem halvingChain_of_lt {n : ℕ} (h : n < 2) : halvingChain n = [] := by
  rw [halvingChain, if_neg (by omega)]

/-- The chain starts with `⌈n/2⌉` for `n ≥ 2`. -/
theorem halvingChain_of_le {n : ℕ} (h : 2 ≤ n) :
    halvingChain n = (n + 1) / 2 :: halvingChain ((n + 1) / 2) := by
  rw [halvingChain, if_pos h]

/-- Every side length of the chain is at least 1 and smaller than `n`. -/
theorem bounds_of_mem_halvingChain {n h : ℕ} (hh : h ∈ halvingChain n) : 1 ≤ h ∧ h < n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hn : 2 ≤ n
    · rw [halvingChain_of_le hn, List.mem_cons] at hh
      rcases hh with rfl | hh
      · omega
      · have := ih _ (by omega) hh
        omega
    · rw [halvingChain_of_lt (by omega)] at hh
      exact absurd hh List.not_mem_nil

/-- The side lengths of the chain add up to at most `2n` (to at most `2n - 2`, for `n ≥ 1`). -/
theorem sum_halvingChain_le (n : ℕ) : (halvingChain n).sum ≤ 2 * n := by
  suffices h : ∀ n, 1 ≤ n → (halvingChain n).sum + 2 ≤ 2 * n by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [halvingChain_of_lt]
    · exact (Nat.le_add_right _ 2).trans (h n hn)
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn1
    by_cases hn : 2 ≤ n
    · -- With `m = ⌈n/2⌉` the sum is `m` plus at most `2m - 2`, and `3m ≤ 2n` for `n ≥ 2`.
      have hrest := ih ((n + 1) / 2) (by omega) (by omega)
      rw [halvingChain_of_le hn, List.sum_cons]
      omega
    · rw [halvingChain_of_lt (by omega), List.sum_nil]
      omega

end ThreeSumApsp.Spec
