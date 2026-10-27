/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import StepMachines.Prog.GridDefs
public import StepMachines.Prog.Chunks
public import Groundwork.Grid.Expand

/-! The patterns ι, functions from the rectangles to {0,…,n} (the ι of the proof of Proposition 3),
as numbers: the number y stands for the pattern that gives
rectangle number q the digit number q of y in base n+1. The rectangle on the rows a < b and the
columns i < i' has the
number tri a b · C(g,2) + tri i i'. -/

@[expose] public section

namespace Groundwork.Grid

open Finset
open Groundwork.Prog (digit nRect)

/-! ### Two digits in mixed radix -/

/-- x·n + y with y < n determines x and y. -/
theorem mixed_inj {n x x' y y' : ℕ} (hy : y < n) (hy' : y' < n) (h : x * n + y = x' * n + y') : x = x' ∧ y = y' := by
  have h1 : (x * n + y) / n = x := by
    rw [mul_comm, Nat.mul_add_div (by omega), Nat.div_eq_of_lt hy, add_zero]
  have h2 : (x' * n + y') / n = x' := by
    rw [mul_comm, Nat.mul_add_div (by omega), Nat.div_eq_of_lt hy', add_zero]
  have hx : x = x' := by rw [← h1, h, h2]
  subst hx
  exact ⟨rfl, by omega⟩

/-- x·n + y < m·n for x < m and y < n. -/
theorem mixed_lt {m n x y : ℕ} (hx : x < m) (hy : y < n) : x * n + y < m * n := by
  calc x * n + y < x * n + n := by omega
    _ = (x + 1) * n := by ring
    _ ≤ m * n := Nat.mul_le_mul_right _ hx

/-- Every number below m·n is x·n + y with x < m and y < n. -/
theorem mixed_surj {m n z : ℕ} (h : z < m * n) : ∃ x < m, ∃ y < n, x * n + y = z := by
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0; simp at h
    · exact h0
  exact ⟨z / n, (Nat.div_lt_iff_lt_mul hn).2 h, z % n, Nat.mod_lt _ hn, by rw [mul_comm]; exact Nat.div_add_mod z n⟩

/-! ### Numbering the rectangles -/

/-- The number of pairs a < b below g. -/
def c2 (g : ℕ) : ℕ := g * (g - 1) / 2

/-- The number of rectangles is the square of the number of pairs. -/
theorem nRect_eq (g : ℕ) : nRect g = c2 g * c2 g := by
  unfold nRect c2
  rw [Nat.choose_two_right, sq]

/-- There are at most g²/2 pairs. -/
theorem two_mul_c2_le (g : ℕ) : 2 * c2 g ≤ g ^ 2 := by
  calc 2 * (g * (g - 1) / 2) ≤ g * (g - 1) := Nat.mul_div_le _ _
    _ ≤ g * g := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
    _ = g ^ 2 := (sq g).symm

/-- The number of a rectangle, from the number p of its pair of parts (rows, or columns if tr) and
the number κ of its other
pair. -/
def rectIx (g : ℕ) (tr : Bool) (p κ : ℕ) : ℕ := if tr = true then κ * c2 g + p else p * c2 g + κ

/-- The number of a rectangle. -/
def ixOf (g : ℕ) (ω : Rect (Fin g) (Fin g)) : ℕ := tri ω.1.1 ω.1.2 * c2 g + tri ω.2.1 ω.2.2

/-- The rectangles get the numbers below nRect g, each number once. -/
theorem ixOf_bijOn (g : ℕ) : Set.BijOn (ixOf g) (Ω (Fin g) (Fin g)) (range (nRect g)) := by
  rw [nRect_eq]
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨⟨a, b⟩, ⟨i, i'⟩⟩ h
    simp only [Ω, coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at h
    simp only [coe_range, Set.mem_Iio, ixOf]
    exact mixed_lt (tri_lt (Fin.lt_def.1 h.1) b.2) (tri_lt (Fin.lt_def.1 h.2) i'.2)
  · rintro ⟨⟨a, b⟩, ⟨i, i'⟩⟩ h ⟨⟨a₂, b₂⟩, ⟨i₂, i₂'⟩⟩ h₂ heq
    simp only [Ω, coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at h h₂
    simp only [ixOf] at heq
    obtain ⟨e1, e2⟩ := mixed_inj (n := c2 g) (tri_lt (Fin.lt_def.1 h.2) i'.2) (tri_lt (Fin.lt_def.1 h₂.2) i₂'.2) heq
    obtain ⟨e3, e4⟩ := tri_inj (Fin.lt_def.1 h.1) (Fin.lt_def.1 h₂.1) e1
    obtain ⟨e5, e6⟩ := tri_inj (Fin.lt_def.1 h.2) (Fin.lt_def.1 h₂.2) e2
    rw [Fin.ext e3, Fin.ext e4, Fin.ext e5, Fin.ext e6]
  · intro z hz
    simp only [coe_range, Set.mem_Iio] at hz
    obtain ⟨x, hx, y, hy, rfl⟩ := mixed_surj hz
    obtain ⟨a, b, hab, hb, rfl⟩ := tri_surj (K := g) hx
    obtain ⟨i, i', hii, hi', rfl⟩ := tri_surj (K := g) hy
    refine ⟨((⟨a, by omega⟩, ⟨b, hb⟩), (⟨i, by omega⟩, ⟨i', hi'⟩)), ?_, rfl⟩
    simp only [Ω, coe_filter, mem_univ, true_and, Set.mem_ofPred_eq, Fin.lt_def]
    exact ⟨hab, hii⟩

/-- The pairs i < i' below g are numbered 0, …, c2 g − 1 by tri, each number once. -/
theorem tri_bijOn (g : ℕ) : Set.BijOn (fun k : Fin g × Fin g => tri k.1 k.2) {k | k.1 < k.2} (range (c2 g)) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨i, i'⟩ h
    simp only [Set.mem_ofPred_eq] at h
    simp only [coe_range, Set.mem_Iio]
    exact tri_lt (Fin.lt_def.1 h) i'.2
  · rintro ⟨i, i'⟩ h ⟨i₂, i₂'⟩ h₂ heq
    simp only [Set.mem_ofPred_eq] at h h₂
    obtain ⟨e1, e2⟩ := tri_inj (Fin.lt_def.1 h) (Fin.lt_def.1 h₂) heq
    rw [Fin.ext e1, Fin.ext e2]
  · intro z hz
    simp only [coe_range, Set.mem_Iio] at hz
    obtain ⟨i, i', hii, hi', rfl⟩ := tri_surj (K := g) hz
    exact ⟨(⟨i, by omega⟩, ⟨i', hi'⟩), Fin.lt_def.2 hii, rfl⟩

/-- A digit in base n + 1 is at most n. -/
theorem digit_le (n y q : ℕ) : digit n y q ≤ n := by
  exact Prog.digit_le n y q

/-- The pattern written by the number y: a rectangle gets the digit of y in base n + 1 at its
number. -/
def patOf (g n y : ℕ) : Rect (Fin g) (Fin g) → ℕ :=
  fun ω => if ω ∈ Ω (Fin g) (Fin g) then digit n y (ixOf g ω) else 0

/-- Summing over the numbers y < (n+1)^(nRect g) is summing over the patterns. -/
theorem sum_patOf (g n : ℕ) (F : (Rect (Fin g) (Fin g) → ℕ) → ℤ) :
    ∑ y ∈ range ((n + 1) ^ nRect g), F (patOf g n y) = ∑ ι ∈ Pat (Fin g) (Fin g) n, F ι := by
  have hlt : ∀ ω ∈ Ω (Fin g) (Fin g), ixOf g ω < nRect g := fun ω hω =>
    Finset.mem_range.1 (Finset.mem_coe.1 ((ixOf_bijOn g).mapsTo (Finset.mem_coe.2 hω)))
  -- a function of the numbers of the rectangles, read as a function of the rectangles
  set E : (Fin (nRect g) → ℕ) → Rect (Fin g) (Fin g) → ℕ :=
    fun φ ω => if h : ω ∈ Ω (Fin g) (Fin g) then φ ⟨ixOf g ω, hlt ω h⟩ else 0 with hE
  have h1 : ∀ y, patOf g n y = E fun q => digit n y q := by
    intro y
    funext ω
    simp only [patOf, hE]
    split_ifs <;> rfl
  have hs : ∀ q : Fin (nRect g), ∃ ω ∈ Ω (Fin g) (Fin g), ixOf g ω = q := fun q => by
    obtain ⟨ω, hω, hq⟩ := (ixOf_bijOn g).surjOn (Finset.mem_coe.2 (Finset.mem_range.2 q.2))
    exact ⟨ω, Finset.mem_coe.1 hω, hq⟩
  choose inv hinv1 hinv2 using hs
  simp only [h1]
  rw [Prog.sum_digits n (nRect g) fun φ => F (E φ)]
  refine Finset.sum_nbij E ?_ ?_ ?_ fun _ _ => rfl
  · intro φ hφ
    rw [Pat, mem_tuples]
    refine fun ω => ⟨fun h => ?_, fun h => ?_⟩
    · simp only [hE, dif_pos h]
      exact Fintype.mem_piFinset.1 hφ _
    · simp only [hE, dif_neg h]
  · intro φ _ φ' _ heq
    funext q
    have h2 := congrFun heq (inv q)
    simp only [hE, dif_pos (hinv1 q)] at h2
    have hq : (⟨ixOf g (inv q), hlt _ (hinv1 q)⟩ : Fin (nRect g)) = q := Fin.ext (hinv2 q)
    rwa [hq] at h2
  · intro ι hι
    have hι' := (mem_tuples _ _ _ _).1 (Finset.mem_coe.1 hι)
    refine ⟨fun q => ι (inv q), Finset.mem_coe.2 (Fintype.mem_piFinset.2 fun q => (hι' (inv q)).1 (hinv1 q)), ?_⟩
    funext ω
    by_cases h : ω ∈ Ω (Fin g) (Fin g)
    · simp only [hE, dif_pos h]
      exact congrArg ι ((ixOf_bijOn g).injOn (Finset.mem_coe.2 (hinv1 _)) (Finset.mem_coe.2 h) (hinv2 _))
    · simp only [hE, dif_neg h]
      exact ((hι' ω).2 h).symm

/-- A sum over the rectangles is the sum over their numbers. -/
theorem sum_Ω_ixOf (g : ℕ) (f : ℕ → ℕ) : ∑ ω ∈ Ω (Fin g) (Fin g), f (ixOf g ω) = ∑ q ∈ range (nRect g), f q := by
  exact Finset.sum_nbij (ixOf g) (fun ω hω => Finset.mem_coe.1 ((ixOf_bijOn g).mapsTo (Finset.mem_coe.2 hω)))
    (ixOf_bijOn g).injOn (ixOf_bijOn g).surjOn fun _ _ => rfl

/-- ZG reads the functions G at the rectangles only. -/
theorem ZG_congr {ρ γ α : Type} [Fintype ρ] [LinearOrder ρ] [Fintype γ] [LinearOrder γ] [Fintype α] [DecidableEq α]
    (R : Inst (ρ × γ) α) {G G' : Rect ρ γ → α → α → α → α → ℤ} (h : ∀ ω ∈ Ω ρ γ, G ω = G' ω) : ZG R G = ZG R G' := by
  unfold ZG
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  rw [Finset.prod_congr rfl fun ω hω => show app (G ω) ℓ ω = app (G' ω) ℓ ω by rw [h ω hω]]

end Groundwork.Grid
