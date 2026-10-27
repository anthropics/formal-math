/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import CountedRecursion.SolverCall
import Mathlib.Tactic

/-! # The room of the solver

«each of the following takes at most Ξ^{C₃} operations …»: here the sizes. Everything that the
solver of the level ℓ + 1 holds (ℓ, λ, B, K and g in unary; the list of 𝓘, d, the numbers c^row_i,
c^col_i; the number of a pattern; the sum of the Z_ι; the context of a call) has size at most a
power of Ξ = g²(λ + B) whose exponent depends on c only (and on the constants of the loop for K and
g and of the lemma on groupings).
* `pw_add`, `pw_mul`, `pw_num`, `pw_pow`, `pw_up`: sums, products, constants and powers of numbers
  that are at most powers of X ≥ 2.
* `room_arith`: the arithmetic, for plain numbers.
* `solver_room`: the bound for the solver. -/

public section

namespace ExplicitCost

open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed

/-- A sum of two numbers that are at most powers of X ≥ 2. -/
theorem pw_add {X a b i j : ℕ} (hX : 2 ≤ X) (ha : a ≤ X ^ i) (hb : b ≤ X ^ j) : a + b ≤ X ^ (i + j + 1) := by
  have h1 : X ^ i ≤ X ^ (i + j) := Nat.pow_le_pow_right (by omega) (by omega)
  have h2 : X ^ j ≤ X ^ (i + j) := Nat.pow_le_pow_right (by omega) (by omega)
  have h3 : 2 * X ^ (i + j) ≤ X * X ^ (i + j) := Nat.mul_le_mul_right _ hX
  have e : X ^ (i + j + 1) = X * X ^ (i + j) := by rw [pow_succ, mul_comm]
  rw [e]
  omega

/-- A product of two numbers that are at most powers of X. -/
theorem pw_mul {X a b i j : ℕ} (ha : a ≤ X ^ i) (hb : b ≤ X ^ j) : a * b ≤ X ^ (i + j) := by
  rw [pow_add]
  exact Nat.mul_le_mul ha hb

/-- n ≤ X^n for X ≥ 2. -/
theorem pw_num {X : ℕ} (hX : 2 ≤ X) (n : ℕ) : n ≤ X ^ n := Nat.lt_two_pow_self.le.trans (Nat.pow_le_pow_left hX n)

/-- A power of a number that is at most a power of X. -/
theorem pw_pow {X a i : ℕ} (ha : a ≤ X ^ i) (k : ℕ) : a ^ k ≤ X ^ (i * k) := by
  rw [pow_mul]
  exact Nat.pow_le_pow_left ha k

/-- A larger exponent. -/
theorem pw_up {X a i j : ℕ} (hX : 2 ≤ X) (ha : a ≤ X ^ i) (h : i ≤ j) : a ≤ X ^ j := ha.trans (Nat.pow_le_pow_right (by omega) h)

/-- The arithmetic of the sizes. -/
theorem room_arith (c Cn Cg : ℕ) : ∃ C : ℕ, ∀ X g K p l lam B m n A : ℕ, 2 ≤ X → g * g ≤ X → K ≤ g → p ≤ g → l ≤ g → 2 * lam ≤ X → B ≤ X → m ≤ X ^ c → n ≤ m → A ≤ X ^ (c + 4) →
    20 * (Cn * g + (2 * l + 2 * lam + 2 * B + 2 * p + 2 * K + (n * (m + 2) + 1) + (m + 1) + 2 * (n * (2 * lam + 2) + 1) + 9) + (X * (c * g ^ 4) + 2) + (X * (c * g ^ 4) + (A + g * A) + 2) + (A + (l + 9)) ^ Cg +
      (A + g * A) + (K * g + 2) + g + A + (g ^ 4 * lam + g * A) + 4) ≤ X ^ C := by
  apply Exists.intro
  intro X g K p l lam B m n A hX hgg hK hp hl hlam hB hm hn hA
  have hXX : X ≤ X ^ 1 := (pow_one X).ge
  have hg : g ≤ X ^ 1 := ((Nat.le_mul_self g).trans hgg).trans hXX
  have hKx := hK.trans hg
  have hpx := hp.trans hg
  have hlx := hl.trans hg
  have h2lam := hlam.trans hXX
  have hlamx : lam ≤ X ^ 1 := le_trans (by omega) h2lam
  have hBx := hB.trans hXX
  have hnx := hn.trans hm
  have hg4 : g ^ 4 ≤ X ^ 2 := by
    calc g ^ 4 = (g * g) * (g * g) := by ring
      _ ≤ X * X := Nat.mul_le_mul hgg hgg
      _ = X ^ 2 := (sq X).symm
  have u6 := pw_add hX (pw_mul hnx (pw_add hX hm (pw_num hX 2))) (pw_num hX 1)
  have u7 := pw_add hX hm (pw_num hX 1)
  have u8 := pw_mul (pw_num hX 2) (pw_add hX (pw_mul hnx (pw_add hX h2lam (pw_num hX 2))) (pw_num hX 1))
  have t2 := pw_add hX (pw_add hX (pw_add hX (pw_add hX (pw_add hX (pw_add hX (pw_add hX (pw_add hX (pw_mul (pw_num hX 2) hlx) h2lam) (pw_mul (pw_num hX 2) hBx)) (pw_mul (pw_num hX 2) hpx)) (pw_mul (pw_num hX 2) hKx)) u6) u7) u8) (pw_num hX 9)
  have e0 := pw_mul hXX (pw_mul (pw_num hX c) hg4)
  have gA := pw_mul hg hA
  have G := pw_add hX hA gA
  have t5 := pw_pow (pw_add hX hA (pw_add hX hlx (pw_num hX 9))) Cg
  exact pw_mul (pw_num hX 20) (pw_add hX (pw_add hX (pw_add hX (pw_add hX (pw_add hX (pw_add hX (pw_add hX (pw_add hX (pw_add hX (pw_add hX (pw_mul (pw_num hX Cn) hg) t2) (pw_add hX e0 (pw_num hX 2)))
    (pw_add hX (pw_add hX e0 G) (pw_num hX 2))) t5) G) (pw_add hX (pw_mul hKx hg) (pw_num hX 2))) hg) hA) (pw_add hX (pw_mul hg4 hlamx) gA)) (pw_num hX 4))

/-! ### Sizes of numbers and lists -/

/-- A number n ≤ 2^k has size at most k + 2. -/
theorem size_of_le_two_pow {n k : ℕ} (h : n ≤ 2 ^ k) : size n ≤ k + 2 :=
  Nat.succ_le_succ (Nat.size_le.2 (h.trans_lt (Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self k))))

/-- X^e ≤ 2^{Xe}. -/
theorem pow_le_two_pow (X e : ℕ) : X ^ e ≤ 2 ^ (X * e) := by
  rw [pow_mul]
  exact Nat.pow_le_pow_left Nat.lt_two_pow_self.le e

/-- An integer below 2^m in absolute value has size at most m + 1. -/
theorem size_of_abs_lt {v : ℤ} {m : ℕ} (h : |v| < 2 ^ m) : size v ≤ m + 1 := by
  rw [size_int]
  refine Nat.succ_le_succ (Nat.size_le.2 ?_)
  have h1 : (v.natAbs : ℤ) < 2 ^ m := by rwa [Int.natCast_natAbs]
  exact_mod_cast h1

/-- A list of k elements, each of size below s, has size at most ks + 1. -/
theorem size_of_elements {α : Type} [HasSize α] (l : List α) (s : ℕ) (h : ∀ x ∈ l, size x + 1 ≤ s) : size l ≤ l.length * s + 1 := by
  induction l with
  | nil => simp [size_list]
  | cons y l ih =>
    have h1 := ih fun x hx => h x (List.mem_cons_of_mem _ hx)
    have h2 := h y List.mem_cons_self
    simp only [size_list, List.map_cons, List.sum_cons, List.length_cons] at h1 ⊢
    have e : (l.length + 1) * s = l.length * s + s := by ring
    rw [e]
    omega

/-- **The room of the solver**, and the two small counts: one exponent for all, which depends on c,
Cn, Cg only. -/
theorem solver_room (hFew : PatternsFew) (hCr : CrudeBounds) (c Cn Cg : ℕ) : ∃ C : ℕ, ∀ (ρ : ℝ) (x₀ : ℕ) (D : PiecesCounted.Data), Setting ρ c x₀ D → ∀ (a : Ctx) (l : ℕ), 1 ≤ cLam a → 1 ≤ cB a → cLev a = l + 1 →
    20 * (Cn * Levels.Gen.g x₀ l + size (readyOf D x₀ a.1) + size (nPatterns (readyOf D x₀ a.1)) + size (nPatterns (readyOf D x₀ a.1) * 2 ^ (Levels.Gen.g x₀ l * (Levels.Gen.g x₀ l ^ 3 * cLam a) + Levels.Gen.g x₀ l * Levels.Gen.g x₀ l * (bitsOne c (Levels.Gen.g x₀ l) (cLam a) (cB a)))) + (Levels.Gen.g x₀ l * ((Levels.Gen.g x₀ l ^ 3 * cLam a) + (bitsOne c (Levels.Gen.g x₀ l) (cLam a) (cB a))) + size ((1 : ℕ), 2 ^ (l + 5))) ^ Cg + (Levels.Gen.g x₀ l * (Levels.Gen.g x₀ l ^ 3 * cLam a) + Levels.Gen.g x₀ l * Levels.Gen.g x₀ l * (bitsOne c (Levels.Gen.g x₀ l) (cLam a) (cB a))) + size (Levels.Gen.K x₀ l ^ Levels.Gen.g x₀ l) + Levels.Gen.g x₀ l + Levels.Gen.g x₀ l * (Levels.Gen.g x₀ l ^ 3 * cLam a) + bitsOut (Levels.Gen.K x₀ l) (Levels.Gen.g x₀ l) (Levels.Gen.g x₀ l ^ 3 * cLam a) (bitsOne c (Levels.Gen.g x₀ l) (cLam a) (cB a)) + 4) ≤ Xi (Levels.Gen.g x₀ l) (cLam a) (cB a) ^ C ∧
    Cg + 3 ≤ Xi (Levels.Gen.g x₀ l) (cLam a) (cB a) ^ C ∧ 2 * l + 7 + 2 * #(D.fam (cLam a)).I ≤ Xi (Levels.Gen.g x₀ l) (cLam a) (cB a) ^ C := by
  obtain ⟨C, hC⟩ := room_arith c Cn Cg
  refine ⟨C + (Cg + 3) + (2 + 1 + 7 + 1 + (2 + c) + 1), fun ρ x₀ D hS a l hlam hB hl => ?_⟩
  have hx := hS.x₀_ge
  have hK2 := two_le_K (by omega : 1 ≤ x₀) l
  have hKg := K_le_g x₀ l
  have hp : 2 ^ (3 * l + x₀) ≤ Levels.Gen.g x₀ l := Nat.le_mul_of_pos_right _ (by omega)
  have hlg : l ≤ Levels.Gen.g x₀ l := (Nat.lt_two_pow_self.le.trans (Nat.pow_le_pow_right (by norm_num) (by omega))).trans hp
  have hgg : Levels.Gen.g x₀ l * Levels.Gen.g x₀ l ≤ Xi (Levels.Gen.g x₀ l) (cLam a) (cB a) := by
    calc Levels.Gen.g x₀ l * Levels.Gen.g x₀ l = Levels.Gen.g x₀ l ^ 2 * 1 := by ring
      _ ≤ Levels.Gen.g x₀ l ^ 2 * (cLam a + cB a) := Nat.mul_le_mul_left _ (by omega)
  have h4 : 2 * 2 ≤ Levels.Gen.g x₀ l * Levels.Gen.g x₀ l := Nat.mul_le_mul (by omega) (by omega)
  have hX : 2 ≤ Xi (Levels.Gen.g x₀ l) (cLam a) (cB a) := by omega
  have h2lam : 2 * cLam a ≤ Xi (Levels.Gen.g x₀ l) (cLam a) (cB a) := by
    calc 2 * cLam a ≤ Levels.Gen.g x₀ l ^ 2 * cLam a := Nat.mul_le_mul_right _ (by rw [sq]; omega)
      _ ≤ Levels.Gen.g x₀ l ^ 2 * (cLam a + cB a) := Nat.mul_le_mul_left _ (by omega)
  have hBX : cB a ≤ Xi (Levels.Gen.g x₀ l) (cLam a) (cB a) := by
    calc cB a ≤ Levels.Gen.g x₀ l ^ 2 * cB a := Nat.le_mul_of_pos_left _ (by rw [sq]; omega)
      _ ≤ Levels.Gen.g x₀ l ^ 2 * (cLam a + cB a) := Nat.mul_le_mul_left _ (by omega)
  have hm : (2 * cLam a) ^ c ≤ Xi (Levels.Gen.g x₀ l) (cLam a) (cB a) ^ c := Nat.pow_le_pow_left h2lam c
  have hn : #(D.fam (cLam a)).I ≤ (2 * cLam a) ^ c := hS.is.card _ hlam
  obtain ⟨hB', hA, -⟩ := hCr c x₀ l (cLam a) (cB a) 0 hx hlam hB (Nat.zero_le _)
  have hXX : Xi (Levels.Gen.g x₀ l) (cLam a) (cB a) ≤ Xi (Levels.Gen.g x₀ l) (cLam a) (cB a) ^ 1 := (pow_one _).ge
  refine ⟨?_, pw_up hX (pw_num hX (Cg + 3)) (by omega), pw_up hX (pw_add hX (pw_add hX (pw_mul (pw_num hX 2) ((hlg.trans ((Nat.le_mul_self _).trans hgg)).trans hXX)) (pw_num hX 7)) (pw_mul (pw_num hX 2) (hn.trans hm))) (by omega)⟩
  refine le_trans ?_ (pw_up hX (hC _ _ _ _ l _ _ _ _ _ hX hgg hKg hp hlg h2lam hBX hm hn hA) (by omega))
  refine Nat.mul_le_mul_left 20 ?_
  -- what the solver holds
  have s3 : size (readyOf D x₀ a.1) = size a.1.1 + (size a.1.2.1 + size a.1.2.2) + (size (unary (2 ^ (3 * (hLev a.1 - 1) + x₀))) + size (unary (Levels.Gen.K x₀ (hLev a.1 - 1)))) + size (listsOf D (cLam a)).1 +
      size (D.fam (cLam a)).d + size (listsOf D (cLam a)).2.1 + size (listsOf D (cLam a)).2.2 := rfl
  have s5 : hLev a.1 - 1 = l := by
    have : hLev a.1 = l + 1 := hl
    omega
  rw [s5, size_units, size_units, size_units, size_unary', size_unary'] at s3
  have s6 : a.1.2.1.length = cLam a := rfl
  have s7 : a.1.2.2.length = cB a := rfl
  have s8 : a.1.1.length = l + 1 := hl
  have sI : size (listsOf D (cLam a)).1 ≤ #(D.fam (cLam a)).I * ((2 * cLam a) ^ c + 2) + 1 := by
    have h := size_of_elements ((D.fam (cLam a)).I.sort) ((2 * cLam a) ^ c + 2) fun i hi => by
      have := size_of_abs_lt (hS.is.size_I _ hlam i ((Finset.mem_sort _).1 hi))
      omega
    rwa [Finset.length_sort] at h
  have sd : size (D.fam (cLam a)).d ≤ (2 * cLam a) ^ c + 1 := size_of_abs_lt (by
    rw [abs_of_pos (by have := hS.is.d_pos _ hlam; omega)]
    exact hS.is.size_d _ hlam)
  have sc : ∀ tr : Bool, size (((D.fam (cLam a)).I.sort).map fun i => D.cap (cLam a) tr i) ≤ #(D.fam (cLam a)).I * (2 * cLam a + 2) + 1 := fun tr => by
    have h := size_of_elements (((D.fam (cLam a)).I.sort).map fun i => D.cap (cLam a) tr i) (2 * cLam a + 2) fun x hx => by
      obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
      have h1 := size_le_of_le (hS.short (cLam a) tr i)
      have h2 := size_le_succ (2 * cLam a)
      omega
    rwa [List.length_map, Finset.length_sort] at h
  have sc0 : size (listsOf D (cLam a)).2.1 ≤ #(D.fam (cLam a)).I * (2 * cLam a + 2) + 1 := sc false
  have sc1 : size (listsOf D (cLam a)).2.2 ≤ #(D.fam (cLam a)).I * (2 * cLam a + 2) + 1 := sc true
  -- the number of patterns
  have hnP : nPatterns (readyOf D x₀ a.1) ≤ 2 ^ (Xi (Levels.Gen.g x₀ l) (cLam a) (cB a) * (c * Levels.Gen.g x₀ l ^ 4)) := by
    rw [nPatterns_ready D x₀ a.1 hl]
    exact ((Nat.le_self_pow (by norm_num) _).trans (hFew ρ c x₀ D hS (Levels.Gen.g x₀ l) (cLam a) (cB a) (by omega) hlam hB).2).trans (pow_le_two_pow _ _)
  have sP := size_of_le_two_pow hnP
  have hgP : Levels.Gen.g x₀ l * (Levels.Gen.g x₀ l ^ 3 * cLam a) ≤ (Levels.Gen.g x₀ l * ((Levels.Gen.g x₀ l ^ 3 * cLam a) + (bitsOne c (Levels.Gen.g x₀ l) (cLam a) (cB a)))) := Nat.mul_le_mul_left _ (Nat.le_add_right _ _)
  have hgB : Levels.Gen.g x₀ l * Levels.Gen.g x₀ l * (bitsOne c (Levels.Gen.g x₀ l) (cLam a) (cB a)) ≤ Levels.Gen.g x₀ l * (Levels.Gen.g x₀ l * ((Levels.Gen.g x₀ l ^ 3 * cLam a) + (bitsOne c (Levels.Gen.g x₀ l) (cLam a) (cB a)))) := by
    rw [Nat.mul_assoc]
    exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.le_add_left _ _))
  have sV : size (nPatterns (readyOf D x₀ a.1) * 2 ^ (Levels.Gen.g x₀ l * (Levels.Gen.g x₀ l ^ 3 * cLam a) + Levels.Gen.g x₀ l * Levels.Gen.g x₀ l * (bitsOne c (Levels.Gen.g x₀ l) (cLam a) (cB a)))) ≤ Xi (Levels.Gen.g x₀ l) (cLam a) (cB a) * (c * Levels.Gen.g x₀ l ^ 4) + ((Levels.Gen.g x₀ l * ((Levels.Gen.g x₀ l ^ 3 * cLam a) + (bitsOne c (Levels.Gen.g x₀ l) (cLam a) (cB a)))) + Levels.Gen.g x₀ l * (Levels.Gen.g x₀ l * ((Levels.Gen.g x₀ l ^ 3 * cLam a) + (bitsOne c (Levels.Gen.g x₀ l) (cLam a) (cB a))))) + 2 := size_of_le_two_pow
    ((Nat.mul_le_mul hnP (Nat.pow_le_pow_right (by norm_num) (by omega))).trans (pow_add 2 (Xi (Levels.Gen.g x₀ l) (cLam a) (cB a) * (c * Levels.Gen.g x₀ l ^ 4)) ((Levels.Gen.g x₀ l * ((Levels.Gen.g x₀ l ^ 3 * cLam a) + (bitsOne c (Levels.Gen.g x₀ l) (cLam a) (cB a)))) + Levels.Gen.g x₀ l * (Levels.Gen.g x₀ l * ((Levels.Gen.g x₀ l ^ 3 * cLam a) + (bitsOne c (Levels.Gen.g x₀ l) (cLam a) (cB a)))))).ge)
  have sK : size (Levels.Gen.K x₀ l ^ Levels.Gen.g x₀ l) ≤ Levels.Gen.K x₀ l * Levels.Gen.g x₀ l + 2 := size_of_le_two_pow (pow_le_two_pow _ _)
  have sz : size ((1 : ℕ), 2 ^ (l + 5)) ≤ l + 9 := by
    have h1 : size ((1 : ℕ), 2 ^ (l + 5)) = size (1 : ℕ) + size (2 ^ (l + 5)) := rfl
    have h2 := size_le_succ 1
    have h3 := size_of_le_two_pow (le_refl (2 ^ (l + 5)))
    omega
  have sg : (Levels.Gen.g x₀ l * ((Levels.Gen.g x₀ l ^ 3 * cLam a) + (bitsOne c (Levels.Gen.g x₀ l) (cLam a) (cB a))) + size ((1 : ℕ), 2 ^ (l + 5))) ^ Cg ≤ ((Levels.Gen.g x₀ l * ((Levels.Gen.g x₀ l ^ 3 * cLam a) + (bitsOne c (Levels.Gen.g x₀ l) (cLam a) (cB a)))) + (l + 9)) ^ Cg := Nat.pow_le_pow_left (by omega) _
  have hB2 : Levels.Gen.g x₀ l ^ 2 * (bitsOne c (Levels.Gen.g x₀ l) (cLam a) (cB a)) ≤ Levels.Gen.g x₀ l * (Levels.Gen.g x₀ l * ((Levels.Gen.g x₀ l ^ 3 * cLam a) + (bitsOne c (Levels.Gen.g x₀ l) (cLam a) (cB a)))) := by rw [sq]; exact hgB
  omega

end ExplicitCost
