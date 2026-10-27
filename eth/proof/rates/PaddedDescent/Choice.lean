/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import PaddedDescent.Seq
public import SparsifyWidthK.Thresholds
public import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-! # The parameters chosen from one integer s

For precision s the algorithm uses the threshold τ = 2^(4s+17), the code parameter β = (s+7)² and
the depth t = ⌊19s/3⌋ + 700, whatever the width k of the clauses. The
thresholds of the sparsification for clauses of width k are those of `WidthK.Defs`: there a path of
the tree has at most bsum τ k · n steps and a leaf has at most
leafC τ k · n clauses. Both numbers are at most a power of τ whose exponent depends on k only, so
that they are below 2^β as soon as s ≥ `s0K k` = 2^(k+4). This file
proves that; the inequality (k/τ)·log₂(e·τ·bsum τ k) ≤ 1/2^s for such s, from which
`WidthK.stLeafCount` bounds the number of leaves by 2^(n/2^s); that t levels with
contraction 8963/10000 make up for the factor 2^10·(s + 8)⁶·2^s; and that K_t is at least 2^(4β +
10s + 1000). -/

public section

namespace PaddedDescent

open WidthK (theta bsum leafC)
open WidthK.Thresholds

/-! ### The threshold of the sparsification -/

/-- 2^17 ≤ τ. -/
theorem two_pow_le_tauOf (s : ℕ) : 2 ^ 17 ≤ tauOf s := Nat.pow_le_pow_right (by norm_num) (by omega)

/-- 4 ≤ τ. -/
theorem four_le_tauOf (s : ℕ) : 4 ≤ tauOf s := le_trans (by norm_num) (two_pow_le_tauOf s)

/-- 2 ≤ τ. -/
theorem two_le_tauOf (s : ℕ) : 2 ≤ tauOf s := le_trans (by norm_num) (two_pow_le_tauOf s)

/-- 1 ≤ τ. -/
theorem one_le_tauOf (s : ℕ) : 1 ≤ tauOf s := le_trans (by norm_num) (two_pow_le_tauOf s)

/-- τ^e = 2^((4s+17)·e). -/
theorem tauOf_pow (s e : ℕ) : tauOf s ^ e = 2 ^ ((4 * s + 17) * e) := by rw [tauOf, ← pow_mul]

/-- bsum τ k ≤ 2^((4s+17)·2^(k+1)). -/
theorem bsum_tauOf_le (k s : ℕ) : bsum (tauOf s) k ≤ 2 ^ ((4 * s + 17) * 2 ^ (k + 1)) :=
  (bsum_le_pow (four_le_tauOf s) k).trans (tauOf_pow s _).le

/-- θ_j ≤ 2^((4s+17)·2^k) for j < k. -/
theorem theta_tauOf_le {j k : ℕ} (hj : j < k) (s : ℕ) : theta (tauOf s) j ≤ 2 ^ ((4 * s + 17) * 2 ^ k) := by
  have h1 := sq_mul_theta_le (four_le_tauOf s) j
  have h2 : theta (tauOf s) j ≤ tauOf s ^ 2 * theta (tauOf s) j :=
    Nat.le_mul_of_pos_left _ (Nat.pow_pos (lt_of_lt_of_le (by norm_num) (one_le_tauOf s)))
  calc theta (tauOf s) j ≤ tauOf s ^ 2 ^ (j + 1) := h2.trans h1
    _ = 2 ^ ((4 * s + 17) * 2 ^ (j + 1)) := tauOf_pow s _
    _ ≤ 2 ^ ((4 * s + 17) * 2 ^ k) :=
        Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hj))

/-- leafC τ k ≤ 2k·2^((4s+17)·2^k). -/
theorem leafC_tauOf_le (k s : ℕ) : leafC (tauOf s) k ≤ 2 * (k * 2 ^ ((4 * s + 17) * 2 ^ k)) := by
  rw [leafC]
  refine Nat.mul_le_mul_left _ ?_
  calc ∑ j ∈ Finset.range k, theta (tauOf s) j ≤ ∑ _j ∈ Finset.range k, 2 ^ ((4 * s + 17) * 2 ^ k) :=
        Finset.sum_le_sum fun j hj => theta_tauOf_le (Finset.mem_range.1 hj) s
    _ = k * 2 ^ ((4 * s + 17) * 2 ^ k) := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul]

/-! ### From s0K k on, the parameters are large enough for width k -/

/-- 2^(s0K k) ≤ C0K k: the pad suffices for exhaustive search while s < s0K k. -/
theorem two_pow_s0K_le (k : ℕ) : 2 ^ s0K k ≤ C0K k := Nat.le_mul_of_pos_left _ (by norm_num)

/-- k ≤ s for s ≥ s0K k. -/
theorem le_of_s0K_le {k s : ℕ} (hs : s0K k ≤ s) : k ≤ s := by
  have h1 : k < 2 ^ k := Nat.lt_two_pow_self
  have h2 : 2 ^ k ≤ 2 ^ (k + 4) := Nat.pow_le_pow_right (by norm_num) (by omega)
  unfold s0K at hs
  omega

/-- The inequality between exponents behind the three lemmas that follow: (4s+17)·(2^(k+1) + 1) + k +
3 ≤ (s+7)² for s ≥ 2^(k+4). -/
theorem exponent_le_betaOf {k s : ℕ} (hs : s0K k ≤ s) : (4 * s + 17) * (2 ^ (k + 1) + 1) + k + 3 ≤ betaOf s := by
  have hk : k + 1 < 2 ^ (k + 1) := Nat.lt_two_pow_self
  have e : s0K k = 8 * 2 ^ (k + 1) := by rw [s0K, show k + 4 = k + 1 + 3 by ring, pow_add]; ring
  rw [e] at hs
  unfold betaOf
  generalize 2 ^ (k + 1) = a at hk hs ⊢
  nlinarith [Nat.mul_le_mul hs (le_refl s)]

/-- 3·τ·bsum τ k ≤ 2^β for s ≥ s0K k. -/
theorem three_mul_tauOf_mul_bsum_le {k s : ℕ} (hs : s0K k ≤ s) : 3 * tauOf s * bsum (tauOf s) k ≤ 2 ^ betaOf s := by
  have h := exponent_le_betaOf hs
  calc 3 * tauOf s * bsum (tauOf s) k ≤ 2 ^ 2 * 2 ^ (4 * s + 17) * 2 ^ ((4 * s + 17) * 2 ^ (k + 1)) :=
        Nat.mul_le_mul (Nat.mul_le_mul (by norm_num) le_rfl) (bsum_tauOf_le k s)
    _ = 2 ^ (2 + (4 * s + 17) + (4 * s + 17) * 2 ^ (k + 1)) := by rw [← pow_add, ← pow_add]
    _ ≤ 2 ^ betaOf s := Nat.pow_le_pow_right (by norm_num) (by
        have e : (4 * s + 17) * (2 ^ (k + 1) + 1) = (4 * s + 17) * 2 ^ (k + 1) + (4 * s + 17) := by ring
        omega)

/-- bsum τ k ≤ 2^β for s ≥ s0K k. -/
theorem bsum_le_two_pow_betaOf {k s : ℕ} (hs : s0K k ≤ s) : bsum (tauOf s) k ≤ 2 ^ betaOf s := by
  have h1 : 1 ≤ 3 * tauOf s := by have := two_le_tauOf s; omega
  exact le_trans (Nat.le_mul_of_pos_left _ h1) (three_mul_tauOf_mul_bsum_le hs)

/-- leafC τ k + 2 ≤ 2^β for s ≥ s0K k: in a leaf of the tree for width k every variable occurs in at
most 2^β − 2 clauses. -/
theorem leafC_add_two_le {k s : ℕ} (hs : s0K k ≤ s) : leafC (tauOf s) k + 2 ≤ 2 ^ betaOf s := by
  have h := exponent_le_betaOf hs
  have hk : k + 1 ≤ 2 ^ k := Nat.lt_two_pow_self
  obtain ⟨E, hE⟩ : ∃ E, E = (4 * s + 17) * 2 ^ k := ⟨_, rfl⟩
  have hE1 : 1 ≤ 2 ^ E := Nat.one_le_two_pow
  have h2 : E + k + 1 ≤ betaOf s := by
    have e1 : (4 * s + 17) * (2 ^ (k + 1) + 1) = 2 * E + (4 * s + 17) := by rw [hE, pow_succ]; ring
    omega
  calc leafC (tauOf s) k + 2 ≤ 2 * (k * 2 ^ E) + 2 * 2 ^ E := Nat.add_le_add (hE ▸ leafC_tauOf_le k s) (by omega)
    _ = 2 * ((k + 1) * 2 ^ E) := by ring
    _ ≤ 2 * (2 ^ k * 2 ^ E) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hk)
    _ = 2 ^ (E + k + 1) := by rw [pow_add, pow_add]; ring
    _ ≤ 2 ^ betaOf s := Nat.pow_le_pow_right (by norm_num) h2

/-- s + 7 ≤ 7·2^s. -/
theorem add_seven_le (s : ℕ) : s + 7 ≤ 7 * 2 ^ s := by
  have h : s + 1 ≤ 2 ^ s := Nat.lt_two_pow_self
  omega

/-- β ≤ 49·4^s. -/
theorem betaOf_le (s : ℕ) : betaOf s ≤ 49 * 2 ^ (2 * s) := by
  calc betaOf s ≤ (7 * 2 ^ s) ^ 2 := Nat.pow_le_pow_left (add_seven_le s) 2
    _ = 49 * 2 ^ (2 * s) := by rw [mul_pow, ← pow_mul, Nat.mul_comm s 2]; norm_num

/-- (k/τ)·log₂(e·τ·bsum τ k) ≤ 1/2^s for τ = 2^(4s+17) and s ≥ s0K k: this is the hypothesis of
`WidthK.StLeafCount` with ε = 1/2^s.
Indeed e·τ·bsum τ k ≤ 3·τ·bsum τ k ≤ 2^β, and k·β ≤ 2^s·49·4^s ≤ 2^(3s+17). -/
theorem tauOf_works {k s : ℕ} (hs : s0K k ≤ s) :
    ((k : ℝ) / (tauOf s : ℝ)) * Real.logb 2 (Real.exp 1 * (tauOf s : ℝ) * (bsum (tauOf s) k : ℝ)) ≤ 1 / 2 ^ s := by
  have hτ0 : (0 : ℝ) < (tauOf s : ℝ) := by exact_mod_cast lt_of_lt_of_le (by norm_num) (two_le_tauOf s)
  have hb0 : (0 : ℝ) < (bsum (tauOf s) k : ℝ) := by exact_mod_cast lt_of_lt_of_le (by norm_num) (two_le_bsum (tauOf s) k)
  have he : Real.exp 1 ≤ 3 := Real.exp_one_lt_three.le
  have h3 : (3 : ℝ) * (tauOf s : ℝ) * (bsum (tauOf s) k : ℝ) ≤ (2 : ℝ) ^ betaOf s := by
    exact_mod_cast three_mul_tauOf_mul_bsum_le hs
  have hle : Real.exp 1 * (tauOf s : ℝ) * (bsum (tauOf s) k : ℝ) ≤ (2 : ℝ) ^ betaOf s :=
    le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right he hτ0.le) hb0.le) h3
  have hlogb : Real.logb 2 (Real.exp 1 * (tauOf s : ℝ) * (bsum (tauOf s) k : ℝ)) ≤ (betaOf s : ℝ) := by
    have hpos : 0 < Real.exp 1 * (tauOf s : ℝ) * (bsum (tauOf s) k : ℝ) := mul_pos (mul_pos (Real.exp_pos 1) hτ0) hb0
    calc Real.logb 2 (Real.exp 1 * (tauOf s : ℝ) * (bsum (tauOf s) k : ℝ)) ≤ Real.logb 2 ((2 : ℝ) ^ betaOf s) :=
          Real.logb_le_logb_of_le one_lt_two hpos hle
      _ = (betaOf s : ℝ) := by rw [Real.logb_pow, Real.logb_self_eq_one one_lt_two, mul_one]
  have h2s : (0 : ℝ) < (2 : ℝ) ^ s := by positivity
  have hnat : k * betaOf s * 2 ^ s ≤ 1 * tauOf s := by
    have hk : k ≤ 2 ^ s := (le_of_s0K_le hs).trans Nat.lt_two_pow_self.le
    calc k * betaOf s * 2 ^ s ≤ 2 ^ s * (49 * 2 ^ (2 * s)) * 2 ^ s := Nat.mul_le_mul_right _ (Nat.mul_le_mul hk (betaOf_le s))
      _ = 49 * 2 ^ (4 * s) := by rw [show 4 * s = s + 2 * s + s by ring, pow_add, pow_add]; ring
      _ ≤ 2 ^ 17 * 2 ^ (4 * s) := Nat.mul_le_mul_right _ (by norm_num)
      _ = 1 * tauOf s := by rw [tauOf, pow_add]; ring
  calc ((k : ℝ) / (tauOf s : ℝ)) * Real.logb 2 (Real.exp 1 * (tauOf s : ℝ) * (bsum (tauOf s) k : ℝ))
      ≤ ((k : ℝ) / (tauOf s : ℝ)) * (betaOf s : ℝ) := mul_le_mul_of_nonneg_left hlogb (div_nonneg (Nat.cast_nonneg k) hτ0.le)
    _ ≤ 1 / 2 ^ s := by
        rw [div_mul_eq_mul_div, div_le_div_iff₀ hτ0 h2s]
        exact_mod_cast hnat

/-! ### The decay over the levels -/

/-- n < 2^s·(⌊n/2^s⌋ + 1). -/
theorem lt_two_pow_mul_div_add_one (n s : ℕ) : n < 2 ^ s * (n / 2 ^ s + 1) :=
  Nat.lt_mul_div_succ n (by positivity)

/-- Three more units of s: 19 more levels, each of which multiplies by 8963/10000, make up for the
factor 8 that 2^s gains and for the growth of
(s + 2^15)⁶. The margin is small: (8963/10000)^19·8 = 0.99936…. This is why 2^15 stands here in
place of 8: it makes the growth of the sixth power small enough. -/
theorem decay_step (s : ℕ) :
    8963 ^ 19 * (8 * (s + 3 + 2 ^ 15) ^ 6) ≤ 10000 ^ 19 * (s + 2 ^ 15) ^ 6 := by
  have hx : (s + 3 + 2 ^ 15) * 2 ^ 15 ≤ (2 ^ 15 + 3) * (s + 2 ^ 15) := by omega
  have hnum : 8963 ^ 19 * (8 * (2 ^ 15 + 3) ^ 6) ≤ 10000 ^ 19 * (2 ^ 15) ^ 6 := by norm_num
  obtain ⟨A, hA⟩ : ∃ A, A = 8963 ^ 19 := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B, B = 10000 ^ 19 := ⟨_, rfl⟩
  obtain ⟨M, hM⟩ : ∃ M, M = 2 ^ 15 := ⟨_, rfl⟩
  rw [← hA, ← hB, ← hM] at hnum ⊢
  rw [← hM] at hx
  refine Nat.le_of_mul_le_mul_right ?_ (show 0 < M ^ 6 by rw [hM]; norm_num)
  calc A * (8 * (s + 3 + M) ^ 6) * M ^ 6 = A * 8 * ((s + 3 + M) * M) ^ 6 := by ring
    _ ≤ A * 8 * ((M + 3) * (s + M)) ^ 6 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hx 6)
    _ = A * (8 * (M + 3) ^ 6) * (s + M) ^ 6 := by ring
    _ ≤ B * M ^ 6 * (s + M) ^ 6 := Nat.mul_le_mul_right _ hnum
    _ = B * (s + M) ^ 6 * M ^ 6 := by ring

/-- From s to s + 3 in `decay_aux`. -/
theorem decay_aux_step {s : ℕ} (ih : 8963 ^ (19 * s / 3 + 700) * (2 ^ 10 * (s + 2 ^ 15) ^ 6 * 2 ^ s) ≤ 10000 ^ (19 * s / 3 + 700)) :
    8963 ^ (19 * (s + 3) / 3 + 700) * (2 ^ 10 * (s + 3 + 2 ^ 15) ^ 6 * 2 ^ (s + 3)) ≤ 10000 ^ (19 * (s + 3) / 3 + 700) := by
  have hs := decay_step s
  have e : 19 * (s + 3) / 3 + 700 = 19 * s / 3 + 700 + 19 := by omega
  rw [e, pow_add 8963 (19 * s / 3 + 700) 19, pow_add 10000 (19 * s / 3 + 700) 19]
  obtain ⟨t, ht⟩ : ∃ t, t = 19 * s / 3 + 700 := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A, A = 8963 ^ 19 := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B, B = 10000 ^ 19 := ⟨_, rfl⟩
  obtain ⟨M, hM⟩ : ∃ M, M = 2 ^ 15 := ⟨_, rfl⟩
  rw [← hA, ← hB, ← hM] at hs ⊢
  rw [← ht, ← hM] at ih
  rw [← ht]
  calc 8963 ^ t * A * (2 ^ 10 * (s + 3 + M) ^ 6 * 2 ^ (s + 3))
      = 8963 ^ t * (2 ^ 10 * 2 ^ s) * (A * (8 * (s + 3 + M) ^ 6)) := by ring
    _ ≤ 8963 ^ t * (2 ^ 10 * 2 ^ s) * (B * (s + M) ^ 6) := Nat.mul_le_mul_left _ hs
    _ = 8963 ^ t * (2 ^ 10 * (s + M) ^ 6 * 2 ^ s) * B := by ring
    _ ≤ 10000 ^ t * B := Nat.mul_le_mul_right _ ih

/-- 8963^(⌊19s/3⌋+700)·2^10·(s + 2^15)⁶·2^s ≤ 10000^(⌊19s/3⌋+700): by induction in steps of 3, from
s = 0, 1, 2. -/
theorem decay_aux : ∀ s : ℕ,
    8963 ^ (19 * s / 3 + 700) * (2 ^ 10 * (s + 2 ^ 15) ^ 6 * 2 ^ s) ≤ 10000 ^ (19 * s / 3 + 700)
  | 0 => by norm_num
  | 1 => by norm_num
  | 2 => by norm_num
  | s + 3 => decay_aux_step (decay_aux s)

/-- t levels, each of which multiplies by 8963/10000, make up for the factor C·(s + 8)⁶·2^s, for
every C ≤ 2^10. -/
theorem decay {C : ℕ} (hC : C ≤ 2 ^ 10) (s : ℕ) :
    8963 ^ depthOf s * (C * (s + 8) ^ 6 * 2 ^ s) ≤ 10000 ^ depthOf s := by
  rw [depthOf]
  have h : (s + 8) ^ 6 ≤ (s + 2 ^ 15) ^ 6 := Nat.pow_le_pow_left (by omega) 6
  exact le_trans (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul hC h))) (decay_aux s)

/-! ### K_t is large compared with 2^β -/

/-- 2^(4β + 10s + 1000) ≤ K_t. -/
theorem two_pow_betaOf_le_Ktop (s : ℕ) : 2 ^ (4 * betaOf s + 10 * s + 1000) ≤ Ktop s := by
  refine two_pow_le_Ktop ?_
  have h1 := betaOf_le s
  have h2 : s + 1 ≤ 2 ^ s := Nat.lt_two_pow_self
  have h3 : 2 ^ s ≤ 2 ^ (2 * s) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h4 : 1 ≤ 2 ^ (2 * s) := Nat.one_le_two_pow
  calc 4 * betaOf s + 10 * s + 1000 ≤ 2 ^ 11 * 2 ^ (2 * s) := by omega
    _ = 2 ^ (11 + 2 * s) := by rw [← pow_add]
    _ ≤ 2 ^ depthOf s := Nat.pow_le_pow_right (by norm_num) (by unfold depthOf; omega)

end PaddedDescent
