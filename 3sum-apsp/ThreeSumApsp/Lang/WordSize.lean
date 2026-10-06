/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import PaperStatements
public import ThreeSumApsp.Util.Basic
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.List
public import Mathlib.Data.Nat.Size
public import Mathlib.Data.Nat.SuccPred
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# A polynomial bound in the parameters fits in a word

The running-time claims hold at every word size W ≥ b (log₂ p₁ + ⋯ + log₂ p_r + 1), where p₁, …, p_r
are the parameters of the instance and the slope b is chosen with the program (`Admissible`).  A
light program states its limits as a polynomial in the parameters,
`polyBound s k params` = 2^s ((p₁ + 1) ⋯ (p_r + 1))^k.

The main fact is `polyBound_le`: this bound is at most 2^W as soon as b ≥ s + k r + k.  Each factor
p + 1 is at most 2^(log₂ p + 1) (`prod_succ_le`), so with S the sum of the logarithms the bound is
at most 2^(s + k (S + r)), and s + k (S + r) ≤ (s + k r + k) (S + 1) ≤ W.
-/

@[expose] public section

namespace Light

open ThreeSumApsp.WordRam

/-- The bound 2^s · ((p₁ + 1) (p₂ + 1) ⋯)^k in the parameters of an instance. -/
def polyBound (s k : ℕ) (params : List ℕ) : ℕ := 2 ^ s * ((params.map (· + 1)).prod) ^ k

private theorem prod_succ_le (params : List ℕ) :
    (params.map (· + 1)).prod ≤ 2 ^ ((params.map Nat.log2).sum + params.length) := by
  induction params with
  | nil => simp
  | cons p ps ih =>
    simp only [List.map_cons, List.prod_cons, List.sum_cons, List.length_cons]
    calc (p + 1) * (ps.map (· + 1)).prod
        ≤ 2 ^ (p.log2 + 1) * 2 ^ ((ps.map Nat.log2).sum + ps.length) :=
          Nat.mul_le_mul Nat.lt_log2_self ih
      _ = 2 ^ (p.log2 + (ps.map Nat.log2).sum + (ps.length + 1)) := by
          rw [← pow_add]
          congr 1
          omega

/-- At an admissible word size, words have room for a polynomial bound in the parameters, if the
slope is large enough. -/
theorem polyBound_le {b W s k r : ℕ} {params : List ℕ} (h : Admissible b params W)
    (hr : params.length ≤ r) (hb : s + k * r + k ≤ b) : polyBound s k params ≤ 2 ^ W := by
  set S := (params.map Nat.log2).sum
  have hexp : s + (S + params.length) * k ≤ W :=
    calc s + (S + params.length) * k ≤ s + (S + r) * k := by gcongr
      -- the difference is s S + k r S + k
      _ ≤ (s + k * r + k) * (S + 1) := Nat.le.intro (k := s * S + k * r * S + k) (by ring)
      _ ≤ b * (S + 1) := Nat.mul_le_mul_right _ hb
      _ ≤ W := h
  calc polyBound s k params ≤ 2 ^ s * (2 ^ (S + params.length)) ^ k :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (prod_succ_le params) k)
    _ = 2 ^ (s + (S + params.length) * k) := by rw [← pow_mul, ← pow_add]
    _ ≤ 2 ^ W := Nat.pow_le_pow_right (by norm_num) hexp

/-- The bound is positive. -/
theorem one_le_polyBound (s k : ℕ) (params : List ℕ) : 1 ≤ polyBound s k params := by
  have : 0 < (params.map (· + 1)).prod := List.prod_pos (by simp)
  exact Nat.mul_pos (by positivity) (by positivity)

/-- The bound grows with its first parameter. -/
theorem polyBound_cons_le {p p' : ℕ} (h : p ≤ p') (s k : ℕ) (params : List ℕ) :
    polyBound s k (p :: params) ≤ polyBound s k (p' :: params) := by
  simp only [polyBound, List.map_cons, List.prod_cons]
  gcongr

/-- The bound grows with its two exponents. -/
theorem polyBound_mono {s s' k k' : ℕ} (hs : s ≤ s') (hk : k ≤ k') (params : List ℕ) :
    polyBound s k params ≤ polyBound s' k' params := by
  have : 0 < (params.map (· + 1)).prod := List.prod_pos (by simp)
  exact Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) hs) (Nat.pow_le_pow_right this hk)

/-- A number that is at most A (n + 1)^e with e ≤ k has a bound of this form in n. -/
theorem le_polyBound_of_le_pow {n A s m e k : ℕ} (he : e ≤ k) (h : m ≤ A * (n + 1) ^ e) :
    m ≤ polyBound (s + Nat.size A) k [n] := by
  have hA : A ≤ 2 ^ (s + Nat.size A) :=
    (Nat.lt_size_self A).le.trans (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hn : (n + 1) ^ e ≤ (n + 1) ^ k := Nat.pow_le_pow_right (by omega) he
  have hbound : polyBound (s + Nat.size A) k [n] = 2 ^ (s + Nat.size A) * (n + 1) ^ k := by
    simp [polyBound]
  rw [hbound]
  exact h.trans (Nat.mul_le_mul hA hn)

/-- A bound in two parameters is a bound in n, of twice the degree, if both are at most n. -/
theorem polyBound_pair_le {s k p₁ p₂ n : ℕ} (h₁ : p₁ ≤ n) (h₂ : p₂ ≤ n) :
    polyBound s k [p₁, p₂] ≤ polyBound s (2 * k) [n] := by
  have hprod : (p₁ + 1) * (p₂ + 1) ≤ (n + 1) * (n + 1) := Nat.mul_le_mul (by omega) (by omega)
  have hpair : polyBound s k [p₁, p₂] = 2 ^ s * ((p₁ + 1) * (p₂ + 1)) ^ k := by simp [polyBound]
  have hone : polyBound s (2 * k) [n] = 2 ^ s * ((n + 1) * (n + 1)) ^ k := by
    simp only [polyBound, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    rw [← pow_two, ← pow_mul]
  rw [hpair, hone]
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hprod k)

/-- A power of two times the bound is a bound of the same form. -/
theorem polyBound_mul (s s' k : ℕ) (params : List ℕ) :
    2 ^ s' * polyBound s k params = polyBound (s' + s) k params := by
  simp only [polyBound, pow_add, mul_assoc]

/-- The sum of two numbers with such bounds has such a bound. -/
theorem add_le_polyBound {a b s s' k k' : ℕ} {params : List ℕ} (ha : a ≤ polyBound s k params)
    (hb : b ≤ polyBound s' k' params) : a + b ≤ polyBound (1 + (s + s')) (k + k') params := by
  have ha' := ha.trans (polyBound_mono (Nat.le_add_right s s') (Nat.le_add_right k k') params)
  have hb' := hb.trans (polyBound_mono (Nat.le_add_left s' s) (Nat.le_add_left k' k) params)
  rw [← polyBound_mul]
  omega

end Light
