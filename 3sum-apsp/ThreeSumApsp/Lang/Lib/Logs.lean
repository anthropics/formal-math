/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Lang.Tactics
public import Mathlib.Data.Nat.Log
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Logarithms, the cube root and halves, without division

Four routines on local variables only; none of them touches the memory.

* log2(x) returns ⌊log₂ x⌋ (0 for x = 0) by doubling (`log2_meets`).
* clog2(x) returns ⌈log₂ x⌉ (0 for x ≤ 1) by doubling (`clog2_meets`).
* cbrtCeil(n) returns the least s with s³ ≥ n, which is ⌈n^{1/3}⌉, by counting up
  (`cbrtCeil_meets`).
* half(h) returns ⌈h/2⌉ by counting up (`half_meets`).

Each of them is one loop that tries the candidates 0, 1, 2, … in turn.  Local variable 0 holds the
argument and receives the result, local variable 1 holds the candidate (`Arg`, `Cand`), and the two
logarithms keep a power of two in local variable 2 (`Power`).
-/

@[expose] public section

namespace Light

variable {lim : Limits} {P : Program} {d : ℕ}

namespace Logs

/-- The local variables of the routines: the argument, which the result replaces, the candidate,
and a power of two. -/
abbrev Arg : ℕ := 0
@[inherit_doc Arg] abbrev Cand : ℕ := 1
@[inherit_doc Arg] abbrev Power : ℕ := 2

end Logs

open Logs

/-! ## The logarithm, rounded down -/

/-- log2(x): the candidate is L, and the power is 2^(L + 1). -/
def log2Body : Stmt :=
  .set Cand (k 0) ;;
  .set Power (k 2) ;;
  .while (v Power ≤' v Arg) (
    .set Power (v Power +' v Power) ;;
    .set Cand (v Cand +' k 1)) ;;
  .set Arg (v Cand)

/-- The time of log2. -/
@[simp] def log2Time (x : ℕ) : ℕ := 14 * Nat.log 2 x + 12

/-- **log2(x)** returns ⌊log₂ x⌋ and leaves the memory as it is. -/
theorem log2_meets {p x : ℕ} (hp : P[p]? = some log2Body) (μ : ℕ → ℤ)
    (hword : ((2 * x + 2 : ℕ) : ℤ) ≤ lim.word) :
    Meets lim P p d [x] μ (log2Time x) fun r μ' => r = (Nat.log 2 x : ℤ) ∧ μ' = μ := by
  have hlt : x < 2 ^ (Nat.log 2 x + 1) := Nat.lt_pow_succ_log_self (by norm_num) x
  refine .of_body hp ?_
  unfold log2Body log2Time
  -- L := 0; p := 2
  light_set 0
  light_set 2
  -- while p ≤ x.  Before round i, L = i and p = 2^(i + 1).
  refine Ends.next _ (Ends.whileBlock (fun i σ => σ = ⟨frame [x, i, (2 ^ (i + 1) : ℕ)], μ⟩)
    (Nat.log 2 x) (by simp) ?round ?done le_rfl)
  case round =>
    rintro i _ hi rfl
    have hx : x ≠ 0 := by
      rintro rfl
      simp at hi
    have hle : 2 ^ (i + 1) ≤ x :=
      (Nat.pow_le_pow_right (by norm_num) (by omega)).trans (Nat.pow_log_le_self 2 hx)
    have hix : i < x := lt_of_lt_of_le (Nat.lt_pow_self (by norm_num))
      ((Nat.pow_le_pow_right (by norm_num) (by omega)).trans hle)
    rw [show 2 ^ (i + 1 + 1) = 2 ^ (i + 1) + 2 ^ (i + 1) by ring]
    generalize 2 ^ (i + 1) = q at hle
    -- The test is safe and holds.  p := p + p; L := L + 1 is safe and leads to the next state.
    exact ⟨by light_side, by light_side, by light_side, by simp [update_frame_setLocal]⟩
  case done =>
    rintro _ rfl
    generalize 2 ^ (Nat.log 2 x + 1) = q at hlt
    refine ⟨by light_side, by light_side, ?_⟩
    -- the result is L
    light_set (Nat.log 2 x)
    exact ⟨rfl, rfl⟩

/-! ## The logarithm, rounded up -/

/-- clog2(x): the candidate is L, and the power is 2^L. -/
def clog2Body : Stmt :=
  .set Cand (k 0) ;;
  .set Power (k 1) ;;
  .while (v Power <' v Arg) (
    .set Power (v Power +' v Power) ;;
    .set Cand (v Cand +' k 1)) ;;
  .set Arg (v Cand)

/-- The time of clog2. -/
@[simp] def clog2Time (x : ℕ) : ℕ := 12 * Nat.clog 2 x + 10

/-- **clog2(x)** returns ⌈log₂ x⌉ and leaves the memory as it is. -/
theorem clog2_meets {p x : ℕ} (hp : P[p]? = some clog2Body) (μ : ℕ → ℤ)
    (hword : ((2 * x + 1 : ℕ) : ℤ) ≤ lim.word) :
    Meets lim P p d [x] μ (clog2Time x) fun r μ' => r = (Nat.clog 2 x : ℤ) ∧ μ' = μ := by
  have hle : x ≤ 2 ^ Nat.clog 2 x := Nat.le_pow_clog (by norm_num) x
  refine .of_body hp ?_
  unfold clog2Body clog2Time
  -- L := 0; p := 1
  light_set 0
  light_set 1
  -- while p < x.  Before round i, L = i and p = 2^i.
  refine Ends.next _ (Ends.whileBlock (fun i σ => σ = ⟨frame [x, i, (2 ^ i : ℕ)], μ⟩)
    (Nat.clog 2 x) (by simp) ?round ?done le_rfl)
  case round =>
    rintro i _ hi rfl
    have hlt : 2 ^ i < x := (Nat.lt_clog_iff_pow_lt (by norm_num)).1 hi
    have hix : i < x := lt_trans (Nat.lt_pow_self (by norm_num)) hlt
    rw [show 2 ^ (i + 1) = 2 ^ i + 2 ^ i by ring]
    generalize 2 ^ i = q at hlt
    -- The test is safe and holds.  p := p + p; L := L + 1 is safe and leads to the next state.
    exact ⟨by light_side, by light_side, by light_side, by simp [update_frame_setLocal]⟩
  case done =>
    rintro _ rfl
    generalize 2 ^ Nat.clog 2 x = q at hle
    refine ⟨by light_side, by light_side, ?_⟩
    -- the result is L
    light_set (Nat.clog 2 x)
    exact ⟨rfl, rfl⟩

/-! ## The cube root, rounded up -/

/-- Some cube is at least n. -/
theorem exists_le_cube (n : ℕ) : ∃ s, n ≤ s ^ 3 := ⟨n, Nat.le_self_pow (by norm_num) n⟩

/-- The least s with s³ ≥ n. -/
def cbrtLeast (n : ℕ) : ℕ := Nat.find (exists_le_cube n)

theorem le_cbrtLeast_pow (n : ℕ) : n ≤ cbrtLeast n ^ 3 := Nat.find_spec (exists_le_cube n)

theorem pow_lt_of_lt_cbrtLeast {n s : ℕ} (h : s < cbrtLeast n) : s ^ 3 < n :=
  not_le.1 (Nat.find_min (exists_le_cube n) h)

theorem cbrtLeast_le {n s : ℕ} (h : n ≤ s ^ 3) : cbrtLeast n ≤ s :=
  Nat.find_min' (exists_le_cube n) h

theorem cbrtLeast_le_self (n : ℕ) : cbrtLeast n ≤ n :=
  cbrtLeast_le (Nat.le_self_pow (by norm_num) n)

/-- The number ⌈n^{1/3}⌉ is at least 1 for n ≥ 1. -/
theorem one_le_cbrtLeast {n : ℕ} (hn : 1 ≤ n) : 1 ≤ cbrtLeast n := by
  by_contra h
  have hpow := le_cbrtLeast_pow n
  rw [show cbrtLeast n = 0 by omega] at hpow
  omega

/-- The cube of the rounded cube root is at most 8 n. -/
theorem cbrtLeast_pow_le (n : ℕ) : cbrtLeast n ^ 3 ≤ 8 * n := by
  rcases Nat.eq_zero_or_pos (cbrtLeast n) with h | h
  · simp [h]
  obtain ⟨s, hs⟩ : ∃ s, cbrtLeast n = s + 1 := ⟨cbrtLeast n - 1, by omega⟩
  have h1 : s ^ 3 < n := pow_lt_of_lt_cbrtLeast (by omega)
  rw [hs]
  rcases Nat.eq_zero_or_pos s with h0 | h0
  · subst h0
    omega
  · calc (s + 1) ^ 3 ≤ (2 * s) ^ 3 := Nat.pow_le_pow_left (by omega) 3
      _ = 8 * s ^ 3 := by ring
      _ ≤ 8 * n := by omega

/-- The squares and cubes of the candidates fit in a word. -/
private theorem abs_cube_le {n i : ℕ} (hword : ((8 * n + 1 : ℕ) : ℤ) ≤ lim.word)
    (hi : i ≤ cbrtLeast n) : |(i : ℤ) * i| ≤ lim.word ∧ |(i : ℤ) * i * i| ≤ lim.word := by
  have hcube : i * i * i ≤ 8 * n :=
    calc i * i * i = i ^ 3 := by ring
      _ ≤ cbrtLeast n ^ 3 := Nat.pow_le_pow_left hi 3
      _ ≤ 8 * n := cbrtLeast_pow_le n
  have hsquare : i * i ≤ i * i * i := by
    rcases Nat.eq_zero_or_pos i with rfl | h
    · simp
    · exact Nat.le_mul_of_pos_right _ h
  have hcube' : (i : ℤ) * i * i ≤ 8 * n := by exact_mod_cast hcube
  have hsquare' : (i : ℤ) * i ≤ 8 * n := by exact_mod_cast hsquare.trans hcube
  have h2 : (0 : ℤ) ≤ (i : ℤ) * i := by positivity
  have h3 : (0 : ℤ) ≤ (i : ℤ) * i * i := by positivity
  push_cast at hword
  exact ⟨abs_le.2 ⟨by omega, by omega⟩, abs_le.2 ⟨by omega, by omega⟩⟩

/-- cbrtCeil(n): the candidate is s. -/
def cbrtCeilBody : Stmt :=
  .set Cand (k 0) ;;
  .while (v Cand *' v Cand *' v Cand <' v Arg) (
    .set Cand (v Cand +' k 1)) ;;
  .set Arg (v Cand)

/-- The time of cbrtCeil. -/
@[simp] def cbrtCeilTime (n : ℕ) : ℕ := 12 * cbrtLeast n + 12

/-- **cbrtCeil(n)** returns the least s with s³ ≥ n and leaves the memory as it is. -/
theorem cbrtCeil_meets {p n : ℕ} (hp : P[p]? = some cbrtCeilBody) (μ : ℕ → ℤ)
    (hword : ((8 * n + 1 : ℕ) : ℤ) ≤ lim.word) :
    Meets lim P p d [n] μ (cbrtCeilTime n) fun r μ' => r = (cbrtLeast n : ℤ) ∧ μ' = μ := by
  have hsn : cbrtLeast n ≤ n := cbrtLeast_le_self n
  refine .of_body hp ?_
  unfold cbrtCeilBody cbrtCeilTime
  -- s := 0
  light_set 0
  -- while s³ < n.  Before round i, s = i.
  refine Ends.next _ (Ends.whileBlock (fun i σ => σ = ⟨frame [n, i], μ⟩) (cbrtLeast n) (by simp)
    ?round ?done le_rfl)
  case round =>
    rintro i _ hi rfl
    have hlt : (i : ℤ) * i * i < n := by
      have := pow_lt_of_lt_cbrtLeast hi
      rw [show i ^ 3 = i * i * i by ring] at this
      exact_mod_cast this
    -- The test is safe and holds.  s := s + 1 is safe and leads to the next state.
    exact ⟨by simpa using abs_cube_le hword hi.le, by simpa using hlt, by light_side,
      by simp [update_frame_setLocal]⟩
  case done =>
    rintro _ rfl
    have hle : (n : ℤ) ≤ (cbrtLeast n : ℤ) * cbrtLeast n * cbrtLeast n := by
      have := le_cbrtLeast_pow n
      rw [show cbrtLeast n ^ 3 = cbrtLeast n * cbrtLeast n * cbrtLeast n by ring] at this
      exact_mod_cast this
    refine ⟨by simpa using abs_cube_le hword le_rfl, by simpa using hle, ?_⟩
    -- the result is s
    light_set (cbrtLeast n)
    exact ⟨rfl, rfl⟩

/-! ## Halves, rounded up -/

/-- half(h): the candidate is r. -/
def halfBody : Stmt :=
  .set Cand (k 0) ;;
  .while (v Cand +' v Cand <' v Arg) (
    .set Cand (v Cand +' k 1)) ;;
  .set Arg (v Cand)

/-- The time of half. -/
@[simp] def halfTime (h : ℕ) : ℕ := 10 * ((h + 1) / 2) + 10

/-- **half(h)** returns ⌈h/2⌉ and leaves the memory as it is. -/
theorem half_meets {p h : ℕ} (hp : P[p]? = some halfBody) (μ : ℕ → ℤ)
    (hword : ((h + 1 : ℕ) : ℤ) ≤ lim.word) :
    Meets lim P p d [h] μ (halfTime h) fun r μ' => r = (((h + 1) / 2 : ℕ) : ℤ) ∧ μ' = μ := by
  refine .of_body hp ?_
  unfold halfBody halfTime
  -- r := 0
  light_set 0
  -- while r + r < h.  Before round i, r = i.
  refine Ends.next _ (Ends.whileBlock (fun i σ => σ = ⟨frame [h, i], μ⟩) ((h + 1) / 2) (by simp)
    ?round ?done le_rfl)
  case round =>
    rintro i _ hi rfl
    -- The test is safe and holds.  r := r + 1 is safe and leads to the next state.
    exact ⟨by light_side, by light_side, by light_side, by simp [update_frame_setLocal]⟩
  case done =>
    rintro _ rfl
    refine ⟨by light_side, by light_side, ?_⟩
    -- the result is r
    light_set ((h + 1) / 2 : ℕ)
    exact ⟨rfl, rfl⟩

end Light
