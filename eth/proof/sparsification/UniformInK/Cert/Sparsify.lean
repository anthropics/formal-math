/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import UniformInK.Spars.Defs
public import SparsifyWidthK.Poly.Sparsify
public import ToTuring.Lib.Unary
public import ToTuring.Lib.Nat2
public import ToTuring.Lib.List2

/-! # The choice of the heart at one step of the sparsification is polynomial-time jointly in the width k

The twin of proof/sparsification/SparsifyWidthK/Poly/Sparsify.lean and of the first half of
proof/rates/PaddedDescent/F/CertSparsify.lean. There the width k is a constant of every certificate,
and so are the lists that depend
on k alone: the 2^k masks, and the pairs (j, h) with their thresholds. Here k is a function of the
context x, and the two lists are computed. This takes polynomial time if k and 2^k are given in
unary: `masks k` is the list of the words of k bits of the numbers below 2^k, lowest bit first
(`masks_eq`), and each threshold in the list is 4 times a power of τ with an exponent below 2k.
The functions `heartsL`, `tryL`, `pickL` are `heartsP`, `tryT`, `pickK` with the two lists as
arguments. -/

@[expose] public section

namespace UniformInK.CertSparsify

open Groundwork Groundwork.Sparsify WidthK.Prog

variable {α : Type} [Enc α]

/-! ### The masks -/

/-- The numbers below 2N are 0, 1, then 2, 3, and so on up to 2N-2, 2N-1. -/
theorem range_two_mul (N : ℕ) : List.range (2 * N) = (List.range N).flatMap fun i => [2 * i, 2 * i + 1] := by
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [List.range_succ, List.flatMap_append, ← ih, show 2 * (N + 1) = 2 * N + 1 + 1 by ring, List.range_succ, List.range_succ]
    simp

/-- The list `masks k` consists of the words of k bits of the numbers 0, 1, …, 2^k - 1, lowest bit
first. -/
theorem masks_eq (k : ℕ) : masks k = (List.range (2 ^ k)).map (toWord k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [masks, ih, pow_succ', range_two_mul, List.flatMap_map, List.map_flatMap]
    refine List.flatMap_congr fun i _ => ?_
    have h1 : (2 * i + 1) / 2 = i := by omega
    simp [toWord, h1]

/-- The list of all masks of length k is polynomial-time if k and 2^k are given in unary. -/
theorem masks_polyT {k : α → ℕ} (hk : Unary k) (h2 : Unary fun x => 2 ^ k x) : PolyT fun x => masks (k x) := by
  have hr := PolyT.range h2
  have hw : PolyT fun p : α × ℕ => toWord (k p.1) p.2 := PolyT.toWord' (hk.comp (by fun_prop)) (by fun_prop)
  have h : PolyT fun x => (List.range (2 ^ k x)).map fun y => toWord (k x) y := by fun_prop
  exact h.congr fun x => (masks_eq (k x)).symm

/-! ### The pairs (j, h) and their thresholds -/

/-- The list of the pairs (j, h) with 1 ≤ h < j ≤ k is polynomial-time if k is given in unary. -/
theorem pairsK_polyT {k : α → ℕ} (hk : Unary k) : PolyT fun x => pairsK (k x) := by
  have h0 := hk.poly
  have h1 : PolyT fun x => List.range (k x + 1) := PolyT.range (hk.add (Unary.const 1))
  have h2 : PolyT fun p : α × ℕ => List.range (min p.2 (k p.1)) :=
    PolyT.range ((hk.comp (h := fun p : α × ℕ => p.1) (by fun_prop)).of_le (by fun_prop) fun p => Nat.min_le_right _ _)
  have h : PolyT fun x => (List.range (k x + 1)).flatMap fun j =>
      ((List.range (min j (k x))).reverse.filter fun h => decide (0 < h)).map fun h => (j, h) := by fun_prop
  refine h.congr fun x => ?_
  unfold pairsK
  refine List.flatMap_congr fun j hj => ?_
  rw [Nat.min_eq_left (by have := List.mem_range.1 hj; omega)]

/-- In a pair (j, h) of the list, j is at most k. -/
theorem le_of_mem_pairsK {k : ℕ} {jh : ℕ × ℕ} (h : jh ∈ pairsK k) : jh.1 ≤ k := by
  unfold pairsK at h
  obtain ⟨j, hj, h⟩ := List.mem_flatMap.1 h
  obtain ⟨_, _, rfl⟩ := List.mem_map.1 h
  have := List.mem_range.1 hj
  omega

/-- `thetaU τ i` as one expression: 1 if i = 0, otherwise 4·τ^(2i−1). -/
theorem thetaU_eq (τ i : ℕ) : thetaU τ i = if i = 0 then 1 else 4 * τ ^ (2 * i - 1) := by
  cases i with
  | zero => rfl
  | succ i => simp [thetaU, show 2 * (i + 1) - 1 = 2 * i + 1 by omega]

/-- The threshold θ i is polynomial-time jointly in τ and i, if i is given in unary. -/
theorem thetaU_polyT {τ i : α → ℕ} (hτ : PolyT τ) (hi : Unary i) : PolyT fun x => thetaU (τ x) (i x) := by
  have h0 := hi.poly
  have hp : PolyT fun x => τ x ^ (2 * i x - 1) :=
    PolyT.pow_unary hτ (((Unary.const 2).mul hi).of_le (by fun_prop) fun x => Nat.sub_le _ _)
  simp only [thetaU_eq]; fun_prop

/-- The list of the pairs (j, h), each with its threshold θ (j - h), is polynomial-time jointly in τ
and k, if k is given in unary. -/
theorem thrList_polyT {k τ : α → ℕ} (hk : Unary k) (hτ : PolyT τ) :
    PolyT fun x => (pairsK (k x)).map fun jh => (jh, thetaU (τ x) (jh.1 - jh.2)) := by
  have h1 := pairsK_polyT hk
  have h2 : PolyT fun p : α × ℕ × ℕ => thetaU (τ p.1) (min (p.2.1 - p.2.2) (k p.1)) :=
    thetaU_polyT (by fun_prop)
      ((hk.comp (h := fun p : α × ℕ × ℕ => p.1) (by fun_prop)).of_le (by have := hk.poly; fun_prop) fun p => Nat.min_le_right _ _)
  have h : PolyT fun x => (pairsK (k x)).map fun jh => (jh, thetaU (τ x) (min (jh.1 - jh.2) (k x))) := by fun_prop
  refine h.congr fun x => List.map_congr_left fun jh hjh => ?_
  rw [Nat.min_eq_left (by have := le_of_mem_pairsK hjh; omega)]

/-! ### The rule with the two lists as arguments -/

/-- `heartsP` with the list M in place of `masks k`. -/
def heartsL (M : List (List Bool)) (s : PFml) (j h : ℕ) : PFml :=
  (s.filter fun C => decide (C.length = j)).flatMap fun C => (M.map fun m => maskP m C).filter fun H => decide (H.length = h)

/-- `tryT` with the list M in place of `masks k`. -/
def tryL (M : List (List Bool)) (s : PFml) (c : (ℕ × ℕ) × ℕ) : Option (PCl × PFml) :=
  ((heartsL M s c.1.1 c.1.2).find? fun H => decide (c.2 ≤ (overP s c.1.1 H).length)).map fun H => (H, (overP s c.1.1 H).map (minusP H))

/-- `pickK` with the list M in place of `masks k` and the list L in place of the pairs (j, h) with
their thresholds. -/
def pickL (M : List (List Bool)) (L : List ((ℕ × ℕ) × ℕ)) (s : PFml) : Option (PCl × PFml) := (L.filterMap (tryL M s)).head?

/-- `pickK` is `pickL` at the two lists that belong to θ and k. -/
theorem pickK_eq_pickL (θ : ℕ → ℕ) (k : ℕ) (s : PFml) :
    pickK θ k s = pickL (masks k) ((pairsK k).map fun jh => (jh, θ (jh.1 - jh.2))) s := pickK_eq θ k s

/-- Listing the candidate hearts is polynomial-time jointly in the list of masks, the formula and
the sizes j and h. -/
@[fun_prop] theorem polyT_heartsL {M : α → List (List Bool)} {s : α → PFml} {j h : α → ℕ} (hM : PolyT M) (hs : PolyT s) (hj : PolyT j)
    (hh : PolyT h) : PolyT fun x => heartsL (M x) (s x) (j x) (h x) := by
  unfold heartsL; fun_prop

/-- The search for a heart of a given size that reaches a given threshold is polynomial-time jointly
in the list of masks. -/
@[fun_prop] theorem polyT_tryL {M : α → List (List Bool)} {s : α → PFml} {c : α → (ℕ × ℕ) × ℕ} (hM : PolyT M) (hs : PolyT s) (hc : PolyT c) :
    PolyT fun x => tryL (M x) (s x) (c x) := by
  unfold tryL; fun_prop

/-- The choice of the heart and its petals is polynomial-time jointly in the two lists. -/
@[fun_prop] theorem polyT_pickL {M : α → List (List Bool)} {L : α → List ((ℕ × ℕ) × ℕ)} {s : α → PFml} (hM : PolyT M) (hL : PolyT L)
    (hs : PolyT s) : PolyT fun x => pickL (M x) (L x) (s x) := by
  unfold pickL; fun_prop

/-- The choice of the heart and its petals at a node is polynomial-time jointly in k, τ and the
formula, if k and 2^k are given in unary. -/
theorem polyT_pickKU {k τ : α → ℕ} {s : α → PFml} (hk : Unary k) (h2 : Unary fun x => 2 ^ k x) (hτ : PolyT τ) (hs : PolyT s) :
    PolyT fun x => pickK (thetaU (τ x)) (k x) (s x) := by
  simp only [pickK_eq_pickL]
  exact polyT_pickL (masks_polyT hk h2) (thrList_polyT hk hτ) hs

end UniformInK.CertSparsify
