/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ClauseBound.Inst.HalfPart
public import ClauseBound.Inst.HalfTab
public import ClauseBound.Alg.Prog

/-! # The pieces with ρ = 1/√2 as programs: definitions

For strings of λ bits let h be the least number ≥ 2 with p(h) ≥ 2^λ. A string x stands for the
partition number x in the list of the partitions of h. The pieces are numbered
0, …, 4h; the piece number i is A_s with s = i − 2h. A label θ of a factorization is read as a
number and stands for the pair (j, τ) with that number in the list of all pairs with
0 ≤ j ≤ 2h and τ a partition of s + j (row-wise) or of 2h − s − j (column-wise). The two functions
of a factorization are entries of the matrices of the operators, read off tables
that are rebuilt at every call. Two constants have no explicit value and are parameters: c₀ (h is
searched for up to c₀·λ²) and c (no piece needs more than 2cλ bits, a pad of length 2^{cλ} suffices,
and all
values have at most (2λ)^c bits). Definitions only. -/

@[expose] public section

namespace ClauseBound.Inst.Half

open Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.Inst.Rec

/-- s = i − 2h; the number i of the piece is cut off at 4h. -/
def sOf (h i : ℕ) : ℤ := ((min i (4 * h) : ℕ) : ℤ) - 2 * h

/-- The weight of τ in the pair (j, τ). -/
def wOf (tr : Bool) (h : ℕ) (s : ℤ) (j : ℕ) : ℤ := bif tr then 2 * h - s - j else s + j

/-- The list of the pairs (j, τ). -/
def labs (T : PT) (tr : Bool) (h : ℕ) (s : ℤ) : List (ℕ × List ℕ) :=
  (List.range (2 * h + 1)).flatMap fun j =>
    if 0 ≤ wOf tr h s j then (T.getD (wOf tr h s j).toNat []).map fun τ => (j, τ) else []

/-- The partition of h that the string x stands for. -/
def encF (T : PT) (h : ℕ) (x : List Bool) : List ℕ := (T.getD h []).getD (ofWord x) []

/-- One of the two functions of a factorization, given h, s and the table T of the partitions of 0,
…, 4h. On top the strings are (x, y) row-wise and (x, u) column-wise;
below they are (u, v) row-wise and (y, v) column-wise. -/
def partT (pad : U) (tr top : Bool) (h : ℕ) (s : ℤ) (T : PT) (a b θ : List Bool) : ℤ :=
  ((labs T tr h s)[ofWord θ]?).elim 0 fun p =>
    bif top then
      (bif tr then topF pad (4 * h) T.flatten h (encF T h a) p.1 (s - h + p.1) (encF T h b) p.2
       else topF pad (4 * h) T.flatten h (encF T h a) p.1 (s - h + p.1) p.2 (encF T h b))
    else
      (bif tr then botF pad (4 * h) T.flatten h (encF T h b) (h - s - p.1) p.2 (encF T h a)
       else botF pad (4 * h) T.flatten h (encF T h b) (h - s - p.1) (encF T h a) p.2)

/-- One of the two functions of a factorization, as a function of (pad, direction), (unused
parameter, number of the piece), (two strings, label). -/
def partH (c₀ : ℕ) (top : Bool) (q : PQ) : ℤ :=
  partT q.1.1 q.1.2 top (hF c₀ q.2.2.1.length) (sOf (hF c₀ q.2.2.1.length) q.2.1.2) (allTabF q.1.1 (4 * hF c₀ q.2.2.1.length))
    q.2.2.1 q.2.2.2.1 q.2.2.2.2

/-- The number of all partitions of 0, …, 4h. -/
def deltaF (h : ℕ) : ℕ := (pTab (4 * h)).sum

/-- A length of the pad that suffices for all tables. -/
def padLen (h : ℕ) : ℕ := 2 ^ 10 * (h + 2) ^ 4 * (deltaF h + 1) ^ 2

/-- The pieces with ρ = 1/√2. -/
def halfF (c₀ c : ℕ) : PiecesF where
  cnt _ lam := 4 * hF c₀ lam + 1
  d _ lam := factN (hF c₀ lam)
  cap tr _ lam i := min (2 * c * lam)
    (Nat.clog 2 (bif tr then RcolF (hF c₀ lam) (sOf (hF c₀ lam) i) else RrowF (hF c₀ lam) (sOf (hF c₀ lam) i)))
  top := partH c₀ true
  bot := partH c₀ false
  need _ lam := c * lam
  bits _ lam := (2 * lam) ^ c
  m := c

end ClauseBound.Inst.Half
