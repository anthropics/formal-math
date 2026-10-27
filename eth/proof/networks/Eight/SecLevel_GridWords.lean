/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Eight.SecLevel_Grid
public import Eight.Level.Defs
import Mathlib.Tactic

/-! # Section 5 «One level of the recursion»: sentences of the proof of Proposition 3 for the networks that Algorithm 1 runs

Procedure CLIQUE of Algorithm 1 (`Eight.Level.levelAlg`) works with tables that take bit strings
written as lists, writes a function ι : ℛ → {0, …, t} as a number y < (t+1)^{|ℛ|}, whose digits in
base t + 1 are the values ι(q), and runs
the network `Eight.Level.netOfι g tr lam y Rm` (tr = false: rows, tr = true: columns), whose
settings and indices are words.

`netOfι_row` and `netOfι_col` say what this network is: the row network, or the column network, of
proof/networks/Eight/SecLevel_Grid.lean, for the tables carried to the grid and the function ι
written by y, with every setting and every index θ written
as a word (`Network.pull`). From this and the theorems of that file, several sentences of the proof
get a statement about the network that the algorithm runs:
display (34): `eqExpansion_words`; the settings: `netOfι_S`; «the value is Z_ι»: `value_netOfι`;
Definition 2 with P = g³λ and all values at most 2^{gB + g²t}: `netOfι_sized_t`; the totals:
`U_netOfι`; display (36): `eqMinTotal_words` (and `stMin` in proof/networks/Eight/Level/Min.lean). -/

public section

namespace Eight.Level

open Finset Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet
open Paper (Rectangle rectangles mem_rectangles FactorsThrough)

variable {g lam : ℕ}

/-! ## A function ι written as a number -/

theorem digOf_le (g lam y : ℕ) (q : Rectangle g) : digOf g lam y q ≤ tOf lam := Prog.digit_le _ _ _

theorem patOf_eq (g lam y : ℕ) {q : Rectangle g} (hq : q ∈ rectangles g) : patOf g lam y q = digOf g lam y q := if_pos hq

/-- The number of rectangles: |ℛ| is `nRect g`, the number that the algorithm uses. -/
theorem card_rectangles_eq (g : ℕ) : #(rectangles g) = nRect g := Paper.card_rectangles g

/-- The numbers y < (t+1)^{|ℛ|} write every function ι of display (34) exactly once: a sum over
these numbers is the sum over the functions. -/
theorem sum_patOf (g lam : ℕ) (F : (Rectangle g → ℕ) → ℤ) :
    ∑ y ∈ range ((tOf lam + 1) ^ nRect g), F (patOf g lam y) = ∑ ι ∈ patterns g lam, F ι := by
  rw [nRect_eq]
  exact sum_patG g g (tOf lam) F

/-- Z_ι depends only on the values of ι on ℛ. -/
theorem Zι_digOf (W : Inst (Fin g × Fin g) (Bits lam)) (y : ℕ) : Zι W (digOf g lam y) = Zι W (patOf g lam y) :=
  ZG_congr _ fun q hq => by rw [patOf_eq g lam y hq]

/-! ## Display (34) -/

/-- **Display (34)** for the clique that the algorithm is given: 2^{t|ℛ|} · Z = ∑_ι Z_ι.
`Inst.ZW lam [] Rm` is the value of the (g², λ)-clique whose tables Rm take strings written as
lists; the sum is over the numbers y that write the functions ι.
From `Eight.eqExpansion`. -/
theorem eqExpansion_words (hlam : 1 ≤ lam) (Rm : Inst (Fin (g * g)) (List Bool)) :
    2 ^ (tOf lam * nRect g) * Inst.ZW lam [] Rm = ∑ y ∈ range ((tOf lam + 1) ^ nRect g), Zι (gridR0 g g lam Rm) (patOf g lam y) := by
  rw [sum_patOf g lam fun ι => Zι (gridR0 g g lam Rm) ι, ZW_eq_Z lam Rm fun _ => false, ← card_rectangles_eq]
  exact eqExpansion hlam (instW lam Rm) (fun _ => false) finProdFinEquiv.symm

/-! ## What the networks of the algorithm are -/

/-- **The row network that the algorithm runs** is the row network of the proof of Proposition 3
(`Eight.rowNetwork`), for the tables carried to the grid and the function ι written by y, with
settings and indices written as words: a setting of a row
in g · g² · λ bits (`stC`), an index θ of two rows in c_{a,a'} bits (`gridCl`). -/
theorem netOfι_row (g lam y : ℕ) (Rm : Inst (Fin (g * g)) (List Bool)) :
    netOfι g false lam y Rm = (rowNetwork (gridR0 g g lam Rm) (digOf g lam y)).pull (fun _ => g * (g * g) * lam) (fun _ => stC g g false lam)
      (gridCl eightF [] g g false 0 lam y (gridR g g false lam Rm)) := rfl

/-- **The column network that the algorithm runs** is the column network of the proof of Proposition
3 (`Eight.colNetwork`), with settings and indices written as words. -/
theorem netOfι_col (g lam y : ℕ) (Rm : Inst (Fin (g * g)) (List Bool)) :
    netOfι g true lam y Rm = (colNetwork (gridR0 g g lam Rm) (digOf g lam y)).pull (fun _ => g * (g * g) * lam) (fun _ => stC g g true lam)
      (gridCl eightF [] g g true 0 lam y (gridR g g true lam Rm)) := rfl

/-- «S_a is the set of these tuples, encoded by concatenation in g(g² − 1)λ ≤ P bits, where P =
g³λ.» Different from the paper: the settings are all words of exactly g³λ bits, because a setting of
a grid point has a dummy string for the grid point
itself (see `Eight.eqExpansion`). -/
theorem netOfι_S (g : ℕ) (tr : Bool) (lam y : ℕ) (Rm : Inst (Fin (g * g)) (List Bool)) (a : Fin (nParts g g tr)) :
    (netOfι g tr lam y Rm).S a = words (g ^ 3 * lam) := by
  have e : g * (g * g) * lam = g ^ 3 * lam := by ring
  cases tr
  · rw [netOfι_row, ← e]
    rfl
  · rw [netOfι_col, ← e]
    rfl

/-! ## «Each factor in (34) is used exactly once, so the value is Z_ι» -/

/-- Both networks that the algorithm runs have the value Z_ι of display (34). From
`Eight.value_rowNetwork` and `Eight.value_colNetwork`: writing the settings as words does not change
the value, because every word of the right length writes a setting. -/
theorem value_netOfι (hlam : 1 ≤ lam) (g : ℕ) (tr : Bool) (y : ℕ) (Rm : Inst (Fin (g * g)) (List Bool)) :
    (netOfι g tr lam y Rm).value = Zι (gridR0 g g lam Rm) (patOf g lam y) := by
  rw [← Zι_digOf]
  cases tr
  · rw [netOfι_row, ← value_rowNetwork hlam (gridR0 g g lam Rm) (digOf_le g lam y)]
    exact Network.value_pull (rowNetwork (gridR0 g g lam Rm) (digOf g lam y)) _ _ _ fun _ => stC_full g g false lam
  · rw [netOfι_col, ← value_colNetwork hlam (gridR0 g g lam Rm) (digOf_le g lam y)]
    exact Network.value_pull (colNetwork (gridR0 g g lam Rm) (digOf g lam y)) _ _ _ fun _ => stC_full g g true lam

/-! ## Definition 2 with P = g³λ and B₁ -/

/-- Both networks that the algorithm runs satisfy conditions (i) and (ii) of Definition 2 with P =
g³λ and all values at most 2^{gB + g²t}; this is the form that the proof of the cost of a level
uses. From `Eight.rowNetwork_sized_t` and
`Eight.colNetwork_sized_t`. `BoundedInst lam B Rm`: the tables are at most 2^B in absolute value at
the queries that are asked. -/
theorem netOfι_sized_t {B : ℕ} (hlam : 1 ≤ lam) (g : ℕ) (tr : Bool) (y : ℕ) {Rm : Inst (Fin (g * g)) (List Bool)} (hR : BoundedInst lam B Rm) :
    (netOfι g tr lam y Rm).Sized (g ^ 3 * lam) (g * B + g ^ 2 * tOf lam) := by
  have hW : ∀ w h, |gridR0 g g lam Rm w h| ≤ 2 ^ B := abs_gridR_le false hR
  cases tr
  · rw [netOfι_row]
    exact Network.sized_pull_of_le (rowNetwork (gridR0 g g lam Rm) (digOf g lam y)) _ _ _ (rowNetwork_sized_t hlam _ hW (digOf_le g lam y)) fun _ => le_of_eq (by ring)
  · rw [netOfι_col]
    exact Network.sized_pull_of_le (colNetwork (gridR0 g g lam Rm) (digOf g lam y)) _ _ _ (colNetwork_sized_t hlam _ hW (digOf_le g lam y)) fun _ => le_of_eq (by ring)

/-! ## The smaller total (36) -/

/-- The number that the algorithm computes for a network (`totalG`) is its total U. -/
theorem U_netOfι (g : ℕ) (tr : Bool) (lam y : ℕ) (Rm : Inst (Fin (g * g)) (List Bool)) :
    (netOfι g tr lam y Rm).U = totalG eightF g g tr 0 lam y := U_gridN eightF [] g g tr 0 lam y Rm

/-- **Display (36)** for the two networks that the algorithm runs: min(U_row, U_col) ≤ N(ρ + 1/g) +
2g⁴, N = g⁴λ, ρ = 11/12. From `Eight.eqMinTotal`. -/
theorem eqMinTotal_words (hlam : 1 ≤ lam) (g y : ℕ) (Rm : Inst (Fin (g * g)) (List Bool)) :
    ((min (netOfι g false lam y Rm).U (netOfι g true lam y Rm).U : ℕ) : ℝ) ≤ rho * ((g : ℝ) ^ 4 * lam) + (g : ℝ) ^ 3 * lam + 2 * (g : ℝ) ^ 4 := by
  rw [netOfι_row, netOfι_col]
  exact eqMinTotal hlam (gridR0 g g lam Rm) (digOf_le g lam y)

end Eight.Level
