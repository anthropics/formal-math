/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import NetworkStatements
public import StepMachines.Prog.Spec
public import StepMachines.Prog.Comb
public import StepMachines.Math.GridArith

/-! One level of the recursion as a program, the boundary between the loop over the patterns and the
two networks of a term:
patterns ι ∈ {0,…,λ}^R as numbers y < (λ+1)^R, where R = C(g,2)² is the number of rectangles (the
digits of y in base λ+1
are the numbers ι_q); what the rectangles cost in the row and in the column network; and what the
loop needs of the two
networks. -/

@[expose] public section

namespace Groundwork.Prog

open Finset Stepped

/-! ### Patterns as numbers, and what a rectangle costs -/

/-- R = C(g,2)², the number of rectangles of the g × g grid. -/
def nRect (g : ℕ) : ℕ := g.choose 2 ^ 2

/-- ι_q, the digit number q of the counter y in base n + 1. -/
def digit (n y q : ℕ) : ℕ := y / (n + 1) ^ q % (n + 1)

/-- The number of binary digits of 3^c: enough to write any number below 3^c (for c ≥ 1 no fewer
will do; tb 0 = 1, one bit to
spare). -/
def tb (c : ℕ) : ℕ := Nat.size (3 ^ c)

theorem tb_le (c : ℕ) : tb c ≤ 2 * c + 1 := by
  unfold tb
  rw [Nat.size_le]
  calc 3 ^ c ≤ 4 ^ c := Nat.pow_le_pow_left (by norm_num) c
    _ = 2 ^ (2 * c) := by rw [pow_mul]; norm_num
    _ < 2 ^ (2 * c + 1) := Nat.pow_lt_pow_right (by omega) (by omega)

/-- The number of bits of the name of a string of n symbols out of four of which at most c differ
from a fixed one:
n bits for the set of these positions, then one number below 3^c. -/
def capW (n c : ℕ) : ℕ := n + tb c

/-- What the rectangles cost in the row network of the pattern y (strings with at most n − ι_q
symbols other than the
singlet). Every rectangle counts twice, since `Network.U` sums over ordered pairs of nodes. -/
def priceRow (g n y : ℕ) : ℕ := 2 * ∑ q ∈ range (nRect g), capW n (n - digit n y q)

/-- What the rectangles cost in the column network of the pattern y (strings with at most ι_q
symbols other than Φ⁺). -/
def priceCol (g n y : ℕ) : ℕ := 2 * ∑ q ∈ range (nRect g), capW n (digit n y q)

theorem digit_le (n y q : ℕ) : digit n y q ≤ n := Nat.lt_succ_iff.1 (Nat.mod_lt _ (Nat.succ_pos _))

/-- The cheaper total is at most the average: at most ρ·g⁴λ + g⁴/2 bits. -/
theorem min_price_le (g n y : ℕ) :
    ((min (priceRow g n y) (priceCol g n y) : ℕ) : ℝ) ≤ ρ * ((g : ℝ) ^ 4 * n) + (g : ℝ) ^ 4 / 2 := by
  have hsum : priceRow g n y + priceCol g n y
      = 2 * ∑ q ∈ range (nRect g), (capW n (n - digit n y q) + capW n (digit n y q)) := by
    unfold priceRow priceCol
    rw [← Nat.mul_add, ← Finset.sum_add_distrib]
  have hq : ((∑ q ∈ range (nRect g), (capW n (n - digit n y q) + capW n (digit n y q)) : ℕ) : ℝ)
      ≤ (nRect g : ℝ) * (4 * ρ * n + 2) := by
    rw [Nat.cast_sum]
    calc _ ≤ ∑ _q ∈ range (nRect g), (4 * ρ * n + 2) :=
          Finset.sum_le_sum fun q _ => GridArith.cap_pair_le (digit_le n y q)
      _ = _ := by rw [Finset.sum_const, card_range, nsmul_eq_mul]
  have hmin : 2 * min (priceRow g n y) (priceCol g n y) ≤ priceRow g n y + priceCol g n y := by omega
  have hmin' : 2 * ((min (priceRow g n y) (priceCol g n y) : ℕ) : ℝ)
      ≤ 2 * ((∑ q ∈ range (nRect g), (capW n (n - digit n y q) + capW n (digit n y q)) : ℕ) : ℝ) := by
    rw [hsum] at hmin
    exact_mod_cast hmin
  have hR : 4 * (nRect g : ℝ) ≤ (g : ℝ) ^ 4 := by exact_mod_cast GridArith.four_mul_choose_sq_le g
  have hρ : 0 ≤ 4 * ρ * n + 2 := by
    have : 0 ≤ ρ := by unfold ρ; exact div_nonneg (Real.logb_nonneg (by norm_num) (by norm_num)) (by norm_num)
    positivity
  have := mul_le_mul_of_nonneg_right hR hρ
  linarith

/-! ### The boundary between the loop and the two networks -/

/-- Presents is monotone in the bounds. -/
theorem PNet.Presents.mono {C : Type} {Np : PNet C} {c : C} {g : ℕ} {N : Network (Fin g) (List Bool) (List Bool)}
    {t t' S S' : ℕ} (h : Np.Presents c N t S) (ht : t ≤ t') (hS : S ≤ S') : Np.Presents c N t' S' :=
  ⟨h.S_eq, h.c_eq, h.lab_eq, fun a z hz => (h.W_runs a z hz).mono ht hS,
    fun a b z θ hab hz hθ => (h.f_runs a b z θ hab hz hθ).mono ht hS⟩

/-- From the length function and the procedure of an instance on g² nodes, a network on g nodes
given by procedures,
in the contexts (c, y), y the pattern. -/
abbrev NetFormer : Type 1 :=
  {C : Type} → [HasSize C] → (C → ℕ) → Stepped (C × IQ) ℤ → PNet (C × ℕ)

/-- The row or the column network, with bit strings as states and labels, as a function of λ, of the
instance and of the
pattern y. -/
abbrev SideNet (g : ℕ) : Type :=
  ℕ → Inst (Fin (g * g)) (List Bool) → ℕ → Network (Fin g) (List Bool) (List Bool)

/-- The entries of Rm are at most 2^B in absolute value at the queries that are asked: labels of
length n, the empty word at
the node itself. -/
def BoundedInst {K : ℕ} (n B : ℕ) (Rm : Inst (Fin K) (List Bool)) : Prop :=
  ∀ v θ, (∀ u, u ≠ v → (θ u).length = n) → θ v = [] → |Rm v θ| ≤ 2 ^ B

/-- The counters y < (n+1)^R are the patterns: summing over y is summing over all families of R
digits. -/
theorem sum_digits (n R : ℕ) (F : (Fin R → ℕ) → ℤ) :
    ∑ y ∈ range ((n + 1) ^ R), F (fun q => digit n y q) = ∑ ι ∈ Fintype.piFinset fun _ : Fin R => range (n + 1), F ι := by
  rw [Finset.sum_range fun y => F fun q : Fin R => digit n y q,
    ← (finFunctionFinEquiv (m := n + 1) (n := R)).sum_comp]
  refine Finset.sum_bij' (fun f _ q => (f q).val)
    (fun ι hι q => ⟨ι q, Finset.mem_range.1 (Fintype.mem_piFinset.1 hι q)⟩) ?_ ?_ ?_ ?_ ?_
  · exact fun f _ => Fintype.mem_piFinset.2 fun q => Finset.mem_range.2 (f q).2
  · exact fun _ _ => Finset.mem_univ _
  · exact fun _ _ => rfl
  · exact fun _ _ => rfl
  · intro f _
    congr 1
    funext q
    have := congrFun (finFunctionFinEquiv.symm_apply_apply f) q
    rw [← this]
    rfl

end Groundwork.Prog
