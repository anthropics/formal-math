/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import CountedRecursion.ParentNumbers
public import CountedRecursion.Within
import Mathlib.Tactic

/-! # The procedure for W_a

`rowWeight_within`: on a setting z of the row a, the procedure `rowWeight` returns W_a(z) of the
network of the pattern within g·(tq + 1) operations, if a query to the tables of the clique costs
tq: «W_a is the product of the g table entries of row a and of the factors of the straight edges
inside row a» (proof of Proposition 3). The bound on the states is explicit.
Also here: what the procedures that compute the network of a pattern have in common (the oracle,
sizes of answers). -/

public section

namespace ExplicitCost

open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet ClauseBound.Alg.GridPresents Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed

variable {D : PiecesCounted.Data} {c g lam y B tq Lam : ℕ} {tr : Bool} {W : ℕ → List Bool → ℤ}

/-- The oracle of the procedures: the tables of the clique on g² nodes, and the pieces. -/
abbrev upOracle (D : PiecesCounted.Data) (g lam Lam : ℕ) (W : ℕ → List Bool → ℤ) : UpQuery → Option Ans := Sum.elim (answersOf (g * g) lam W) (piecesUpTo D Lam)

/-- An integer below 2^n in absolute value, as an answer, has size at most n + 2. -/
theorem size_answer {v : ℤ} {n : ℕ} (h : |v| < 2 ^ n) : size (Sum.inl v : Ans) ≤ n + 2 := by
  have := size_entry h
  change size v + 1 ≤ n + 2
  omega

/-- A counter below n has size at most the size of n. -/
theorem size_lt_le {i n : ℕ} (h : i < n) : size i ≤ size n := by
  simp only [size_nat]
  exact Nat.succ_le_succ (Nat.size_le_size h.le)

/-- The size of (2^n)^k. -/
theorem size_two_pow_pow (n k : ℕ) : size ((2 ^ n) ^ k) = n * k + 2 := by
  rw [← pow_mul, size_nat, Nat.size_pow]

/-- A legitimate query to the tables is answered by the entry. -/
theorem answersOf_eq {K : ℕ} {q : TableQuery} (h1 : q.1 < K) (h2 : q.2.length = (K - 1) * lam) : answersOf K lam W q = some (Sum.inl (W q.1 q.2)) := by
  unfold answersOf tables
  rw [if_pos ⟨h1, h2⟩]
  rfl

/-- ι(q) is in 𝓘. -/
theorem dig_mem {ρ : ℝ} {x₀ : ℕ} (hS : Setting ρ c x₀ D) (hlam : 1 ≤ lam) (g : ℕ) (tr : Bool) (y q κ : ℕ) : indexAt D lam (digG (piecesOf D c) g tr 0 lam y q κ) ∈ (D.fam lam).I :=
  indexAt_mem D lam (digG_lt (P := piecesOf D c) (h := 0) (ℓ := lam) (card_I_pos hS.is hlam) g tr y q κ)

/-- **The procedure for W_a.** -/
theorem rowWeight_within {p : Parent} (hG : pG p = g) (hL : pLam p = lam) (hT : pTr p = tr) (hg : 1 ≤ g) (hW : ∀ w < g * g, ∀ z ∈ words ((g * g - 1) * lam), |W w z| < 2 ^ B)
    (a : Fin (nParts g g tr)) {z : List Bool} (hz : z.length = nMemb g g tr * (g * g) * lam) :
    rowWeight.Within (upOracle D g lam Lam W) (upPrices c tq) (p, (a.val, z)) (g * (tq + 1)) (2 * size (p, (a.val, z)) + 2 * size g + B * g + B + 8) ((patternNet D c g tr lam y W).W a z) := by
  subst hG hL hT
  rw [weight_eq a hz]
  by_cases hc : chkG (pG p) (pG p) (pTr p) (pLam p) (a.val, z) = true
  · rw [if_pos hc, nMemb_self]
    have hbody : ∀ i < pG p, (askInt fun v : (Parent × WQ) × ℕ => (Sum.inl (toTable (pointQuery (pG v.1.1) (pTr v.1.1) (pLam v.1.1) v.1.2 v.2)) : UpQuery)).Within
        (upOracle D (pG p) (pLam p) Lam W) (upPrices c tq) ((p, (a.val, z)), i) tq (size (p, (a.val, z)) + size (pG p) + B + 3)
        (W (toTable (pointQuery (pG p) (pTr p) (pLam p) (a.val, z) i)).1 (toTable (pointQuery (pG p) (pTr p) (pLam p) (a.val, z) i)).2) := by
      intro i hi
      obtain ⟨q1, q2⟩ := pointQuery_ok a hz (by rw [nMemb_self]; exact hi)
      have hq := query_within (A := Ans) (h := fun v : (Parent × WQ) × ℕ => (Sum.inl (toTable (pointQuery (pG v.1.1) (pTr v.1.1) (pLam v.1.1) v.1.2 v.2)) : UpQuery))
        (O := upOracle D (pG p) (pLam p) Lam W) (w := upPrices c tq) (a := ((p, (a.val, z)), i)) (answersOf_eq q1 q2)
      dsimp only at hq
      refine (mapOut_within (g := asInt) hq).mono le_rfl ?_
      have s1 := size_answer (hW _ q1 _ (mem_words.2 q2))
      have s2 := size_lt_le hi
      have s3 : size ((p, (a.val, z)), i) = size (p, (a.val, z)) + size i := rfl
      omega
    have hprod := prodRange_within (N := fun x : Parent × WQ => pG x.1) (a := (p, (a.val, z))) (fun _ => tq)
      (fun i => W (toTable (pointQuery (pG p) (pTr p) (pLam p) (a.val, z) i)).1 (toTable (pointQuery (pG p) (pTr p) (pLam p) (a.val, z) i)).2) (2 ^ B) _ Nat.one_le_two_pow hbody
      fun i hi => by
        obtain ⟨q1, q2⟩ := pointQuery_ok a hz (by rw [nMemb_self]; exact hi)
        exact Table.natAbs_le (hW _ q1 _ (mem_words.2 q2)).le
    dsimp only at hprod
    refine (ite_within_true (p := fun x : Parent × WQ => chkG (pG x.1) (pG x.1) (pTr x.1) (pLam x.1) x.2) (a := (p, (a.val, z))) hc hprod).mono (le_of_eq ?_) ?_
    · rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
    · have := size_two_pow_pow B (pG p)
      omega
  · rw [if_neg hc]
    rw [Bool.not_eq_true] at hc
    refine (ite_within_false (p := fun x : Parent × WQ => chkG (pG x.1) (pG x.1) (pTr x.1) (pLam x.1) x.2) (a := (p, (a.val, z))) hc (lift_within (Stepped.const_runs (0 : ℤ) _))).mono ?_ ?_
    · exact Nat.mul_pos hg (Nat.succ_pos _)
    · have : size (0 : ℤ) = 1 := rfl
      omega

end ExplicitCost
