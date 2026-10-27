/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import AppVariablesStatement
import all ClauseBound.ParityChecks.StepOne
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.List.GetD

/-! # Appendix D, Step 1, as printed: parity checks, and a cut-off modulo a power of 2

This file proves these statements of the section «Step 1» of `AppVariablesStatement.lean`:

* display (63): if X(𝓛) = 0, then F(𝓛) is the number of satisfying assignments;
* if m ≤ n̄, the empty list has X = 0;
* Lemma 12 (Cut-off);
* display (65);
* «The residues determine the numbers».

The proofs are the printed ones. The three cases of display (63) for one ξ and the cut-off for
checks numbered by `Fin r` are in `proof/rates/ClauseBound/ParityChecks/StepOne.lean`, the latter in
a more
general form (a second set of checks with weights (−2)^i, here empty); this file passes from a list
of checks to numbered checks, proves that X(𝓛) = 0 makes the product over j vanish at every ξ with
|V(ξ)| > n̄ (the terms of X(𝓛) are nonnegative), and writes φ(ξ) as a sum over sets Π_0. -/

public section

namespace VariableBound.StepParity

open Finset ParityChecks AppVariables

variable {X E : Type} [DecidableEq E]

/-! ### From a list of checks to numbered checks -/

/-- The product over the checks of a list is the product over their numbers j : Fin r; check number
j is `L.getD j ∅`. -/
theorem allEven_eq_fin (V : X → Finset E) (L : List (Finset E)) (ξ : X) : allEven V L ξ = ∏ j : Fin L.length, ev #(L.getD j ∅ ∩ V ξ) := by
  rw [allEven, ← Fin.prod_univ_fun_getElem]
  exact prod_congr rfl fun j _ => by rw [List.getD_eq_getElem _ _ j.isLt]

/-- The product over the checks of a list is the product over their numbers j < r. -/
theorem allEven_eq_range (V : X → Finset E) (L : List (Finset E)) (ξ : X) : allEven V L ξ = ∏ j ∈ range L.length, ev #(L.getD j ∅ ∩ V ξ) := by
  rw [allEven_eq_fin, prod_range fun j => ev #(L.getD j ∅ ∩ V ξ)]

/-- [q even] is at least 0. -/
theorem ev_nonneg (q : ℕ) : 0 ≤ ev q := by
  unfold ev; split_ifs <;> norm_num

/-- [q even] is at most 1. -/
theorem ev_le_one (q : ℕ) : ev q ≤ 1 := by
  unfold ev; split_ifs <;> norm_num

/-- The product over j is at least 0. -/
theorem allEven_nonneg (V : X → Finset E) (L : List (Finset E)) (ξ : X) : 0 ≤ allEven V L ξ := by
  rw [allEven_eq_fin]
  exact prod_nonneg fun j _ => ev_nonneg _

/-- The product over j is at most 1. -/
theorem allEven_le_one (V : X → Finset E) (L : List (Finset E)) (ξ : X) : allEven V L ξ ≤ 1 := by
  rw [allEven_eq_fin]
  exact prod_le_one (fun j _ => ev_nonneg _) fun j _ => ev_le_one _

/-- C(|A|, c)·y as a sum of y over the subsets of A with c elements. -/
theorem choose_mul {E : Type} (A : Finset E) (c : ℕ) (y : ℤ) : ((#A).choose c : ℤ) * y = ∑ _S₀ ∈ A.powerset with #_S₀ = c, y := by
  rw [sum_const, ← powersetCard_eq_filter, card_powersetCard, nsmul_eq_mul]

/-! ### Display (63) -/

/-- The terms of X(𝓛) are nonnegative. -/
theorem term_nonneg (V : X → Finset E) (nb : ℕ) (L : List (Finset E)) (ξ : X) : 0 ≤ ((#(V ξ)).choose (nb + 1) : ℤ) * allEven V L ξ :=
  mul_nonneg (Int.natCast_nonneg _) (allEven_nonneg V L ξ)

variable [Fintype X]

/-- If X(𝓛) = 0, then for every ξ with |V(ξ)| > n̄ the product over j is 0. -/
theorem allEven_eq_zero {V : X → Finset E} {nb : ℕ} {L : List (Finset E)} (h : Xsum V nb L = 0) {ξ : X} (hξ : nb < #(V ξ)) : allEven V L ξ = 0 := by
  have h1 := (sum_eq_zero_iff_of_nonneg fun ξ _ => term_nonneg V nb L ξ).1 h ξ (mem_univ ξ)
  have h2 : ((#(V ξ)).choose (nb + 1) : ℤ) ≠ 0 := Int.natCast_ne_zero.2 (Nat.choose_pos hξ).ne'
  exact (mul_eq_zero.1 h1).resolve_left h2

/-- If X(𝓛) = 0, then every ξ with |V(ξ)| > n̄ violates an odd number of clauses of some check. -/
theorem good_of_Xsum_eq_zero {V : X → Finset E} {nb : ℕ} {L : List (Finset E)} (h : Xsum V nb L = 0) (ξ : X) (hξ : nb < #(V ξ)) :
    ∃ j < L.length, Odd #(L.getD j ∅ ∩ V ξ) := by
  have h1 := allEven_eq_zero h hξ
  rw [allEven_eq_range, prod_eq_zero_iff] at h1
  obtain ⟨j, hj, h2⟩ := h1
  refine ⟨j, mem_range.1 hj, Nat.not_even_iff_odd.1 fun he => ?_⟩
  rw [ev, if_pos he] at h2
  exact one_ne_zero h2

/-- If X(𝓛) = 0, then η(ξ)·∏_j [ |V_j(ξ)| even ] = [V(ξ) = ∅] for every ξ. -/
theorem eta_mul_allEven {V : X → Finset E} {nb : ℕ} {L : List (Finset E)} (h : Xsum V nb L = 0) (ξ : X) :
    eta V nb ξ * allEven V L ξ = if V ξ = ∅ then 1 else 0 := by
  rw [allEven_eq_range]
  exact ClauseBound.ParityChecks.StepOne.product V nb L.length (fun j => L.getD j ∅) (good_of_Xsum_eq_zero h) ξ

/-- If X(𝓛) = 0, then F(𝓛) is the number of ξ with V(ξ) = ∅. -/
theorem Fsum_eq {V : X → Finset E} {nb : ℕ} {L : List (Finset E)} (h : Xsum V nb L = 0) : Fsum V nb L = #{ξ | V ξ = ∅} := by
  rw [Fsum, card_filter, Nat.cast_sum]
  refine sum_congr rfl fun ξ _ => ?_
  rw [eta_mul_allEven h]
  split_ifs <;> simp

/-! ### Lemma 12 (Cut-off) -/

/-- Lemma 12 (Cut-off), with implicit arguments. Hypotheses: ν ≥ 1 and M' ≥ ν − 1 + r. -/
theorem cutoff (V : X → Finset E) (L : List (Finset E)) (φ : X → ℤ) {ν M' : ℕ} (hν : 1 ≤ ν) (hM : ν - 1 + L.length ≤ M') :
    ∑ ξ, φ ξ * allEven V L ξ ≡ ∑ ξ, φ ξ * ∑ S ∈ tup V L M' ξ, ∏ j, sig #(S j) [ZMOD 2 ^ ν] := by
  refine Int.ModEq.sum fun ξ _ => Int.ModEq.mul_left _ ?_
  have h := ClauseBound.ParityChecks.StepOne.cutoff_one (M := M') (disjoint_empty_right (univ : Finset (Fin L.length))) (fun j => L.getD j ∅ ∩ V ξ) hν
    (by rw [card_univ, Fintype.card_fin]; exact hM)
  simp only [prod_empty, mul_one, union_empty] at h
  rw [allEven_eq_fin]
  exact h

end VariableBound.StepParity

namespace VariableBound

open Finset ParityChecks AppVariables StepParity

/-- Display (63): if X(𝓛) = 0, then F(𝓛) is the number of satisfying assignments of Φ. -/
theorem product : AppVariables.ProductStmt := fun _ _ _ _ _ _ _ _ h => Fsum_eq h

/-- Step 1, «If m ≤ n̄, the empty list has X = 0». -/
theorem emptyList : AppVariables.EmptyListStmt := by
  intro X E _ _ _ V nb h
  refine sum_eq_zero fun ξ _ => ?_
  rw [Nat.choose_eq_zero_of_lt (Nat.lt_succ_of_le ((card_le_univ (V ξ)).trans h)), Nat.cast_zero, zero_mul]

/-- Lemma 12 (Cut-off): for a list 𝓛 of r checks, a function φ with integer values, ν ≥ 1 and M' ≥ ν
− 1 + r, the sum of φ(ξ)·∏_j [ |V_j(ξ)| even ] over ξ is congruent modulo 2^ν to the sum of
φ(ξ)·Σ ∏_j σ_{|Π_j|}, the inner sum over the tuples with Π_j ⊆ V_j(ξ) and at most M' marks in all. -/
theorem lemCutoff : AppVariables.LemCutoff := fun _ _ _ _ _ V L φ _ _ hν hM => cutoff V L φ hν hM

/-- Display (65), for a list of r checks, β ≥ 1, M ≥ β − 1 + r and M ≥ n + r: Lemma 12 with (φ, ν) =
(C(|V|, n̄ + 1), β) and with (φ, ν) = (η, n + 1), and φ(ξ) written as a sum over sets Π_0 ⊆ V(ξ). -/
theorem xf : AppVariables.XFStmt := by
  intro X E _ _ _ V nb L β n M hβ hM hn
  constructor
  · simp only [← choose_mul]
    exact lemCutoff X E V L (fun ξ => ((#(V ξ)).choose (nb + 1) : ℤ)) β M hβ hM
  · simp only [← sum_mul]
    exact lemCutoff X E V L (eta V nb) (n + 1) M (Nat.succ_pos n) hn

/-- Step 1, «The residues determine the numbers»: if there are at most 2^n assignments, then 0 ≤
X(𝓛) ≤ 2^n·C(m, n̄ + 1) ≤ 2^(β − 1), where β = n + ⌈log C(m, n̄ + 1)⌉ + 1,
and 0 ≤ F(𝓛) ≤ 2^n if X(𝓛) = 0. -/
theorem residues : AppVariables.ResiduesStmt := by
  intro X E _ _ _ V nb L n hX
  have hX' : (Fintype.card X : ℤ) ≤ 2 ^ n := by exact_mod_cast hX
  refine ⟨⟨sum_nonneg fun ξ _ => term_nonneg V nb L ξ, ?_, ?_⟩, fun h => ?_⟩
  · have h1 : ∀ ξ ∈ (univ : Finset X), ((#(V ξ)).choose (nb + 1) : ℤ) * allEven V L ξ ≤ ((Fintype.card E).choose (nb + 1) : ℤ) := fun ξ _ =>
      (mul_le_of_le_one_right (Int.natCast_nonneg _) (allEven_le_one V L ξ)).trans
        (by exact_mod_cast Nat.choose_le_choose (nb + 1) (card_le_univ (V ξ)))
    refine (sum_le_card_nsmul _ _ _ h1).trans ?_
    rw [nsmul_eq_mul, card_univ]
    exact mul_le_mul_of_nonneg_right hX' (Int.natCast_nonneg _)
  · rw [pow_add]
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.le_pow_clog one_lt_two _) (by positivity)
  · rw [Fsum_eq h]
    exact ⟨Int.natCast_nonneg _, le_trans (by exact_mod_cast card_le_univ _) hX'⟩

end VariableBound
