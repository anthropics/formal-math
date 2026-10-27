/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ClauseBound.ParityChecks.BridgeInc
public import ClauseBound.ParityChecks.StepOne

/-! # The sums over marks in three layers (for B_i) and in two layers (for A and the count) are 2^r times B_i, A and the count, modulo 2^{M+1}

An assignment of the n + r variables is a pair (ξ, y) of an assignment of the variables of the
formula and of values of the dummy variables. The numbers of violated clauses of the three layers
for B_i are
the numbers of elements of V(ξ), of D ∩ V(ξ), where D = `Dof` ψ t is a set of clauses, and of the
set of the violated incidences; the two layers for A and the count are the first and the last of
these. A sum Σ_{q ≤ M} w^q·C(c, q) is the sum of w^|S| over the subsets S with at most M elements of
a set with c elements.
So each sum is the right side of a form of the Cut-off lemma (Lemma 12) with dummy variables,
`Dummy.cutoff_dummy`, for f = ω·C(|D ∩ V(ξ)|, i), f = ω and f = η, where ω(ξ) = C(|V(ξ)|, n̄ + 1)
and η(ξ) is the sum of (-1)^|S| over the sets S ⊆ V(ξ) with |S| ≤ n̄, as in Step 1 of Appendix D.
B_i is `Bint`, and A is the sum over ξ of ω(ξ) times the parity brackets of the checks before j. For
the count, the identity `StepOne.product` of Step 1 of Appendix D turns the left side into the
number of satisfying assignments. -/

public section

open Finset ParityChecks

namespace ClauseBound.ParityChecks.Bridge

open Groundwork.Prog (Fml)
open PaddedDescent.F.Mark (nvio vio nSat)
open ClauseBound.TopN.EvalW (truncW)
open ClauseBound.ParityChecks ClauseBound.ParityChecks.BridgeInc

/-! ### Sums and products -/

/-- Σ_{q ≤ M} w^q·C(|T|, q) is the sum of w^|S| over the subsets S of T with at most M elements. -/
theorem sum_Icc_choose {α : Type} (w : ℤ) (M : ℕ) (T : Finset α) :
    ∑ q ∈ Icc 0 M, w ^ q * ((#T).choose q : ℤ) = ∑ S ∈ T.powerset with #S ≤ M, w ^ #S := by
  rw [sum_filter, sum_powerset_apply_card fun q => if q ≤ M then w ^ q else 0]
  have h1 : Icc 0 M = (range (M + #T + 1)).filter (· ≤ M) := by
    ext q
    simp only [mem_Icc, mem_filter, mem_range]
    omega
  have h2 : ∑ m ∈ range (#T + 1), (#T).choose m • (if m ≤ M then w ^ m else 0) =
      ∑ m ∈ range (M + #T + 1), (#T).choose m • (if m ≤ M then w ^ m else 0) :=
    sum_subset (range_subset_range.2 (by omega)) fun q _ hq => by
      rw [Nat.choose_eq_zero_of_lt (by simpa using hq), zero_smul]
  rw [h1, h2, sum_filter]
  refine sum_congr rfl fun q _ => ?_
  split_ifs
  · rw [nsmul_eq_mul, mul_comm]
  · rw [smul_zero]

/-- The sum with one value of q and the weight 1. -/
theorem sum_Icc_self (a v : ℕ) : ∑ q ∈ Icc a a, (1 : ℤ) ^ q * (v.choose q : ℤ) = (v.choose a : ℤ) := by
  rw [Icc_self, sum_singleton, one_pow, one_mul]

/-- A sum over the assignments of n + r variables is a sum over the two parts. -/
theorem sum_split {n r : ℕ} (F : (Fin n → Bool) → (Fin r → Bool) → ℤ) :
    ∑ σ : Fin (n + r) → Bool, F (xi σ) (yy σ) = ∑ ξ, ∑ y, F ξ y := by
  rw [← Fintype.sum_prod_type']
  exact Fintype.sum_equiv (Fin.appendEquiv n r).symm _ _ fun _ => rfl

/-- The sum over marks in three layers, written out. -/
theorem truncW3 (N : ℕ) (w₀ w₁ w₂ : ℤ) (l₀ l₁ l₂ h₀ h₁ h₂ : ℕ) (L₀ L₁ L₂ : Fml) :
    truncW N [w₀, w₁, w₂] [l₀, l₁, l₂] [h₀, h₁, h₂] [L₀, L₁, L₂] = ∑ σ : Fin N → Bool,
      (∑ q ∈ Icc l₀ h₀, w₀ ^ q * ((nvio (PaddedDescent.F.Mark.ext σ) L₀).choose q : ℤ)) *
        ((∑ q ∈ Icc l₁ h₁, w₁ ^ q * ((nvio (PaddedDescent.F.Mark.ext σ) L₁).choose q : ℤ)) *
          ((∑ q ∈ Icc l₂ h₂, w₂ ^ q * ((nvio (PaddedDescent.F.Mark.ext σ) L₂).choose q : ℤ)) * 1)) := rfl

/-- The sum over marks in two layers, written out. -/
theorem truncW2 (N : ℕ) (w₀ w₁ : ℤ) (l₀ l₁ h₀ h₁ : ℕ) (L₀ L₁ : Fml) :
    truncW N [w₀, w₁] [l₀, l₁] [h₀, h₁] [L₀, L₁] = ∑ σ : Fin N → Bool,
      (∑ q ∈ Icc l₀ h₀, w₀ ^ q * ((nvio (PaddedDescent.F.Mark.ext σ) L₀).choose q : ℤ)) *
        ((∑ q ∈ Icc l₁ h₁, w₁ ^ q * ((nvio (PaddedDescent.F.Mark.ext σ) L₁).choose q : ℤ)) * 1) := rfl

/-! ### The three sums -/

/-- The sum for B_i is 2^r·B_i modulo 2^{M+1}. -/
theorem stBridgeB : StBridgeB := by
  intro n r nb M i j t ψ Lam hψ hW hj
  have e : sumB n r nb M i ψ Lam j t = ∑ ξ, ((omega (Vof (n := n) ψ) nb ξ : ℤ) * ((#(Dof ψ t ∩ Vof ψ ξ)).choose i : ℤ)) *
      ∑ y : Fin r → Bool, ∑ S ∈ (Dummy.inc (Vof (n := n) ψ) r (Lof ψ Lam) (J1 r j) (J2 r j) ξ y).powerset with #S ≤ M, (-2 : ℤ) ^ #S := by
    rw [sumB, truncW3, ← sum_congr rfl fun ξ _ => (mul_sum _ _ _).symm,
      ← sum_split fun ξ y => ((omega (Vof (n := n) ψ) nb ξ : ℤ) * ((#(Dof ψ t ∩ Vof ψ ξ)).choose i : ℤ)) *
        ∑ S ∈ (Dummy.inc (Vof (n := n) ψ) r (Lof ψ Lam) (J1 r j) (J2 r j) ξ y).powerset with #S ≤ M, (-2 : ℤ) ^ #S]
    refine sum_congr rfl fun σ _ => ?_
    rw [sum_Icc_self, sum_Icc_self, nvio_all hψ, nvio_incL hψ hW hj.le, nvio_drop hψ, sum_Icc_choose, omega]
    ring
  rw [e]
  refine (Dummy.cutoff_dummy (Vof (n := n) ψ) r (Lof ψ Lam) (J1 r j) (J2 r j) (disjoint_J r j) _ M).symm.trans ?_
  have e2 : ∑ ξ, ((omega (Vof (n := n) ψ) nb ξ : ℤ) * ((#(Dof ψ t ∩ Vof ψ ξ)).choose i : ℤ)) *
      (∏ j' ∈ J1 r j, ev #(Lof ψ Lam j' ∩ Vof ψ ξ)) * ∏ j' ∈ J2 r j, (-1 : ℤ) ^ #(Lof ψ Lam j' ∩ Vof ψ ξ) =
      Bint (Vof (n := n) ψ) nb i j (Lof ψ Lam) (Dof ψ t) := by
    unfold Bint
    refine sum_congr rfl fun ξ _ => ?_
    rw [prod_J1 hj.le fun j' => ev #(Lof ψ Lam j' ∩ Vof ψ ξ), prod_J2 hj fun j' => (-1 : ℤ) ^ #(Lof ψ Lam j' ∩ Vof ψ ξ)]
    ring
  rw [e2]

/-- A sum over marks in two layers, the second one the incidences of the complete checks before j,
is 2^r·Σ_ξ f(ξ)·∏_{j' < j} [|V_j'(ξ)| even] modulo 2^{M+1}. -/
theorem two_layers {n r j : ℕ} {ψ : Fml} {Lam : List (List ℕ)} (hψ : ∀ C ∈ ψ, ∀ l ∈ C, l.1 < n) (hW : WfC ψ r Lam) (hj : j ≤ r) (M : ℕ)
    (w : ℤ) (l h : ℕ) (f : (Fin n → Bool) → ℤ) (hf : ∀ ξ, ∑ q ∈ Icc l h, w ^ q * ((#(Vof ψ ξ)).choose q : ℤ) = f ξ) :
    truncW (n + r) [w, -2] [l, 0] [h, M] [ψ, incL n ψ (Lam.take j) j] ≡
      2 ^ r * ∑ ξ, f ξ * ∏ j' ∈ range j, ev #(Lof ψ Lam j' ∩ Vof ψ ξ) [ZMOD 2 ^ (M + 1)] := by
  have e : truncW (n + r) [w, -2] [l, 0] [h, M] [ψ, incL n ψ (Lam.take j) j] = ∑ ξ, f ξ *
      ∑ y : Fin r → Bool, ∑ S ∈ (Dummy.inc (Vof (n := n) ψ) r (Lof ψ Lam) (J1 r j) ∅ ξ y).powerset with #S ≤ M, (-2 : ℤ) ^ #S := by
    rw [truncW2, ← sum_congr rfl fun ξ _ => (mul_sum _ _ _).symm,
      ← sum_split fun ξ y => f ξ *
        ∑ S ∈ (Dummy.inc (Vof (n := n) ψ) r (Lof ψ Lam) (J1 r j) ∅ ξ y).powerset with #S ≤ M, (-2 : ℤ) ^ #S]
    refine sum_congr rfl fun σ _ => ?_
    rw [nvio_all hψ, nvio_incL_take hψ hW hj, sum_Icc_choose, hf, mul_one]
  rw [e]
  refine (Dummy.cutoff_dummy (Vof (n := n) ψ) r (Lof ψ Lam) (J1 r j) ∅ (disjoint_empty_right _) f M).symm.trans ?_
  have e2 : ∑ ξ, f ξ * (∏ j' ∈ J1 r j, ev #(Lof ψ Lam j' ∩ Vof ψ ξ)) * ∏ j' ∈ (∅ : Finset (Fin r)), (-1 : ℤ) ^ #(Lof ψ Lam j' ∩ Vof ψ ξ) =
      ∑ ξ, f ξ * ∏ j' ∈ range j, ev #(Lof ψ Lam j' ∩ Vof ψ ξ) := by
    refine sum_congr rfl fun ξ _ => ?_
    rw [prod_J1 hj fun j' => ev #(Lof ψ Lam j' ∩ Vof ψ ξ), prod_empty, mul_one]
  rw [e2]

/-- The sum for A is 2^r·A modulo 2^{M+1}. -/
theorem stBridgeA : StBridgeA := by
  intro n r nb M j ψ Lam hψ hW hj
  exact two_layers hψ hW hj M 1 (nb + 1) (nb + 1) (fun ξ => (omega (Vof (n := n) ψ) nb ξ : ℤ)) fun ξ => sum_Icc_self _ _

/-- A clause is not violated iff one of its literals is true. -/
theorem not_vio_iff (σ : ℕ → Bool) (C : List (ℕ × Bool)) : ¬ vio σ C = true ↔ ∃ l ∈ C, σ l.1 = l.2 := by
  unfold vio
  rw [List.all_eq_true]
  simp only [not_forall, exists_prop, bne_iff_ne, ne_eq, not_not]

/-- ξ violates no clause iff it satisfies the formula. -/
theorem Vof_eq_empty_iff {n : ℕ} (ψ : Fml) (ξ : Fin n → Bool) :
    Vof ψ ξ = ∅ ↔ ∀ C ∈ ψ, ∃ l ∈ C, PaddedDescent.F.Mark.ext ξ l.1 = l.2 := by
  rw [Vof, filter_eq_empty_iff]
  constructor
  · intro H C hC
    obtain ⟨e, he, rfl⟩ := List.mem_iff_getElem.1 hC
    have h1 := H (mem_univ (⟨e, he⟩ : Fin ψ.length))
    rw [List.getD_eq_getElem _ _ he] at h1
    exact (not_vio_iff _ _).1 h1
  · intro H e _
    have h1 := H _ (List.getElem_mem e.2)
    rw [List.getD_eq_getElem _ _ e.2]
    exact (not_vio_iff _ _).2 h1

/-- The sum for the final count is 2^r times the number of satisfying assignments modulo 2^{M+1}, if
the checks are good. -/
theorem stBridgeF : StBridgeF := by
  intro n r nb M ψ Lam hψ hW hG
  refine (two_layers hψ hW le_rfl M (-1) 0 nb (fun ξ => ∑ S ∈ (Vof ψ ξ).powerset with #S ≤ nb, (-1 : ℤ) ^ #S)
    fun ξ => sum_Icc_choose _ _ _).trans ?_
  have e : ∑ ξ : Fin n → Bool, (∑ S ∈ (Vof ψ ξ).powerset with #S ≤ nb, (-1 : ℤ) ^ #S) * ∏ j' ∈ range r, ev #(Lof ψ Lam j' ∩ Vof ψ ξ) =
      (nSat n ψ : ℤ) := by
    rw [sum_congr rfl fun ξ _ => StepOne.product (Vof (n := n) ψ) nb r (Lof ψ Lam) hG ξ, sum_boole, nSat]
    exact congrArg (fun s : Finset (Fin n → Bool) => (#s : ℤ)) (filter_congr fun ξ _ => Vof_eq_empty_iff ψ ξ)
  rw [e]

end ClauseBound.ParityChecks.Bridge
