/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Acc.Line

/-!
# The paper, proof of Lemma lem:lowdeg: chains
-/

namespace Paper

open Finset Nc.Acc
open Nc (IsStep)

variable {F : Type*} [CommRing F] {σ : Type*} {s : ℕ}

/-- **Paper: proof of Lemma lem:lowdeg, the chain constants and the degree identity.** "(g,1) = ∑_l λ_{g,l} x_l,
(g,i) = ∑ κ_{g,g′,g″} ∑_{0<j<i} (g′,j)(g″,i−j) for i ≥ 2. These constants do not depend on i." Here (g,m+1) is the
coefficient of degree m+1 of the gate along the line through the point u, which is the part of that degree at u. -/
theorem lem_lowdeg_chains [Fintype σ] (l : ℕ → MvPolynomial σ F) (hl : ∀ k < s, IsStep l k) :
    ∃ (κ : Fin s → Fin s → F) (lam : Fin s → σ → F) (left right : Fin s → Fin s),
      ∀ (k : Fin s) (u : σ → F) (m : ℕ),
        (line u (l k)).coeff (m + 1) = (if m = 0 then ∑ i, lam k i * u i else 0) +
          ∑ h, κ k h * ∑ j ∈ range m, (line u (l (left h))).coeff (j + 1) *
            (line u (l (right h))).coeff (m - j) := by
  classical
  have hch : ∀ k : Fin s, ∃ a b : Fin s, (∃ i < k.1, ∃ j < k.1, l k = l i * l j) →
      (a.1 < k.1 ∧ b.1 < k.1 ∧ l k = l a * l b) := by
    intro k
    by_cases h : ∃ i < k.1, ∃ j < k.1, l k = l i * l j
    · obtain ⟨i, hi, j, hj, e⟩ := h
      exact ⟨⟨i, hi.trans k.2⟩, ⟨j, hj.trans k.2⟩, fun _ => ⟨hi, hj, e⟩⟩
    · exact ⟨k, k, fun h' => absurd h' h⟩
  choose left right hlr using hch
  have key : ∀ n (hn : n < s), ∃ (κ : Fin s → F) (lam : σ → F), ∀ (u : σ → F) (m : ℕ),
        (line u (l n)).coeff (m + 1) = (if m = 0 then ∑ i, lam i * u i else 0) +
          ∑ h, κ h * ∑ j ∈ range m, (line u (l (left h))).coeff (j + 1) *
            (line u (l (right h))).coeff (m - j) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro hn
      by_cases hmul : ∃ i < n, ∃ j < n, l n = l i * l j
      · obtain ⟨ha, hb, e⟩ := hlr ⟨n, hn⟩ hmul
        obtain ⟨κa, la, Ha⟩ := ih _ ha (left ⟨n, hn⟩).2
        obtain ⟨κb, lb, Hb⟩ := ih _ hb (right ⟨n, hn⟩).2
        set a := left ⟨n, hn⟩ with hadef
        set b := right ⟨n, hn⟩ with hbdef
        refine ⟨fun h => MvPolynomial.constantCoeff (l a) * κb h +
          MvPolynomial.constantCoeff (l b) * κa h + (if h = ⟨n, hn⟩ then 1 else 0),
          fun i => MvPolynomial.constantCoeff (l a) * lb i +
          MvPolynomial.constantCoeff (l b) * la i, fun u m => ?_⟩
        have e' : l n = l a * l b := e
        rw [e', map_mul, coeff_mul_succ, line_coeff_zero, line_coeff_zero, Ha, Hb]
        have h1 : ∀ X : Fin s → F, ∑ h, (MvPolynomial.constantCoeff (l a) * κb h +
          MvPolynomial.constantCoeff (l b) * κa h + (if h = ⟨n, hn⟩ then 1 else 0)) * X h =
          MvPolynomial.constantCoeff (l a) * ∑ h, κb h * X h +
          MvPolynomial.constantCoeff (l b) * ∑ h, κa h * X h + X ⟨n, hn⟩ := by
          intro X
          simp only [add_mul, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc, ite_mul, one_mul,
            zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
        rw [h1]
        by_cases hm : m = 0
        · subst hm
          simp only [if_true, add_mul, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]
          simp [Finset.mul_sum]
        · simp only [hm, if_false]
          ring
      · have hs := hl n hn
        rcases hs with ⟨i, e⟩ | ⟨c, e⟩ | ⟨i, hi, j, hj, e⟩ | h
        · refine ⟨0, fun i' => if i' = i then 1 else 0, fun u m => ?_⟩
          rw [e]
          simp only [line, MvPolynomial.aeval_X, Polynomial.coeff_C_mul, Polynomial.coeff_X]
          by_cases hm : m = 0
          · subst hm; simp
          · simp [hm]
        · refine ⟨0, 0, fun u m => ?_⟩
          rw [e]
          simp [line]
        · obtain ⟨κa, la, Ha⟩ := ih i hi (hi.trans hn)
          obtain ⟨κb, lb, Hb⟩ := ih j hj (hj.trans hn)
          refine ⟨κa + κb, la + lb, fun u m => ?_⟩
          rw [e, map_add, Polynomial.coeff_add, Ha, Hb]
          simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
          by_cases hm : m = 0
          · simp only [hm, if_true]; ring
          · simp only [hm, if_false]; ring
        · exact absurd h hmul
  choose κ lam H using key
  exact ⟨fun k => κ k k.2, fun k => lam k k.2, left, right, fun k u m => H k k.2 u m⟩

end Paper
