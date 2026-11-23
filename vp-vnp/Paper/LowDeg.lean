/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Acc.Main
import Nc.Final.CClasses

/-!
# The paper, section "One scale is all scales": low degree is fast
-/

namespace Paper

open Finset NS1
open _root_.NS1.Tree

open Nc.Acc in
/-- The part of degree i is what the point scales by the ith power. -/
theorem line_coeff_eq {R σ : Type} [CommRing R] (u : σ → R) (p : MvPolynomial σ R) (i : ℕ) :
    (line u p).coeff i = MvPolynomial.eval u (MvPolynomial.homogeneousComponent i p) := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial d a =>
    rw [MvPolynomial.homogeneousComponent_of_mem ((MvPolynomial.mem_homogeneousSubmodule _ _).2
      (MvPolynomial.isHomogeneous_monomial a rfl : (MvPolynomial.monomial d a).IsHomogeneous d.degree))]
    have e : line u (MvPolynomial.monomial d a) =
        Polynomial.C (MvPolynomial.eval u (MvPolynomial.monomial d a)) * Polynomial.X ^ d.degree := by
      simp only [line, MvPolynomial.aeval_monomial, MvPolynomial.eval_monomial, Finsupp.prod, mul_pow,
        Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, map_mul, map_prod, map_pow, Polynomial.algebraMap_eq]
      simp [Finsupp.degree, mul_assoc]
      rfl
    rw [e, Polynomial.coeff_C_mul_X_pow]
    split_ifs <;> simp
  | add p q hp hq => simp [map_add, hp, hq]

open Nc.Acc in
/-- **Paper: Lemma lem:lowdeg.** "Let a polynomial over R in variables (place, symbol), with n places, have a circuit
with S gates. A program of size O(log S + log n + d), with O((S+n)³) constants, has as value the sum of its parts of
degree at most d at the code of the word of every z with |z| < n, in (d+|z|+1)(log(S+n+d))^O(1) steps. All its runs halt, and it names only constants, not powers." The bound on
the height of the trie, O(log S + log n), is the one that Lemma lem:circuit needs. -/
theorem lem_lowdeg : ∃ c : ℕ, ∀ (R : Type) [CommRing R] (M m N d S : ℕ) (p : MvPolynomial (Fin N × Option Bool) R),
    Nc.Computes p S → S ≤ 2 ^ M → N ≤ 2 ^ m →
    ∃ (K : KT R) (D : Tree),
      K.nds ≤ 2 ^ (3 * M + 1) + 2 ^ (M + m + 3) + 3 ∧ K.ht ≤ 3 * M + m + 4 ∧ D.size ≤ c * (M + m + 1) + 2 * (d + 1) ∧
      ∀ (A : Type) [CommRing A] [Algebra A R] (θ : List Bool → A) (z : Tree), z.size < N →
        Hl θ (Fm.ofTree D) z ∧
        (∀ r ∈ evl θ (Fm.ofTree D) z,
          r.cost ≤ (d + 1) * (800 * (M + m) + 4000) + (z.size + 2) * (40 * m + 60) + 10 * m + 100 ∧
          ∀ q ∈ r.bill, K.InB 1 q) ∧
        val K.lk (evl θ (Fm.ofTree D) z) =
          ∑ i ∈ Finset.range (d + 1), MvPolynomial.eval (codeB R N (tbits z)) (MvPolynomial.homogeneousComponent i p) := by
  obtain ⟨c, hc⟩ := size_accF
  refine ⟨c, fun R _ M m N d S p hp hS hN => ?_⟩
  -- d' = d, but a constant needs d' = 1
  obtain ⟨d', q, hd', hd'1, hq, hqv⟩ : ∃ (d' : ℕ) (q : MvPolynomial (Fin N × Option Bool) R), 0 < d' ∧ d' ≤ d + 1 ∧
      Nc.Computes q S ∧ ∀ u : Fin N × Option Bool → R, ∑ i ∈ Finset.range (d' + 1), (line u q).coeff i =
        ∑ i ∈ Finset.range (d + 1), MvPolynomial.eval u (MvPolynomial.homogeneousComponent i p) := by
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · refine ⟨1, MvPolynomial.C (MvPolynomial.constantCoeff p), one_pos, le_rfl, ?_, fun u => ?_⟩
      · have hS1 : 1 ≤ S := by
          obtain ⟨l, -, a, ha, -⟩ := hp
          omega
        exact (Nc.CSize.const _).1.mono hS1
      · simp [Finset.sum_range_succ, line, MvPolynomial.homogeneousComponent_zero, MvPolynomial.constantCoeff_eq]
    · exact ⟨d, p, hd, Nat.le_succ d, hp, fun u => Finset.sum_congr rfl fun i _ => line_coeff_eq u p i⟩
  obtain ⟨K, out, hout, hnds, hht, hkv⟩ := accF_kv hq hS hd' hN
  refine ⟨K, (accF M m d' out).code, hnds, hht, (hc M m d' out hout).trans (by omega), fun A _ _ θ z hz => ?_⟩
  have h := hkv A θ z hz
  rw [Fm.ofTree_code]
  refine ⟨h.hl, fun r hr => ⟨(h.evl.1 r hr).1.trans ?_, (h.evl.1 r hr).2⟩, by rw [h.evl.2, hqv]⟩
  exact Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right (Nat.mul_le_mul_right _ hd'1) _) _) _

end Paper
