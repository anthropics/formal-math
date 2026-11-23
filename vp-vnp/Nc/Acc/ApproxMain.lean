/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import NS1.ApproxMain
import Nc.Rate.Truncate

/-!
# The parts of low degree of an approximated polynomial
-/

set_option linter.unusedSectionVars false

namespace NS1

open _root_.NS1.Tree

section Values

open LaurentPolynomial

variable {A : Type} [CommRing A] {E : Type} [CommRing E] [Algebra A E]

/-- All coefficients are without terms below ε ^ r. -/
def PolyOrdGE (r : ℤ) (P : Polynomial E[T;T⁻¹]) : Prop := ∀ i, OrdGE r (P.coeff i)

theorem PolyOrdGE.mul {r s : ℤ} {P Q : Polynomial E[T;T⁻¹]} (hP : PolyOrdGE r P) (hQ : PolyOrdGE s Q) :
    PolyOrdGE (r + s) (P * Q) := by
  intro i
  rw [Polynomial.coeff_mul, ← Finset.sum_map_toList]
  refine OrdGE.list_sum fun x hx => ?_
  rw [List.mem_map] at hx
  obtain ⟨ab, -, rfl⟩ := hx
  exact (hP _).mul (hQ _)

theorem polyOrdGE_C {r : ℤ} {a : E[T;T⁻¹]} (h : OrdGE r a) : PolyOrdGE r (Polynomial.C a) := by
  intro i
  rw [Polynomial.coeff_C]
  split_ifs
  · exact h
  · exact OrdGE.zero r

theorem ordGE_one : OrdGE 0 (1 : E[T;T⁻¹]) := by
  simpa using OrdGE.of_algebraMap (E := E) (1 : E)

/-- **The parts of a small error stay small** at points whose coordinates have no poles. -/
theorem ordGE_line_coeff {σ : Type} {u : σ → E[T;T⁻¹]} (hu : ∀ i, OrdGE 0 (u i))
    {r : MvPolynomial σ E[T;T⁻¹]} (hr : ∀ d, OrdGE 1 (MvPolynomial.coeff d r)) (i : ℕ) :
    OrdGE 1 ((Nc.Acc.line u r).coeff i) := by
  classical
  have hpow : ∀ (l : σ) (k : ℕ), PolyOrdGE 0 ((Polynomial.C (u l) * Polynomial.X) ^ k) := by
    intro l k
    induction k with
    | zero => simpa using polyOrdGE_C (ordGE_one (E := E))
    | succ k ih =>
      rw [pow_succ]
      refine ih.mul (s := 0) fun j => ?_
      rw [Polynomial.coeff_C_mul_X]
      split_ifs
      · exact hu l
      · exact OrdGE.zero 0
  have hprod : ∀ d : σ →₀ ℕ, PolyOrdGE 0 (d.prod fun l k => (Polynomial.C (u l) * Polynomial.X) ^ k) := fun d =>
    Finset.prod_induction _ (PolyOrdGE 0) (fun P Q hP hQ => hP.mul hQ) (polyOrdGE_C ordGE_one) fun l _ => hpow l _
  rw [r.as_sum, map_sum, Polynomial.finsetSum_coeff, ← Finset.sum_map_toList]
  refine OrdGE.list_sum fun x hx => ?_
  rw [List.mem_map] at hx
  obtain ⟨d, -, rfl⟩ := hx
  rw [Nc.Acc.line, MvPolynomial.aeval_monomial, Polynomial.algebraMap_eq]
  exact ((polyOrdGE_C (hr d)).mul (hprod d)) i

theorem ordGE_codeB (N : ℕ) (w : List Bool) (q : Fin N × Option Bool) : OrdGE 0 (codeB E[T;T⁻¹] N w q) := by
  unfold codeB
  split_ifs
  · exact ordGE_one
  · exact OrdGE.zero 0

/-- **Paper: proof of Theorem thm:approx, the parts of an approximated polynomial approximate its value.** -/
theorem ordGE_sum_coeff_sub {N d n : ℕ} {f : MvPolynomial (Fin N × Option Bool) E}
    {p : MvPolynomial (Fin N × Option Bool) E[T;T⁻¹]}
    (hp : ∀ e (i : ℤ), i ≤ 0 → (MvPolynomial.coeff e p).coeff i = if i = 0 then MvPolynomial.coeff e f else 0)
    (hd : f.totalDegree ≤ d) (hn : d < n) (w : List Bool) (a : A)
    (hval : MvPolynomial.eval (codeB E N w) f = algebraMap A E a) :
    OrdGE 1 (∑ i ∈ Finset.range n, (Nc.Acc.line (codeB E[T;T⁻¹] N w) p).coeff i - algebraMap A E[T;T⁻¹] a) := by
  classical
  obtain ⟨φ, hφ⟩ : ∃ φ, φ = algebraMap E E[T;T⁻¹] := ⟨_, rfl⟩
  have hdiff : ∀ e, OrdGE 1 (MvPolynomial.coeff e (p - MvPolynomial.map φ f)) := by
    intro e i hi
    rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_map, AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply, hp e i (by omega),
      hφ, coeff_algebraMap, Algebra.algebraMap_self_apply]
    exact sub_self _
  have hu : (codeB E[T;T⁻¹] N w) = φ ∘ codeB E N w := by
    funext q
    simp only [Function.comp_apply, codeB]
    split_ifs <;> simp
  have hf : ∑ i ∈ Finset.range n, (Nc.Acc.line (codeB E[T;T⁻¹] N w) (MvPolynomial.map φ f)).coeff i =
      algebraMap A E[T;T⁻¹] a := by
    rw [Nc.Acc.sum_coeff_eq_eval _ _ ((Finset.sup_mono (MvPolynomial.support_map_subset φ f)).trans hd) hn, hu]
    have h1 : MvPolynomial.eval (φ ∘ codeB E N w) (MvPolynomial.map φ f) = φ (MvPolynomial.eval (codeB E N w) f) :=
      (MvPolynomial.map_eval φ (codeB E N w) f).symm
    rw [h1, hval, hφ, ← IsScalarTower.algebraMap_apply]
  rw [← hf, ← Finset.sum_sub_distrib, ← Finset.sum_map_toList]
  refine OrdGE.list_sum fun x hx => ?_
  rw [List.mem_map] at hx
  obtain ⟨i, -, rfl⟩ := hx
  rw [← Polynomial.coeff_sub, ← map_sub]
  exact ordGE_line_coeff (ordGE_codeB N w) hdiff i

end Values

end NS1
