/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Rate.Transfer

/-!
# The paper, appendices A and B: constants in KK
-/

namespace Paper

open MvPolynomial Nc

variable {F : Type*} {KK : Type} [Field F] [Field KK] [IsAlgClosed KK] {X : Type*}

/-- **Paper: Lemma lem:transfer.** "Let a polynomial with integer coefficients have a circuit with S gates over a field
of characteristic p. It has one with S gates over KK." Here KK is any algebraically closed field of that
characteristic. -/
theorem lem_transfer (p : ℕ) [CharP F p] [CharP KK p] (q : MvPolynomial X ℤ) {S : ℕ}
    (h : Computes (MvPolynomial.map (Int.castRingHom F) q) S) :
    Computes (MvPolynomial.map (Int.castRingHom KK) q) S := by
  obtain ⟨T, _, _, ⟨f⟩, ⟨g⟩⟩ := exists_common_ring F KK p
  obtain ⟨l, hl, k, hk, e⟩ := Computes.map f h
  classical
  obtain ⟨A, hA, ⟨ψ⟩⟩ := exists_specialisation g ((Finset.range S).image fun k => coeff 0 (l k))
  obtain ⟨L, hL, hm⟩ := exists_lift_steps A.subtype hl fun k hk c hc =>
    ⟨⟨c, hA (Finset.mem_coe.2 (Finset.mem_image.2 ⟨k, Finset.mem_range.2 hk, by rw [hc, coeff_zero_C]⟩))⟩, rfl⟩
  have e1 : L k = MvPolynomial.map (Int.castRingHom A) q := by
    apply map_injective A.subtype A.subtype_injective
    rw [hm k hk, e, MvPolynomial.map_map, MvPolynomial.map_map]
    exact congrArg (fun r => MvPolynomial.map r q) (Subsingleton.elim _ _)
  have h2 : Computes (MvPolynomial.map ψ (L k)) S := Computes.map ψ ⟨L, hL, k, hk, rfl⟩
  rw [e1, MvPolynomial.map_map] at h2
  exact (congrArg (fun r => Computes (MvPolynomial.map r q) S) (Subsingleton.elim _ _)).mp h2

/-- **Paper: Lemma lem:transfer-approx.** "An approximating circuit for a polynomial with integer coefficients, over a
field of characteristic p, gives one of the same size with constants in KK[ε,ε⁻¹] and output in f + εKK[ε][x]": the
constants are cut off, and the argument of Lemma lem:transfer is applied to their coefficients. -/
theorem lem_transfer_approx (p : ℕ) [CharP F p] [CharP KK p] (q : MvPolynomial X ℤ) {s : ℕ}
    (h : Approximates (MvPolynomial.map (Int.castRingHom F) q) s) :
    ∃ P : MvPolynomial X (LaurentPolynomial KK), Computes P s ∧
      ∀ d : X →₀ ℕ, (∀ i : ℤ, i < 0 → (coeff d P).coeff i = 0) ∧
        (coeff d P).coeff 0 = coeff d (MvPolynomial.map (Int.castRingHom KK) q) := by
  suffices main : ∃ P : MvPolynomial X (LaurentPolynomial KK), Computes P s ∧ ∀ (d : X →₀ ℕ) (i : ℤ), i ≤ 0 →
      (coeff d P).coeff i = if i = 0 then coeff d (MvPolynomial.map (Int.castRingHom KK) q) else 0 by
    obtain ⟨P, hP, hc⟩ := main
    exact ⟨P, hP, fun d => ⟨fun i hi => by rw [hc d i hi.le, if_neg hi.ne], by rw [hc d 0 le_rfl, if_pos rfl]⟩⟩
  obtain ⟨T, _, _, ⟨f⟩, ⟨g⟩⟩ := exists_common_ring F KK p
  obtain ⟨P₀, hP₀, hc₀⟩ := h.exists_laurentPolynomial
  obtain ⟨l, hl, k, hk, e⟩ := Computes.map (AddMonoidAlgebra.mapRingHom ℤ f) hP₀
  classical
  obtain ⟨A, hA, ⟨ψ⟩⟩ := exists_specialisation g
    ((Finset.range s).biUnion fun k => (coeff 0 (l k)).coeff.support.image fun i => (coeff 0 (l k)).coeff i)
  obtain ⟨L, hL, hm⟩ := exists_lift_steps (AddMonoidAlgebra.mapRingHom ℤ A.subtype) hl fun k hk c hc => by
    refine mem_range_mapRingHom_subtype A c fun i => ?_
    by_cases hi : c.coeff i = 0
    · rw [hi]
      exact A.zero_mem
    · refine hA (Finset.mem_coe.2 (Finset.mem_biUnion.2 ⟨k, Finset.mem_range.2 hk, Finset.mem_image.2 ⟨i, ?_, ?_⟩⟩))
      · rw [hc, coeff_zero_C]
        exact Finsupp.mem_support_iff.2 hi
      · rw [hc, coeff_zero_C]
  refine ⟨map (AddMonoidAlgebra.mapRingHom ℤ ψ) (L k), Computes.map _ ⟨L, hL, k, hk, rfl⟩, fun d i hi => ?_⟩
  have e1 : (coeff d (L k)).coeff i = if i = 0 then ((coeff d q : ℤ) : A) else 0 := by
    apply A.subtype_injective
    rw [← AddMonoidAlgebra.coeff_mapRingHom, ← coeff_map, hm k hk, e, coeff_map, AddMonoidAlgebra.coeff_mapRingHom,
      hc₀ d i hi, coeff_map]
    split_ifs <;> simp
  rw [coeff_map, AddMonoidAlgebra.coeff_mapRingHom, e1, coeff_map]
  split_ifs <;> simp

end Paper
