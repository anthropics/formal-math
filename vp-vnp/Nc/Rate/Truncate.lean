/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Rate.Defs
import Nc.Final.CClasses

/-!
# Truncation of the constants of an approximate circuit

An approximate circuit has constants in the field of Laurent series in ε. If every constant is cut off at a high power
of ε, the output changes only by terms with positive powers of ε. So the constants may be taken to be Laurent
polynomials. This is the first half of the proof of the lemma of the paper that reduces to the algebraic closure of the
prime field; the second half is in Nc/Rate/Transfer.lean.
-/

namespace Nc

open MvPolynomial

section Steps

variable {A R X : Type*} [CommSemiring A] [CommSemiring R]

/-- A circuit with t gates is extended by one gate g, which is a variable, a constant, or the sum or product of two of
the t gates. -/
theorem isStep_update {L : ℕ → MvPolynomial X A} {t : ℕ} (h : ∀ k < t, IsStep L k) {g : MvPolynomial X A}
    (hg : (∃ i : X, g = MvPolynomial.X i) ∨ (∃ a : A, g = C a) ∨ (∃ i < t, ∃ j < t, g = L i + L j) ∨
      (∃ i < t, ∃ j < t, g = L i * L j)) :
    ∀ k < t + 1, IsStep (Function.update L t g) k := by
  have e : ∀ i < t, Function.update L t g i = L i := fun i hi => Function.update_of_ne (by omega) _ _
  intro k hk
  rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
  · rcases h k hk with ⟨i, h1⟩ | ⟨c, h1⟩ | ⟨i, hi, j, hj, h1⟩ | ⟨i, hi, j, hj, h1⟩
    · exact Or.inl ⟨i, by rw [e k hk, h1]⟩
    · exact Or.inr (Or.inl ⟨c, by rw [e k hk, h1]⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨i, hi, j, hj, by rw [e k hk, e i (by omega), e j (by omega), h1]⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨i, hi, j, hj, by rw [e k hk, e i (by omega), e j (by omega), h1]⟩))
  · rcases hg with ⟨i, h1⟩ | ⟨c, h1⟩ | ⟨i, hi, j, hj, h1⟩ | ⟨i, hi, j, hj, h1⟩
    · exact Or.inl ⟨i, by rw [Function.update_self, h1]⟩
    · exact Or.inr (Or.inl ⟨c, by rw [Function.update_self, h1]⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨i, hi, j, hj, by rw [Function.update_self, e i hi, e j hj, h1]⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨i, hi, j, hj, by rw [Function.update_self, e i hi, e j hj, h1]⟩))

/-- A circuit over R all of whose constants are images of elements of A under a homomorphism φ is the image under φ,
gate by gate, of a circuit over A. -/
theorem exists_lift_steps (φ : A →+* R) {l : ℕ → MvPolynomial X R} {s : ℕ} (hl : ∀ k < s, IsStep l k)
    (hc : ∀ k < s, ∀ c, l k = C c → c ∈ Set.range φ) :
    ∃ L : ℕ → MvPolynomial X A, (∀ k < s, IsStep L k) ∧ ∀ k < s, map φ (L k) = l k := by
  induction s with
  | zero => exact ⟨fun _ => 0, fun k hk => absurd hk (Nat.not_lt_zero k), fun k hk => absurd hk (Nat.not_lt_zero k)⟩
  | succ t ih =>
    obtain ⟨L, hL, hm⟩ := ih (fun k hk => hl k (by omega)) (fun k hk => hc k (by omega))
    have key : ∃ g : MvPolynomial X A, ((∃ i : X, g = MvPolynomial.X i) ∨ (∃ a : A, g = C a) ∨
        (∃ i < t, ∃ j < t, g = L i + L j) ∨ (∃ i < t, ∃ j < t, g = L i * L j)) ∧ map φ g = l t := by
      rcases hl t (by omega) with ⟨i, h1⟩ | ⟨c, h1⟩ | ⟨i, hi, j, hj, h1⟩ | ⟨i, hi, j, hj, h1⟩
      · exact ⟨MvPolynomial.X i, Or.inl ⟨i, rfl⟩, by rw [h1, map_X]⟩
      · obtain ⟨a, rfl⟩ := hc t (by omega) c h1
        exact ⟨C a, Or.inr (Or.inl ⟨a, rfl⟩), by rw [h1, map_C]⟩
      · exact ⟨L i + L j, Or.inr (Or.inr (Or.inl ⟨i, hi, j, hj, rfl⟩)), by rw [h1, map_add, hm i hi, hm j hj]⟩
      · exact ⟨L i * L j, Or.inr (Or.inr (Or.inr ⟨i, hi, j, hj, rfl⟩)), by rw [h1, map_mul, hm i hi, hm j hj]⟩
    obtain ⟨g, hg, hgm⟩ := key
    refine ⟨Function.update L t g, isStep_update hL hg, fun k hk => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
    · rw [Function.update_of_ne (by omega), hm k hk]
    · rw [Function.update_self, hgm]

end Steps

section Series

variable {F : Type*} [CommRing F]

/-- A Laurent polynomial in ε, read as a Laurent series in ε. -/
noncomputable def laurentToSeries (F : Type*) [CommRing F] : LaurentPolynomial F →+* LaurentSeries F :=
  AddMonoidAlgebra.liftNCRingHom HahnSeries.C
    { toFun := fun n => HahnSeries.single n.toAdd 1
      map_one' := rfl
      map_mul' := fun a b => by rw [HahnSeries.single_mul_single, toAdd_mul, one_mul] }
    fun _ _ => Commute.all _ _

/-- The series of a Laurent polynomial has the same coefficients. -/
@[simp] theorem coeff_laurentToSeries (x : LaurentPolynomial F) (i : ℤ) :
    (laurentToSeries F x).coeff i = x.coeff i := by
  induction x using LaurentPolynomial.induction_on' with
  | add p q hp hq => rw [map_add, HahnSeries.coeff_add, hp, hq, AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
  | C_mul_T n a =>
    rw [← LaurentPolynomial.single_eq_C_mul_T]
    classical
    rw [laurentToSeries, AddMonoidAlgebra.liftNCRingHom_single, AddMonoidAlgebra.coeff_single, Finsupp.single_apply,
      HahnSeries.C_apply, HahnSeries.coeff_single_zero_mul]
    change a * (HahnSeries.single n (1 : F)).coeff i = _
    rw [HahnSeries.coeff_single]
    by_cases h : i = n
    · simp [h]
    · simp [h, Ne.symm h]

/-- Every Laurent series agrees below any given power ε ^ n with a Laurent polynomial. -/
theorem exists_laurentPolynomial_coeff (c : LaurentSeries F) (n : ℤ) :
    ∃ c' : LaurentPolynomial F, ∀ i < n, c'.coeff i = c.coeff i := by
  refine ⟨.ofCoeff (Finsupp.onFinset (Finset.Ico c.order n) (fun i => if i < n then c.coeff i else 0) ?_), ?_⟩
  · intro i hi
    by_cases h : i < n
    · rw [if_pos h] at hi
      refine Finset.mem_Ico.2 ⟨?_, h⟩
      by_contra h'
      exact hi (HahnSeries.coeff_eq_zero_of_lt_order (not_le.1 h'))
    · exact absurd (if_neg h) hi
  · intro i hi
    simp [hi]

end Series

section Order

variable {F : Type*} [CommRing F] {X : Type*}

/-- All coefficients of the polynomial u are Laurent series without terms below ε ^ n. -/
def OrdGe (n : ℤ) (u : MvPolynomial X (LaurentSeries F)) : Prop :=
  ∀ (d : X →₀ ℕ) (i : ℤ), i < n → (coeff d u).coeff i = 0

theorem OrdGe.mono {m n : ℤ} {u : MvPolynomial X (LaurentSeries F)} (h : OrdGe n u) (hmn : m ≤ n) : OrdGe m u :=
  fun d i hi => h d i (by omega)

theorem OrdGe.zero (n : ℤ) : OrdGe n (0 : MvPolynomial X (LaurentSeries F)) := fun d i _ => by simp

theorem OrdGe.add {n : ℤ} {u v : MvPolynomial X (LaurentSeries F)} (hu : OrdGe n u) (hv : OrdGe n v) :
    OrdGe n (u + v) := fun d i hi => by rw [coeff_add, HahnSeries.coeff_add, hu d i hi, hv d i hi, add_zero]

/-- The product of a series without terms below ε ^ m and one without terms below ε ^ n has none below ε ^ (m + n). -/
theorem coeff_mul_eq_zero {m n : ℤ} {x y : LaurentSeries F} (hx : ∀ i < m, x.coeff i = 0)
    (hy : ∀ i < n, y.coeff i = 0) {i : ℤ} (hi : i < m + n) : (x * y).coeff i = 0 := by
  rw [HahnSeries.coeff_mul]
  refine Finset.sum_eq_zero fun ij hij => ?_
  have h := (Finset.mem_antidiagonal.1 hij).2.2
  by_cases h1 : ij.1 < m
  · rw [hx _ h1, zero_mul]
  · rw [hy ij.2 (by omega), mul_zero]

theorem OrdGe.mul {m n : ℤ} {u v : MvPolynomial X (LaurentSeries F)} (hu : OrdGe m u) (hv : OrdGe n v) :
    OrdGe (m + n) (u * v) := fun d i hi => by
  classical
  rw [coeff_mul, HahnSeries.coeff_sum]
  exact Finset.sum_eq_zero fun x _ => coeff_mul_eq_zero (hu x.1) (hv x.2) hi

/-- The poles of the coefficients of finitely many polynomials over the Laurent series have bounded order. -/
theorem exists_ordGe (l : ℕ → MvPolynomial X (LaurentSeries F)) (s : ℕ) :
    ∃ B : ℤ, 0 ≤ B ∧ ∀ k < s, OrdGe (-B) (l k) := by
  have one : ∀ u : MvPolynomial X (LaurentSeries F), ∃ B : ℤ, 0 ≤ B ∧ OrdGe (-B) u := by
    intro u
    induction u using MvPolynomial.induction_on' with
    | monomial e a =>
      refine ⟨|a.order|, abs_nonneg _, fun d i hi => ?_⟩
      classical
      rw [coeff_monomial]
      split_ifs
      · exact HahnSeries.coeff_eq_zero_of_lt_order (lt_of_lt_of_le hi (neg_abs_le _))
      · rfl
    | add p q hp hq =>
      obtain ⟨B, hB, h⟩ := hp
      obtain ⟨B', hB', h'⟩ := hq
      exact ⟨B + B', by omega, (h.mono (by omega)).add (h'.mono (by omega))⟩
  induction s with
  | zero => exact ⟨0, le_rfl, fun k hk => absurd hk (Nat.not_lt_zero k)⟩
  | succ t ih =>
    obtain ⟨B, hB, h⟩ := ih
    obtain ⟨B', hB', h'⟩ := one (l t)
    refine ⟨B + B', by omega, fun k hk => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
    · exact (h k hk).mono (by omega)
    · exact h'.mono (by omega)

end Order

section Truncate

variable {F : Type*} [CommRing F] {X : Type*}

/-- If every constant of a circuit over the Laurent series is cut off
at a sufficiently high power of ε, every gate changes only by terms from ε ^ n on: for every circuit over the Laurent
series and every n there is a circuit of the same shape over the Laurent polynomials whose gates differ from the given
ones by polynomials all of whose coefficients have no terms below ε ^ n. -/
theorem exists_truncated_steps {l : ℕ → MvPolynomial X (LaurentSeries F)} {s : ℕ} (hl : ∀ k < s, IsStep l k) (n : ℤ) :
    ∃ L : ℕ → MvPolynomial X (LaurentPolynomial F), (∀ k < s, IsStep L k) ∧
      ∀ k < s, ∃ r, OrdGe n r ∧ map (laurentToSeries F) (L k) = l k + r := by
  obtain ⟨B, hB, hlB⟩ := exists_ordGe l s
  suffices H : ∀ t ≤ s, ∀ n : ℤ, 0 ≤ n → ∃ L : ℕ → MvPolynomial X (LaurentPolynomial F), (∀ k < t, IsStep L k) ∧
      ∀ k < t, ∃ r, OrdGe n r ∧ map (laurentToSeries F) (L k) = l k + r by
    obtain ⟨L, hL, h⟩ := H s le_rfl |n| (abs_nonneg n)
    exact ⟨L, hL, fun k hk => let ⟨r, hr, e⟩ := h k hk; ⟨r, hr.mono (le_abs_self n), e⟩⟩
  intro t
  induction t with
  | zero =>
    exact fun _ _ _ => ⟨fun _ => 0, fun k hk => absurd hk (Nat.not_lt_zero k), fun k hk => absurd hk (Nat.not_lt_zero k)⟩
  | succ t ih =>
    intro ht n hn
    obtain ⟨L, hL, hr⟩ := ih (by omega) (n + B) (by omega)
    have key : ∃ g : MvPolynomial X (LaurentPolynomial F), ((∃ i : X, g = MvPolynomial.X i) ∨ (∃ a, g = C a) ∨
        (∃ i < t, ∃ j < t, g = L i + L j) ∨ (∃ i < t, ∃ j < t, g = L i * L j)) ∧
        ∃ r, OrdGe n r ∧ map (laurentToSeries F) g = l t + r := by
      rcases hl t (by omega) with ⟨i, h1⟩ | ⟨c, h1⟩ | ⟨i, hi, j, hj, h1⟩ | ⟨i, hi, j, hj, h1⟩
      · exact ⟨MvPolynomial.X i, Or.inl ⟨i, rfl⟩, 0, OrdGe.zero n, by rw [h1, map_X, add_zero]⟩
      · obtain ⟨c', hc'⟩ := exists_laurentPolynomial_coeff c n
        refine ⟨C c', Or.inr (Or.inl ⟨c', rfl⟩), C (laurentToSeries F c' - c), fun d i hi => ?_, ?_⟩
        · classical
          rw [coeff_C]
          split_ifs
          · rw [HahnSeries.coeff_sub, coeff_laurentToSeries, hc' i hi, sub_self]
          · rfl
        · rw [h1, map_C, ← C_add, add_sub_cancel]
      · obtain ⟨ri, hri, ei⟩ := hr i hi
        obtain ⟨rj, hrj, ej⟩ := hr j hj
        exact ⟨L i + L j, Or.inr (Or.inr (Or.inl ⟨i, hi, j, hj, rfl⟩)), ri + rj,
          (hri.add hrj).mono (by omega), by rw [h1, map_add, ei, ej]; ring⟩
      · obtain ⟨ri, hri, ei⟩ := hr i hi
        obtain ⟨rj, hrj, ej⟩ := hr j hj
        refine ⟨L i * L j, Or.inr (Or.inr (Or.inr ⟨i, hi, j, hj, rfl⟩)), ri * l j + l i * rj + ri * rj,
          ((?_ : OrdGe n _).add ?_).add ?_, by rw [h1, map_mul, ei, ej]; ring⟩
        · exact (hri.mul (hlB j (by omega))).mono (by omega)
        · exact ((hlB i (by omega)).mul hrj).mono (by omega)
        · exact (hri.mul hrj).mono (by omega)
    obtain ⟨g, hg, hgr⟩ := key
    refine ⟨Function.update L t g, isStep_update hL hg, fun k hk => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
    · rw [Function.update_of_ne (by omega)]
      obtain ⟨r, h, e⟩ := hr k hk
      exact ⟨r, h.mono (by omega), e⟩
    · rw [Function.update_self]
      exact hgr

end Truncate

section Approx

variable {F X : Type*} [Field F] {s : ℕ}

/-- A polynomial f that is approximated by a circuit with s gates is approximated
by one whose constants are Laurent polynomials in ε: this circuit computes a polynomial p over the Laurent polynomials
in which no negative power of ε occurs and in which the terms without ε are those of f. -/
theorem Approximates.exists_laurentPolynomial {f : MvPolynomial X F} (h : Approximates f s) :
    ∃ p : MvPolynomial X (LaurentPolynomial F), Computes p s ∧
      ∀ (d : X →₀ ℕ) (i : ℤ), i ≤ 0 → (coeff d p).coeff i = if i = 0 then coeff d f else 0 := by
  obtain ⟨_, ⟨l, hl, k, hk, rfl⟩, hp⟩ := h
  obtain ⟨L, hL, hr⟩ := exists_truncated_steps hl 1
  obtain ⟨r, hr, e⟩ := hr k hk
  refine ⟨L k, ⟨L, hL, k, hk, rfl⟩, fun d i hi => ?_⟩
  rw [← hp d i hi, ← coeff_laurentToSeries, ← coeff_map, e, coeff_add, HahnSeries.coeff_add, hr d i (by omega), add_zero]

/-- Conversely, a circuit over the Laurent polynomials in ε is a circuit over the Laurent series. -/
theorem Approximates.of_laurentPolynomial {f : MvPolynomial X F} {p : MvPolynomial X (LaurentPolynomial F)}
    (hp : Computes p s) (h : ∀ (d : X →₀ ℕ) (i : ℤ), i ≤ 0 → (coeff d p).coeff i = if i = 0 then coeff d f else 0) :
    Approximates f s :=
  ⟨map (laurentToSeries F) p, hp.map _, fun d i hi => by rw [coeff_map, coeff_laurentToSeries, h d i hi]⟩

end Approx

end Nc
