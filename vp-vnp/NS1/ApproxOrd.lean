/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import NS1.Main

/-!
# Laurent polynomials in ε: orders, spans, rescaling

Used for approximate accelerators, whose constants are Laurent polynomials in ε.
-/

set_option linter.unusedSectionVars false

namespace NS1

open LaurentPolynomial

variable {A : Type} [CommRing A] {E : Type} [CommRing E] [Algebra A E]

/-- All coefficients of exponents below `r` are 0: the polynomial lies in ε^r E[ε]. -/
def OrdGE (r : ℤ) (P : E[T;T⁻¹]) : Prop := ∀ i < r, P.coeff i = 0

/-- All exponents that occur lie between `-n` and `n`. -/
def Span (n : ℕ) (P : E[T;T⁻¹]) : Prop := ∀ i, P.coeff i ≠ 0 → i.natAbs ≤ n

theorem coeff_algebraMap (a : A) (i : ℤ) :
    (algebraMap A E[T;T⁻¹] a).coeff i = if i = 0 then algebraMap A E a else 0 := by
  rw [AddMonoidAlgebra.coe_algebraMap, Function.comp_apply, AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
  exact if_congr eq_comm rfl rfl

theorem exists_coeff_mul_ne_zero {P Q : E[T;T⁻¹]} {i : ℤ} (h : (P * Q).coeff i ≠ 0) :
    ∃ a b, P.coeff a ≠ 0 ∧ Q.coeff b ≠ 0 ∧ a + b = i := by
  classical
  rw [AddMonoidAlgebra.coeff_mul] at h
  obtain ⟨a, ha, h1⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  obtain ⟨b, hb, h2⟩ := Finset.exists_ne_zero_of_sum_ne_zero h1
  refine ⟨a, b, Finsupp.mem_support_iff.1 ha, Finsupp.mem_support_iff.1 hb, ?_⟩
  by_contra hne
  exact h2 (if_neg hne)

theorem OrdGE.zero (r : ℤ) : OrdGE r (0 : E[T;T⁻¹]) := fun i _ => by simp

theorem OrdGE.mono {r s : ℤ} {P : E[T;T⁻¹]} (h : OrdGE r P) (hs : s ≤ r) : OrdGE s P :=
  fun i hi => h i (lt_of_lt_of_le hi hs)

theorem OrdGE.add {r : ℤ} {P Q : E[T;T⁻¹]} (h : OrdGE r P) (h' : OrdGE r Q) : OrdGE r (P + Q) :=
  fun i hi => by simp [h i hi, h' i hi]

theorem OrdGE.mul {r s : ℤ} {P Q : E[T;T⁻¹]} (h : OrdGE r P) (h' : OrdGE s Q) : OrdGE (r + s) (P * Q) := by
  intro i hi
  by_contra hne
  obtain ⟨a, b, ha, hb, hab⟩ := exists_coeff_mul_ne_zero hne
  have h1 : r ≤ a := by
    by_contra h1
    exact ha (h a (by omega))
  have h2 : s ≤ b := by
    by_contra h2
    exact hb (h' b (by omega))
  omega

theorem OrdGE.list_sum {r : ℤ} {l : List E[T;T⁻¹]} (h : ∀ P ∈ l, OrdGE r P) : OrdGE r l.sum := by
  induction l with
  | nil => simpa using OrdGE.zero r
  | cons P l ih =>
    rw [List.sum_cons]
    exact (h P List.mem_cons_self).add (ih fun Q hQ => h Q (List.mem_cons_of_mem _ hQ))

theorem OrdGE.of_algebraMap (a : A) : OrdGE 0 (algebraMap A E[T;T⁻¹] a) := fun i hi => by
  rw [coeff_algebraMap, if_neg hi.ne]

/-- A product of approximations approximates the product. -/
theorem OrdGE.prod_sub {β : Type*} {r : ℤ} (hr : 0 ≤ r) (l : List β) (f : β → E[T;T⁻¹]) (g : β → A)
    (h : ∀ y ∈ l, OrdGE r (f y - algebraMap A E[T;T⁻¹] (g y))) :
    OrdGE r ((l.map f).prod - algebraMap A E[T;T⁻¹] (l.map g).prod) := by
  induction l with
  | nil => simpa using OrdGE.zero r
  | cons y l ih =>
    have h1 := h y List.mem_cons_self
    have h2 := ih fun z hz => h z (List.mem_cons_of_mem _ hz)
    obtain ⟨a, ha⟩ : ∃ a, a = algebraMap A E[T;T⁻¹] (g y) := ⟨_, rfl⟩
    obtain ⟨b, hb⟩ : ∃ b, b = algebraMap A E[T;T⁻¹] (l.map g).prod := ⟨_, rfl⟩
    rw [← ha] at h1
    rw [← hb] at h2
    have e : ((y :: l).map f).prod - algebraMap A E[T;T⁻¹] ((y :: l).map g).prod =
        (f y - a) * ((l.map f).prod - b) + ((f y - a) * b + a * ((l.map f).prod - b)) := by
      simp only [List.map_cons, List.prod_cons, map_mul, ← ha, ← hb]
      ring
    rw [e]
    refine ((h1.mul h2).mono (by omega)).add ((?_ : OrdGE r _).add ?_)
    · exact (h1.mul (hb ▸ OrdGE.of_algebraMap (E := E) ((l.map g).prod))).mono (by omega)
    · exact ((ha ▸ OrdGE.of_algebraMap (E := E) (g y) : OrdGE 0 a).mul h2).mono (by omega)

theorem Span.mono {n m : ℕ} {P : E[T;T⁻¹]} (h : Span n P) (hm : n ≤ m) : Span m P := fun i hi => (h i hi).trans hm

theorem Span.ordGE {n : ℕ} {P : E[T;T⁻¹]} (h : Span n P) : OrdGE (-(n : ℤ)) P := by
  intro i hi
  by_contra hne
  have := h i hne
  omega

theorem Span.zero (n : ℕ) : Span n (0 : E[T;T⁻¹]) := fun i hi => absurd (by simp) hi

theorem Span.of_algebraMap (a : A) (n : ℕ) : Span n (algebraMap A E[T;T⁻¹] a) := fun i hi => by
  rw [coeff_algebraMap] at hi
  by_cases h : i = 0
  · simp [h]
  · exact absurd (if_neg h) hi

theorem Span.one (n : ℕ) : Span n (1 : E[T;T⁻¹]) := by
  have := Span.of_algebraMap (E := E) (1 : E) n
  rwa [map_one] at this

theorem Span.add {n : ℕ} {P Q : E[T;T⁻¹]} (h : Span n P) (h' : Span n Q) : Span n (P + Q) := by
  intro i hi
  by_cases h1 : P.coeff i = 0
  · exact h' i (by simpa [h1] using hi)
  · exact h i h1

theorem Span.mul {n m : ℕ} {P Q : E[T;T⁻¹]} (h : Span n P) (h' : Span m Q) : Span (n + m) (P * Q) := by
  intro i hi
  obtain ⟨a, b, ha, hb, hab⟩ := exists_coeff_mul_ne_zero hi
  have := h a ha
  have := h' b hb
  omega

theorem Span.pow {n : ℕ} {P : E[T;T⁻¹]} (h : Span n P) (k : ℕ) : Span (k * n) (P ^ k) := by
  induction k with
  | zero => simpa using Span.one (E := E) 0
  | succ k ih =>
    rw [pow_succ, add_mul, one_mul]
    exact ih.mul h

theorem Span.card_support {n : ℕ} {P : E[T;T⁻¹]} (h : Span n P) : P.coeff.support.card ≤ 2 * n + 1 := by
  refine (Finset.card_le_card (t := Finset.Icc (-(n : ℤ)) n) fun i hi => ?_).trans ?_
  · have := h i (Finsupp.mem_support_iff.1 hi)
    rw [Finset.mem_Icc]
    omega
  · rw [Int.card_Icc]
    omega

/-- ε ↦ ε^r. -/
noncomputable def rescale (A : Type) [CommRing A] {E : Type} [CommRing E] [Algebra A E] (r : ℕ) :
    E[T;T⁻¹] →ₐ[A] E[T;T⁻¹] :=
  AddMonoidAlgebra.mapDomainAlgHom A E (AddMonoidHom.mulLeft (r : ℤ))

theorem coeff_rescale_ne_zero {r : ℕ} {P : E[T;T⁻¹]} {i : ℤ} (h : (rescale A r P).coeff i ≠ 0) :
    ∃ j, P.coeff j ≠ 0 ∧ i = r * j := by
  classical
  have h1 : i ∈ (Finsupp.mapDomain (fun j : ℤ => (r : ℤ) * j) P.coeff).support := Finsupp.mem_support_iff.2 h
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support h1)
  exact ⟨j, Finsupp.mem_support_iff.1 hj, rfl⟩

theorem OrdGE.rescale {r : ℕ} {P : E[T;T⁻¹]} (h : OrdGE 1 P) : OrdGE (r : ℤ) (rescale A r P) := by
  intro i hi
  by_contra hne
  obtain ⟨j, hj, rfl⟩ := coeff_rescale_ne_zero hne
  have h1 : 1 ≤ j := by
    by_contra h1
    exact hj (h j (by omega))
  nlinarith

theorem Span.rescale {n : ℕ} {P : E[T;T⁻¹]} (h : Span n P) (r : ℕ) : Span (r * n) (rescale A r P) := by
  intro i hi
  obtain ⟨j, hj, rfl⟩ := coeff_rescale_ne_zero hi
  rw [Int.natAbs_mul, Int.natAbs_natCast]
  exact Nat.mul_le_mul_left _ (h j hj)

theorem card_support_rescale (r : ℕ) (P : E[T;T⁻¹]) :
    (rescale A r P).coeff.support.card ≤ P.coeff.support.card := by
  classical
  refine (Finset.card_le_card ?_).trans (Finset.card_image_le (f := fun j : ℤ => (r : ℤ) * j))
  intro i hi
  obtain ⟨j, hj, rfl⟩ := coeff_rescale_ne_zero (Finsupp.mem_support_iff.1 hi)
  exact Finset.mem_image_of_mem _ (Finsupp.mem_support_iff.2 hj)

/-- The powers of `c` have few terms, as few as those of a polynomial of span `Δ`. -/
def Thin (Δ : ℕ) (c : E[T;T⁻¹]) : Prop := ∀ n, (c ^ n).coeff.support.card ≤ 2 * (n * Δ) + 1

theorem Span.thin {Δ : ℕ} {P : E[T;T⁻¹]} (h : Span Δ P) : Thin Δ P := fun n => (h.pow n).card_support

theorem Thin.rescale {Δ : ℕ} {P : E[T;T⁻¹]} (h : Thin Δ P) (r : ℕ) : Thin Δ (rescale A r P) := fun n => by
  rw [← map_pow]
  exact (card_support_rescale r _).trans (h n)

namespace KT

variable {R R' : Type} [CommRing R] [CommRing R']

/-- All constants satisfy `P`. -/
def All (P : R → Prop) : KT R → Prop
  | none => True
  | leaf c => P c
  | node l r => l.All P ∧ r.All P

theorem All.imp {P Q : R → Prop} (hPQ : ∀ c, P c → Q c) {K : KT R} (h : K.All P) : K.All Q := by
  induction K with
  | none => trivial
  | leaf c => exact hPQ c h
  | node l r ihl ihr => exact ⟨ihl h.1, ihr h.2⟩

theorem All.map {P : R → Prop} {Q : R' → Prop} {f : R → R'} (hPQ : ∀ c, P c → Q (f c)) {K : KT R} (h : K.All P) :
    (K.map f).All Q := by
  induction K with
  | none => trivial
  | leaf c => exact hPQ c h
  | node l r ihl ihr => exact ⟨ihl h.1, ihr h.2⟩

theorem All.expand {P Q : R → Prop} {B : ℕ} (hPQ : ∀ c, P c → ∀ b < B, Q (c ^ 2 ^ b)) {K : KT R} (h : K.All P) :
    (K.expand B).All Q := by
  induction K with
  | none => trivial
  | node l r ihl ihr => exact ⟨ihl h.1, ihr h.2⟩
  | leaf c =>
    have h1 : ∀ n b, b + n ≤ B → (comb (c ^ 2 ^ b) n).All Q := by
      intro n
      induction n with
      | zero => exact fun _ _ => trivial
      | succ n ih =>
        intro b hb
        refine ⟨hPQ c h b (by omega), ?_⟩
        rw [← pow_mul, ← pow_succ]
        exact ih (b + 1) (by omega)
    have := h1 B 0 (by omega)
    rwa [pow_zero, pow_one] at this

theorem exists_bound {P : ℕ → R → Prop} (hP : ∀ c, ∃ n, P n c) (hm : ∀ n m c, n ≤ m → P n c → P m c) (K : KT R) :
    ∃ n, K.All (P n) := by
  induction K with
  | none => exact ⟨0, trivial⟩
  | leaf c => exact hP c
  | node l r ihl ihr =>
    obtain ⟨n, hn⟩ := ihl
    obtain ⟨m, hm'⟩ := ihr
    exact ⟨max n m, hn.imp fun c => hm _ _ c (le_max_left _ _), hm'.imp fun c => hm _ _ c (le_max_right _ _)⟩

end KT

theorem exists_span (P : E[T;T⁻¹]) : ∃ n, Span n P :=
  ⟨P.coeff.support.sup Int.natAbs, fun _ hi => Finset.le_sup (Finsupp.mem_support_iff.2 hi)⟩

/-- **The orders of the products of powers of the constants**, for all budgets with `J` digits. -/
theorem span_budg {n J : ℕ} {K : KT E[T;T⁻¹]} (h : K.All (Span n)) {q : Bt × E[T;T⁻¹]} (hq : q ∈ K.budg J) :
    Span (K.nds * 2 ^ J * n) q.2 := by
  induction K generalizing q with
  | none =>
    simp only [KT.budg, List.mem_singleton] at hq
    subst hq
    exact Span.one _
  | leaf c =>
    simp only [KT.budg, List.mem_map] at hq
    obtain ⟨w, hw, rfl⟩ := hq
    refine ((show Span n c from h).pow _).mono ?_
    rw [KT.nds, one_mul]
    exact Nat.mul_le_mul_right _ (val_lt_of_length' w (KT.length_words hw)).le
  | node l r ihl ihr =>
    simp only [KT.budg, List.mem_flatMap, List.mem_map] at hq
    obtain ⟨p, hp, q', hq', rfl⟩ := hq
    refine ((ihl h.1 hp).mul (ihr h.2 hq')).mono ?_
    simp only [KT.nds, add_mul]
    exact Nat.le_add_right _ _
where
  val_lt_of_length' {J : ℕ} (w : List Bool) (hw : w.length = J) : KT.val w < 2 ^ J := by
    induction w generalizing J with
    | nil => simp [KT.val, ← hw]
    | cons b w ih =>
      subst hw
      have := ih rfl
      rw [KT.val, List.length_cons, pow_succ]
      cases b <;> simp <;> omega

end NS1
