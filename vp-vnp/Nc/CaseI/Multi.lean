/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.LowDegree

/-!
# Multilinear parts of circuits

Variables (a, t), a < k (blocks), t ∈ T. `cf S P x` is the coefficient of the product of the variables
(a, x a), a ∈ S, in P. If a circuit with s gates computes P, then the part of P that is linear in each of
the k blocks is a sum, over the sets A of blocks with k/3 ≤ |A| ≤ 2k/3 and the gates, of products of a
function of the x a, a ∈ A, and a function of the other x a.
-/

set_option linter.unusedSectionVars false

namespace Nc.CaseI

open Finset MvPolynomial

variable {F : Type*} [CommSemiring F] {k : ℕ} {T : Type*} [DecidableEq T]

/-- The exponent of the product of the variables (a, x a), a ∈ S. -/
noncomputable def mono (S : Finset (Fin k)) (x : Fin k → T) : (Fin k × T) →₀ ℕ :=
  ∑ a ∈ S, Finsupp.single (a, x a) 1

theorem mono_apply (S : Finset (Fin k)) (x : Fin k → T) (i : Fin k × T) :
    mono S x i = if i.1 ∈ S ∧ x i.1 = i.2 then 1 else 0 := by
  rw [mono, Finsupp.finsetSum_apply]
  by_cases h : i.1 ∈ S ∧ x i.1 = i.2
  · rw [if_pos h, Finset.sum_eq_single i.1]
    · rw [Finsupp.single_apply, if_pos (show (i.1, x i.1) = i from Prod.ext rfl h.2)]
    · intro b _ hb
      rw [Finsupp.single_apply, if_neg]
      rintro rfl
      exact hb rfl
    · exact fun hn => absurd h.1 hn
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun b hb => ?_
    rw [Finsupp.single_apply, if_neg]
    rintro rfl
    exact h ⟨hb, rfl⟩

theorem mono_congr {S : Finset (Fin k)} {x y : Fin k → T} (h : ∀ a ∈ S, x a = y a) :
    mono S x = mono S y :=
  Finset.sum_congr rfl fun a ha => by rw [h a ha]

theorem mono_add {S A : Finset (Fin k)} (h : A ⊆ S) (x : Fin k → T) :
    mono A x + mono (S \ A) x = mono S x := by
  rw [mono, mono, mono, add_comm, Finset.sum_sdiff h]

/-- The coefficient of the product of the variables (a, x a), a ∈ S. -/
noncomputable def cf (S : Finset (Fin k)) (P : MvPolynomial (Fin k × T) F) (x : Fin k → T) : F :=
  P.coeff (mono S x)

theorem cf_congr {S : Finset (Fin k)} (P : MvPolynomial (Fin k × T) F) {x y : Fin k → T}
    (h : ∀ a ∈ S, x a = y a) : cf S P x = cf S P y := by
  rw [cf, cf, mono_congr h]

theorem cf_add (S : Finset (Fin k)) (P Q : MvPolynomial (Fin k × T) F) (x : Fin k → T) :
    cf S (P + Q) x = cf S P x + cf S Q x := coeff_add _ _ _

theorem cf_mul (S : Finset (Fin k)) (P Q : MvPolynomial (Fin k × T) F) (x : Fin k → T) :
    cf S (P * Q) x = ∑ A ∈ S.powerset, cf A P x * cf (S \ A) Q x := by
  rw [cf, coeff_mul]
  symm
  refine Finset.sum_bij (fun A _ => (mono A x, mono (S \ A) x)) ?_ ?_ ?_ ?_
  · intro A hA
    rw [Finset.HasAntidiagonal.mem_antidiagonal]
    exact mono_add (Finset.mem_powerset.1 hA) x
  · intro A hA B hB h
    have h1 := (Prod.ext_iff.1 h).1
    ext a
    have h2 := DFunLike.congr_fun h1 (a, x a)
    simp only [mono_apply, and_true] at h2
    by_cases ha : a ∈ A <;> by_cases hb : a ∈ B <;> simp_all
  · rintro ⟨u, v⟩ huv
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at huv
    simp only at huv
    have hv : ∀ i, u i + v i = if i.1 ∈ S ∧ x i.1 = i.2 then 1 else 0 := by
      intro i
      rw [← mono_apply, ← huv, Finsupp.add_apply]
    refine ⟨S.filter fun a => u (a, x a) = 1, Finset.mem_powerset.2 (Finset.filter_subset _ _), ?_⟩
    have e1 : mono (S.filter fun a => u (a, x a) = 1) x = u := by
      ext ⟨a, t⟩
      rw [mono_apply]
      have h1 := hv (a, t)
      simp only [Finset.mem_filter]
      by_cases h2 : a ∈ S ∧ x a = t
      · rw [if_pos h2] at h1
        obtain ⟨h3, rfl⟩ := h2
        by_cases h4 : u (a, x a) = 1
        · simp [h3, h4]
        · simp only [h4, and_false, false_and, if_false]
          omega
      · rw [if_neg h2] at h1
        rw [if_neg]
        · omega
        · rintro ⟨⟨h3, -⟩, h4⟩
          exact h2 ⟨h3, h4⟩
    refine Prod.ext e1 ?_
    have e2 := mono_add (Finset.filter_subset (fun a => u (a, x a) = 1) S) x
    rw [e1, ← huv] at e2
    exact add_left_cancel e2
  · intro A hA
    rfl

theorem cf_X {S : Finset (Fin k)} (hS : 2 ≤ S.card) (i : Fin k × T) (x : Fin k → T) :
    cf S (X i : MvPolynomial (Fin k × T) F) x = 0 := by
  classical
  rw [cf, coeff_X, if_neg]
  intro h
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 (by omega : 1 < S.card)
  have h1 := DFunLike.congr_fun h (a, x a)
  have h2 := DFunLike.congr_fun h (b, x b)
  rw [mono_apply, if_pos ⟨ha, rfl⟩, Finsupp.single_apply] at h1
  rw [mono_apply, if_pos ⟨hb, rfl⟩, Finsupp.single_apply] at h2
  split_ifs at h1 with e1
  split_ifs at h2 with e2
  exact hab (Prod.ext_iff.1 (e1.symm.trans e2)).1

theorem cf_C {S : Finset (Fin k)} (hS : S.Nonempty) (c : F) (x : Fin k → T) :
    cf S (C c : MvPolynomial (Fin k × T) F) x = 0 := by
  classical
  rw [cf, coeff_C, if_neg]
  intro h
  obtain ⟨a, ha⟩ := hS
  have h1 := DFunLike.congr_fun h (a, x a)
  rw [mono_apply, if_pos ⟨ha, rfl⟩] at h1
  simp at h1

/-- The balanced subsets of S. -/
def bal (S : Finset (Fin k)) : Finset (Finset (Fin k)) :=
  S.powerset.filter fun A => k ≤ 3 * A.card ∧ 3 * A.card ≤ 2 * k

theorem mem_bal {S A : Finset (Fin k)} :
    A ∈ bal S ↔ A ⊆ S ∧ k ≤ 3 * A.card ∧ 3 * A.card ≤ 2 * k := by
  rw [bal, Finset.mem_filter, Finset.mem_powerset]

variable (l : ℕ → MvPolynomial (Fin k × T) F) (s : ℕ)

/-- f is a sum of products of coefficients of gates for balanced sets A ⊆ S, and functions of the rest
of S. -/
def Dec (S : Finset (Fin k)) (f : (Fin k → T) → F) : Prop :=
  ∃ h : Fin s → Finset (Fin k) → (Fin k → T) → F,
    (∀ δ A x y, (∀ a ∈ S \ A, x a = y a) → h δ A x = h δ A y) ∧
    ∀ x, f x = ∑ δ : Fin s, ∑ A ∈ bal S, cf A (l δ) x * h δ A x

variable {l s}

theorem Dec.zero (S : Finset (Fin k)) : Dec l s S fun _ => 0 :=
  ⟨fun _ _ _ => 0, fun _ _ _ _ _ => rfl, fun x => by simp⟩

theorem Dec.add {S : Finset (Fin k)} {f g : (Fin k → T) → F} (hf : Dec l s S f) (hg : Dec l s S g) :
    Dec l s S fun x => f x + g x := by
  obtain ⟨h, h1, h2⟩ := hf
  obtain ⟨h', h1', h2'⟩ := hg
  refine ⟨fun δ A x => h δ A x + h' δ A x, fun δ A x y hxy => ?_, fun x => ?_⟩
  · beta_reduce
    rw [h1 δ A x y hxy, h1' δ A x y hxy]
  · simp only [mul_add, Finset.sum_add_distrib]
    rw [h2, h2']

theorem Dec.sum {ι : Type*} (A : Finset ι) {S : Finset (Fin k)} {f : ι → (Fin k → T) → F}
    (h : ∀ i ∈ A, Dec l s S (f i)) : Dec l s S fun x => ∑ i ∈ A, f i x := by
  classical
  induction A using Finset.induction_on with
  | empty => simpa using Dec.zero S
  | insert i A hi ih =>
    simp only [Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self i A)).add
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

/-- One term. -/
theorem Dec.single {S A : Finset (Fin k)} (hA : A ∈ bal S) {δ : ℕ} (hδ : δ < s)
    {q : (Fin k → T) → F} (hq : ∀ x y, (∀ a ∈ S \ A, x a = y a) → q x = q y) :
    Dec l s S fun x => cf A (l δ) x * q x := by
  refine ⟨fun δ' A' x => if δ' = ⟨δ, hδ⟩ ∧ A' = A then q x else 0, fun δ' A' x y hxy => ?_, fun x => ?_⟩
  · beta_reduce
    split_ifs with h
    · obtain ⟨-, rfl⟩ := h
      exact hq x y hxy
    · rfl
  · rw [Finset.sum_eq_single ⟨δ, hδ⟩, Finset.sum_eq_single A]
    · simp
    · intro B _ hB
      beta_reduce
      rw [if_neg fun h => hB h.2, mul_zero]
    · exact fun h => absurd hA h
    · intro δ' _ hδ'
      refine Finset.sum_eq_zero fun B _ => ?_
      beta_reduce
      rw [if_neg fun h => hδ' h.1, mul_zero]
    · exact fun h => absurd (Finset.mem_univ _) h

/-- Products with functions of other blocks. -/
theorem Dec.mul {S S' : Finset (Fin k)} (hS : S ⊆ S') {f q : (Fin k → T) → F} (hf : Dec l s S f)
    (hq : ∀ x y, (∀ a ∈ S' \ S, x a = y a) → q x = q y) : Dec l s S' fun x => f x * q x := by
  classical
  obtain ⟨h, h1, h2⟩ := hf
  refine ⟨fun δ A x => if A ⊆ S then h δ A x * q x else 0, fun δ A x y hxy => ?_, fun x => ?_⟩
  · beta_reduce
    split_ifs with hA
    · rw [h1 δ A x y fun a ha => hxy a ?_, hq x y fun a ha => hxy a ?_]
      · rw [Finset.mem_sdiff] at ha ⊢
        exact ⟨ha.1, fun h => ha.2 (hA h)⟩
      · rw [Finset.mem_sdiff] at ha ⊢
        exact ⟨hS ha.1, ha.2⟩
    · rfl
  · beta_reduce
    rw [h2, Finset.sum_mul]
    refine Finset.sum_congr rfl fun δ _ => ?_
    rw [Finset.sum_mul]
    have hsub : bal S ⊆ bal S' := fun A hA => by
      rw [mem_bal] at hA ⊢
      exact ⟨hA.1.trans hS, hA.2⟩
    rw [← Finset.sum_subset hsub]
    · refine Finset.sum_congr rfl fun A hA => ?_
      rw [if_pos (mem_bal.1 hA).1, mul_assoc]
    · intro A hA hA'
      rw [if_neg, mul_zero]
      intro h3
      exact hA' (mem_bal.2 ⟨h3, (mem_bal.1 hA).2⟩)

/-- The induction for one gate. -/
theorem dec_gate (hl : ∀ γ < s, IsStep l γ) (hk : 2 ≤ k) (γ : ℕ) (hγ : γ < s) (S : Finset (Fin k))
    (hS : 2 * k < 3 * S.card) : Dec l s S (cf S (l γ)) := by
  induction γ using Nat.strong_induction_on generalizing S with
  | _ γ ih =>
    rcases hl γ hγ with ⟨i, h1⟩ | ⟨c, h1⟩ | ⟨i, hi, j, hj, h1⟩ | ⟨i, hi, j, hj, h1⟩
    · have : cf S (l γ) = fun _ => 0 := by
        funext x
        rw [h1]
        exact cf_X (by omega) i x
      rw [this]
      exact Dec.zero S
    · have : cf S (l γ) = fun _ => 0 := by
        funext x
        rw [h1]
        exact cf_C (Finset.card_pos.1 (by omega)) c x
      rw [this]
      exact Dec.zero S
    · have : cf S (l γ) = fun x => cf S (l i) x + cf S (l j) x := by
        funext x
        rw [h1, cf_add]
      rw [this]
      exact (ih i hi (by omega) S hS).add (ih j hj (by omega) S hS)
    · have : cf S (l γ) = fun x => ∑ A ∈ S.powerset, cf A (l i) x * cf (S \ A) (l j) x := by
        funext x
        rw [h1, cf_mul]
      rw [this]
      refine Dec.sum _ fun A hA => ?_
      have hAS := Finset.mem_powerset.1 hA
      have hcard : (S \ A).card + A.card = S.card := Finset.card_sdiff_add_card_eq_card hAS
      have hSA : S \ (S \ A) = A := Finset.sdiff_sdiff_eq_self hAS
      by_cases c1 : 2 * k < 3 * A.card
      · exact (ih i hi (by omega) A c1).mul hAS fun x y h => cf_congr _ h
      by_cases c2 : k ≤ 3 * A.card
      · exact Dec.single (mem_bal.2 ⟨hAS, c2, by omega⟩) (by omega) fun x y h => cf_congr _ h
      have hcomm : (fun x => cf A (l i) x * cf (S \ A) (l j) x) =
          fun x => cf (S \ A) (l j) x * cf A (l i) x := by
        funext x
        exact mul_comm _ _
      rw [hcomm]
      by_cases c3 : 2 * k < 3 * (S \ A).card
      · exact (ih j hj (by omega) _ c3).mul Finset.sdiff_subset fun x y h =>
          cf_congr _ (by rwa [hSA] at h)
      · exact Dec.single (mem_bal.2 ⟨Finset.sdiff_subset, by omega, by omega⟩) (by omega)
          fun x y h => cf_congr _ (by rwa [hSA] at h)

end Nc.CaseI
