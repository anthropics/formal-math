/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Ov.Duality.Cert
import Ov.Duality.Minimal
import Ov.Core.Spec

/-!
# Certificates

For the proof of Theorem thm:duality (`Paper/Gauges.lean`), in a commutative monoid with a covering relation, with an
element C and a finite family of elements A β: certificates, their products and sums.
-/

namespace Nc.Price

open Ov Ov.Duality Finset

variable {M : Type*} [CommMonoid M] {D : Cover M} {B : Type} [Fintype B]

/-- A product of the members of a family. -/
def mon (A : B → M) (v : B → ℕ) : M := ∏ β, A β ^ v β

theorem mon_zero (A : B → M) : mon A (fun _ => 0) = 1 := by simp [mon]

theorem mon_add (A : B → M) (v w : B → ℕ) : mon A (fun β => v β + w β) = mon A v * mon A w := by
  simp [mon, pow_add, Finset.prod_mul_distrib]

theorem mon_single [DecidableEq B] (A : B → M) (β : B) (n : ℕ) :
    mon A (fun γ => if γ = β then n else 0) = A β ^ n := by
  rw [mon, Finset.prod_eq_single β]
  · simp
  · intro γ _ h
    simp [h]
  · simp

/-- A certificate of level k and weight at most W for t: t·C^k is covered by products
C^u·∏A^v with u + Σv = k, and the numbers η^(Σv) add up to at most W. -/
def Cert (D : Cover M) (C : M) (A : B → M) (η : ℝ) (t : M) (k : ℕ) (W : ℝ) : Prop :=
  ∃ (κ : Type) (_ : Fintype κ) (u : κ → ℕ) (v : κ → B → ℕ), (∀ j, u j + ∑ β, v j β = k) ∧
    D.cov (t * C ^ k) (fun j => C ^ u j * mon A (v j)) ∧ ∑ j, η ^ (∑ β, v j β) ≤ W

namespace Cert

variable {C : M} {A : B → M} {η : ℝ} {s t : M} {k l : ℕ} {W V : ℝ}

theorem nonneg (hη : 0 < η) (h : Cert D C A η t k W) : 0 ≤ W := by
  obtain ⟨κ, _, u, v, -, -, hW⟩ := h
  exact (Finset.sum_nonneg fun j _ => by positivity).trans hW

theorem one (k : ℕ) : Cert D C A η 1 k 1 :=
  ⟨Unit, inferInstance, fun _ => k, fun _ _ => 0, by simp,
    by simpa [mon_zero] using D.refl (C ^ k), by simp⟩

theorem mul (hη : 0 < η) (h : Cert D C A η s k W) (h' : Cert D C A η t l V) :
    Cert D C A η (s * t) (k + l) (W * V) := by
  have hW0 := h.nonneg hη
  obtain ⟨κ, _, u, v, hu, hc, hW⟩ := h
  obtain ⟨κ', _, u', v', hu', hc', hW'⟩ := h'
  refine ⟨Σ _ : κ, κ', inferInstance, fun x => u x.1 + u' x.2, fun x β => v x.1 β + v' x.2 β,
    fun x => ?_, ?_, ?_⟩
  · have h1 := hu x.1
    have h2 := hu' x.2
    rw [Finset.sum_add_distrib]
    dsimp only
    omega
  · have h1 := D.mul_mul hc hc'
    have e1 : s * t * C ^ (k + l) = s * C ^ k * (t * C ^ l) := by
      rw [pow_add]; exact mul_mul_mul_comm _ _ _ _
    rw [e1]
    convert h1 using 2 with x
    rw [mon_add, pow_add]
    exact mul_mul_mul_comm _ _ _ _
  · rw [Fintype.sum_sigma]
    calc ∑ j, ∑ j', η ^ (∑ β, (v j β + v' j' β)) =
        (∑ j, η ^ (∑ β, v j β)) * ∑ j', η ^ (∑ β, v' j' β) := by
          rw [Finset.sum_mul_sum]
          refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun j' _ => ?_
          rw [← pow_add, Finset.sum_add_distrib]
      _ ≤ W * V := mul_le_mul hW hW' (Finset.sum_nonneg fun j _ => by positivity) hW0

theorem raise (hη : 0 < η) (h : Cert D C A η t k W) (hkl : k ≤ l) : Cert D C A η t l W := by
  have h1 := h.mul hη (one (D := D) (C := C) (A := A) (η := η) (l - k))
  rwa [mul_one, mul_one, Nat.add_sub_cancel' hkl] at h1

theorem cover {κ : Type} [Fintype κ] {b : κ → M} {W : κ → ℝ} (h : D.cov t b)
    (hb : ∀ j, Cert D C A η (b j) k (W j)) : Cert D C A η t k (∑ j, W j) := by
  choose μ i u v hu hc hW using hb
  refine ⟨Σ j, μ j, inferInstance, fun x => u x.1 x.2, fun x => v x.1 x.2,
    fun x => hu _ _, D.bind (b := fun j => b j * C ^ k) (D.mul _ h) hc, ?_⟩
  rw [Fintype.sum_sigma]
  exact Finset.sum_le_sum fun j _ => hW j

theorem mul_gen (hη : 0 < η) (β : B) (h : Cert D C A η (t * C) k W) :
    Cert D C A η (t * A β) (k + 1) (η * W) := by
  classical
  obtain ⟨κ, _, u, v, hu, hc, hW⟩ := h
  have hs : ∀ j, ∑ γ, (v j γ + if γ = β then 1 else 0) = ∑ γ, v j γ + 1 := fun j => by
    rw [Finset.sum_add_distrib]; simp
  refine ⟨κ, inferInstance, u, fun j γ => v j γ + if γ = β then 1 else 0,
    fun j => by have := hu j; rw [hs]; omega, ?_, ?_⟩
  · have h1 := D.mul (A β) hc
    have e1 : t * A β * C ^ (k + 1) = t * C * C ^ k * A β := by rw [pow_succ]; ac_rfl
    rw [e1]
    convert h1 using 2 with j
    rw [mon_add, mon_single, pow_one, mul_assoc]
  · calc ∑ j, η ^ (∑ γ, (v j γ + if γ = β then 1 else 0)) = η * ∑ j, η ^ (∑ γ, v j γ) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by rw [hs, ← pow_succ']
      _ ≤ η * W := by gcongr

end Cert

section Tensors

variable {K : Type} [Field K] {I : Type} [Fintype I] [DecidableEq I]

theorem cls_prod {κ : Type} [Fintype κ] [DecidableEq κ] (b : κ → Ten K I) :
    cls (Ten.prod b) = ∏ k, cls (b k) := by
  have key : ∀ {n : ℕ} (b : Fin n → Ten K I), cls (Ten.prod b) = ∏ k, cls (b k) := by
    intro n
    induction n with
    | zero => intro b; rw [Fin.prod_univ_zero, ← cls_one]; exact cls_eq.2 (Ten.Equi.prod_empty b)
    | succ n ih =>
      intro b
      rw [Fin.prod_univ_succ, ← ih, ← cls_mul]
      exact cls_eq.2 (Ten.Equi.prod_fin_succ b)
  rw [cls_eq.2 (Ten.Equi.prod_reindex b (Fintype.equivFin κ).symm), key]
  exact Fintype.prod_equiv (Fintype.equivFin κ).symm _ _ fun _ => rfl

theorem cls_mon [DecidableEq B] (A : B → Ten K I) (v : B → ℕ) :
    mon (fun β => cls (A β)) v = cls (Ten.prod fun β => Ten.kpow (A β) (v β)) := by
  rw [cls_prod]
  exact Finset.prod_congr rfl fun β _ => (cls_kpow _ _).symm

end Tensors

end Nc.Price
