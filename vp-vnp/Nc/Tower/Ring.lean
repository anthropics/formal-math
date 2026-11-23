/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib

/-!
# The rings F₂[s]/(s^m)
-/

namespace Nc.Tower

open Polynomial

/-- The ring F₂[s]/(s^m). -/
def R (m : ℕ) : Type := (ZMod 2)[X] ⧸ Ideal.span {(X : (ZMod 2)[X]) ^ m}

noncomputable instance (m : ℕ) : CommRing (R m) :=
  inferInstanceAs (CommRing ((ZMod 2)[X] ⧸ Ideal.span {(X : (ZMod 2)[X]) ^ m}))

instance (m : ℕ) : Finite (R m) := by
  have : Module.Finite (ZMod 2) ((ZMod 2)[X] ⧸ Ideal.span {(X : (ZMod 2)[X]) ^ m}) :=
    (monic_X_pow m).finite_quotient
  exact Module.finite_of_finite (M := (ZMod 2)[X] ⧸ Ideal.span {(X : (ZMod 2)[X]) ^ m}) (ZMod 2)

noncomputable instance (m : ℕ) : Fintype (R m) := Fintype.ofFinite _

noncomputable instance (m : ℕ) : DecidableEq (R m) := Classical.decEq _

/-- The class of a polynomial. -/
noncomputable def mkR (m : ℕ) : (ZMod 2)[X] →+* R m := Ideal.Quotient.mk (Ideal.span {(X : (ZMod 2)[X]) ^ m})

theorem mkR_surjective (m : ℕ) : Function.Surjective (mkR m) := Ideal.Quotient.mk_surjective

theorem mkR_eq_zero {m : ℕ} {p : (ZMod 2)[X]} : mkR m p = 0 ↔ X ^ m ∣ p := by
  rw [← Ideal.mem_span_singleton]
  exact Ideal.Quotient.eq_zero_iff_mem

/-- Homomorphisms from the ring. -/
noncomputable def liftR {m : ℕ} {S : Type*} [CommRing S] (f : (ZMod 2)[X] →+* S) (hf : f (X ^ m) = 0) : R m →+* S :=
  Ideal.Quotient.lift (Ideal.span {(X : (ZMod 2)[X]) ^ m}) f (by
    intro p hp
    rw [Ideal.mem_span_singleton] at hp
    obtain ⟨q, rfl⟩ := hp
    rw [map_mul, hf, zero_mul])

theorem liftR_mk {m : ℕ} {S : Type*} [CommRing S] (f : (ZMod 2)[X] →+* S) (hf : f (X ^ m) = 0) (p : (ZMod 2)[X]) :
    liftR f hf (mkR m p) = f p := Ideal.Quotient.lift_mk _ _ _

/-- The constants. -/
noncomputable def cst (m : ℕ) : ZMod 2 →+* R m := (mkR m).comp C

theorem cst_apply (m : ℕ) (a : ZMod 2) : cst m a = mkR m (C a) := rfl

/-- The nilpotent element. -/
noncomputable def s (m : ℕ) : R m := mkR m X

theorem s_pow (m n : ℕ) : s m ^ n = mkR m (X ^ n) := by rw [s, map_pow]

theorem s_pow_self (m : ℕ) : s m ^ m = 0 := by rw [s_pow, mkR_eq_zero]

theorem s_pow_ge {m n : ℕ} (h : m ≤ n) : s m ^ n = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [pow_add, s_pow_self, zero_mul]

theorem s_pow_ne {m n : ℕ} (h : n < m) : s m ^ n ≠ 0 := by
  rw [s_pow, Ne, mkR_eq_zero]
  intro hd
  have := Polynomial.degree_le_of_dvd hd (pow_ne_zero _ X_ne_zero)
  rw [degree_X_pow, degree_X_pow] at this
  have : m ≤ n := by exact_mod_cast this
  omega

theorem two_eq_zero (m : ℕ) : (2 : R m) = 0 := by
  have h : cst m 2 = 2 := map_ofNat _ 2
  rw [← h, show (2 : ZMod 2) = 0 from rfl, map_zero]

theorem add_self (m : ℕ) (x : R m) : x + x = 0 := by rw [← two_mul, two_eq_zero, zero_mul]

/-- Reduction modulo s^m. -/
noncomputable def red (m : ℕ) : R (m + 1) →+* R m :=
  liftR (mkR m) (by rw [mkR_eq_zero]; exact pow_dvd_pow X (Nat.le_succ m))

theorem red_mk (m : ℕ) (p : (ZMod 2)[X]) : red m (mkR (m + 1) p) = mkR m p := liftR_mk _ _ p

theorem red_s (m : ℕ) : red m (s (m + 1)) = s m := red_mk m X

theorem red_surjective (m : ℕ) : Function.Surjective (red m) := by
  intro x
  obtain ⟨p, rfl⟩ := mkR_surjective m x
  exact ⟨mkR (m + 1) p, red_mk m p⟩

/-- The kernel of the reduction. -/
theorem exists_of_red_eq_zero {m : ℕ} {x : R (m + 1)} (h : red m x = 0) :
    ∃ c : ZMod 2, x = cst (m + 1) c * s (m + 1) ^ m := by
  obtain ⟨p, rfl⟩ := mkR_surjective _ x
  rw [red_mk, mkR_eq_zero] at h
  obtain ⟨q, rfl⟩ := h
  refine ⟨q.coeff 0, ?_⟩
  have h1 : q = C (q.coeff 0) + X * q.divX := by
    rw [add_comm, mul_comm, divX_mul_X_add]
  have h2 : mkR (m + 1) (X ^ (m + 1)) = 0 := mkR_eq_zero.2 dvd_rfl
  rw [s_pow, cst_apply]
  conv_lhs => rw [h1, mul_add, ← mul_assoc, ← pow_succ, map_add, map_mul, map_mul _ (X ^ (m + 1)), h2, zero_mul,
    add_zero, mul_comm]

/-- The value at s = 0. -/
noncomputable def ev (m : ℕ) : R (m + 1) →+* ZMod 2 := liftR (Polynomial.evalRingHom 0) (by simp)

theorem ev_mk (m : ℕ) (p : (ZMod 2)[X]) : ev m (mkR (m + 1) p) = p.eval 0 := liftR_mk _ _ p

theorem ev_s (m : ℕ) : ev m (s (m + 1)) = 0 := by rw [s, ev_mk, eval_X]

theorem ev_cst (m : ℕ) (a : ZMod 2) : ev m (cst (m + 1) a) = a := by rw [cst_apply, ev_mk, eval_C]

/-- In F₂[s]/(s) every element is a constant. -/
theorem eq_cst_ev (x : R 1) : x = cst 1 (ev 0 x) := by
  obtain ⟨p, rfl⟩ := mkR_surjective _ x
  have h1 : p = C (p.coeff 0) + X * p.divX := by
    rw [add_comm, mul_comm, divX_mul_X_add]
  have h2 : mkR 1 X = 0 := by rw [mkR_eq_zero, pow_one]
  have h3 : ev 0 (mkR 1 p) = p.coeff 0 := by
    rw [Polynomial.coeff_zero_eq_eval_zero]
    exact ev_mk 0 p
  rw [h3, cst_apply]
  conv_lhs => rw [h1, map_add, map_mul, h2, zero_mul, add_zero]

/-- The unit t = 1 + s. -/
noncomputable def t (m : ℕ) : R m := 1 + s m

theorem isUnit_t (m : ℕ) : IsUnit (t m) := by
  have h : IsNilpotent (s m) := ⟨m, s_pow_self m⟩
  exact h.isUnit_one_add

theorem red_t (m : ℕ) : red m (t (m + 1)) = t m := by rw [t, map_add, map_one, red_s]; rfl

theorem ev_t (m : ℕ) : ev m (t (m + 1)) = 1 := by rw [t, map_add, map_one, ev_s, add_zero]

theorem s_eq (m : ℕ) : s m = 1 + t m := by
  rw [t, ← add_assoc, add_self, zero_add]

end Nc.Tower
