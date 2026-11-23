/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Price.Basic
import Nc.Price.Cover
import Nc.Price.Network

/-!
# Covers of wires as identities between functions of bits

For the proof of Theorem thm:laws (`Paper/Laws.lean`): a cover of a product of wires by products of wires is an identity
between functions of bits (`WireId`); powers and products of products of wires; their values at a spectral point.
-/

namespace Nc.Price

open Ov Ov.Ten Ov.Duality Finset

/-- An identity that rewrites wires. Parties V; old wires e with ends a e, b e and n e bits; new wires ν
with ends c ν, d ν. For all copies X p (of the bits of the old wires at p, for every party p):
[for every old wire the two copies agree] = Σ_i Σ_(bits g of all new wires) ∏_p tab i p (X p) (g at p);
in the term i the new wire ν has len i ν bits. -/
def WireId (R : Type) [CommRing R] {V E N ι : Type} [Fintype V] [Fintype E] [Fintype N]
    [DecidableEq N] [Fintype ι] (a b : E → V) (c d : N → V) (n : E → ℕ) (len : ι → N → ℕ)
    (tab : ∀ (i : ι) (p : V), (∀ e : {e // a e = p ∨ b e = p}, Fin (n e) → Bool) →
      (∀ ν : {ν // c ν = p ∨ d ν = p}, Fin (len i ν) → Bool) → R) : Prop :=
  ∀ X : ∀ p, ∀ e : {e // a e = p ∨ b e = p}, Fin (n e) → Bool,
    (if ∀ e, X (a e) ⟨e, Or.inl rfl⟩ = X (b e) ⟨e, Or.inr rfl⟩ then (1 : R) else 0) =
      ∑ i, ∑ g : ∀ ν, Fin (len i ν) → Bool, ∏ p, tab i p (X p) (fun ν => g ν)

section Bits

variable {K : Type} [Field K] {V : Type} [Fintype V] [DecidableEq V]

/-- Strings of k bits as numbers. -/
def enc (k : ℕ) : (Fin k → Bool) ≃ Fin (2 ^ k) :=
  (Equiv.arrowCongr (Equiv.refl _) finTwoEquiv.symm).trans finFunctionFinEquiv

variable {E N : Type} [Fintype E] [DecidableEq E] [Fintype N] [DecidableEq N]

omit [Fintype V] [DecidableEq V] in
theorem at_of_end {a b p : V} {j : Fin 2} (h : (![a, b] : Fin 2 → V) j = p) : a = p ∨ b = p := by
  fin_cases j
  · exact Or.inl h
  · exact Or.inr h

/-- A sum of restrictions of wires is an identity between functions of bits. -/
theorem exists_wireId {ι : Type} [Fintype ι] {a b : E → V} {c d : N → V} {n : E → ℕ}
    {len : ι → N → ℕ}
    (h : SumRestr (wires K a b fun e => 2 ^ n e) fun i => wires K c d fun ν => 2 ^ len i ν) :
    ∃ tab, WireId K a b c d n len tab := by
  classical
  obtain ⟨L, hL⟩ := h
  refine ⟨fun i p x g => L i p (fun e j => enc _ (x ⟨e, at_of_end j.2⟩))
    (fun ν j => enc _ (g ⟨ν, at_of_end j.2⟩)), fun X => ?_⟩
  let x : ∀ p, (wires K a b fun e => 2 ^ n e).ι p := fun p e j => enc _ (X p ⟨e, at_of_end j.2⟩)
  have h1 : (wires K a b fun e => 2 ^ n e).val x =
      if ∀ e, X (a e) ⟨e, Or.inl rfl⟩ = X (b e) ⟨e, Or.inr rfl⟩ then (1 : K) else 0 := by
    have key : ∀ e, (wire K (2 ^ n e) (a e) (b e)).val (fun p => x p e) =
        if X (a e) ⟨e, Or.inl rfl⟩ = X (b e) ⟨e, Or.inr rfl⟩ then 1 else 0 := by
      intro e
      exact (unit_two_val fun j => enc (n e) (X (![a e, b e] j) ⟨e, at_of_end rfl⟩)).trans
        (if_congr (enc (n e)).injective.eq_iff rfl rfl)
    show ∏ e, (wire K (2 ^ n e) (a e) (b e)).val (fun p => x p e) = _
    rw [Finset.prod_congr rfl fun e _ => key e, Finset.prod_ite_zero]
    simp
  rw [← h1, hL]
  refine Finset.sum_congr rfl fun i _ => ?_
  let Φ : (∀ p, (wires K c d fun ν => 2 ^ len i ν).ι p) ≃ (∀ ν, Fin 2 → Fin (2 ^ len i ν)) :=
    ⟨fun y ν j => y (![c ν, d ν] j) ν ⟨j, rfl⟩, fun z p ν j => z ν j.1,
      fun y => by
        funext p ν j
        obtain ⟨j, rfl⟩ := j
        rfl,
      fun z => rfl⟩
  have h2 : app (L i) x = ∑ z : ∀ ν, Fin 2 → Fin (2 ^ len i ν),
      (∏ p, L i p (x p) (Φ.symm z p)) * ∏ ν, (unit K (Fin 2) (2 ^ len i ν)).val (z ν) := by
    refine Fintype.sum_equiv Φ _ _ fun y => ?_
    rw [Φ.symm_apply_apply]
    rfl
  rw [h2, sum_unit_two (fun ν => 2 ^ len i ν) fun z => ∏ p, L i p (x p) (Φ.symm z p)]
  symm
  exact Fintype.sum_equiv (Equiv.piCongrRight fun ν => enc (len i ν)) _ _ fun g => rfl

/-- Wires with the ends p, q, as a homomorphism from numbers to classes of tensors. -/
noncomputable def wcls (K : Type) [Field K] (p q : V) : ℕ →* Cls K V where
  toFun n := cls (wire K n p q)
  map_one' := cls_eq.2 (Equi.wire_one p q)
  map_mul' m n := by
    rw [← cls_mul]
    exact cls_eq.2 (Equi.wire_mul m n p q)

theorem cls_wires (a b : E → V) (n : E → ℕ) :
    cls (wires K a b n) = ∏ e, wcls K (a e) (b e) (n e) := cls_prod _

theorem Equi.wires_kpow (a b : E → V) (n : E → ℕ) (q : ℕ) :
    Equi (Ten.kpow (wires K a b fun e => 2 ^ n e) q) (wires K a b fun e => 2 ^ (q * n e)) := by
  refine cls_eq.1 ?_
  rw [cls_kpow, cls_wires, cls_wires, ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun e _ => ?_
  rw [← map_pow, ← pow_mul, mul_comm]

theorem Equi.wires_prod {B : Type} [Fintype B] [DecidableEq B] (c d : N → V) (ℬ : B → N → ℕ)
    (v : B → ℕ) :
    Equi (Ten.prod fun β => Ten.kpow (wires K c d fun ν => 2 ^ ℬ β ν) (v β))
      (wires K c d fun ν => 2 ^ ∑ β, v β * ℬ β ν) := by
  refine cls_eq.1 ?_
  rw [cls_prod, cls_wires]
  simp only [cls_kpow, cls_wires, ← Finset.prod_pow]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun ν _ => ?_
  rw [← Finset.prod_pow_eq_pow_sum, map_prod]
  refine Finset.prod_congr rfl fun β _ => ?_
  rw [← map_pow, ← pow_mul, mul_comm]

/-- The price of wires of n e bits. -/
theorem F_wires_two (F : Spec K V) (a b : E → V) (n : E → ℕ) :
    F.F (wires K a b fun e => 2 ^ n e) = 2 ^ ∑ e, (n e : ℝ) * F.e (a e) (b e) := by
  rw [F_wires F a b fun e => Nat.one_le_two_pow, Real.rpow_sum_of_pos (by norm_num)]
  refine Finset.prod_congr rfl fun e _ => ?_
  rw [Real.rpow_mul (by norm_num)]
  norm_num

end Bits

end Nc.Price
