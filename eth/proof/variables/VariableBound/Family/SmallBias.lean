/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import AppVariablesStatement
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.ZMod.Basic

/-! # Lemma 13 (Family of checks): the small-bias parity

The sentences of the proof of Lemma 13 from «For every nonempty set V′ of clauses» to «the
probability is 1/2», and the half of «A clause lies in Γ_u with probability at most 1/v» that speaks
of (u₃, u₄).

Setting: 𝔽 is a finite field that is an algebra over ZMod 2, and `bits` is a linear bijection from 𝔽
to the strings of s bits, so 𝔽 has 2^s elements (`card_eq`). The clauses are the numbers E < m, and
ι(E) = E.
Probabilities are counts with the fractions cleared: «with probability at least 15/32» over (u₃, u₄)
∈ 𝔽² is 15·|𝔽|² ≤ 32·(number of pairs).

In the order of the text:
* `sum_ip`, `odd_iff_ip`: the sum of the ⟨u₃^ι(E), u₄⟩ over E ∈ V′ is ⟨w, u₄⟩ modulo 2 with w = Σ_{E
  ∈ V′} u₃^ι(E);
* `poly_ne_zero`, `poly_natDegree_le`, `roots`: w is a nonzero polynomial of degree at most m − 1 in
  u₃, so w = 0 for at most m − 1 values of u₃;
* `ip_half`: for w ≠ 0 the probability is 1/2 (and `ip_zero`: for w = 0 it is 0);
* `small_bias_count`: the probability is at least (1/2)·(1 − (m−1)/2^s); `small_bias`: this is at
  least 15/32 if 16m ≤ 2^s;
* `half`: for one clause E, ⟨u₃^ι(E), u₄⟩ = 1 with probability at most 1/2. -/

public section

namespace VariableBound.SmallBias

open Finset AppVariables

/-! ## The inner product of strings of bits -/

section Strings

variable {s : ℕ}

/-- ⟨x, y + z⟩ = ⟨x, y⟩ + ⟨x, z⟩. -/
theorem ip_add_right (x y z : Fin s → ZMod 2) : ip x (y + z) = ip x y + ip x z := by
  simp [ip, mul_add, sum_add_distrib]

/-- ⟨Σ_e f e, y⟩ = Σ_e ⟨f e, y⟩. -/
theorem ip_sum_left {ι : Type} (T : Finset ι) (f : ι → Fin s → ZMod 2) (y : Fin s → ZMod 2) : ip (∑ e ∈ T, f e) y = ∑ e ∈ T, ip (f e) y := by
  simp only [ip, Finset.sum_apply, sum_mul]
  exact sum_comm

/-- ⟨0, y⟩ = 0. -/
theorem ip_zero_left (y : Fin s → ZMod 2) : ip 0 y = 0 := by
  simp [ip]

/-- ⟨x, e_i⟩ = x_i for the string e_i with the single bit 1 at place i. -/
theorem ip_single (x : Fin s → ZMod 2) (i : Fin s) : ip x (Pi.single i 1) = x i := by
  simp [ip, Pi.single_apply]

/-- For a string x ≠ 0, exactly half of the strings y of s bits have ⟨x, y⟩ = 1: if x_i = 1, then y
↦ y + e_i exchanges the y with ⟨x, y⟩ = 1 and the others. -/
theorem half_strings (x : Fin s → ZMod 2) (hx : x ≠ 0) : 2 * #{y : Fin s → ZMod 2 | ip x y = 1} = Fintype.card (Fin s → ZMod 2) := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
  have hi1 : x i = 1 := by
    have h : ∀ c : ZMod 2, c ≠ 0 → c = 1 := by decide
    exact h _ hi
  have hsw : #{y : Fin s → ZMod 2 | ip x y = 1} = #{y : Fin s → ZMod 2 | ¬ ip x y = 1} := by
    refine card_equiv (Equiv.addRight (Pi.single i 1)) fun y => ?_
    have h : ∀ c : ZMod 2, c = 1 ↔ ¬ c + 1 = 1 := by decide
    simp only [mem_filter, mem_univ, true_and, Equiv.coe_addRight, ip_add_right, ip_single, hi1]
    exact h _
  have hsum := card_filter_add_card_filter_not (s := (univ : Finset (Fin s → ZMod 2))) (fun y => ip x y = 1)
  rw [card_univ] at hsum
  omega

end Strings

/-- For f with values in ZMod 2, the number of e ∈ T with f e = 1 is odd if and only if the sum of
the f e over e ∈ T is 1. -/
theorem odd_iff {ι : Type} (T : Finset ι) (f : ι → ZMod 2) : Odd #{e ∈ T | f e = 1} ↔ ∑ e ∈ T, f e = 1 := by
  have h : ∀ c : ZMod 2, c = if c = 1 then 1 else 0 := by decide
  rw [← ZMod.natCast_eq_one_iff_odd, natCast_card_filter]
  rw [sum_congr rfl fun e _ => h (f e)]

/-- The number of pairs with a property is the sum, over the first entry, of the number of second
entries. -/
theorem card_pairs {A : Type} [Fintype A] (Q : A × A → Prop) [DecidablePred Q] : #{p : A × A | Q p} = ∑ a : A, #{b : A | Q (a, b)} := by
  simp only [card_filter]
  exact Fintype.sum_prod_type _

/-! ## The sum is ⟨w, u₄⟩ -/

section Sum

variable {F : Type} [Field F] [Algebra (ZMod 2) F] {m s : ℕ}

/-- Proof of Lemma 13 (Family of checks), «the sum is ⟨w, u₄⟩ modulo 2 with w = Σ_{E ∈ V′} u₃^ι(E)»:
for every set V′ of clauses and all u₃, u₄ ∈ 𝔽. -/
theorem sum_ip (bits : F ≃ₗ[ZMod 2] (Fin s → ZMod 2)) (V' : Finset (Fin m)) (u₃ u₄ : F) :
    ∑ E ∈ V', ip (bits (u₃ ^ E.val)) (bits u₄) = ip (bits (∑ E ∈ V', u₃ ^ E.val)) (bits u₄) := by
  rw [map_sum, ip_sum_left]

/-- For every set V′ of clauses and all u₃, u₄ ∈ 𝔽, the number of E ∈ V′ with ⟨u₃^ι(E), u₄⟩ = 1 is
odd if and only if ⟨w, u₄⟩ = 1, with w = Σ_{E ∈ V′} u₃^ι(E). -/
theorem odd_iff_ip (bits : F ≃ₗ[ZMod 2] (Fin s → ZMod 2)) (V' : Finset (Fin m)) (u₃ u₄ : F) :
    Odd #{E ∈ V' | ip (bits (u₃ ^ E.val)) (bits u₄) = 1} ↔ ip (bits (∑ E ∈ V', u₃ ^ E.val)) (bits u₄) = 1 := by
  rw [odd_iff, sum_ip]

end Sum

/-! ## The polynomial w -/

section Poly

variable {F : Type} [Field F] {m : ℕ}

/-- w as a polynomial in u₃: Σ_{E ∈ V′} X^ι(E). -/
@[expose] noncomputable def poly (F : Type) [Field F] {m : ℕ} (V' : Finset (Fin m)) : Polynomial F := ∑ E ∈ V', Polynomial.X ^ E.val

/-- The value of the polynomial at u₃ is w = Σ_{E ∈ V′} u₃^ι(E); at u₃ = 0 the power with exponent 0
is 1. -/
theorem eval_poly (V' : Finset (Fin m)) (u₃ : F) : (poly F V').eval u₃ = ∑ E ∈ V', u₃ ^ E.val := by
  simp [poly, Polynomial.eval_finsetSum]

/-- Proof of Lemma 13 (Family of checks), «a nonzero polynomial»: for V′ nonempty; the coefficient
of X^ι(E) is 1 for E ∈ V′, because ι is injective. -/
theorem poly_ne_zero (V' : Finset (Fin m)) (hV : V'.Nonempty) : poly F V' ≠ 0 := by
  obtain ⟨E₀, hE₀⟩ := hV
  intro h0
  have hc : (poly F V').coeff E₀.val = 1 := by
    rw [poly, Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_X_pow]
    rw [sum_eq_single E₀]
    · simp
    · intro E _ hne
      rw [if_neg]
      exact fun h => hne (Fin.ext h.symm)
    · exact fun h => absurd hE₀ h
  rw [h0, Polynomial.coeff_zero] at hc
  exact zero_ne_one hc

/-- Proof of Lemma 13 (Family of checks), «of degree at most m − 1»: for every set V′ of clauses. -/
theorem poly_natDegree_le (V' : Finset (Fin m)) : (poly F V').natDegree ≤ m - 1 := by
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun E _ => ?_
  rw [Polynomial.natDegree_X_pow]
  have := E.isLt
  omega

/-- Proof of Lemma 13 (Family of checks), «so w = 0 for at most m − 1 values of u₃»: for V′
nonempty. -/
theorem roots [Fintype F] [DecidableEq F] (V' : Finset (Fin m)) (hV : V'.Nonempty) : #{u₃ : F | ∑ E ∈ V', u₃ ^ E.val = 0} ≤ m - 1 := by
  refine le_trans (Polynomial.card_le_degree_of_subset_roots (p := poly F V') fun u hu => ?_) (poly_natDegree_le V')
  rw [Polynomial.mem_roots (poly_ne_zero V' hV), Polynomial.IsRoot, eval_poly]
  simpa using hu

end Poly

/-! ## For w ≠ 0 the probability is 1/2 -/

section Half

variable {F : Type} [Field F] [Fintype F] [Algebra (ZMod 2) F] {s : ℕ}

/-- A field whose elements are written, by `bits`, as the strings of s bits has 2^s elements. -/
theorem card_eq (bits : F ≃ₗ[ZMod 2] (Fin s → ZMod 2)) : Fintype.card F = 2 ^ s := by
  rw [Fintype.card_congr bits.toEquiv, Fintype.card_pi_const, ZMod.card]

/-- Proof of Lemma 13 (Family of checks), «for w ≠ 0 the probability is 1/2»: for w ∈ 𝔽, w ≠ 0,
exactly half of the u₄ ∈ 𝔽 have ⟨w, u₄⟩ = 1. -/
theorem ip_half (bits : F ≃ₗ[ZMod 2] (Fin s → ZMod 2)) (w : F) (hw : w ≠ 0) : 2 * #{u₄ : F | ip (bits w) (bits u₄) = 1} = Fintype.card F := by
  have hx : bits w ≠ 0 := fun h => hw (bits.map_eq_zero_iff.mp h)
  have hc : #{u₄ : F | ip (bits w) (bits u₄) = 1} = #{y : Fin s → ZMod 2 | ip (bits w) y = 1} :=
    card_equiv bits.toEquiv fun u => by simp
  rw [hc, half_strings _ hx, Fintype.card_congr bits.toEquiv]

/-- For w = 0 no u₄ ∈ 𝔽 has ⟨w, u₄⟩ = 1. -/
theorem ip_zero (bits : F ≃ₗ[ZMod 2] (Fin s → ZMod 2)) : #{u₄ : F | ip (bits 0) (bits u₄) = 1} = 0 := by
  simp [ip_zero_left]

/-- For every w ∈ 𝔽, at most half of the u₄ ∈ 𝔽 have ⟨w, u₄⟩ = 1. -/
theorem ip_le_half (bits : F ≃ₗ[ZMod 2] (Fin s → ZMod 2)) (w : F) : 2 * #{u₄ : F | ip (bits w) (bits u₄) = 1} ≤ Fintype.card F := by
  rcases eq_or_ne w 0 with hw | hw
  · rw [hw, ip_zero]
    exact Nat.zero_le _
  · exact (ip_half bits w hw).le

end Half

/-! ## The two counts over (u₃, u₄) -/

section Counts

variable {F : Type} [Field F] [Fintype F] [Algebra (ZMod 2) F] {m s : ℕ}

/-- Proof of Lemma 13 (Family of checks), «for every nonempty set V′ of clauses, Σ_{E ∈ V′}
⟨u₃^ι(E), u₄⟩ is odd with probability at least (1/2)·(1 − (m−1)/2^s)» over (u₃, u₄) ∈ 𝔽²: multiplied
by 2·|𝔽|², where |𝔽| = 2^s,
this is |𝔽|² ≤ 2·(number of pairs) + (m−1)·|𝔽|. As V′ is nonempty, m ≥ 1. -/
theorem small_bias_count (bits : F ≃ₗ[ZMod 2] (Fin s → ZMod 2)) (V' : Finset (Fin m)) (hV : V'.Nonempty) :
    Fintype.card F ^ 2 ≤ 2 * #{p : F × F | Odd #{E ∈ V' | ip (bits (p.1 ^ E.val)) (bits p.2) = 1}} + (m - 1) * Fintype.card F := by
  classical
  rw [card_pairs, mul_sum]
  have hterm : ∀ u₃ : F, Fintype.card F ≤ 2 * #{u₄ : F | Odd #{E ∈ V' | ip (bits (u₃ ^ E.val)) (bits u₄) = 1}} + if ∑ E ∈ V', u₃ ^ E.val = 0 then Fintype.card F else 0 := by
    intro u₃
    simp only [odd_iff_ip]
    split_ifs with h0
    · exact Nat.le_add_left _ _
    · exact (ip_half bits _ h0).ge
  calc Fintype.card F ^ 2 = ∑ _u₃ : F, Fintype.card F := by rw [sum_const, card_univ, smul_eq_mul, sq]
    _ ≤ ∑ u₃ : F, (2 * #{u₄ : F | Odd #{E ∈ V' | ip (bits (u₃ ^ E.val)) (bits u₄) = 1}} + if ∑ E ∈ V', u₃ ^ E.val = 0 then Fintype.card F else 0) := sum_le_sum fun u₃ _ => hterm u₃
    _ = ∑ u₃ : F, 2 * #{u₄ : F | Odd #{E ∈ V' | ip (bits (u₃ ^ E.val)) (bits u₄) = 1}} + #{u₃ : F | ∑ E ∈ V', u₃ ^ E.val = 0} * Fintype.card F := by
        rw [sum_add_distrib, ← sum_filter, sum_const, smul_eq_mul]
    _ ≤ _ := Nat.add_le_add_left (Nat.mul_le_mul_right _ (roots V' hV)) _

/-- Proof of Lemma 13 (Family of checks), the small-bias parity: if 16m ≤ 2^s, then for every
nonempty set V′ of clauses, Σ_{E ∈ V′} ⟨u₃^ι(E), u₄⟩ is odd with probability at least 15/32 over
(u₃, u₄) ∈ 𝔽². -/
theorem small_bias (bits : F ≃ₗ[ZMod 2] (Fin s → ZMod 2)) (h16 : 16 * m ≤ 2 ^ s) (V' : Finset (Fin m)) (hV : V'.Nonempty) :
    15 * Fintype.card F ^ 2 ≤ 32 * #{p : F × F | Odd #{E ∈ V' | ip (bits (p.1 ^ E.val)) (bits p.2) = 1}} := by
  have h1 := small_bias_count bits V' hV
  rw [← card_eq bits] at h16
  have h2 : 16 * ((m - 1) * Fintype.card F) ≤ Fintype.card F ^ 2 := by
    rw [sq, ← mul_assoc]
    exact Nat.mul_le_mul_right _ (le_trans (by omega) h16)
  omega

/-- Proof of Lemma 13 (Family of checks), the half of «a clause lies in Γ_u with probability at most
1/v» on (u₃, u₄): for every clause E, ⟨u₃^ι(E), u₄⟩ = 1 with probability at most 1/2 over (u₃, u₄) ∈
𝔽². -/
theorem half (bits : F ≃ₗ[ZMod 2] (Fin s → ZMod 2)) (E : Fin m) :
    2 * #{p : F × F | ip (bits (p.1 ^ E.val)) (bits p.2) = 1} ≤ Fintype.card F ^ 2 := by
  rw [card_pairs, mul_sum]
  calc ∑ u₃ : F, 2 * #{u₄ : F | ip (bits (u₃ ^ E.val)) (bits u₄) = 1} ≤ ∑ _u₃ : F, Fintype.card F := sum_le_sum fun u₃ _ => ip_le_half bits _
    _ = Fintype.card F ^ 2 := by rw [sum_const, card_univ, smul_eq_mul, sq]

end Counts

end VariableBound.SmallBias
