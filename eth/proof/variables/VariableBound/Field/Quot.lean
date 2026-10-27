/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import VariableBound.Field.Alg
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.Ideal.Maximal
import Mathlib.Data.List.GetD
import Mathlib.Data.List.OfFn

/-! # The residues modulo X^s + g

Facts on residues for the proof of Lemma 13 (Family of checks), which takes 𝔽 = GF(2^s), finds an
irreducible polynomial of degree s by search, and writes the elements of 𝔽 as strings of s bits.
Here g is a word of s bits,
`modP g` = X^s + g, and `FW g` is the ring of residues modulo it.

* `monic_modP`, `natDegree_modP`: X^s + g is monic of degree s; `two_eq_zero_FW`: 2 = 0 in the ring;
  `root_pow`: X^s ≡ g.
* `bitsW g`: the coordinates of a residue in the basis 1, X, …, X^(s−1), a linear bijection onto the
  strings of s bits. `bitsW_decW`: the coordinates of the residue that a word of s bits stands for
  are its
  bits; so the words of s bits and the residues correspond one to one (`decW_inj`, `decW_surj`).
* `exists_irreducible_modP`: for every s ≥ 1 some X^s + g is irreducible; with `irrW_iff` this makes
  the search succeed (`modW_spec`, proof/variables/VariableBound/Field/Search.lean).
  `irreducible_of_inv`: if every residue other than 0 has an inverse, X^s + g is irreducible. -/

public section

namespace VariableBound.Fld

open Polynomial

namespace Quot

/-- A homomorphism of rings maps a bit to the same bit. -/
theorem map_bitR {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (b : Bool) : φ (bitR R b) = bitR S b := by
  cases b <;> simp [bitR]

/-- In ZMod 2, c is the bit «c = 1». -/
theorem bitR_decide (c : ZMod 2) : bitR (ZMod 2) (decide (c = 1)) = c := by
  revert c
  decide

/-- Different bits are different elements of ZMod 2. -/
theorem bitR_inj {b b' : Bool} (h : bitR (ZMod 2) b = bitR (ZMod 2) b') : b = b' := by
  revert b b'
  decide

/-- The i-th entry of the word of the bits x_0, …, x_(n−1) is x_i. -/
theorem getD_ofFn {n : ℕ} (x : Fin n → Bool) (i : Fin n) : (List.ofFn x).getD i.val false = x i := by
  rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]

/-- The coefficient of X^i in the polynomial of the word w is the i-th bit of w, and 0 beyond the
end of w. -/
theorem coeff_polyW (w : List Bool) (i : ℕ) : (polyW w).coeff i = bitR (ZMod 2) (w.getD i false) := by
  induction w generalizing i with
  | nil => simp [polyW, decR, bitR]
  | cons b w ih =>
    have h : polyW (b :: w) = C (bitR (ZMod 2) b) + X * polyW w := by
      rw [polyW, decR, ← map_bitR (C : ZMod 2 →+* (ZMod 2)[X])]
      rfl
    rw [h, coeff_add]
    cases i with
    | zero => simp
    | succ i => simp [coeff_X_mul, ih, coeff_C_succ]

end Quot

open VariableBound.Fld.Quot

/-- A homomorphism φ of rings maps b_0 + b_1·r + … to b_0 + b_1·φ(r) + …. -/
theorem map_decR {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (r : R) (w : List Bool) : φ (decR r w) = decR (φ r) w := by
  induction w with
  | nil => simp [decR]
  | cons b w ih => simp [decR, ih, map_bitR]

/-- The polynomial of a word of n bits has degree less than n. -/
theorem degree_polyW_lt (w : List Bool) : (polyW w).degree < w.length := by
  rw [degree_lt_iff_coeff_zero]
  intro i hi
  rw [coeff_polyW, List.getD_eq_default _ _ hi]
  rfl

/-- X^s + g is monic. -/
theorem monic_modP (g : List Bool) : (modP g).Monic :=
  monic_X_pow_add (degree_polyW_lt g)

/-- X^s + g has degree s, the length of g. -/
theorem natDegree_modP (g : List Bool) : (modP g).natDegree = g.length := by
  rw [modP, add_comm]
  exact natDegree_add_eq_right_of_degree_lt (by rw [degree_X_pow]; exact degree_polyW_lt g) |>.trans (natDegree_X_pow _)

/-- 2 = 0 in the ring of residues. -/
theorem two_eq_zero_FW (g : List Bool) : (2 : FW g) = 0 := by
  have h : (2 : ZMod 2) = 0 := by decide
  rw [← map_ofNat (algebraMap (ZMod 2) (FW g)) 2, h, map_zero]

/-- The residue of the polynomial of the word w is the residue that w stands for. -/
theorem mk_polyW (g w : List Bool) : AdjoinRoot.mk (modP g) (polyW w) = decW g w := by
  rw [polyW, map_decR, AdjoinRoot.mk_X, decW]

/-- X^s ≡ g modulo X^s + g. -/
theorem root_pow (g : List Bool) : AdjoinRoot.root (modP g) ^ g.length = decW g g := by
  have h0 : AdjoinRoot.root (modP g) ^ g.length + decW g g = 0 := by
    have h : AdjoinRoot.mk (modP g) (X ^ g.length + polyW g) = 0 := AdjoinRoot.mk_self (f := modP g)
    rwa [map_add, map_pow, AdjoinRoot.mk_X, mk_polyW] at h
  have h2 : decW g g + decW g g = 0 := by rw [← two_mul, two_eq_zero_FW, zero_mul]
  calc AdjoinRoot.root (modP g) ^ g.length = AdjoinRoot.root (modP g) ^ g.length + (decW g g + decW g g) := by rw [h2, add_zero]
    _ = decW g g := by rw [← add_assoc, h0, zero_add]

/-- The elements of the ring of residues written as strings of s bits: the coordinates in the basis
1, X, …, X^(s−1). -/
@[expose] noncomputable def bitsW (g : List Bool) : FW g ≃ₗ[ZMod 2] (Fin g.length → ZMod 2) :=
  (AdjoinRoot.powerBasisAux' (monic_modP g)).equivFun.trans (LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2) (finCongr (natDegree_modP g).symm))

/-- The i-th coordinate of the residue of a polynomial p is the coefficient of X^i in the remainder
of p modulo X^s + g. -/
theorem Quot.bitsW_mk (g : List Bool) (p : (ZMod 2)[X]) (i : Fin g.length) : bitsW g (AdjoinRoot.mk (modP g) p) i = (p %ₘ modP g).coeff i.val := by
  rw [bitsW, LinearEquiv.trans_apply, LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply, Module.Basis.equivFun_apply, AdjoinRoot.powerBasisAux'_repr_apply_to_fun,
    AdjoinRoot.modByMonicHom_mk]
  rfl

/-- The coordinates of the residue that a word w of s bits stands for are the bits of w. -/
theorem bitsW_decW (g w : List Bool) (hw : w.length = g.length) (i : Fin g.length) : bitsW g (decW g w) i = bitR (ZMod 2) (w.getD i.val false) := by
  have hdeg : (polyW w).degree < (modP g).degree := by
    rw [degree_eq_natDegree (monic_modP g).ne_zero, natDegree_modP, ← hw]
    exact degree_polyW_lt w
  rw [← mk_polyW, bitsW_mk, (modByMonic_eq_self_iff (monic_modP g)).mpr hdeg, coeff_polyW]

/-- Every residue is the one that some word of s bits stands for. -/
theorem decW_surj (g : List Bool) (z : FW g) : ∃ w : List Bool, w.length = g.length ∧ decW g w = z := by
  refine ⟨List.ofFn fun i => decide (bitsW g z i = 1), List.length_ofFn, (bitsW g).injective (funext fun i => ?_)⟩
  rw [bitsW_decW g _ List.length_ofFn, getD_ofFn, bitR_decide]

/-- Two words of s bits that stand for the same residue are equal. -/
theorem decW_inj (g : List Bool) {w w' : List Bool} (hw : w.length = g.length) (hw' : w'.length = g.length) (h : decW g w = decW g w') : w = w' := by
  refine List.ext_getElem (hw.trans hw'.symm) fun i hi hi' => ?_
  have h1 := bitsW_decW g w hw ⟨i, hw ▸ hi⟩
  rw [h, bitsW_decW g w' hw'] at h1
  have h2 := bitR_inj h1
  rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hi'] at h2
  exact h2.symm

/-- Over the field with two elements there is a monic irreducible polynomial of every degree s ≥ 1:
the minimal polynomial of a generator of the field with 2^s elements. -/
theorem Quot.exists_irreducible (s : ℕ) (hs : 1 ≤ s) : ∃ f : (ZMod 2)[X], f.Monic ∧ Irreducible f ∧ f.natDegree = s := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨α, hα⟩ := Field.exists_primitive_element_of_finite_top (ZMod 2) (GaloisField 2 s)
  have hint : IsIntegral (ZMod 2) α := Algebra.IsIntegral.isIntegral α
  refine ⟨minpoly (ZMod 2) α, minpoly.monic hint, minpoly.irreducible hint, ?_⟩
  rw [(Field.primitive_element_iff_minpoly_natDegree_eq (ZMod 2) α).mp hα, GaloisField.finrank 2 (by omega)]

/-- A monic polynomial of degree s over the field with two elements is X^s + g for the word g of its
s lower coefficients. -/
theorem Quot.eq_modP (f : (ZMod 2)[X]) (hf : f.Monic) : modP (List.ofFn fun i : Fin f.natDegree => decide (f.coeff i = 1)) = f := by
  ext n
  rw [modP, coeff_add, coeff_X_pow, coeff_polyW, List.length_ofFn]
  rcases lt_trichotomy n f.natDegree with hn | hn | hn
  · rw [if_neg hn.ne, zero_add]
    exact (congrArg _ (getD_ofFn _ ⟨n, hn⟩)).trans (bitR_decide _)
  · rw [if_pos hn, List.getD_eq_default _ _ (by simp [hn]), hn, hf.coeff_natDegree]
    simp [bitR]
  · rw [if_neg hn.ne', List.getD_eq_default _ _ (by simp [hn.le]), coeff_eq_zero_of_natDegree_lt hn]
    simp [bitR]

/-- For every s ≥ 1 there is a word g of s bits such that X^s + g is irreducible. -/
theorem exists_irreducible_modP (s : ℕ) (hs : 1 ≤ s) : ∃ g : List Bool, g.length = s ∧ Irreducible (modP g) := by
  obtain ⟨f, hm, hi, hd⟩ := exists_irreducible s hs
  refine ⟨List.ofFn fun i : Fin f.natDegree => decide (f.coeff i = 1), by rw [List.length_ofFn, hd], ?_⟩
  rw [eq_modP f hm]
  exact hi

/-- For g of length s ≥ 1: if every residue other than 0 modulo X^s + g has an inverse, then X^s + g
is irreducible. -/
theorem irreducible_of_inv (g : List Bool) (hg : 1 ≤ g.length) (h : ∀ z : FW g, z ≠ 0 → ∃ z', z * z' = 1) : Irreducible (modP g) := by
  have hnt : Nontrivial (FW g) := AdjoinRoot.nontrivial _ (by
    rw [degree_eq_natDegree (monic_modP g).ne_zero, natDegree_modP]
    exact_mod_cast (by omega : g.length ≠ 0))
  have hfield : IsField (FW g) := { exists_pair_ne := ⟨0, 1, zero_ne_one⟩, mul_comm := mul_comm, mul_inv_cancel := fun {a} ha => h a ha }
  have hmax : (Ideal.span {modP g}).IsMaximal := Ideal.Quotient.maximal_of_isField _ hfield
  exact ((Ideal.span_singleton_prime (monic_modP g).ne_zero).mp hmax.isPrime).irreducible

end VariableBound.Fld
