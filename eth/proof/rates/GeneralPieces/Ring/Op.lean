/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import GeneralPieces.Ring.OpFacts

/-! # The properties (O1) and (O3) of the operators a[r] of Appendix B

The appendix says "Clearly"; the arguments here start from display (47). (O1): a term of (47) maps
V_E to V_{E+r}, because ∇_k maps V_E to V_{E−k} (`term_mem`, `op_mem`), and it maps integer
polynomials to
integer polynomials (`isInt_term`). (O3): "if some k_i is negative, the positive ones add up to more
than h". Besides: t_n·t^μ as a monomial, coefficients of sums, the partitions of m, and a ↦ a[r]·f
as a linear map. -/

public section

namespace GeneralPieces.Ring

open AppHalfPieces MvPolynomial Finset

/-! ### (O1): weights -/

theorem foldr_nabla_mem (l : List ℤ) (hl : ∀ k ∈ l, k ≠ 0) {E : ℤ} {f : V} (hf : f ∈ VE E) : l.foldr nabla f ∈ VE (E - l.sum) := by
  induction l with
  | nil => simpa using hf
  | cons k l ih =>
    rw [List.foldr_cons, List.sum_cons]
    have := nabla_mem (hl k (by simp)) (ih fun x hx => hl x (by simp [hx]))
    rwa [show E - l.sum - k = E - (k + l.sum) by ring] at this

/-- A term of (47) with Σ k_i = −r maps V_E to V_{E+r}. -/
theorem term_mem (μ : List ℕ+) (ks : List ℤ) {E : ℤ} {f : V} (hf : f ∈ VE E) : term μ ks f ∈ VE (E - ks.sum) := by
  obtain ⟨-, -, a3, -⟩ := filter_sums ks
  rw [term_eq]
  refine Submodule.smul_mem _ _ ?_
  have h1 := foldr_nabla_mem (ks.filter (0 < ·)) (fun k hk => (by simpa using (List.mem_filter.1 hk).2 : 0 < k).ne') hf
  have h2 := foldr_nabla_mem (ks.filter (· < 0)) (fun k hk => (by simpa using (List.mem_filter.1 hk).2 : k < 0).ne) h1
  rwa [show E - (ks.filter (0 < ·)).sum - (ks.filter (· < 0)).sum = E - ks.sum by rw [a3]; ring] at h2

theorem opMon_mem (μ : List ℕ+) (r : ℤ) {E : ℤ} {f : V} (hf : f ∈ VE E) : opMon μ r f ∈ VE (E + r) := by
  obtain ⟨E', M, hE, h1, h2⟩ := exists_window f r
  rw [opMon_eq_opWin hE μ h1 h2]
  refine Submodule.sum_mem _ fun ks hks => ?_
  have := term_mem μ ks hf
  rwa [(mem_filter.1 hks).2, sub_neg_eq_add] at this

theorem op_mem (a : V) (r : ℤ) {E : ℤ} {f : V} (hf : f ∈ VE E) : op a r f ∈ VE (E + r) :=
  Submodule.sum_mem _ fun _ _ => Submodule.smul_mem _ _ (opMon_mem _ r hf)

theorem op_eq_zero (a : V) (r : ℤ) {E : ℤ} {f : V} (hf : f ∈ VE E) (h : E + r < 0) : op a r f = 0 := by
  have := op_mem a r hf
  rwa [VE_neg h, Submodule.mem_bot] at this

/-! ### (O1): integer polynomials -/

theorem isInt_zero : IsInt 0 := fun m => ⟨0, by simp⟩

theorem isInt_add {f g : V} (hf : IsInt f) (hg : IsInt g) : IsInt (f + g) := fun m => by
  obtain ⟨z, hz⟩ := hf m
  obtain ⟨z', hz'⟩ := hg m
  exact ⟨z + z', by rw [coeff_add, hz, hz']; push_cast; rfl⟩

theorem isInt_sum {ι : Type} (s : Finset ι) (F : ι → V) (h : ∀ i ∈ s, IsInt (F i)) : IsInt (∑ i ∈ s, F i) :=
  sum_induction F IsInt (fun _ _ => isInt_add) isInt_zero h

theorem isInt_zsmul {f : V} (hf : IsInt f) (z : ℤ) : IsInt ((z : ℚ) • f) := fun m => by
  obtain ⟨z', hz'⟩ := hf m
  exact ⟨z * z', by rw [coeff_smul, hz', smul_eq_mul]; push_cast; rfl⟩

theorem isInt_nabla {f : V} (hf : IsInt f) (k : ℤ) : IsInt (nabla k f) := by
  unfold AppHalfPieces.nabla
  split_ifs
  · intro m
    rw [coeff_X_mul']
    split_ifs
    · exact hf _
    · exact ⟨0, by simp⟩
  · refine isInt_zsmul (fun m => ?_) k
    obtain ⟨z, hz⟩ := hf (m + Finsupp.single (pn k) 1)
    exact ⟨z * (m (pn k) + 1), by rw [coeff_pderiv, hz]; push_cast; rfl⟩
  · exact isInt_zero

theorem isInt_foldr {f : V} (hf : IsInt f) (l : List ℤ) : IsInt (l.foldr AppHalfPieces.nabla f) := by
  induction l with
  | nil => exact hf
  | cons k l ih => exact isInt_nabla ih k

theorem isInt_term {f : V} (hf : IsInt f) (μ : List ℕ+) (ks : List ℤ) : IsInt (term μ ks f) := by
  rw [term_eq]
  exact isInt_zsmul (isInt_foldr (isInt_foldr hf _) _) _

theorem isInt_opMon {f : V} (hf : IsInt f) (μ : List ℕ+) (r : ℤ) : IsInt (opMon μ r f) := by
  obtain ⟨E, M, hE, h1, h2⟩ := exists_window f r
  rw [opMon_eq_opWin hE μ h1 h2]
  exact isInt_sum _ _ fun ks _ => isInt_term hf μ ks

theorem isInt_op {a f : V} (ha : IsInt a) (hf : IsInt f) (r : ℤ) : IsInt (op a r f) :=
  isInt_sum _ _ fun m _ => by
    obtain ⟨z, hz⟩ := ha m
    rw [hz]
    exact isInt_zsmul (isInt_opMon hf _ r) z

/-! ### (O1): 1[r] = [r = 0]·Id -/

theorem opMon_nil (r : ℤ) (f : V) : opMon [] r f = if r = 0 then f else 0 := by
  obtain ⟨E, M, hE, h1, h2⟩ := exists_window f r
  rw [opMon_eq_opWin hE [] h1 h2]
  unfold opWin
  rw [sum_filter]
  simp only [List.length_nil, ClauseBound.Boson.tup, sum_singleton]
  have ht : term [] [] f = f := by rw [term_eq, nordQ_nil]; simp [wtQ]
  by_cases hr : r = 0
  · rw [if_pos hr, if_pos (by rw [List.sum_nil]; omega), ht]
  · rw [if_neg hr, if_neg (by rw [List.sum_nil]; omega)]

theorem op_one (r : ℤ) (f : V) : op 1 r f = if r = 0 then f else 0 := by
  have h : (1 : V) = tpow (([] : List ℕ+) : Multiset ℕ+) := by simp [tpow]
  rw [h, op_tpow, opMon_nil]

/-! ### Monomials t_n·t^μ -/

theorem X_mul_tpow (n : ℕ+) (μ : Ptn) : X n * tpow μ = tpow (n ::ₘ μ) := by
  unfold tpow X
  rw [monomial_mul, one_mul, ← Multiset.singleton_add, map_add, Multiset.toFinsupp_singleton]

/-! ### Coefficients of sums, partitions of m, and a ↦ a[r]·f as a linear map -/

theorem coef_sum {ι : Type} (π : Ptn) (s : Finset ι) (F : ι → V) : coef π (∑ i ∈ s, F i) = ∑ i ∈ s, coef π (F i) := by
  unfold coef
  rw [coeff_sum]

/-- The index set `ClauseBound.Boson.Pz m`, the multisets of natural numbers without 0 with sum m,
is the image of the partitions of m. -/
theorem Pz_eq (m : ℤ) : ClauseBound.Boson.Pz m = (ptnsZ m).image toN := by
  ext τ
  rw [ClauseBound.Boson.mem_Pz, mem_image]
  constructor
  · rintro ⟨h1, h2⟩
    have hpos : ∀ i ∈ τ, 0 < i := fun i hi => Nat.pos_of_ne_zero fun h0 => h2 (h0 ▸ hi)
    refine ⟨τ.map Nat.toPNat', (mem_ptnsZ m _).2 ?_, toN_map_toPNat' hpos⟩
    rw [← sum_toN, toN_map_toPNat' hpos, h1]
  · rintro ⟨μ, hμ, rfl⟩
    exact ⟨by rw [sum_toN]; exact (mem_ptnsZ m μ).1 hμ, zero_notMem_toN μ⟩

theorem sum_Pz {A : Type} [AddCommMonoid A] (m : ℤ) (G : Multiset ℕ → A) : ∑ τ ∈ ClauseBound.Boson.Pz m, G τ = ∑ τ ∈ ptnsZ m, G (toN τ) := by
  rw [Pz_eq, sum_image fun _ _ _ _ h => toN_injective h]

/-- a ↦ a[r]·f as a linear map. -/
@[expose] noncomputable def opLeft (r : ℤ) (f : V) : V →ₗ[ℚ] V where
  toFun := fun a => op a r f
  map_add' := fun a a' => op_add_left a a' r f
  map_smul' := fun q a => op_smul_left a r q f

end GeneralPieces.Ring

namespace GeneralPieces

open AppHalfPieces MvPolynomial Finset GeneralPieces.Ring

/-- (O1). -/
theorem o1 : O1 where
  maps := fun a r _ _ hf => op_mem a r hf
  zero := fun a r _ _ hf h => op_eq_zero a r hf h
  int := fun _ r _ ha hf => isInt_op ha hf r
  one := op_one

/-- (O3). -/
theorem o3 : O3 where
  number := fun h a b hb => by
    have h1 := op_mem a (-(h : ℤ)) hb
    rw [add_neg_cancel] at h1
    obtain ⟨q, hq⟩ := (mem_VE_zero _).1 h1
    rw [pairing, hq, coeff_C, if_pos rfl]
  positive := fun h μ b ks hb hks hneg => by
    obtain ⟨a1, a2, a3, a4⟩ := filter_sums ks
    obtain ⟨k, hk, hk'⟩ := hneg
    have a5 := a4 k hk
    have a6 : ks.sum = -(-(h : ℤ)) := hks.2.2
    rw [term_eq, nordQ_eq_zero (Bd_of_mem hb) ks (by omega), smul_zero]

end GeneralPieces
