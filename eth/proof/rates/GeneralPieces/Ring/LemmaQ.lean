/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import GeneralPieces.Ring.Basic

/-! # The lemma on the operators Q_s, on the ring ℚ[t₁, t₂, …]

`GeneralPieces.lemmaQ` is a conditional statement. Its conclusion is Lemma 9 of Appendix B in the
form in which the paper states it (`AppHalfPieces.LemmaQ`): for h ≥ 1, b ∈ V_h, a a combination of
monomials of weight at most
h, on V_E. It is derived from the same three claims for the integer matrices of the operators, in
which a is an integer combination of monomials, given as a list of (coefficient, parts) pairs, b is
a
monomial and the claim is about one entry; these are the hypotheses `StMatA`, `StMatB`, `StMatC`,
and they carry the content of the lemma. They are proved along the paper's proof of the lemma:
`proof/rates/GeneralPieces/Main.lean` proves them by applying `GeneralPieces.Series.Qk_eq_Qk'_of`,
`Qk_eq_zero_of` and `sum_Qk_of` to the expansion of f₊ and f₋ (`AppHalfPieces.stExpansion`).
The steps: "All three claims are linear in a and b", and in the polynomial they are applied to
(`Tri`, `Tri.eq_zero`), so a, b and f may be taken to be monomials; for a monomial a of weight h',
a^⟨i⟩ = C(h'+h, i)·a (`angle_tpow`); the coefficients of a[r]b[r']t^σ are the entries of the product
of the two matrices (`coef_comp`), because b[r']t^σ has weight |σ| + r' by (O1).
The facts on a[r] that come with display (47) (proved as `GeneralPieces.opFacts`), the property (O1)
(`GeneralPieces.o1`) and the agreement of the matrices with the operators (`GeneralPieces.stBridge`)
are hypotheses as well.
`proof/rates/GeneralPieces/Main.lean` feeds all of them in and has the lemma without hypotheses. -/

public section

namespace GeneralPieces.LemQ

open AppHalfPieces MvPolynomial Finset GeneralPieces.Ring

/-! ### The three claims for the matrices -/

/-- Claim (a) for the matrices. -/
@[expose] def StMatA : Prop := ∀ (A : ClauseBound.Boson.FA) (b : List ℕ), A.Ok b.sum → ClauseBound.Boson.Pos b → 1 ≤ b.sum → ∀ (s : ℤ) (π σ : Multiset ℕ), 0 ∉ π → 0 ∉ σ →
  ClauseBound.Boson.Qk A b s π σ = ClauseBound.Boson.Qk' A b s π σ

/-- Claim (b) for the matrices. -/
@[expose] def StMatB : Prop := ∀ (A : ClauseBound.Boson.FA) (b : List ℕ), A.Ok b.sum → ClauseBound.Boson.Pos b → 1 ≤ b.sum → ∀ (s : ℤ) (π σ : Multiset ℕ), 0 ∉ π → 0 ∉ σ →
  (σ.sum : ℤ) + b.sum < |s| → ClauseBound.Boson.Qk A b s π σ = 0

/-- Claim (c) for the matrices, with the constant a[−h]b, the entry in the row of the monomial 1 and
the column of b of the matrix of a[−h]. -/
@[expose] def StMatC : Prop := ∀ (A : ClauseBound.Boson.FA) (b : List ℕ), A.Ok b.sum → ClauseBound.Boson.Pos b → 1 ≤ b.sum → ∀ (π σ : Multiset ℕ), 0 ∉ π → 0 ∉ σ →
  ∑ s ∈ Icc (-((σ.sum : ℤ) + b.sum)) ((σ.sum : ℤ) + b.sum), ClauseBound.Boson.Qk A b s π σ =
    if π = σ then (A.map fun c => c.1 * ClauseBound.Boson.op c.2 (-(b.sum : ℤ)) 0 (b : Multiset ℕ)).sum else 0

/-! ### Coefficients -/

theorem coef_add (π : Ptn) (f g : V) : coef π (f + g) = coef π f + coef π g := coeff_add _ _ _

theorem coef_sub (π : Ptn) (f g : V) : coef π (f - g) = coef π f - coef π g := coeff_sub _ _ _ _

theorem coef_zero (π : Ptn) : coef π (0 : V) = 0 := coeff_zero _

theorem coef_sum {ι : Type} (π : Ptn) (s : Finset ι) (F : ι → V) : coef π (∑ i ∈ s, F i) = ∑ i ∈ s, coef π (F i) := coeff_sum _ _ _

/-- A polynomial is the sum of its monomials, over any finite set of partitions that contains all
that occur. -/
theorem eq_sum_of_subset (f : V) (S : Finset Ptn) (hS : ∀ μ, coef μ f ≠ 0 → μ ∈ S) : f = ∑ μ ∈ S, coef μ f • tpow μ := by
  refine ext_coef fun π => ?_
  rw [coef_sum]
  simp only [coef_smul, coef_tpow, mul_ite, mul_one, mul_zero]
  rw [sum_ite_eq]
  split_ifs with h
  · rfl
  · by_contra h'
    exact h (hS π h')

/-- A polynomial of weight E is a combination of the t^μ with |μ| = E. -/
theorem eq_sum_ptnsZ {E : ℤ} {f : V} (hf : f ∈ VE E) : f = ∑ μ ∈ ptnsZ E, coef μ f • tpow μ :=
  eq_sum_of_subset f _ fun μ hμ => (mem_ptnsZ E μ).2 ((mem_VE_iff E f).1 hf μ hμ)

theorem coef_part (π : Ptn) (h' : ℕ) (a : V) : coef π (part h' a) = if wt π = h' then coef π a else 0 := by
  unfold coef part
  rw [coeff_weightedHomogeneousComponent]
  have := weight_toFinsupp π
  unfold wgt at this
  rw [this]

/-- The partitions of weight at most h. -/
@[expose] def ptnsLe (h : ℕ) : Finset Ptn := (range (h + 1)).biUnion ptns

theorem mem_ptnsLe (h : ℕ) (μ : Ptn) : μ ∈ ptnsLe h ↔ wt μ ≤ h := by
  unfold ptnsLe
  simp only [mem_biUnion, mem_range, mem_ptns]
  exact ⟨fun ⟨e, h1, h2⟩ => by omega, fun h1 => ⟨_, by omega, rfl⟩⟩

/-- a = Σ_{h' ≤ h} ā_{h'} is a combination of the t^μ with |μ| ≤ h. -/
theorem eq_sum_ptnsLe {h : ℕ} {a : V} (ha : WtLe h a) : a = ∑ μ ∈ ptnsLe h, coef μ a • tpow μ := by
  refine eq_sum_of_subset a _ fun μ hμ => (mem_ptnsLe h μ).2 ?_
  by_contra hlt
  refine hμ ?_
  rw [ha, coef_sum]
  refine sum_eq_zero fun h' hh' => ?_
  rw [coef_part, if_neg (by have := mem_range.1 hh'; omega)]

/-! ### "All three claims are linear in a and b" -/

/-- T(a, b, f) is linear in each of a, b and f. -/
structure Tri (T : V → V → V → V) : Prop where
  add₁ : ∀ a a' b f, T (a + a') b f = T a b f + T a' b f
  smul₁ : ∀ (q : ℚ) a b f, T (q • a) b f = q • T a b f
  add₂ : ∀ a b b' f, T a (b + b') f = T a b f + T a b' f
  smul₂ : ∀ (q : ℚ) a b f, T a (q • b) f = q • T a b f
  add₃ : ∀ a b f f', T a b (f + f') = T a b f + T a b f'
  smul₃ : ∀ (q : ℚ) a b f, T a b (q • f) = q • T a b f

namespace Tri
variable {T T' : V → V → V → V}

theorem smul (hT : Tri T) (c : ℚ) : Tri fun a b f => c • T a b f where
  add₁ a a' b f := by rw [hT.add₁, smul_add]
  smul₁ q a b f := by rw [hT.smul₁, smul_comm]
  add₂ a b b' f := by rw [hT.add₂, smul_add]
  smul₂ q a b f := by rw [hT.smul₂, smul_comm]
  add₃ a b f f' := by rw [hT.add₃, smul_add]
  smul₃ q a b f := by rw [hT.smul₃, smul_comm]

theorem sub (hT : Tri T) (hT' : Tri T') : Tri fun a b f => T a b f - T' a b f where
  add₁ a a' b f := by rw [hT.add₁, hT'.add₁]; abel
  smul₁ q a b f := by rw [hT.smul₁, hT'.smul₁, smul_sub]
  add₂ a b b' f := by rw [hT.add₂, hT'.add₂]; abel
  smul₂ q a b f := by rw [hT.smul₂, hT'.smul₂, smul_sub]
  add₃ a b f f' := by rw [hT.add₃, hT'.add₃]; abel
  smul₃ q a b f := by rw [hT.smul₃, hT'.smul₃, smul_sub]

theorem sum {ι : Type} (s : Finset ι) {F : ι → V → V → V → V} (hF : ∀ i, Tri (F i)) : Tri fun a b f => ∑ i ∈ s, F i a b f where
  add₁ a a' b f := by simp only [(hF _).add₁, sum_add_distrib]
  smul₁ q a b f := by simp only [(hF _).smul₁, smul_sum]
  add₂ a b b' f := by simp only [(hF _).add₂, sum_add_distrib]
  smul₂ q a b f := by simp only [(hF _).smul₂, smul_sum]
  add₃ a b f f' := by simp only [(hF _).add₃, sum_add_distrib]
  smul₃ q a b f := by simp only [(hF _).smul₃, smul_sum]

theorem zero₁ (hT : Tri T) (b f : V) : T 0 b f = 0 := by
  have := hT.smul₁ 0 0 b f
  simpa using this

theorem zero₂ (hT : Tri T) (a f : V) : T a 0 f = 0 := by
  have := hT.smul₂ 0 a 0 f
  simpa using this

theorem zero₃ (hT : Tri T) (a b : V) : T a b 0 = 0 := by
  have := hT.smul₃ 0 a b 0
  simpa using this

theorem sum₁ (hT : Tri T) (S : Finset Ptn) (q : Ptn → ℚ) (b f : V) : T (∑ μ ∈ S, q μ • tpow μ) b f = ∑ μ ∈ S, q μ • T (tpow μ) b f := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [hT.zero₁]
  | insert x S hx ih => rw [sum_insert hx, sum_insert hx, hT.add₁, hT.smul₁, ih]

theorem sum₂ (hT : Tri T) (S : Finset Ptn) (q : Ptn → ℚ) (a f : V) : T a (∑ μ ∈ S, q μ • tpow μ) f = ∑ μ ∈ S, q μ • T a (tpow μ) f := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [hT.zero₂]
  | insert x S hx ih => rw [sum_insert hx, sum_insert hx, hT.add₂, hT.smul₂, ih]

theorem sum₃ (hT : Tri T) (S : Finset Ptn) (q : Ptn → ℚ) (a b : V) : T a b (∑ μ ∈ S, q μ • tpow μ) = ∑ μ ∈ S, q μ • T a b (tpow μ) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [hT.zero₃]
  | insert x S hx ih => rw [sum_insert hx, sum_insert hx, hT.add₃, hT.smul₃, ih]

/-- "So let a = t^μ with |μ| = h' ≤ h and b = t^ν": a claim T(a, b, f) = 0 that is linear in a, b
and f holds for all a = Σ_{h' ≤ h} ā_{h'}, b ∈ V_h and f ∈ V_E if it holds for monomials. -/
theorem eq_zero (hT : Tri T) {h E : ℕ} (hmon : ∀ μ ν σ : Ptn, wt μ ≤ h → wt ν = h → wt σ = E → T (tpow μ) (tpow ν) (tpow σ) = 0)
    {a b f : V} (ha : WtLe h a) (hb : b ∈ VE h) (hf : f ∈ VE E) : T a b f = 0 := by
  rw [eq_sum_ptnsLe ha, eq_sum_ptnsZ hb, eq_sum_ptnsZ hf, hT.sum₁]
  refine sum_eq_zero fun μ hμ => ?_
  rw [hT.sum₂, sum_eq_zero, smul_zero]
  intro ν hν
  rw [hT.sum₃, sum_eq_zero, smul_zero]
  intro σ hσ
  rw [hmon μ ν σ ((mem_ptnsLe h μ).1 hμ) (by exact_mod_cast (mem_ptnsZ _ ν).1 hν) (by exact_mod_cast (mem_ptnsZ _ σ).1 hσ), smul_zero]

end Tri

theorem angle_add (h i : ℕ) (a a' : V) : angle h i (a + a') = angle h i a + angle h i a' := by
  unfold angle part
  simp only [map_add, smul_add, sum_add_distrib]

theorem angle_smul (h i : ℕ) (q : ℚ) (a : V) : angle h i (q • a) = q • angle h i a := by
  unfold angle part
  simp only [map_smul, smul_sum]
  exact sum_congr rfl fun _ _ => smul_comm _ _ _

/-- a^⟨i⟩[r] b[r'] f is linear in a, b and f. -/
theorem tri_ab (hOp : OpFacts) (h i : ℕ) (r r' : ℤ) : Tri fun a b f => op (angle h i a) r (op b r' f) where
  add₁ a a' b f := by rw [angle_add, hOp.add_left]
  smul₁ q a b f := by rw [angle_smul, hOp.smul_left]
  add₂ a b b' f := by rw [hOp.add_left, hOp.add_right]
  smul₂ q a b f := by rw [hOp.smul_left, hOp.smul_right]
  add₃ a b f f' := by rw [hOp.add_right, hOp.add_right]
  smul₃ q a b f := by rw [hOp.smul_right, hOp.smul_right]

/-- b[r'] a^⟨i⟩[r] f is linear in a, b and f. -/
theorem tri_ba (hOp : OpFacts) (h i : ℕ) (r r' : ℤ) : Tri fun a b f => op b r' (op (angle h i a) r f) where
  add₁ a a' b f := by rw [angle_add, hOp.add_left, hOp.add_right]
  smul₁ q a b f := by rw [angle_smul, hOp.smul_left, hOp.smul_right]
  add₂ a b b' f := by rw [hOp.add_left]
  smul₂ q a b f := by rw [hOp.smul_left]
  add₃ a b f f' := by rw [hOp.add_right, hOp.add_right]
  smul₃ q a b f := by rw [hOp.smul_right, hOp.smul_right]

/-- Q_s(a, b) f is linear in a, b and f. -/
theorem tri_Q (hOp : OpFacts) (h : ℕ) (s : ℤ) : Tri (Q h s) := Tri.sum _ fun i => (tri_ab hOp h i _ _).smul _

/-- The same with the factors exchanged. -/
theorem tri_Q' (hOp : OpFacts) (h : ℕ) (s : ℤ) : Tri (Q' h s) := Tri.sum _ fun i => (tri_ba hOp h i _ _).smul _

/-- (a[−h]b)·f is linear in a, b and f. -/
theorem tri_pairing (hOp : OpFacts) (h : ℕ) : Tri fun a b f => pairing h a b • f where
  add₁ a a' b f := by rw [pairing, hOp.add_left, coeff_add, add_smul]; rfl
  smul₁ q a b f := by rw [pairing, hOp.smul_left, coeff_smul, smul_eq_mul, mul_smul]; rfl
  add₂ a b b' f := by rw [pairing, hOp.add_right, coeff_add, add_smul]; rfl
  smul₂ q a b f := by rw [pairing, hOp.smul_right, coeff_smul, smul_eq_mul, mul_smul]; rfl
  add₃ a b f f' := smul_add _ _ _
  smul₃ q a b f := smul_comm _ _ _

/-! ### Monomials -/

/-- The parts of a partition, listed, as natural numbers. -/
@[expose] noncomputable def lst (μ : Ptn) : List ℕ := toL μ.toList

theorem coe_lst (μ : Ptn) : (lst μ : Multiset ℕ) = toN μ := by
  unfold lst toL toN
  rw [← Multiset.map_coe, Multiset.coe_toList]

theorem sum_lst (μ : Ptn) : (lst μ).sum = wt μ := by
  rw [← Multiset.sum_coe, coe_lst]
  rfl

theorem pos_lst (μ : Ptn) : ClauseBound.Boson.Pos (lst μ) := fun n hn => by
  obtain ⟨k, -, rfl⟩ := List.mem_map.1 hn
  exact k.pos

theorem part_tpow (h' : ℕ) (μ : Ptn) : part h' (tpow μ) = if h' = wt μ then tpow μ else 0 := by
  refine ext_coef fun π => ?_
  rw [coef_part]
  by_cases h : h' = wt μ
  · rw [if_pos h]
    by_cases hπ : wt π = h'
    · rw [if_pos hπ]
    · rw [if_neg hπ, coef_tpow, if_neg]
      rintro rfl
      exact hπ h.symm
  · rw [if_neg h, coef_zero]
    split_ifs with hπ
    · rw [coef_tpow, if_neg]
      rintro rfl
      exact h hπ.symm
    · rfl

/-- "Then a^⟨i⟩ = C(H, i)·a with H = h' + h", for a = t^μ with |μ| = h' ≤ h. -/
theorem angle_tpow {h : ℕ} (i : ℕ) {μ : Ptn} (hμ : wt μ ≤ h) : angle h i (tpow μ) = ((wt μ + h).choose i : ℚ) • tpow μ := by
  unfold angle
  simp only [part_tpow, smul_ite, smul_zero]
  rw [sum_ite_eq', if_pos (mem_range.2 (by omega))]

/-- The coefficients of a[r]t^σ, for a monomial a, are the entries of the matrix. -/
theorem coef_op_tpow (hB : StBridge) (hOp : OpFacts) (μ : Ptn) (r : ℤ) (π σ : Ptn) :
    coef π (op (tpow μ) r (tpow σ)) = (ClauseBound.Boson.op (lst μ) r (toN π) (toN σ) : ℚ) := by
  have h := hOp.mono μ.toList r (tpow σ)
  rw [Multiset.coe_toList] at h
  rw [h]
  exact hB _ _ _ _

/-- A sum over the multisets of positive natural numbers with sum m is a sum over the partitions of
m. -/
theorem sum_Pz (m : ℤ) (F : Multiset ℕ → ℤ) : ∑ τ ∈ ClauseBound.Boson.Pz m, F τ = ∑ τ ∈ ptnsZ m, F (toN τ) := by
  unfold ClauseBound.Boson.Pz ptnsZ
  split_ifs
  · have e : ClauseBound.Boson.P m.toNat = (ptns m.toNat).image toN := by
      unfold ClauseBound.Boson.P ptns
      rw [image_image]
      exact image_congr fun q _ => (toN_map_toPNat' fun i hi => q.parts_pos hi).symm
    rw [e, sum_image toN_injective.injOn]
  · rfl

theorem op_sum_right (hOp : OpFacts) (a : V) (r : ℤ) (S : Finset Ptn) (q : Ptn → ℚ) :
    op a r (∑ μ ∈ S, q μ • tpow μ) = ∑ μ ∈ S, q μ • op a r (tpow μ) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    have := hOp.smul_right a r 0 0
    simpa using this
  | insert x S hx ih => rw [sum_insert hx, sum_insert hx, hOp.add_right, hOp.smul_right, ih]

/-- The coefficients of a[r]b[r']t^σ, for monomials a and b, are the entries of the product of the
two matrices: by (O1), b[r']t^σ is a combination of the t^τ with |τ| = |σ| + r'. -/
theorem coef_comp (hB : StBridge) (hOp : OpFacts) (h1 : O1) (μ ν : Ptn) (r r' : ℤ) (π σ : Ptn) :
    coef π (op (tpow μ) r (op (tpow ν) r' (tpow σ))) = (ClauseBound.Boson.mul2 (lst μ) r (lst ν) r' (toN π) (toN σ) : ℚ) := by
  have hg := h1.maps (tpow ν) r' (wt σ) (tpow σ) (tpow_mem_VE σ)
  rw [eq_sum_ptnsZ hg, op_sum_right hOp, coef_sum]
  unfold ClauseBound.Boson.mul2
  rw [sum_Pz, sum_toN]
  push_cast
  refine sum_congr rfl fun τ _ => ?_
  rw [coef_smul, coef_op_tpow hB hOp, coef_op_tpow hB hOp]
  ring

theorem ok_single {h : ℕ} {μ ν : Ptn} (hμ : wt μ ≤ h) (hν : wt ν = h) : ClauseBound.Boson.FA.Ok [((1 : ℤ), lst μ)] (lst ν).sum := fun c hc => by
  rw [List.mem_singleton.1 hc]
  exact ⟨pos_lst μ, by rw [sum_lst, sum_lst, hν]; exact hμ⟩

/-- The coefficients of Q_s(a, b)t^σ for monomials a and b. -/
theorem coef_Q_mon (hB : StBridge) (hOp : OpFacts) (h1 : O1) {h : ℕ} {μ ν : Ptn} (hμ : wt μ ≤ h) (hν : wt ν = h) (s : ℤ) (π σ : Ptn) :
    coef π (Q h s (tpow μ) (tpow ν) (tpow σ)) = (ClauseBound.Boson.Qk [((1 : ℤ), lst μ)] (lst ν) s (toN π) (toN σ) : ℚ) := by
  unfold Q ClauseBound.Boson.Qk
  rw [coef_sum, sum_lst, hν]
  push_cast
  refine sum_congr rfl fun i _ => ?_
  rw [coef_smul, angle_tpow i hμ, hOp.smul_left, coef_smul, coef_comp hB hOp h1]
  simp [sum_lst]

/-- The same with the factors exchanged. -/
theorem coef_Q'_mon (hB : StBridge) (hOp : OpFacts) (h1 : O1) {h : ℕ} {μ ν : Ptn} (hμ : wt μ ≤ h) (hν : wt ν = h) (s : ℤ) (π σ : Ptn) :
    coef π (Q' h s (tpow μ) (tpow ν) (tpow σ)) = (ClauseBound.Boson.Qk' [((1 : ℤ), lst μ)] (lst ν) s (toN π) (toN σ) : ℚ) := by
  unfold Q' ClauseBound.Boson.Qk'
  rw [coef_sum, sum_lst, hν]
  push_cast
  refine sum_congr rfl fun i _ => ?_
  rw [coef_smul, angle_tpow i hμ, hOp.smul_left, hOp.smul_right, coef_smul, coef_comp hB hOp h1]
  simp [sum_lst]

/-- The number a[−h]b for monomials a and b is the entry in the row of the monomial 1 and the column
of b of the matrix of a[−h]. -/
theorem pairing_mon (hB : StBridge) (hOp : OpFacts) (h : ℕ) (μ ν : Ptn) :
    pairing h (tpow μ) (tpow ν) = (ClauseBound.Boson.op (lst μ) (-(h : ℤ)) 0 (toN ν) : ℚ) := by
  have e := coef_op_tpow hB hOp μ (-(h : ℤ)) 0 ν
  unfold coef at e
  rw [map_zero] at e
  exact e

end GeneralPieces.LemQ

namespace GeneralPieces

open AppHalfPieces MvPolynomial Finset GeneralPieces.Ring GeneralPieces.LemQ

/-- If the three claims of Lemma 9 on the operators Q_s hold for the matrices, the lemma holds in
the form in which the paper states it. The hypotheses are proved in the file named at the head. -/
theorem lemmaQ (hB : StBridge) (hOp : OpFacts) (h1 : O1) (hMa : StMatA) (hMb : StMatB) (hMc : StMatC) : LemmaQ where
  a h a b hh hb ha E f hf s := by
    refine sub_eq_zero.1 (((tri_Q hOp h s).sub (tri_Q' hOp h s)).eq_zero (h := h) (E := E) (fun μ ν σ hμ hν _ => ?_) ha hb hf)
    refine ext_coef fun π => ?_
    rw [coef_sub, coef_Q_mon hB hOp h1 hμ hν, coef_Q'_mon hB hOp h1 hμ hν,
      hMa _ _ (ok_single hμ hν) (pos_lst ν) (by rw [sum_lst, hν]; exact hh) s _ _ (zero_notMem_toN π) (zero_notMem_toN σ), sub_self, coef_zero]
  b h a b hh hb ha E f hf s hs := by
    refine (tri_Q hOp h s).eq_zero (h := h) (E := E) (fun μ ν σ hμ hν hσ => ?_) ha hb hf
    refine ext_coef fun π => ?_
    rw [coef_Q_mon hB hOp h1 hμ hν,
      hMb _ _ (ok_single hμ hν) (pos_lst ν) (by rw [sum_lst, hν]; exact hh) s _ _ (zero_notMem_toN π) (zero_notMem_toN σ) (by rw [sum_toN, sum_lst, hσ, hν]; exact hs),
      coef_zero, Int.cast_zero]
  c h a b hh hb ha E f hf := by
    refine sub_eq_zero.1 (((Tri.sum (Icc (-((E : ℤ) + h)) ((E : ℤ) + h)) fun s => tri_Q hOp h s).sub (tri_pairing hOp h)).eq_zero (h := h) (E := E)
      (fun μ ν σ hμ hν hσ => ?_) ha hb hf)
    refine ext_coef fun π => ?_
    have e := hMc _ _ (ok_single hμ hν) (pos_lst ν) (by rw [sum_lst, hν]; exact hh) _ _ (zero_notMem_toN π) (zero_notMem_toN σ)
    rw [sum_toN, sum_lst, hσ, hν, coe_lst] at e
    rw [coef_sub, coef_sum, coef_smul, coef_tpow, pairing_mon hB hOp, coef_zero]
    simp only [coef_Q_mon hB hOp h1 hμ hν]
    rw [← Int.cast_sum, e]
    by_cases hπ : π = σ
    · rw [if_pos hπ, if_pos (by rw [hπ])]
      simp
    · rw [if_neg hπ, if_neg fun h' => hπ (toN_injective h')]
      simp

end GeneralPieces
