/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import GeneralPieces.Ring.Defs
public import ClauseBound.Boson.Text
public import Mathlib.RingTheory.Derivation.Lie

/-! # The integer matrices `ClauseBound.Boson.op` are those of the operators a[r] of Appendix B

`GeneralPieces.stBridge`: the coefficient of t^π in a[r]·t^σ, with a[r] the sum of display (47) over
ℚ[t₁, t₂, …], is the entry (π, σ) of the integer matrix `ClauseBound.Boson.op`, which is defined by
the recursion (O2).
The steps: the rules for ∇_k on monomials; the differentiations commute, so that one more positive
k_i may be applied first (`nordQ_cons_pos`); term by term, the coefficients are those of the same
term
over ℤ[t₀, t₁, …] (`coef_nordQ`); "on f ∈ V_E a term vanishes if its positive k_i add up to more
than E" (`pos_eq_zero`), so that, the sum of the k_i being −r, all k_i of a nonzero term lie
between −M and M for M = E + |r| (`term_eq_zero`, `opMon_eq_sum`); and the finite sum is the entry
of the matrix by `ClauseBound.Boson.op_eq_sum`. -/

public section

namespace GeneralPieces.Ring

open AppHalfPieces MvPolynomial Finset

/-! ### The operators ∇_k -/

theorem nabla_neg {k : ℤ} (hk : k < 0) (f : V) : nabla k f = X (pn k) * f := by rw [nabla, if_pos hk]

theorem nabla_pos {k : ℤ} (hk : 0 < k) (f : V) : nabla k f = (k : ℚ) • pderiv (pn k) f := by rw [nabla, if_neg (by omega), if_pos hk]

theorem nabla_smul (k : ℤ) (q : ℚ) (f : V) : nabla k (q • f) = q • nabla k f := by
  unfold nabla
  split_ifs
  · rw [mul_smul_comm]
  · rw [Derivation.map_smul, smul_comm]
  · rw [smul_zero]

theorem nabla_zero_right (k : ℤ) : nabla k (0 : V) = 0 := by
  have := nabla_smul k 0 0
  simpa using this

/-- The positive integer |k| as a natural number. -/
theorem pn_coe {k : ℤ} (hk : k ≠ 0) : ((pn k : ℕ+) : ℕ) = k.natAbs := PNat.toPNat'_coe (by omega)

/-- ∂/∂t_i and ∂/∂t_j commute. -/
theorem pderiv_comm (i j : ℕ+) (f : V) : pderiv i (pderiv j f) = pderiv j (pderiv i f) := by
  have h : ⁅(pderiv i : Derivation ℚ V V), pderiv j⁆ = 0 := derivation_ext fun k => by
    rw [Derivation.commutator_apply, pderiv_X, pderiv_X]
    simp only [Pi.single_apply]
    split_ifs <;> simp
  have h' := congrArg (fun D : Derivation ℚ V V => D f) h
  simp only [Derivation.commutator_apply] at h'
  exact sub_eq_zero.1 h'

/-- Two differentiations ∇_k, ∇_k' commute. -/
theorem nabla_comm_pos {k k' : ℤ} (hk : 0 < k) (hk' : 0 < k') (f : V) : nabla k (nabla k' f) = nabla k' (nabla k f) := by
  rw [nabla_pos hk, nabla_pos hk', nabla_pos hk', nabla_pos hk, Derivation.map_smul, Derivation.map_smul, pderiv_comm, smul_comm]

theorem toFinsupp_erase (π : Ptn) (l : ℕ+) : Multiset.toFinsupp (π.erase l) = Multiset.toFinsupp π - Finsupp.single l 1 := by
  ext x
  rw [Finsupp.coe_tsub, Pi.sub_apply, Multiset.toFinsupp_apply, Multiset.toFinsupp_apply]
  by_cases h : x = l
  · subst h
    rw [Multiset.count_erase_self, Finsupp.single_eq_same]
  · rw [Multiset.count_erase_of_ne h, Finsupp.single_eq_of_ne h, Nat.sub_zero]

/-- The coefficients of t_l·f. -/
theorem coef_X_mul (π : Ptn) (l : ℕ+) (f : V) : coef π (X l * f) = if l ∈ π then coef (π.erase l) f else 0 := by
  unfold coef
  rw [coeff_X_mul', Multiset.toFinsupp_support, toFinsupp_erase]
  simp only [Multiset.mem_toFinset]

/-- ∇_k on a monomial, k ≥ 1. -/
theorem nabla_pos_tpow {k : ℤ} (hk : 0 < k) (σ : Ptn) : nabla k (tpow σ) = ((k : ℚ) * σ.count (pn k)) • tpow (σ.erase (pn k)) := by
  rw [nabla_pos hk]
  unfold tpow
  rw [pderiv_monomial, toFinsupp_erase, Multiset.toFinsupp_apply, smul_monomial, smul_monomial]
  simp

theorem coef_tpow (π σ : Ptn) : coef π (tpow σ) = if π = σ then 1 else 0 := by
  unfold coef tpow
  rw [coeff_monomial]
  by_cases h : π = σ
  · simp [h]
  · rw [if_neg h, if_neg]
    intro h'
    exact h (Multiset.toFinsupp.injective h'.symm)

theorem coef_smul (π : Ptn) (q : ℚ) (f : V) : coef π (q • f) = q * coef π f := by
  unfold coef
  rw [coeff_smul, smul_eq_mul]

theorem foldr_nabla_smul (l : List ℤ) (q : ℚ) (f : V) : l.foldr nabla (q • f) = q • l.foldr nabla f := by
  induction l with
  | nil => rfl
  | cons k l ih => rw [List.foldr_cons, List.foldr_cons, ih, nabla_smul]

/-- One more differentiation may be applied first. -/
theorem nabla_foldr_pos {k : ℤ} (hk : 0 < k) (l : List ℤ) (hl : ∀ x ∈ l, 0 < x) (f : V) : nabla k (l.foldr nabla f) = l.foldr nabla (nabla k f) := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    rw [List.foldr_cons, List.foldr_cons, nabla_comm_pos hk (hl x (by simp)), ih fun y hy => hl y (by simp [hy])]

/-! ### One term of display (47) -/

/-- ∏_{k_i < 0} ∇_{k_i} · ∏_{k_i > 0} ∇_{k_i}, applied to f. -/
@[expose] noncomputable def nordQ (ks : List ℤ) (f : V) : V := (ks.filter (· < 0)).foldr nabla ((ks.filter (0 < ·)).foldr nabla f)

/-- ∏_i C(−k_i−1, μ_i−1). -/
@[expose] def wtQ (μ : List ℕ+) (ks : List ℤ) : ℤ := (List.zipWith (fun (m : ℕ+) (k : ℤ) => binom (-k - 1) ((m : ℤ) - 1)) μ ks).prod

theorem term_eq (μ : List ℕ+) (ks : List ℤ) (f : V) : term μ ks f = ((wtQ μ ks : ℤ) : ℚ) • nordQ ks f := rfl

theorem nordQ_nil (f : V) : nordQ [] f = f := rfl

/-- A negative index: one more multiplication, applied last. -/
theorem nordQ_cons_neg {k : ℤ} (hk : k < 0) (ks : List ℤ) (f : V) : nordQ (k :: ks) f = X (pn k) * nordQ ks f := by
  have e1 : (k :: ks).filter (· < 0) = k :: ks.filter (· < 0) := List.filter_cons_of_pos (by simpa using hk)
  have e2 : (k :: ks).filter (0 < ·) = ks.filter (0 < ·) := List.filter_cons_of_neg (by simp; omega)
  unfold nordQ
  rw [e1, e2, List.foldr_cons, nabla_neg hk]

/-- A positive index: one more differentiation, which may be applied first. -/
theorem nordQ_cons_pos {k : ℤ} (hk : 0 < k) (ks : List ℤ) (f : V) : nordQ (k :: ks) f = nordQ ks (nabla k f) := by
  have e1 : (k :: ks).filter (· < 0) = ks.filter (· < 0) := List.filter_cons_of_neg (by simp; omega)
  have e2 : (k :: ks).filter (0 < ·) = k :: ks.filter (0 < ·) := List.filter_cons_of_pos (by simpa using hk)
  unfold nordQ
  rw [e1, e2, List.foldr_cons, nabla_foldr_pos hk _ fun x hx => by simpa using (List.mem_filter.1 hx).2]

theorem nordQ_smul (ks : List ℤ) (q : ℚ) (f : V) : nordQ ks (q • f) = q • nordQ ks f := by
  unfold nordQ
  rw [foldr_nabla_smul, foldr_nabla_smul]

/-! ### Partitions as multisets of natural numbers -/

theorem toN_injective : Function.Injective toN := Multiset.map_injective PNat.coe_injective

theorem toN_erase (π : Ptn) (l : ℕ+) : toN (π.erase l) = (toN π).erase (l : ℕ) := Multiset.map_erase _ PNat.coe_injective l π

theorem mem_toN (π : Ptn) (l : ℕ+) : (l : ℕ) ∈ toN π ↔ l ∈ π := Multiset.mem_map_of_injective PNat.coe_injective

theorem count_toN (π : Ptn) (l : ℕ+) : (toN π).count (l : ℕ) = π.count l := Multiset.count_map_eq_count' _ π PNat.coe_injective l

theorem zero_notMem_toN (π : Ptn) : 0 ∉ toN π := fun h => by
  obtain ⟨k, -, hk⟩ := Multiset.mem_map.1 h
  exact k.pos.ne' hk

theorem sum_toN (π : Ptn) : (toN π).sum = wt π := rfl

/-- Without a part l, the weight is smaller by l. -/
theorem wt_erase {σ : Ptn} {l : ℕ+} (h : l ∈ σ) : wt (σ.erase l) + l = wt σ := by
  rw [← sum_toN, ← sum_toN, toN_erase, add_comm]
  exact Multiset.sum_erase ((mem_toN σ l).2 h)

/-! ### Term by term, the coefficients are those over ℤ[t₀, t₁, …] -/

theorem coef_nordQ (ks : List ℤ) : (∀ k ∈ ks, k ≠ 0) → ∀ π σ : Ptn,
    coef π (nordQ ks (tpow σ)) = ((ClauseBound.Boson.coef (toN π) (ClauseBound.Boson.nord ks (ClauseBound.Boson.mon (toN σ))) : ℤ) : ℚ) := by
  induction ks with
  | nil =>
    intro _ π σ
    rw [nordQ_nil, coef_tpow, ClauseBound.Boson.Text.nord_nil, ClauseBound.Boson.Text.coef_mon]
    by_cases h : π = σ
    · simp [h]
    · rw [if_neg h, if_neg fun h' => h (toN_injective h')]
      simp
  | cons k ks ih =>
    intro h0 π σ
    have hk0 : k ≠ 0 := h0 k (by simp)
    have ih' := ih fun x hx => h0 x (by simp [hx])
    rcases lt_or_gt_of_ne hk0 with hk | hk
    · have e : (-k).toNat = ((pn k : ℕ+) : ℕ) := by rw [pn_coe hk0]; omega
      rw [nordQ_cons_neg hk, coef_X_mul, ClauseBound.Boson.Text.nord_cons_neg hk, ClauseBound.Boson.Text.coef_X_mul, e]
      by_cases hm : pn k ∈ π
      · rw [if_pos hm, if_pos ((mem_toN π _).2 hm), ih', toN_erase]
      · rw [if_neg hm, if_neg fun h => hm ((mem_toN π _).1 h)]
        simp
    · have e : k = (((pn k : ℕ+) : ℕ) : ℤ) := by rw [pn_coe hk0]; omega
      rw [nordQ_cons_pos hk, nabla_pos_tpow hk, nordQ_smul, coef_smul, ih', ClauseBound.Boson.Text.nord_cons_pos hk]
      conv_rhs => rw [e, ClauseBound.Boson.Text.nabPos_mon, ClauseBound.Boson.Text.nord_smul, ClauseBound.Boson.Text.coef_smul, count_toN, ← toN_erase, ← e]
      push_cast
      ring

/-- The products of binomial coefficients are the same. -/
theorem wtQ_eq (μ : List ℕ+) (ks : List ℤ) : wtQ μ ks = ClauseBound.Boson.wt (toL μ) ks := by
  unfold wtQ ClauseBound.Boson.wt toL
  rw [List.zipWith_map_left]
  congr 1
  refine congrArg (fun F => List.zipWith F μ ks) ?_
  funext m k
  have hm := m.pos
  rw [binom, if_pos (by omega)]
  congr 1
  omega

/-! ### Only finitely many terms are nonzero -/

/-- "A term vanishes if its positive k_i add up to more than E", on a monomial of weight E. -/
theorem pos_eq_zero (l : List ℤ) : (∀ x ∈ l, 0 < x) → ∀ σ : Ptn, (wt σ : ℤ) < l.sum → l.foldr nabla (tpow σ) = 0 := by
  induction l with
  | nil =>
    intro _ σ h
    simp at h
    omega
  | cons k l ih =>
    intro hl σ h
    have hk : 0 < k := hl k (by simp)
    have hl' : ∀ x ∈ l, 0 < x := fun x hx => hl x (by simp [hx])
    rw [List.foldr_cons, nabla_foldr_pos hk l hl', nabla_pos_tpow hk, foldr_nabla_smul]
    by_cases hm : pn k ∈ σ
    · rw [ih hl' (σ.erase (pn k)) ?_, smul_zero]
      have h1 := wt_erase hm
      have h2 := pn_coe hk.ne'
      rw [List.sum_cons] at h
      omega
    · rw [Multiset.count_eq_zero_of_notMem hm]
      simp

theorem foldr_nabla_zero (l : List ℤ) : l.foldr nabla (0 : V) = 0 := by
  have := foldr_nabla_smul l 0 0
  simpa using this

/-- The negative and the positive entries of a list of integers: their sums add up to the sum of the
list, and every entry lies between them. -/
theorem filter_sums (ks : List ℤ) : (ks.filter (· < 0)).sum ≤ 0 ∧ 0 ≤ (ks.filter (0 < ·)).sum ∧ ks.sum = (ks.filter (· < 0)).sum + (ks.filter (0 < ·)).sum ∧
    ∀ k ∈ ks, (ks.filter (· < 0)).sum ≤ k ∧ k ≤ (ks.filter (0 < ·)).sum := by
  induction ks with
  | nil => simp
  | cons x ks ih =>
    obtain ⟨h1, h2, h3, h4⟩ := ih
    rcases lt_trichotomy x 0 with hx | hx | hx
    · rw [List.filter_cons_of_pos (by simpa using hx), List.filter_cons_of_neg (by simp; omega), List.sum_cons, List.sum_cons]
      refine ⟨by omega, h2, by omega, fun k hk => ?_⟩
      rcases List.mem_cons.1 hk with rfl | hk
      · omega
      · have := h4 k hk; omega
    · rw [List.filter_cons_of_neg (by simp; omega), List.filter_cons_of_neg (by simp; omega), List.sum_cons]
      refine ⟨h1, h2, by omega, fun k hk => ?_⟩
      rcases List.mem_cons.1 hk with rfl | hk
      · omega
      · exact h4 k hk
    · rw [List.filter_cons_of_neg (by simp; omega), List.filter_cons_of_pos (by simpa using hx), List.sum_cons, List.sum_cons]
      refine ⟨h1, by omega, by omega, fun k hk => ?_⟩
      rcases List.mem_cons.1 hk with rfl | hk
      · omega
      · have := h4 k hk; omega

/-- On a monomial of weight E, a term of (47) vanishes unless all k_i lie between −(E + |r|) and E + |r|. -/
theorem term_eq_zero (μ : List ℕ+) (r : ℤ) (σ : Ptn) (ks : List ℤ) (hs : ks.sum = -r) (hb : ∃ k ∈ ks, k < -((wt σ : ℤ) + |r|) ∨ (wt σ : ℤ) + |r| < k) :
    term μ ks (tpow σ) = 0 := by
  obtain ⟨h1, h2, h3, h4⟩ := filter_sums ks
  obtain ⟨k, hk, hk'⟩ := hb
  have h5 := h4 k hk
  have hr1 := le_abs_self r
  have hr2 := neg_abs_le r
  have hr3 := abs_nonneg r
  rw [term_eq, nordQ, pos_eq_zero _ (fun x hx => by simpa using (List.mem_filter.1 hx).2) σ (by omega), foldr_nabla_zero, smul_zero]

/-- Display (47) on a monomial of weight E as a finite sum: over the lists of nonzero integers
between −M and M with sum −r, for any M ≥ E + |r|. -/
theorem opMon_eq_sum (μ : List ℕ+) (r : ℤ) (σ : Ptn) (M : ℕ) (hM : (wt σ : ℤ) + |r| ≤ M) :
    opMon μ r (tpow σ) = ∑ ks ∈ ClauseBound.Boson.tup M μ.length with ks.sum = -r, term μ ks (tpow σ) := by
  unfold opMon
  refine finsum_mem_eq_sum_of_subset _ (fun ks hks => ?_) fun ks hks => ?_
  · obtain ⟨⟨h1, h2, h3⟩, h4⟩ := hks
    refine mem_coe.2 (mem_filter.2 ⟨ClauseBound.Boson.Text.mem_tup.2 ⟨h1, fun k hk => ⟨h2 k hk, ?_⟩⟩, h3⟩)
    by_contra hcon
    exact h4 (term_eq_zero μ r σ ks h3 ⟨k, hk, by omega⟩)
  · obtain ⟨h1, h2⟩ := mem_filter.1 (mem_coe.1 hks)
    obtain ⟨h3, h4⟩ := ClauseBound.Boson.Text.mem_tup.1 h1
    exact ⟨h3, fun k hk => (h4 k hk).1, h2⟩

end GeneralPieces.Ring

namespace GeneralPieces

open AppHalfPieces MvPolynomial Finset GeneralPieces.Ring

/-- The coefficient of t^π in a[r]·t^σ is the entry (π, σ) of the matrix `ClauseBound.Boson.op`. -/
theorem stBridge : StBridge := by
  intro a r π σ
  obtain ⟨M, hM⟩ : ∃ M : ℕ, M = wt σ + r.natAbs + wt π := ⟨_, rfl⟩
  have hlen : (toL a).length = a.length := List.length_map _
  rw [opMon_eq_sum a r σ M (by rw [Int.abs_eq_natAbs]; omega),
    ClauseBound.Boson.op_eq_sum (toL a) r (toN π) (toN σ) M (zero_notMem_toN π) (zero_notMem_toN σ) (by rw [sum_toN]; omega) (by rw [sum_toN]; omega), hlen]
  unfold coef
  rw [coeff_sum]
  push_cast
  refine sum_congr rfl fun ks hks => ?_
  have h0 : ∀ k ∈ ks, k ≠ 0 := fun k hk => ((ClauseBound.Boson.Text.mem_tup.1 (mem_filter.1 hks).1).2 k hk).1
  have := coef_nordQ ks h0 π σ
  unfold coef at this
  rw [term_eq, coeff_smul, smul_eq_mul, this, wtQ_eq]

end GeneralPieces
