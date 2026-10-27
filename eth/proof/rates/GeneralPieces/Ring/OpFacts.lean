/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import GeneralPieces.Ring.Basic

/-! # Display (47) of Appendix B: the operators a[r] are well defined and linear

What the appendix says with display (47) (`GeneralPieces.opFacts`): "on f ∈ V_E a term vanishes if
its positive k_i add up to more than E, so only finitely many terms are nonzero" (`nordQ_eq_zero`,
`term_eq_zero_of_Bd`, `finite_terms`); the order in which the parts of μ are listed does not matter
(`opMon_perm`); a[r] is linear in f and in a. The tool is the sum of (47) over the lists of
nonzero integers between −M and M (`opWin`): it is a[r]·f for all large M (`opMon_eq_opWin`), and
sorting its terms by the integer chosen for the first part gives a recursion (`opWin_cons`), the
form of (O2) for these finite sums. -/

public section

namespace GeneralPieces.Ring

open AppHalfPieces MvPolynomial Finset

/-! ### The terms are linear in f -/

/-- ∇_k as a linear map. -/
@[expose] noncomputable def nablaL (k : ℤ) : V →ₗ[ℚ] V where
  toFun := nabla k
  map_add' := nabla_add k
  map_smul' := nabla_smul k

theorem nabla_sum {ι : Type} (k : ℤ) (s : Finset ι) (F : ι → V) : nabla k (∑ i ∈ s, F i) = ∑ i ∈ s, nabla k (F i) := map_sum (nablaL k) F s

theorem foldr_nabla_add (l : List ℤ) (f g : V) : l.foldr nabla (f + g) = l.foldr nabla f + l.foldr nabla g := by
  induction l with
  | nil => rfl
  | cons k l ih => rw [List.foldr_cons, List.foldr_cons, List.foldr_cons, ih, nabla_add]

theorem nordQ_add (ks : List ℤ) (f g : V) : nordQ ks (f + g) = nordQ ks f + nordQ ks g := by
  unfold nordQ
  rw [foldr_nabla_add, foldr_nabla_add]

/-- One term of (47) as a linear map. -/
@[expose] noncomputable def termL (μ : List ℕ+) (ks : List ℤ) : V →ₗ[ℚ] V where
  toFun := term μ ks
  map_add' := fun f g => by rw [term_eq, term_eq, term_eq, nordQ_add, smul_add]
  map_smul' := fun q f => by rw [term_eq, term_eq, nordQ_smul, smul_comm]; rfl

theorem term_add (μ : List ℕ+) (ks : List ℤ) (f g : V) : term μ ks (f + g) = term μ ks f + term μ ks g := map_add (termL μ ks) f g

theorem term_smul (μ : List ℕ+) (ks : List ℤ) (q : ℚ) (f : V) : term μ ks (q • f) = q • term μ ks f := map_smul (termL μ ks) q f

/-! ### Only finitely many terms are nonzero -/

/-- Every monomial of f has weight at most E. -/
@[expose] def Bd (f : V) (E : ℤ) : Prop := ∀ μ, coef μ f ≠ 0 → (wt μ : ℤ) ≤ E

theorem exists_Bd (f : V) : ∃ E : ℕ, Bd f E := by
  refine ⟨f.support.sup fun d => wt (Finsupp.toMultiset d), fun μ hμ => ?_⟩
  have h := le_sup (f := fun d => wt (Finsupp.toMultiset d)) (mem_support_iff.2 hμ)
  simp only [Multiset.toFinsupp_toMultiset] at h
  exact_mod_cast h

theorem Bd.mono {f : V} {E E' : ℤ} (h : Bd f E) (hE : E ≤ E') : Bd f E' := fun μ hμ => (h μ hμ).trans hE

theorem Bd.add {f g : V} {E : ℤ} (hf : Bd f E) (hg : Bd g E) : Bd (f + g) E := fun μ hμ => by
  by_cases h : coef μ f = 0
  · refine hg μ fun h' => hμ ?_
    unfold coef at *
    rw [coeff_add, h, h', add_zero]
  · exact hf μ h

theorem Bd.smul {f : V} {E : ℤ} (hf : Bd f E) (q : ℚ) : Bd (q • f) E := fun μ hμ => hf μ fun h => hμ (by rw [coef_smul, h, mul_zero])

theorem Bd_of_mem {f : V} {E : ℤ} (hf : f ∈ VE E) : Bd f E := fun μ hμ => ((mem_VE_iff E f).1 hf μ hμ).le

/-- "A term vanishes if its positive k_i add up to more than E." -/
theorem nordQ_eq_zero {f : V} {E : ℤ} (hf : Bd f E) (ks : List ℤ) (h : E < (ks.filter (0 < ·)).sum) : nordQ ks f = 0 := by
  have h0 : (ks.filter (0 < ·)).foldr nabla f = 0 := by
    rw [eq_sum_tpow f]
    have hs : ∀ (l : List ℤ) (s : Finset (ℕ+ →₀ ℕ)) (F : (ℕ+ →₀ ℕ) → V), l.foldr nabla (∑ d ∈ s, F d) = ∑ d ∈ s, l.foldr nabla (F d) := by
      intro l s F
      induction l with
      | nil => rfl
      | cons k l ih => rw [List.foldr_cons, ih, nabla_sum]; rfl
    rw [hs]
    refine sum_eq_zero fun d hd => ?_
    rw [foldr_nabla_smul, pos_eq_zero _ (fun x hx => by simpa using (List.mem_filter.1 hx).2), smul_zero]
    refine lt_of_le_of_lt (hf _ ?_) h
    unfold coef
    rw [Finsupp.toMultiset_toFinsupp]
    exact mem_support_iff.1 hd
  rw [nordQ, h0, foldr_nabla_zero]

/-- A term of (47) vanishes on f unless all k_i lie between −M and M, if the monomials of f have
weight at most E, E ≤ M and E + r ≤ M. -/
theorem term_eq_zero_of_Bd {f : V} {E : ℤ} (hf : Bd f E) (μ : List ℕ+) {r : ℤ} {M : ℕ} (h1 : E ≤ M) (h2 : E + r ≤ M) (ks : List ℤ) (hs : ks.sum = -r)
    (hb : ∃ k ∈ ks, k < -(M : ℤ) ∨ (M : ℤ) < k) : term μ ks f = 0 := by
  obtain ⟨a1, a2, a3, a4⟩ := filter_sums ks
  obtain ⟨k, hk, hk'⟩ := hb
  have a5 := a4 k hk
  rw [term_eq, nordQ_eq_zero hf ks (by omega), smul_zero]

/-- The sum of display (47) over the lists of nonzero integers between −M and M. -/
@[expose] noncomputable def opWin (μ : List ℕ+) (M : ℕ) (r : ℤ) (f : V) : V := ∑ ks ∈ ClauseBound.Boson.tup M μ.length with ks.sum = -r, term μ ks f

/-- a[r]·f is the finite sum, for all large M. -/
theorem opMon_eq_opWin {f : V} {E : ℤ} (hf : Bd f E) (μ : List ℕ+) {r : ℤ} {M : ℕ} (h1 : E ≤ M) (h2 : E + r ≤ M) : opMon μ r f = opWin μ M r f := by
  unfold opMon opWin
  refine finsum_mem_eq_sum_of_subset _ (fun ks hks => ?_) fun ks hks => ?_
  · obtain ⟨⟨a1, a2, a3⟩, a4⟩ := hks
    refine mem_coe.2 (mem_filter.2 ⟨ClauseBound.Boson.Text.mem_tup.2 ⟨a1, fun k hk => ⟨a2 k hk, ?_⟩⟩, a3⟩)
    by_contra hcon
    exact a4 (term_eq_zero_of_Bd hf μ h1 h2 ks a3 ⟨k, hk, by omega⟩)
  · obtain ⟨a1, a2⟩ := mem_filter.1 (mem_coe.1 hks)
    obtain ⟨a3, a4⟩ := ClauseBound.Boson.Text.mem_tup.1 a1
    exact ⟨a3, fun k hk => (a4 k hk).1, a2⟩

/-- A window that is large enough for f and r. -/
theorem exists_window (f : V) (r : ℤ) : ∃ (E : ℤ) (M : ℕ), Bd f E ∧ E ≤ M ∧ E + r ≤ M := by
  obtain ⟨E, hE⟩ := exists_Bd f
  exact ⟨E, E + r.natAbs, hE, by omega, by omega⟩

/-- "So only finitely many terms are nonzero." -/
theorem finite_terms (μ : List ℕ+) (r : ℤ) (f : V) : {ks ∈ Choices μ r | term μ ks f ≠ 0}.Finite := by
  obtain ⟨E, M, hE, h1, h2⟩ := exists_window f r
  refine (finite_toSet (ClauseBound.Boson.tup M μ.length)).subset fun ks hks => ?_
  obtain ⟨⟨a1, a2, a3⟩, a4⟩ := hks
  refine mem_coe.2 (ClauseBound.Boson.Text.mem_tup.2 ⟨a1, fun k hk => ⟨a2 k hk, ?_⟩⟩)
  by_contra hcon
  exact a4 (term_eq_zero_of_Bd hE μ h1 h2 ks a3 ⟨k, hk, by omega⟩)

/-! ### a[r] is linear in f -/

theorem opWin_add (μ : List ℕ+) (M : ℕ) (r : ℤ) (f g : V) : opWin μ M r (f + g) = opWin μ M r f + opWin μ M r g := by
  unfold opWin
  rw [← sum_add_distrib]
  exact sum_congr rfl fun ks _ => term_add μ ks f g

theorem opWin_smul (μ : List ℕ+) (M : ℕ) (r : ℤ) (q : ℚ) (f : V) : opWin μ M r (q • f) = q • opWin μ M r f := by
  unfold opWin
  rw [smul_sum]
  exact sum_congr rfl fun ks _ => term_smul μ ks q f

theorem opMon_add (μ : List ℕ+) (r : ℤ) (f g : V) : opMon μ r (f + g) = opMon μ r f + opMon μ r g := by
  obtain ⟨E, hE⟩ := exists_Bd f
  obtain ⟨E', hE'⟩ := exists_Bd g
  have hf : Bd f ((E + E' : ℕ) : ℤ) := hE.mono (by push_cast; omega)
  have hg : Bd g ((E + E' : ℕ) : ℤ) := hE'.mono (by push_cast; omega)
  have h1 : ((E + E' : ℕ) : ℤ) ≤ ((E + E' + r.natAbs : ℕ) : ℤ) := by omega
  have h2 : ((E + E' : ℕ) : ℤ) + r ≤ ((E + E' + r.natAbs : ℕ) : ℤ) := by omega
  rw [opMon_eq_opWin (hf.add hg) μ h1 h2, opMon_eq_opWin hf μ h1 h2, opMon_eq_opWin hg μ h1 h2, opWin_add]

theorem opMon_smul (μ : List ℕ+) (r : ℤ) (q : ℚ) (f : V) : opMon μ r (q • f) = q • opMon μ r f := by
  obtain ⟨E, M, hE, h1, h2⟩ := exists_window f r
  rw [opMon_eq_opWin (hE.smul q) μ h1 h2, opMon_eq_opWin hE μ h1 h2, opWin_smul]

/-! ### Sorting the terms by the integer chosen for the first part -/

theorem sum_win' {A : Type} [AddCommMonoid A] (M : ℕ) (G : ℤ → A) :
    ∑ k ∈ ClauseBound.Boson.win M, G k = ∑ l ∈ Icc 1 M, G (-(l : ℤ)) + ∑ k ∈ Icc 1 M, G (k : ℤ) := by
  unfold ClauseBound.Boson.win
  rw [sum_union, sum_image, sum_image]
  · intro x _ y _ h; simpa using h
  · intro x _ y _ h; simpa using h
  · rw [disjoint_left]
    intro x hx hy
    obtain ⟨l, hl, rfl⟩ := mem_image.1 hx
    obtain ⟨k, hk, h⟩ := mem_image.1 hy
    have := (mem_Icc.1 hl).1
    have := (mem_Icc.1 hk).1
    omega

theorem sum_tup_succ' {A : Type} [AddCommMonoid A] (M q : ℕ) (G : List ℤ → A) :
    ∑ ks ∈ ClauseBound.Boson.tup M (q + 1), G ks = ∑ k ∈ ClauseBound.Boson.win M, ∑ ks ∈ ClauseBound.Boson.tup M q, G (k :: ks) := by
  rw [ClauseBound.Boson.tup, sum_image, sum_product]
  rintro ⟨k, ks⟩ _ ⟨k', ks'⟩ _ h
  simp only [List.cons.injEq] at h
  exact Prod.ext h.1 h.2

theorem wtQ_cons (n : ℕ+) (μ : List ℕ+) (k : ℤ) (ks : List ℤ) : wtQ (n :: μ) (k :: ks) = binom (-k - 1) ((n : ℤ) - 1) * wtQ μ ks := by
  simp [wtQ]

/-- A negative integer for the first part: one more multiplication, applied last. -/
theorem term_cons_neg (n : ℕ+) (μ : List ℕ+) {k : ℤ} (hk : k < 0) (ks : List ℤ) (f : V) :
    term (n :: μ) (k :: ks) f = (binom (-k - 1) ((n : ℤ) - 1) : ℚ) • nabla k (term μ ks f) := by
  rw [term_eq, term_eq, wtQ_cons, nordQ_cons_neg hk, nabla_smul, nabla_neg hk, smul_smul]
  push_cast
  rfl

/-- A positive integer for the first part: one more differentiation, applied first. -/
theorem term_cons_pos (n : ℕ+) (μ : List ℕ+) {k : ℤ} (hk : 0 < k) (ks : List ℤ) (f : V) :
    term (n :: μ) (k :: ks) f = (binom (-k - 1) ((n : ℤ) - 1) : ℚ) • term μ ks (nabla k f) := by
  rw [term_eq, term_eq, wtQ_cons, nordQ_cons_pos hk, smul_smul]
  push_cast
  rfl

/-- The recursion (O2) for the finite sums. -/
theorem opWin_cons (n : ℕ+) (μ : List ℕ+) (M : ℕ) (r : ℤ) (f : V) : opWin (n :: μ) M r f =
    ∑ l ∈ Icc 1 M, (binom ((l : ℤ) - 1) ((n : ℤ) - 1) : ℚ) • nabla (-(l : ℤ)) (opWin μ M (r - l) f) +
      ∑ k ∈ Icc 1 M, (binom (-(k : ℤ) - 1) ((n : ℤ) - 1) : ℚ) • opWin μ M (r + k) (nabla k f) := by
  unfold opWin
  rw [sum_filter, List.length_cons, sum_tup_succ', sum_win']
  congr 1
  · refine sum_congr rfl fun l hl => ?_
    have hl1 := (mem_Icc.1 hl).1
    rw [nabla_sum, smul_sum, sum_filter]
    refine sum_congr rfl fun ks _ => ?_
    have hc : (-(l : ℤ) :: ks).sum = -r ↔ ks.sum = -(r - l) := by
      rw [List.sum_cons]; constructor <;> intro h <;> omega
    rw [if_congr hc rfl rfl, term_cons_neg n μ (by omega), neg_neg]
  · refine sum_congr rfl fun k hk => ?_
    have hk1 := (mem_Icc.1 hk).1
    rw [smul_sum, sum_filter]
    refine sum_congr rfl fun ks _ => ?_
    have hc : ((k : ℤ) :: ks).sum = -r ↔ ks.sum = -(r + k) := by
      rw [List.sum_cons]; constructor <;> intro h <;> omega
    rw [if_congr hc rfl rfl, term_cons_pos n μ (by omega)]

/-! ### The order in which the parts are listed does not matter -/

/-- The multiplications commute, and so do the differentiations. -/
theorem nordQ_perm {ks ks' : List ℤ} (h : ks.Perm ks') (f : V) : nordQ ks f = nordQ ks' f := by
  unfold nordQ
  rw [(h.filter (0 < ·)).foldr_eq' (f := nabla) (fun x hx y hy z => nabla_comm_pos (by simpa using (List.mem_filter.1 hy).2) (by simpa using (List.mem_filter.1 hx).2) z) f,
    (h.filter (· < 0)).foldr_eq' (f := nabla) (fun x hx y hy z => by
      rw [nabla_neg (by simpa using (List.mem_filter.1 hy).2), nabla_neg (by simpa using (List.mem_filter.1 hx).2),
        nabla_neg (by simpa using (List.mem_filter.1 hx).2), nabla_neg (by simpa using (List.mem_filter.1 hy).2), mul_left_comm]) _]

theorem term_swap (x y : ℕ+) (μ : List ℕ+) (k k' : ℤ) (ks : List ℤ) (f : V) : term (y :: x :: μ) (k :: k' :: ks) f = term (x :: y :: μ) (k' :: k :: ks) f := by
  rw [term_eq, term_eq, wtQ_cons, wtQ_cons, wtQ_cons, wtQ_cons, mul_left_comm, nordQ_perm (List.Perm.swap k' k ks)]

theorem opWin_perm {μ μ' : List ℕ+} (h : μ.Perm μ') : ∀ (M : ℕ) (r : ℤ) (f : V), opWin μ M r f = opWin μ' M r f := by
  induction h with
  | nil => intro M r f; rfl
  | cons x _ ih =>
    intro M r f
    rw [opWin_cons, opWin_cons]
    simp only [ih]
  | swap x y μ =>
    intro M r f
    unfold opWin
    rw [sum_filter, sum_filter, List.length_cons, List.length_cons, List.length_cons, List.length_cons, sum_tup_succ', sum_tup_succ']
    simp only [sum_tup_succ']
    rw [sum_comm]
    refine sum_congr rfl fun k _ => sum_congr rfl fun k' _ => sum_congr rfl fun ks _ => ?_
    have hc : (k' :: k :: ks).sum = -r ↔ (k :: k' :: ks).sum = -r := by
      simp only [List.sum_cons]; constructor <;> intro h <;> omega
    rw [if_congr hc rfl rfl, term_swap]
  | trans _ _ ih1 ih2 => intro M r f; rw [ih1, ih2]

theorem opMon_perm {μ μ' : List ℕ+} (h : μ.Perm μ') (r : ℤ) (f : V) : opMon μ r f = opMon μ' r f := by
  obtain ⟨E, M, hE, h1, h2⟩ := exists_window f r
  rw [opMon_eq_opWin hE μ h1 h2, opMon_eq_opWin hE μ' h1 h2, opWin_perm h]

/-! ### a[r] for all a -/

/-- The sum that defines a[r] may run over any finite set that contains the monomials of a. -/
theorem op_eq_sum (a : V) (r : ℤ) (f : V) {S : Finset (ℕ+ →₀ ℕ)} (hS : a.support ⊆ S) :
    op a r f = ∑ m ∈ S, coeff m a • opMon (Finsupp.toMultiset m).toList r f := by
  unfold op
  refine sum_subset hS fun m _ hm => ?_
  rw [notMem_support_iff.1 hm, zero_smul]

theorem op_tpow (μ : List ℕ+) (r : ℤ) (f : V) : op (tpow (μ : Multiset ℕ+)) r f = opMon μ r f := by
  unfold op tpow
  rw [support_monomial, if_neg one_ne_zero, sum_singleton, coeff_monomial, if_pos rfl, one_smul, Multiset.toFinsupp_toMultiset]
  exact opMon_perm (Multiset.coe_eq_coe.1 (Multiset.coe_toList _)) r f

theorem op_add_right (a : V) (r : ℤ) (f g : V) : op a r (f + g) = op a r f + op a r g := by
  unfold op
  rw [← sum_add_distrib]
  exact sum_congr rfl fun m _ => by rw [opMon_add, smul_add]

theorem op_smul_right (a : V) (r : ℤ) (q : ℚ) (f : V) : op a r (q • f) = q • op a r f := by
  unfold op
  rw [smul_sum]
  exact sum_congr rfl fun m _ => by rw [opMon_smul, smul_comm]

theorem op_add_left (a a' : V) (r : ℤ) (f : V) : op (a + a') r f = op a r f + op a' r f := by
  rw [op_eq_sum (a + a') r f (S := a.support ∪ a'.support) support_add, op_eq_sum a r f (S := a.support ∪ a'.support) subset_union_left,
    op_eq_sum a' r f (S := a.support ∪ a'.support) subset_union_right, ← sum_add_distrib]
  exact sum_congr rfl fun m _ => by rw [coeff_add, add_smul]

theorem op_smul_left (a : V) (r : ℤ) (q : ℚ) (f : V) : op (q • a) r f = q • op a r f := by
  rw [op_eq_sum (q • a) r f (S := a.support) support_smul, op_eq_sum a r f (S := a.support) (Subset.refl _), smul_sum]
  exact sum_congr rfl fun m _ => by rw [coeff_smul, smul_eq_mul, mul_smul]

end GeneralPieces.Ring

namespace GeneralPieces

open AppHalfPieces GeneralPieces.Ring

/-- What the appendix says with display (47). -/
theorem opFacts : OpFacts where
  finite := finite_terms
  perm := fun _ _ r f h => opMon_perm h r f
  mono := op_tpow
  add_right := op_add_right
  smul_right := op_smul_right
  add_left := op_add_left
  smul_left := op_smul_left

end GeneralPieces
