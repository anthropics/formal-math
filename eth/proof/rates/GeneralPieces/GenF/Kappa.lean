/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import GeneralPieces.GenF.Defs
public import GeneralPieces.GenF.Exp

/-! # Lemma 9 (Appendix B), on the operators Q_s: the coefficients of κ and κ', and those of e^κ and e^{κ'}

Two sentences of the proof. From the paragraph "Generating functions": κ = Σ_{j,n}
x_j·x'_n·Γ_{j,n}·ε₊^{j+n}, "because the sum over k is the left side of (49)", and "in the same way"
κ' = Σ_{j,n} x_j·x'_n·Γ_{j,n}·ε₋^{j+n}; here both are stated coefficient by coefficient
(`coeff_kap_false`, `coeff_kap_true`). From the paragraph "One Laurent polynomial":
"the coefficient of x^{μ'}·x'^{ν'} in e^κ is Γ_{μ',ν'}·ε₊^{|μ'|+|ν'|} for a number Γ_{μ',ν'}, and in
e^{κ'} it is Γ_{μ',ν'}·ε₋^{|μ'|+|ν'|}" (`coeff_expW_kap_false`, `coeff_expW_kap_true`).
A monomial x^{μ'}·x'^{ν'} is its exponent α here; |μ'| + |ν'| is `wtX α`, and the number Γ_{μ',ν'}
is `gam α`, the coefficient of the monomial in the exponential of the power series
Σ_{j,n} Γ_{j,n}·x_j·x'_n over ℚ. κ' is κ in the second reading, where the inner variable is ω₂ and
the inner family is B. -/

public section

namespace GeneralPieces.GenF

open GeneralPieces.Series ClauseBound.Boson MvPowerSeries Finset

/-! ### The weight of a monomial in the x_n, x'_n -/

/-- |μ'| + |ν'| for the monomial x^{μ'}·x'^{ν'}: the variables x_n and x'_n have weight n. -/
@[expose] noncomputable def wtX : (X →₀ ℕ) →+ ℕ := Finsupp.weight (Sum.elim id id : X → ℕ)

theorem wtX_single (i : X) (m : ℕ) : wtX (Finsupp.single i m) = m * Sum.elim id id i := by
  rw [wtX, Finsupp.weight_single, smul_eq_mul]

theorem wtX_xi (rd : Bool) (n : ℕ) : wtX (Finsupp.single (xi rd n) 1) = n := by
  rw [wtX_single, one_mul]
  cases rd <;> rfl

theorem wtX_xo (rd : Bool) (n : ℕ) : wtX (Finsupp.single (xo rd n) 1) = n := by
  rw [wtX_single, one_mul]
  cases rd <;> rfl

/-- The weight of the monomial x^μ (or x'^μ) made from the list of the parts of μ is |μ|, if the
variable with index n has weight n. -/
theorem wtX_list_sum (ι : ℕ → X) (hι : ∀ n, wtX (Finsupp.single (ι n) 1) = n) (a : List ℕ) : wtX (a.map fun n => Finsupp.single (ι n) 1).sum = a.sum := by
  induction a with
  | nil => simp
  | cons n a ih => rw [List.map_cons, List.sum_cons, map_add, hι, ih, List.sum_cons]

theorem wtX_list_xi (rd : Bool) (a : List ℕ) : wtX (a.map fun n => Finsupp.single (xi rd n) 1).sum = a.sum := wtX_list_sum _ (wtX_xi rd) a

theorem wtX_list_xo (rd : Bool) (a : List ℕ) : wtX (a.map fun n => Finsupp.single (xo rd n) 1).sum = a.sum := wtX_list_sum _ (wtX_xo rd) a

theorem wtX_list_inl (a : List ℕ) : wtX (a.map fun n => Finsupp.single (Sum.inl n : X) 1).sum = a.sum := wtX_list_xi false a

theorem wtX_list_inr (a : List ℕ) : wtX (a.map fun n => Finsupp.single (Sum.inr n : X) 1).sum = a.sum := wtX_list_xo false a

/-- A monomial of degree 2 in which two different variables occur is their product. -/
theorem eq_add_single {α : X →₀ ℕ} (hα : α.degree = 2) {i i' : X} (hi : i ∈ α.support) (hi' : i' ∈ α.support) (hne : i ≠ i') :
    α = Finsupp.single i 1 + Finsupp.single i' 1 := by
  classical
  have h1 : 1 ≤ α i := Nat.one_le_iff_ne_zero.2 (Finsupp.mem_support_iff.1 hi)
  have h2 : 1 ≤ α i' := Nat.one_le_iff_ne_zero.2 (Finsupp.mem_support_iff.1 hi')
  have hle : Finsupp.single i 1 + Finsupp.single i' 1 ≤ α := by
    intro x
    rw [Finsupp.add_apply, Finsupp.single_apply, Finsupp.single_apply]
    split_ifs with a b b
    · exact absurd (a.trans b.symm) hne
    · subst a
      simpa using h1
    · subst b
      simpa using h2
    · simp
  obtain ⟨γ, hγ⟩ := exists_add_of_le hle
  have hd : γ.degree = 0 := by
    have := congrArg Finsupp.degree hγ
    rw [map_add, map_add, Finsupp.degree_single, Finsupp.degree_single, hα] at this
    omega
  rw [Finsupp.degree_eq_zero_iff] at hd
  rw [hγ, hd, add_zero]

/-! ### The numbers Γ -/

/-- Γ_{j,n} at the pair of variables (x_j, x'_n) with j, n ≥ 1, and 0 at all other pairs. -/
@[expose] def GamX (i i' : X) : ℚ := sel false (fun p => sel false 0 (fun q => (Gam p q : ℚ)) i') 0 i

/-- Σ_{j,n} Γ_{j,n}·x_j·x'_n, a power series over ℚ. -/
@[expose] noncomputable def kapQ : MvPowerSeries X ℚ := bil GamX

/-- The number Γ_{μ',ν'}: the coefficient of x^{μ'}·x'^{ν'} in the exponential of Σ_{j,n}
Γ_{j,n}·x_j·x'_n. -/
@[expose] noncomputable def gam (α : X →₀ ℕ) : ℚ := coeff α (expW kapQ)

/-! ### The sum over k -/

/-- The sum over k in the first reading: Γ_{p,q}·ε₊^{p+q}. -/
theorem kapS_eq_P {p q : ℕ} (hp : 1 ≤ p) (hq : 1 ≤ q) : kapS p q = (Gam p q : ℚ) • epsP ^ (p + q) := kappa_sum hp hq

/-- The sum over k in the second reading, where p is the index of x'_p and q that of x_q:
Γ_{q,p}·ε₋^{q+p}. -/
theorem kapS_eq_M {p q : ℕ} (hp : 1 ≤ p) (hq : 1 ≤ q) : kapS p q = (Gam q p : ℚ) • epsM ^ (q + p) := by
  rw [← kappa'_sum hq hp, kapS, sumP, sumM]
  exact ser_congr _ _ fun k => by ring

theorem z0_zero' {R : Type} [Zero R] (n : ℕ) : z0 (0 : ℕ → R) n = 0 := by
  unfold z0
  split_ifs <;> rfl

theorem z0_at_zero {R : Type} [Zero R] (f : ℕ → R) : z0 f 0 = 0 := if_pos rfl

theorem z0_of_pos {R : Type} [Zero R] (f : ℕ → R) {n : ℕ} (hn : 1 ≤ n) : z0 f n = f n := if_neg (by omega)

/-- One entry of the bilinear form κ, first reading. -/
theorem entry_false {α : X →₀ ℕ} (hα : α.degree = 2) {i i' : X} (hi : i ∈ α.support) (hi' : i' ∈ α.support) :
    sel false (fun p => sel false 0 (fun q => kapS p q) i') 0 i = algebraMap ℚ S (GamX i i') * epsP ^ wtX α := by
  rcases i with p | p
  · rcases i' with q | q
    · change z0 (fun p => z0 (0 : ℕ → S) q) p = algebraMap ℚ S (z0 (fun p => z0 (0 : ℕ → ℚ) q) p) * _
      simp only [z0_zero']
      rw [show (fun _ : ℕ => (0 : S)) = 0 from rfl, show (fun _ : ℕ => (0 : ℚ)) = 0 from rfl, z0_zero', z0_zero', map_zero, zero_mul]
    · change z0 (fun p => z0 (fun q => kapS p q) q) p = algebraMap ℚ S (z0 (fun p => z0 (fun q => (Gam p q : ℚ)) q) p) * _
      rcases Nat.eq_zero_or_pos p with rfl | hp
      · rw [z0_at_zero, z0_at_zero, map_zero, zero_mul]
      rcases Nat.eq_zero_or_pos q with rfl | hq
      · rw [z0_of_pos _ hp, z0_of_pos _ hp, z0_at_zero, z0_at_zero, map_zero, zero_mul]
      rw [z0_of_pos _ hp, z0_of_pos _ hp, z0_of_pos _ hq, z0_of_pos _ hq, kapS_eq_P hp hq, eq_add_single hα hi hi' (by simp), map_add, wtX_single,
        wtX_single, Algebra.smul_def]
      simp
  · change z0 (0 : ℕ → S) p = algebraMap ℚ S (z0 (0 : ℕ → ℚ) p) * _
    rw [z0_zero', z0_zero', map_zero, zero_mul]

/-- One entry of the bilinear form κ, second reading. -/
theorem entry_true {α : X →₀ ℕ} (hα : α.degree = 2) {i i' : X} (hi : i ∈ α.support) (hi' : i' ∈ α.support) :
    sel true (fun p => sel true 0 (fun q => kapS p q) i') 0 i = algebraMap ℚ S (GamX i' i) * epsM ^ wtX α := by
  rcases i with p | p
  · change z0 (0 : ℕ → S) p = _
    rw [z0_zero']
    rcases i' with q | q
    · change 0 = algebraMap ℚ S (z0 (fun q => z0 (0 : ℕ → ℚ) p) q) * _
      simp only [z0_zero']
      rw [show (fun _ : ℕ => (0 : ℚ)) = 0 from rfl, z0_zero', map_zero, zero_mul]
    · change 0 = algebraMap ℚ S (z0 (0 : ℕ → ℚ) q) * _
      rw [z0_zero', map_zero, zero_mul]
  · rcases i' with q | q
    · change z0 (fun p => z0 (fun q => kapS p q) q) p = algebraMap ℚ S (z0 (fun q => z0 (fun p => (Gam q p : ℚ)) p) q) * _
      rcases Nat.eq_zero_or_pos p with rfl | hp
      · rcases Nat.eq_zero_or_pos q with rfl | hq
        · rw [z0_at_zero, z0_at_zero, map_zero, zero_mul]
        · rw [z0_at_zero, z0_of_pos _ hq, z0_at_zero, map_zero, zero_mul]
      rcases Nat.eq_zero_or_pos q with rfl | hq
      · rw [z0_of_pos _ hp, z0_at_zero, z0_at_zero, map_zero, zero_mul]
      rw [z0_of_pos _ hp, z0_of_pos _ hq, z0_of_pos _ hq, z0_of_pos _ hp, kapS_eq_M hp hq, eq_add_single hα hi' hi (by simp), map_add, wtX_single,
        wtX_single, Algebra.smul_def]
      simp
    · change z0 (fun p => z0 (0 : ℕ → S) q) p = algebraMap ℚ S (z0 (0 : ℕ → ℚ) q) * _
      simp only [z0_zero']
      rw [show (fun _ : ℕ => (0 : S)) = 0 from rfl, z0_zero', map_zero, zero_mul]

/-! ### κ, κ' and their exponentials -/

/-- The coefficients of κ: those of Σ_{j,n} Γ_{j,n}·x_j·x'_n, times ε₊^{j+n}. -/
theorem coeff_kap_false (α : X →₀ ℕ) : coeff α (kap false) = algebraMap ℚ S (coeff α kapQ) * epsP ^ wtX α := by
  change (if α.degree = 2 then ∑ i ∈ α.support, ∑ i' ∈ α.support, sel false (fun p => sel false 0 (fun q => kapS p q) i') 0 i else 0) =
    algebraMap ℚ S (if α.degree = 2 then ∑ i ∈ α.support, ∑ i' ∈ α.support, GamX i i' else 0) * _
  split_ifs with h
  · rw [map_sum, sum_mul]
    refine sum_congr rfl fun i hi => ?_
    rw [map_sum, sum_mul]
    exact sum_congr rfl fun i' hi' => entry_false h hi hi'
  · rw [map_zero, zero_mul]

/-- The coefficients of κ': those of Σ_{j,n} Γ_{j,n}·x_j·x'_n, times ε₋^{j+n}. -/
theorem coeff_kap_true (α : X →₀ ℕ) : coeff α (kap true) = algebraMap ℚ S (coeff α kapQ) * epsM ^ wtX α := by
  change (if α.degree = 2 then ∑ i ∈ α.support, ∑ i' ∈ α.support, sel true (fun p => sel true 0 (fun q => kapS p q) i') 0 i else 0) =
    algebraMap ℚ S (if α.degree = 2 then ∑ i ∈ α.support, ∑ i' ∈ α.support, GamX i i' else 0) * _
  split_ifs with h
  · rw [sum_comm (f := fun i i' => GamX i i'), map_sum, sum_mul]
    refine sum_congr rfl fun i hi => ?_
    rw [map_sum, sum_mul]
    exact sum_congr rfl fun i' hi' => entry_true h hi hi'
  · rw [map_zero, zero_mul]

/-- The coefficient of x^{μ'}·x'^{ν'} in e^κ is Γ_{μ',ν'}·ε₊^{|μ'|+|ν'|}. -/
theorem coeff_expW_kap_false (α : X →₀ ℕ) : coeff α (expW (kap false)) = gam α • epsP ^ wtX α := by
  rw [coeff_expW_of_weight wtX epsP kapQ coeff_kap_false, Algebra.smul_def, gam]

/-- The coefficient of x^{μ'}·x'^{ν'} in e^{κ'} is Γ_{μ',ν'}·ε₋^{|μ'|+|ν'|}, with the same number. -/
theorem coeff_expW_kap_true (α : X →₀ ℕ) : coeff α (expW (kap true)) = gam α • epsM ^ wtX α := by
  rw [coeff_expW_of_weight wtX epsM kapQ coeff_kap_true, Algebra.smul_def, gam]

end GeneralPieces.GenF
