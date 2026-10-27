/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import GeneralPieces.Ring.Op
public import GeneralPieces.Ring.Lex
public import ClauseBound.Boson.Size

/-! # The numbers in the proof of the theorem on the pieces with ρ = 1/√2: sizes

Part of the paragraph "Sizes and operations" of that proof in Appendix B, as far as it states
numbers, with the numbers of the appendix:
the number Δ of the partitions of 0, …, 4h is at most (4h+1)·p(4h) (`Delta_le`); each entry of the
table of t_n·a' is a sum of at most 8h entries of the table of a', multiplied by integers of
absolute value at most 4h·2^{5h} (`coef_opMon_cons`, `card_terms_le`, `abs_mult_l_le`,
`abs_mult_k_le`); a monomial of weight at most h has at most h factors (`length_le`); all entries of
all
tables are at most (32h²·2^{5h})^h ≤ 2^{12h²} in absolute value (`abs_entry_le`, `pow_le`,
`abs_entry_le'`); each factor of displays (54) and (55) is a combination of entries with the
coefficients
of a^⟨i⟩ or b (`coef_op`), whose absolute values add up to at most 2^{3h} (`l1_angle_aFam_le`) and
h! (`l1_bFam_le`).
The recursion for the entries is taken from the integer matrices `ClauseBound.Boson.op`, which are
defined by (O2); `GeneralPieces.stBridge` says they are the matrices of the operators a[r]. The
running times are not part of this file. -/

public section

namespace GeneralPieces.Sizes

open AppHalfPieces MvPolynomial Finset GeneralPieces.Ring

/-! ### The list of partitions -/

/-- Δ, the number of the partitions of 0, 1, …, 4h. -/
@[expose] def Delta (h : ℕ) : ℕ := ∑ E ∈ range (4 * h + 1), Partitions.p E

/-- p is nondecreasing. -/
theorem p_mono {E E' : ℕ} (hE : E ≤ E') : Partitions.p E ≤ Partitions.p E' := monotone_nat_of_le_succ ptnFacts.mono hE

/-- Δ ≤ (4h+1)·p(4h). -/
theorem Delta_le (h : ℕ) : Delta h ≤ (4 * h + 1) * Partitions.p (4 * h) := by
  unfold Delta
  refine (sum_le_card_nsmul _ _ (Partitions.p (4 * h)) fun E hE => p_mono (by have := mem_range.1 hE; omega)).trans ?_
  rw [card_range, smul_eq_mul]

/-! ### One step of the computation of the tables -/

/-- The coefficient `ClauseBound.Boson.bet n r` of the matrices `ClauseBound.Boson.op` is C(r−1,
n−1) for r ≠ 0. -/
theorem bet_eq (n : ℕ+) {r : ℤ} (hr : r ≠ 0) : ClauseBound.Boson.bet n r = binom (r - 1) ((n : ℤ) - 1) := by
  have e2 : ((n : ℕ) : ℤ) - 1 = (((n : ℕ) - 1 : ℕ) : ℤ) := by have := n.pos; omega
  rw [ClauseBound.Boson.bet, if_neg hr, e2, binom_natCast]

theorem toFinset_toN (π : Ptn) : (toN π).toFinset = π.toFinset.image fun k : ℕ+ => (k : ℕ) := Multiset.toFinset_map _ _

/-- By (O2), since ∇_k t^σ = k·m_k(σ)·t^σ/t_k and the coefficient of t^{σ'} in t_l·f is that of
t^{σ'}/t_l in f: an entry of the table of t_n·a' as a combination of entries of the table of a'.
The sums run over the different parts l of σ' and k of σ. Proved from the recursion that defines the
matrices `ClauseBound.Boson.op`, which is (O2), through `GeneralPieces.stBridge`. -/
theorem coef_opMon_cons (n : ℕ+) (a' : List ℕ+) (r : ℤ) (σ' σ : Ptn) :
    coef σ' (opMon (n :: a') r (tpow σ)) =
      ∑ l ∈ σ'.toFinset, ((binom (((l : ℕ) : ℤ) - 1) ((n : ℤ) - 1) : ℤ) : ℚ) * coef (σ'.erase l) (opMon a' (r - (l : ℕ)) (tpow σ)) +
        ∑ k ∈ σ.toFinset, ((binom (-((k : ℕ) : ℤ) - 1) ((n : ℤ) - 1) * ((k : ℕ) * σ.count k) : ℤ) : ℚ) *
          coef σ' (opMon a' (r + (k : ℕ)) (tpow (σ.erase k))) := by
  have e : toL (n :: a') = (n : ℕ) :: toL a' := rfl
  rw [stBridge, e, ClauseBound.Boson.op, ClauseBound.Boson.nop, toFinset_toN, toFinset_toN, sum_image PNat.coe_injective.injOn,
    sum_image PNat.coe_injective.injOn]
  push_cast
  congr 1
  · refine sum_congr rfl fun l hl => ?_
    have hl0 : ((l : ℕ) : ℤ) ≠ 0 := by have := l.pos; omega
    rw [ClauseBound.Boson.cre, if_pos ((mem_toN _ _).2 (Multiset.mem_toFinset.1 hl)), ← toN_erase, stBridge, bet_eq n hl0]
  · refine sum_congr rfl fun k _ => ?_
    have hk0 : -((k : ℕ) : ℤ) ≠ 0 := by have := k.pos; omega
    rw [ClauseBound.Boson.ann, count_toN, ← toN_erase, stBridge, bet_eq n hk0]
    push_cast
    ring

/-- A partition has at most as many parts as its weight. -/
theorem card_le_wt (σ : Ptn) : Multiset.card σ ≤ wt σ := by
  unfold wt
  induction σ using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.card_cons, Multiset.map_cons, Multiset.sum_cons]
    have := a.pos
    omega

/-- The sum has at most 8h terms. -/
theorem card_terms_le {h : ℕ} {σ' σ : Ptn} (h1 : wt σ' ≤ 4 * h) (h2 : wt σ ≤ 4 * h) : #σ'.toFinset + #σ.toFinset ≤ 8 * h := by
  have a1 := (Multiset.toFinset_card_le σ').trans (card_le_wt σ')
  have a2 := (Multiset.toFinset_card_le σ).trans (card_le_wt σ)
  omega

theorem le_wt {σ : Ptn} {l : ℕ+} (hl : l ∈ σ) : (l : ℕ) ≤ wt σ := by
  have := wt_erase hl
  omega

theorem wt_erase_le (σ : Ptn) (l : ℕ+) : wt (σ.erase l) ≤ wt σ := by
  by_cases hl : l ∈ σ
  · have := wt_erase hl
    omega
  · rw [Multiset.erase_of_notMem hl]

/-- k·m_k(σ) ≤ |σ|. -/
theorem mul_count_le_wt (σ : Ptn) (k : ℕ+) : (k : ℕ) * σ.count k ≤ wt σ := by
  induction σ using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    have e : wt (a ::ₘ s) = a + wt s := by unfold wt; rw [Multiset.map_cons, Multiset.sum_cons]
    rw [e, Multiset.count_cons]
    split_ifs with hka
    · subst hka
      rw [Nat.mul_add, Nat.mul_one]
      omega
    · rw [Nat.add_zero]
      omega

theorem abs_binom_le (k : ℤ) (n : ℕ+) : |binom k ((n : ℤ) - 1)| ≤ 2 ^ (k.natAbs + ((n : ℕ) - 1)) := by
  have e2 : ((n : ℕ) : ℤ) - 1 = (((n : ℕ) - 1 : ℕ) : ℤ) := by have := n.pos; omega
  rw [e2, binom_natCast]
  exact ClauseBound.Rec.abs_choose_le _ _

/-- The multipliers of the first sum are at most 4h·2^{5h} in absolute value. -/
theorem abs_mult_l_le {h : ℕ} (hh : 1 ≤ h) {n l : ℕ+} (hn : (n : ℕ) ≤ h) {σ' : Ptn} (h1 : wt σ' ≤ 4 * h) (hl : l ∈ σ') :
    |binom (((l : ℕ) : ℤ) - 1) ((n : ℤ) - 1)| ≤ 4 * h * 2 ^ (5 * h) := by
  have a1 := le_wt hl
  have a2 : (2 : ℤ) ^ ((((l : ℕ) : ℤ) - 1).natAbs + ((n : ℕ) - 1)) ≤ 2 ^ (5 * h) := pow_le_pow_right₀ (by norm_num) (by omega)
  have a3 : (1 : ℤ) ≤ 4 * h := by omega
  calc _ ≤ (2 : ℤ) ^ (5 * h) := (abs_binom_le _ n).trans a2
    _ = 1 * 2 ^ (5 * h) := (one_mul _).symm
    _ ≤ 4 * h * 2 ^ (5 * h) := mul_le_mul_of_nonneg_right a3 (by positivity)

/-- The multipliers of the second sum are at most 4h·2^{5h} in absolute value. -/
theorem abs_mult_k_le {h : ℕ} {n k : ℕ+} (hn : (n : ℕ) ≤ h) {σ : Ptn} (h2 : wt σ ≤ 4 * h) (hk : k ∈ σ) :
    |binom (-((k : ℕ) : ℤ) - 1) ((n : ℤ) - 1) * ((k : ℕ) * σ.count k)| ≤ 4 * h * 2 ^ (5 * h) := by
  have a1 := le_wt hk
  have a0 := n.pos
  have a2 : (2 : ℤ) ^ ((-((k : ℕ) : ℤ) - 1).natAbs + ((n : ℕ) - 1)) ≤ 2 ^ (5 * h) := pow_le_pow_right₀ (by norm_num) (by omega)
  have a3 : (((k : ℕ) : ℤ) * σ.count k) ≤ 4 * h := by exact_mod_cast (mul_count_le_wt σ k).trans h2
  have a4 : (0 : ℤ) ≤ ((k : ℕ) : ℤ) * σ.count k := by positivity
  rw [abs_mul, abs_of_nonneg a4, mul_comm]
  exact mul_le_mul a3 ((abs_binom_le _ n).trans a2) (abs_nonneg _) (by positivity)

/-! ### All entries of all tables -/

/-- A monomial has at most as many factors as its weight; so a monomial of weight at most h has at
most h factors. -/
theorem length_le (a : List ℕ+) : a.length ≤ (toL a).sum := by
  have := card_le_wt (a : Multiset ℕ+)
  simpa [wt, toL] using this

/-- An entry of the table of a monomial with q factors, each t_n with n ≤ h, is at most
(32h²·2^{5h})^q in absolute value. -/
theorem abs_entry_le {h : ℕ} (hh : 1 ≤ h) (a : List ℕ+) (ha : ∀ n ∈ a, (n : ℕ) ≤ h) (r : ℤ) {σ' σ : Ptn} (h1 : wt σ' ≤ 4 * h) (h2 : wt σ ≤ 4 * h) :
    |coef σ' (opMon a r (tpow σ))| ≤ (32 * (h : ℚ) ^ 2 * 2 ^ (5 * h)) ^ a.length := by
  induction a generalizing r σ' σ with
  | nil =>
    rw [opMon_nil, List.length_nil, pow_zero]
    split_ifs
    · rw [coef_tpow]
      split_ifs <;> simp
    · simp [coef]
  | cons n a ih =>
    have ih' := fun (r : ℤ) (σ' σ : Ptn) (h1 : wt σ' ≤ 4 * h) (h2 : wt σ ≤ 4 * h) => ih (fun m hm => ha m (List.mem_cons_of_mem _ hm)) r h1 h2
    have hn := ha n List.mem_cons_self
    rw [coef_opMon_cons, List.length_cons, pow_succ]
    generalize (32 * (h : ℚ) ^ 2 * 2 ^ (5 * h)) ^ a.length = B at ih' ⊢
    have hB : 0 ≤ B := (abs_nonneg _).trans (ih' r σ' σ h1 h2)
    have hK : (0 : ℚ) ≤ 4 * h * 2 ^ (5 * h) := by positivity
    have b1 : |∑ l ∈ σ'.toFinset, ((binom (((l : ℕ) : ℤ) - 1) ((n : ℤ) - 1) : ℤ) : ℚ) * coef (σ'.erase l) (opMon a (r - (l : ℕ)) (tpow σ))|
        ≤ #σ'.toFinset • (4 * h * 2 ^ (5 * h) * B) := by
      refine (abs_sum_le_sum_abs _ _).trans (sum_le_card_nsmul _ _ _ fun l hl => ?_)
      rw [abs_mul]
      refine mul_le_mul ?_ (ih' _ _ _ ((wt_erase_le σ' l).trans h1) h2) (abs_nonneg _) hK
      exact_mod_cast abs_mult_l_le hh hn h1 (Multiset.mem_toFinset.1 hl)
    have b2 : |∑ k ∈ σ.toFinset, ((binom (-((k : ℕ) : ℤ) - 1) ((n : ℤ) - 1) * ((k : ℕ) * σ.count k) : ℤ) : ℚ) *
          coef σ' (opMon a (r + (k : ℕ)) (tpow (σ.erase k)))| ≤ #σ.toFinset • (4 * h * 2 ^ (5 * h) * B) := by
      refine (abs_sum_le_sum_abs _ _).trans (sum_le_card_nsmul _ _ _ fun k hk => ?_)
      rw [abs_mul]
      refine mul_le_mul ?_ (ih' _ _ _ h1 ((wt_erase_le σ k).trans h2)) (abs_nonneg _) hK
      exact_mod_cast abs_mult_k_le hn h2 (Multiset.mem_toFinset.1 hk)
    have b3 : ((#σ'.toFinset + #σ.toFinset : ℕ) : ℚ) ≤ 8 * h := by exact_mod_cast card_terms_le h1 h2
    calc _ ≤ #σ'.toFinset • (4 * h * 2 ^ (5 * h) * B) + #σ.toFinset • (4 * h * 2 ^ (5 * h) * B) := (abs_add_le _ _).trans (add_le_add b1 b2)
      _ = ((#σ'.toFinset + #σ.toFinset : ℕ) : ℚ) * (4 * h * 2 ^ (5 * h) * B) := by rw [nsmul_eq_mul, nsmul_eq_mul]; push_cast; ring
      _ ≤ 8 * h * (4 * h * 2 ^ (5 * h) * B) := mul_le_mul_of_nonneg_right b3 (mul_nonneg hK hB)
      _ = B * (32 * (h : ℚ) ^ 2 * 2 ^ (5 * h)) := by ring

/-- (32h²·2^{5h})^h ≤ 2^{12h²}, for h ≥ 1. -/
theorem pow_le {h : ℕ} (hh : 1 ≤ h) : (32 * h ^ 2 * 2 ^ (5 * h)) ^ h ≤ 2 ^ (12 * h ^ 2) := by
  have a1 : h ^ 2 ≤ 2 ^ (2 * h) := by
    rw [Nat.mul_comm, pow_mul]
    exact Nat.pow_le_pow_left Nat.lt_two_pow_self.le 2
  have a2 : 32 ≤ 2 ^ (5 * h) := by
    calc 32 = 2 ^ 5 := by norm_num
      _ ≤ 2 ^ (5 * h) := Nat.pow_le_pow_right (by norm_num) (by omega)
  calc (32 * h ^ 2 * 2 ^ (5 * h)) ^ h ≤ (2 ^ (5 * h) * 2 ^ (2 * h) * 2 ^ (5 * h)) ^ h :=
        Nat.pow_le_pow_left (Nat.mul_le_mul_right _ (Nat.mul_le_mul a2 a1)) h
    _ = 2 ^ (12 * h ^ 2) := by rw [← pow_add, ← pow_add, ← pow_mul]; congr 1; ring

/-- All entries of the tables of the monomials of weight at most h are at most 2^{12h²} in absolute
value. -/
theorem abs_entry_le' {h : ℕ} (hh : 1 ≤ h) (a : List ℕ+) (ha : (toL a).sum ≤ h) (r : ℤ) {σ' σ : Ptn} (h1 : wt σ' ≤ 4 * h) (h2 : wt σ ≤ 4 * h) :
    |coef σ' (opMon a r (tpow σ))| ≤ 2 ^ (12 * h ^ 2) := by
  have a1 : ∀ n ∈ a, (n : ℕ) ≤ h := fun n hn => (List.le_sum_of_mem (List.mem_map_of_mem hn : (n : ℕ) ∈ toL a)).trans ha
  have a2 : (1 : ℚ) ≤ 32 * (h : ℚ) ^ 2 * 2 ^ (5 * h) := by
    have : 1 ≤ 32 * h ^ 2 * 2 ^ (5 * h) := Nat.succ_le_of_lt (by positivity)
    exact_mod_cast this
  calc _ ≤ (32 * (h : ℚ) ^ 2 * 2 ^ (5 * h)) ^ a.length := abs_entry_le hh a a1 r h1 h2
    _ ≤ (32 * (h : ℚ) ^ 2 * 2 ^ (5 * h)) ^ h := pow_le_pow_right₀ a2 ((length_le a).trans ha)
    _ ≤ 2 ^ (12 * h ^ 2) := by exact_mod_cast pow_le hh

/-! ### The sum of the absolute values of the coefficients -/

/-- The sum of the absolute values of the coefficients of a polynomial. -/
@[expose] noncomputable def l1 (a : V) : ℚ := ∑ m ∈ a.support, |coeff m a|

theorem l1_eq_sum {a : V} {S : Finset (ℕ+ →₀ ℕ)} (hS : a.support ⊆ S) : l1 a = ∑ m ∈ S, |coeff m a| :=
  sum_subset hS fun m _ hm => by rw [notMem_support_iff.1 hm, abs_zero]

theorem l1_nonneg (a : V) : 0 ≤ l1 a := sum_nonneg fun _ _ => abs_nonneg _

theorem l1_zero : l1 0 = 0 := by simp [l1]

theorem l1_add_le (a b : V) : l1 (a + b) ≤ l1 a + l1 b := by
  classical
  rw [l1_eq_sum (support_add (p := a) (q := b)), l1_eq_sum (a := a) (subset_union_left (s₂ := b.support)),
    l1_eq_sum (a := b) (subset_union_right (s₁ := a.support)), ← sum_add_distrib]
  exact sum_le_sum fun m _ => by rw [coeff_add]; exact abs_add_le _ _

theorem l1_sum_le {ι : Type} (s : Finset ι) (F : ι → V) : l1 (∑ i ∈ s, F i) ≤ ∑ i ∈ s, l1 (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [l1_zero]
  | insert i s hi ih =>
    rw [sum_insert hi, sum_insert hi]
    exact (l1_add_le _ _).trans (by gcongr)

theorem l1_smul (q : ℚ) (a : V) : l1 (q • a) = |q| * l1 a := by
  rw [l1_eq_sum (support_smul (a := q) (f := a)), l1, mul_sum]
  exact sum_congr rfl fun m _ => by rw [coeff_smul, smul_eq_mul, abs_mul]

theorem l1_monomial_le (m : ℕ+ →₀ ℕ) (q : ℚ) : l1 (monomial m q) ≤ |q| := by
  classical
  rw [l1_eq_sum (support_monomial_subset (s := m) (a := q)), sum_singleton, coeff_monomial, if_pos rfl]

theorem l1_mul_le (a b : V) : l1 (a * b) ≤ l1 a * l1 b := by
  have e : a * b = ∑ m ∈ a.support, ∑ m' ∈ b.support, monomial (m + m') (coeff m a * coeff m' b) := by
    conv_lhs => rw [← support_sum_monomial_coeff a, ← support_sum_monomial_coeff b]
    rw [sum_mul_sum]
    simp_rw [monomial_mul]
  calc l1 (a * b) ≤ ∑ m ∈ a.support, ∑ m' ∈ b.support, |coeff m a| * |coeff m' b| := by
        rw [e]
        exact (l1_sum_le _ _).trans (sum_le_sum fun m _ => (l1_sum_le _ _).trans (sum_le_sum fun m' _ => (l1_monomial_le _ _).trans_eq (abs_mul _ _)))
    _ = l1 a * l1 b := by rw [l1, l1, sum_mul_sum]

/-- The coefficients of y_n add up to at most 2^n. -/
theorem l1_y_le (n : ℕ+) : l1 (y n) ≤ 2 ^ (n : ℕ) := by
  have a1 : ∑ j ∈ Icc 1 (n : ℕ), (n : ℕ).choose j ≤ 2 ^ (n : ℕ) := by
    rw [← Nat.sum_range_choose]
    exact sum_le_sum_of_subset fun j hj => mem_range.2 (by have := (mem_Icc.1 hj).2; omega)
  calc l1 (y n) ≤ ∑ j ∈ Icc 1 (n : ℕ), (((n : ℕ).choose j : ℕ) : ℚ) := by
        refine (l1_sum_le _ _).trans (sum_le_sum fun j _ => ?_)
        rw [l1_smul, Nat.abs_cast]
        have : l1 (X j.toPNat' : V) ≤ 1 := (l1_monomial_le _ _).trans_eq abs_one
        exact mul_le_of_le_one_right (Nat.cast_nonneg _) this
    _ ≤ 2 ^ (n : ℕ) := by exact_mod_cast a1

theorem wt_cons (n : ℕ+) (μ : Ptn) : wt (n ::ₘ μ) = n + wt μ := by
  unfold wt
  rw [Multiset.map_cons, Multiset.sum_cons]

/-- The absolute values of the coefficients of a^μ add up to at most ∏_i 2^{μ_i} = 2^{|μ|}. -/
theorem l1_aFam_le (μ : Ptn) : l1 (aFam μ) ≤ 2 ^ wt μ := by
  induction μ using Multiset.induction_on with
  | empty =>
    have : aFam 0 = monomial 0 1 := by simp [aFam]
    rw [this]
    exact (l1_monomial_le _ _).trans (by simp [wt])
  | cons n μ ih =>
    have e : aFam (n ::ₘ μ) = ((-1 : ℚ) ^ ((n : ℕ) - 1) • y n) * aFam μ := by
      unfold aFam
      rw [Multiset.map_cons, Multiset.prod_cons]
    rw [e, wt_cons, pow_add]
    refine (l1_mul_le _ _).trans (mul_le_mul ?_ ih (l1_nonneg _) (by positivity))
    rw [l1_smul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
    exact l1_y_le n

/-- The coefficients of a^⟨i⟩: C(h'+h, i) times those of a at the monomials of weight h' ≤ h, and 0
at the others. -/
theorem coeff_angle (h i : ℕ) (a : V) (m : ℕ+ →₀ ℕ) :
    coeff m (angle h i a) = if Finsupp.weight wgt m ≤ h then ((Finsupp.weight wgt m + h).choose i : ℚ) * coeff m a else 0 := by
  unfold angle part
  rw [coeff_sum]
  simp_rw [coeff_smul, coeff_weightedHomogeneousComponent, smul_eq_mul, mul_ite, mul_zero]
  rw [sum_ite_eq]
  simp only [mem_range, Nat.lt_succ_iff]
  rfl

/-- The absolute values of the coefficients of a^⟨i⟩ add up to at most 2^{2h} times the sum for a. -/
theorem l1_angle_le (h i : ℕ) (a : V) : l1 (angle h i a) ≤ 2 ^ (2 * h) * l1 a := by
  have hS : (angle h i a).support ⊆ a.support := fun m hm => by
    rw [mem_support_iff, coeff_angle] at hm
    rw [mem_support_iff]
    intro h0
    rw [h0, mul_zero, ite_self] at hm
    exact hm rfl
  rw [l1_eq_sum hS, l1, mul_sum]
  refine sum_le_sum fun m _ => ?_
  rw [coeff_angle]
  split_ifs with hm
  · rw [abs_mul, Nat.abs_cast]
    have : (Finsupp.weight wgt m + h).choose i ≤ 2 ^ (2 * h) :=
      (Nat.choose_le_two_pow _ _).trans (Nat.pow_le_pow_right (by norm_num) (by omega))
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast this) (abs_nonneg _)
  · rw [abs_zero]
    positivity

/-- The absolute values of the coefficients of a^⟨i⟩, for a = a^μ and a partition μ of h, add up to
at most 2^{2h}·∏_i 2^{μ_i} = 2^{3h}. -/
theorem l1_angle_aFam_le {h : ℕ} (i : ℕ) {μ : Ptn} (hμ : wt μ = h) : l1 (angle h i (aFam μ)) ≤ 2 ^ (3 * h) := by
  calc _ ≤ 2 ^ (2 * h) * l1 (aFam μ) := l1_angle_le h i _
    _ ≤ 2 ^ (2 * h) * 2 ^ h := mul_le_mul_of_nonneg_left (hμ ▸ l1_aFam_le μ) (by positivity)
    _ = 2 ^ (3 * h) := by rw [← pow_add]; congr 1; ring

/-- z_μ ≥ 1. -/
theorem zz_pos (μ : Ptn) : 0 < zz μ := prod_pos fun k _ => Nat.mul_pos (pow_pos k.pos _) (Nat.factorial_pos _)

/-- b^μ has one coefficient, h!/z_μ with h = |μ|; it is at most h!. -/
theorem l1_bFam_le (μ : Ptn) : l1 (bFam μ) ≤ (wt μ).factorial := by
  unfold bFam
  rw [l1_smul]
  have a1 : l1 (tpow μ) ≤ 1 := (l1_monomial_le _ _).trans_eq abs_one
  have a2 : (1 : ℚ) ≤ zz μ := by exact_mod_cast zz_pos μ
  have a3 : |((wt μ).factorial : ℚ) / zz μ| ≤ (wt μ).factorial := by
    rw [abs_of_nonneg (by positivity)]
    exact div_le_self (Nat.cast_nonneg _) a2
  calc _ ≤ ((wt μ).factorial : ℚ) * 1 := mul_le_mul a3 a1 (l1_nonneg _) (Nat.cast_nonneg _)
    _ = _ := mul_one _

/-! ### The factors of displays (54) and (55) -/

/-- Each coefficient of a[r]·t^σ is a combination of entries of the tables of the monomials of a,
with the coefficients of a. -/
theorem coef_op (a : V) (r : ℤ) (σ' σ : Ptn) :
    coef σ' (op a r (tpow σ)) = ∑ m ∈ a.support, coeff m a * coef σ' (opMon (Finsupp.toMultiset m).toList r (tpow σ)) := by
  unfold op
  rw [coef_sum]
  exact sum_congr rfl fun m _ => coef_smul _ _ _

theorem sum_toL_toList (m : ℕ+ →₀ ℕ) : (toL (Finsupp.toMultiset m).toList).sum = Finsupp.weight wgt m := by
  have h1 := weight_toFinsupp (Finsupp.toMultiset m)
  rw [Finsupp.toMultiset_toFinsupp] at h1
  rw [h1, wt, toL]
  conv_rhs => rw [← Multiset.coe_toList (Finsupp.toMultiset m)]
  rw [Multiset.map_coe, Multiset.sum_coe]

/-- If all monomials of a have weight at most h, a coefficient of a[r]·t^σ at listed partitions is
at most 2^{12h²} times the sum of the absolute values of the coefficients of a. -/
theorem abs_coef_op_le {h : ℕ} (hh : 1 ≤ h) {a : V} (ha : ∀ m ∈ a.support, Finsupp.weight wgt m ≤ h) (r : ℤ) {σ' σ : Ptn} (h1 : wt σ' ≤ 4 * h)
    (h2 : wt σ ≤ 4 * h) : |coef σ' (op a r (tpow σ))| ≤ l1 a * 2 ^ (12 * h ^ 2) := by
  rw [coef_op, l1, sum_mul]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun m hm => ?_)
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (abs_entry_le' hh _ (by rw [sum_toL_toList]; exact ha m hm) r h1 h2) (abs_nonneg _)

/-- The factors with a^⟨i⟩ in (54) and (55) are at most 2^{3h}·2^{12h²} in absolute value. -/
theorem abs_factor_a_le {h : ℕ} (hh : 1 ≤ h) (i : ℕ) {ξ : Ptn} (hξ : wt ξ = h) (r : ℤ) {σ' σ : Ptn} (h1 : wt σ' ≤ 4 * h) (h2 : wt σ ≤ 4 * h) :
    |coef σ' (op (angle h i (aFam ξ)) r (tpow σ))| ≤ 2 ^ (3 * h) * 2 ^ (12 * h ^ 2) := by
  refine (abs_coef_op_le hh (fun m hm => ?_) r h1 h2).trans (mul_le_mul_of_nonneg_right (l1_angle_aFam_le i hξ) (by positivity))
  rw [mem_support_iff, coeff_angle] at hm
  by_contra h0
  exact hm (if_neg h0)

/-- The factors with b in (54) and (55) are at most h!·2^{12h²} in absolute value. -/
theorem abs_factor_b_le {h : ℕ} (hh : 1 ≤ h) {ν : Ptn} (hν : wt ν = h) (r : ℤ) {σ' σ : Ptn} (h1 : wt σ' ≤ 4 * h) (h2 : wt σ ≤ 4 * h) :
    |coef σ' (op (bFam ν) r (tpow σ))| ≤ h.factorial * 2 ^ (12 * h ^ 2) := by
  refine (abs_coef_op_le hh (fun m hm => ?_) r h1 h2).trans (mul_le_mul_of_nonneg_right (hν ▸ l1_bFam_le ν) (by positivity))
  have h3 : m = Multiset.toFinsupp ν := by
    by_contra h0
    refine (mem_support_iff.1 hm) ?_
    unfold bFam tpow
    rw [coeff_smul, coeff_monomial, if_neg (Ne.symm h0), smul_zero]
  rw [h3, weight_toFinsupp, hν]

end GeneralPieces.Sizes
