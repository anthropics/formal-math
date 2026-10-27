/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import GeneralPieces.Series.ReadOff
public import ClauseBound.Boson.Basic
public import ClauseBound.Boson.Scalars

/-! # The lemma on the operators Q_s, paragraph "The constant"

The number G of the expansion does not depend on the two partitions σ, σ' of E at which the
coefficient is read, so it can be found at E = 0, that is σ = σ' = 0, the empty partition (the
monomial 1). There ⟨𝒩⟩ = 1, so f₊ = G·ε₊^H (`fP_vac`), in which ω₂^0 has the
coefficient G·ω₁^{−H}. In f₊ = Σ_r ⟨a[r]∘b[−r]⟩·ω₁^{r−h'}·ω₂^{−r−h} it has the coefficient
a[−h](b[h]·1)·ω₁^{−H}, and b[h]·1 = b (`op_vac`). Hence G = a[−h]b (`Expansion.const`), which in the
language of matrices is the entry `op a (−h) 0 b`. -/

public section

namespace GeneralPieces.Series

open ClauseBound.Boson Finset

/-- On the monomial 1 only multiplications act: (t_n·b)[r]·1 = Σ_l C(l−1, n−1)·t_l·(b[r−l]·1). -/
theorem op_cons_vac (n : ℕ) (b : List ℕ) (r : ℤ) (τ : Multiset ℕ) :
    op (n :: b) r τ 0 = ∑ l ∈ τ.toFinset, bet n l * op b (r - l) (τ.erase l) 0 := by
  show nop n (op b) r τ 0 = _
  rw [nop, Multiset.toFinset_zero, sum_empty, add_zero]
  exact sum_congr rfl fun l hl => by rw [cre, if_pos (Multiset.mem_toFinset.1 hl)]

/-- C(l−1, n−1) = 0 for l < n. -/
theorem bet_eq_zero {n l : ℕ} (h : l < n) : bet n l = 0 := by
  unfold bet
  split_ifs with h0
  · rfl
  · exact Scalars.choose_eq_zero (by omega) (by omega)

/-- C(n−1, n−1) = 1. -/
theorem bet_self {n : ℕ} (h : 1 ≤ n) : bet n n = 1 := by
  unfold bet
  rw [if_neg (by omega), show (n : ℤ) - 1 = ((n - 1 : ℕ) : ℤ) by omega, Ring.choose_natCast, Nat.choose_self, Nat.cast_one]

/-- b[r]·1 = 0 for r < h: every part ν_i of b needs an l_i ≥ ν_i. -/
theorem op_vac_eq_zero (b : List ℕ) : ∀ {r : ℤ} (τ : Multiset ℕ), r < b.sum → op b r τ 0 = 0 := by
  induction b with
  | nil =>
    intro r τ h
    rw [op, if_neg (by simp at h; omega)]
    rfl
  | cons n b ih =>
    intro r τ h
    rw [op_cons_vac]
    refine sum_eq_zero fun l _ => ?_
    rcases lt_or_ge l n with hl | hl
    · rw [bet_eq_zero hl, zero_mul]
    · rw [ih _ (by rw [List.sum_cons, Nat.cast_add] at h; omega), mul_zero]

/-- b[h]·1 = b: the sum of the l_i is h, which forces l_i = ν_i. -/
theorem op_vac {b : List ℕ} (hb : Pos b) : ∀ τ : Multiset ℕ, op b b.sum τ 0 = if τ = (b : Multiset ℕ) then 1 else 0 := by
  induction b with
  | nil =>
    intro τ
    rw [op, if_pos (by simp), one, Multiset.coe_nil]
  | cons n b ih =>
    intro τ
    have hn : 1 ≤ n := hb n List.mem_cons_self
    have hb' : Pos b := fun x hx => hb x (List.mem_cons_of_mem _ hx)
    have hterm : ∀ l ∈ τ.toFinset, l ≠ n → bet n l * op b (((n :: b).sum : ℕ) - (l : ℤ)) (τ.erase l) 0 = 0 := by
      intro l _ hl
      rcases lt_or_gt_of_ne hl with h | h
      · rw [bet_eq_zero h, zero_mul]
      · rw [op_vac_eq_zero b _ (by rw [List.sum_cons]; push_cast; omega), mul_zero]
    rw [op_cons_vac]
    by_cases hmem : n ∈ τ
    · rw [sum_eq_single_of_mem n (Multiset.mem_toFinset.2 hmem) hterm, bet_self hn, one_mul,
        show (((n :: b).sum : ℕ) : ℤ) - n = (b.sum : ℕ) by rw [List.sum_cons]; push_cast; ring, ih hb']
      refine if_congr ?_ rfl rfl
      rw [← Multiset.cons_coe]
      constructor
      · intro h
        rw [← h, Multiset.cons_erase hmem]
      · intro h
        rw [h, Multiset.erase_cons_head]
    · rw [sum_eq_zero fun l hl => hterm l hl fun h => hmem (h ▸ Multiset.mem_toFinset.1 hl), if_neg]
      intro h
      exact hmem (by rw [h, ← Multiset.cons_coe]; exact Multiset.mem_cons_self _ _)

/-- a[−h](b[h]·1) = a[−h]b. -/
theorem mul2_vac (a : List ℕ) {b : List ℕ} (hb : Pos b) : mul2 a (-(b.sum : ℤ)) b b.sum 0 0 = op a (-(b.sum : ℤ)) 0 (b : Multiset ℕ) := by
  rw [mul2, sum_eq_single_of_mem (b : Multiset ℕ)]
  · rw [op_vac hb, if_pos rfl, mul_one]
  · rw [mem_Pz]
    refine ⟨by simp, fun h => ?_⟩
    have := hb 0 (by simpa using h)
    omega
  · intro τ _ hτ
    rw [op_vac hb, if_neg hτ, mul_zero]

/-- For a list of terms c = (q, N, n) with N ≤ H, n = 0 when N < H and n = 1 when N = H, the sum of
q·e^N·φ(n) is (the sum of the q of the terms with N = H)·e^H. -/
theorem terms_vac (φ : L →ₐ[ℚ] S) (e : S) (H : ℕ) (l : List (ℚ × ℕ × L)) (hl : ∀ c ∈ l, c.2.1 ≤ H) (ht : ∀ c ∈ l, c.2.1 = H → c.2.2 = 1)
    (hv : ∀ c ∈ l, c.2.1 < H → c.2.2 = 0) :
    (l.map fun c => c.1 • (e ^ c.2.1 * φ c.2.2)).sum = ((l.filter fun c => c.2.1 = H).map fun c => c.1).sum • e ^ H := by
  induction l with
  | nil => simp
  | cons c l ih =>
    rw [List.map_cons, List.sum_cons, ih (fun c' hc' => hl c' (List.mem_cons_of_mem _ hc')) (fun c' hc' => ht c' (List.mem_cons_of_mem _ hc'))
      (fun c' hc' => hv c' (List.mem_cons_of_mem _ hc'))]
    by_cases h : c.2.1 = H
    · rw [List.filter_cons_of_pos (by simpa using h), List.map_cons, List.sum_cons, ht c List.mem_cons_self h, h, map_one, mul_one, add_smul]
    · rw [List.filter_cons_of_neg (by simpa using h), hv c List.mem_cons_self (lt_of_le_of_ne (hl c List.mem_cons_self) h), map_zero, mul_zero, smul_zero, zero_add]

variable {a b : List ℕ} {G : ℚ}

/-- For E = 0: f₊ = G·ε₊^H. -/
theorem Expansion.fP_vac (X : Expansion a b G 0 0) : fP a b 0 0 = G • epsP ^ (a.sum + b.sum) := by
  rw [X.plus, terms_vac toP epsP _ _ X.le (fun c hc h => by rw [X.top c hc h, if_pos rfl]) (X.vac rfl rfl), X.tot]

/-- In ε₊^N the coefficient of ω₁^{−N}·ω₂^0 is 1. -/
theorem cfP_epsP_pow (N : ℕ) : cfP (epsP ^ N) (-(N : ℤ)) 0 = 1 := by
  rw [cfP, epsP]
  rcases N with _ | N
  · rw [pow_zero, cf_one]
    simp
  · rw [eps_pow_succ, cf_diag, if_pos ⟨le_refl _, by push_cast; ring⟩]
    simp

/-- The constant: G = a[−h]b. -/
theorem Expansion.const (X : Expansion a b G 0 0) (hb : Pos b) : G = op a (-(b.sum : ℤ)) 0 (b : Multiset ℕ) := by
  have h1 : cfP (fP a b 0 0) (-((a.sum + b.sum : ℕ) : ℤ)) 0 = G := by
    rw [X.fP_vac, cfP, cf_smul, ← cfP, cfP_epsP_pow, mul_one]
  rw [cfP_fP, if_pos (by push_cast; ring), show -((a.sum + b.sum : ℕ) : ℤ) + a.sum = -(b.sum : ℤ) by push_cast; ring, zero_add, mul2_vac a hb] at h1
  exact h1.symm

end GeneralPieces.Series
