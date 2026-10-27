/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Push

/-! # A colouring lemma for few points

g points carry c a b ≤ M bits between a and b. The proof of Lemma 1 of the paper colours them with K
colours so that any two classes share about
U/K² bits (U = the sum of all c a b); it uses second moments, knows only the row sums of c, and
needs g ≥ 3K⁸. Here the single entries are bounded by M,
and g of the order K·log K is enough: if 4·D²·m·K ≤ g and (g+2)·K < 2^m, some colouring has classes
of fewer than 2g/K points and at most
U/K² + 3g²M/(D·K²) bits from any class to any class.

The proof counts colourings. Only three kinds of sums that are linear in the colouring are
controlled: the size of a class, the bits from one point into a
class, and the sum of the row sums over a class. For weights 0 ≤ x b ≤ 1, the sum over all
colourings χ of exp(θ·Σ_{χ b = γ} x b) is a product over the
points (`sum_exp_le`); this bounds the number of colourings that put at least the mean plus δ·g/K
into the class γ (`card_tail_le`); there are (g+2)·K such events
(`exists_all_good`). Main results: `exists_colouring_cap`, `exists_colouring_cap_nat`. -/

public section

open Finset

namespace PaddedDescent.Col

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- The weight that the colouring χ puts into the class γ. -/
noncomputable def Wt (x : ι → ℝ) (γ : κ) (χ : ι → κ) : ℝ := ∑ b, if χ b = γ then x b else 0

/-- exp y ≤ 1 + y + y² for 0 ≤ y ≤ 1. -/
theorem exp_le_quad {y : ℝ} (h0 : 0 ≤ y) (h1 : y ≤ 1) : Real.exp y ≤ 1 + y + y ^ 2 := by
  have h := Real.abs_exp_sub_one_sub_id_le (x := y) (by rw [abs_of_nonneg h0]; exact h1)
  have := (abs_le.1 h).2
  linarith

/-- The exponential moment, as a sum over all colourings: at most K^g·exp((θ+θ²)·mean), for 0 ≤ θ ≤ 1. -/
theorem sum_exp_le (x : ι → ℝ) (hx0 : ∀ b, 0 ≤ x b) (hx1 : ∀ b, x b ≤ 1) (γ : κ) {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    ∑ χ : ι → κ, Real.exp (θ * Wt x γ χ)
      ≤ (Fintype.card κ : ℝ) ^ Fintype.card ι * Real.exp ((θ + θ ^ 2) * ((∑ b, x b) / Fintype.card κ)) := by
  have hK : (0 : ℝ) < Fintype.card κ := by exact_mod_cast Fintype.card_pos_iff.2 ⟨γ⟩
  have e1 : ∀ χ : ι → κ, Real.exp (θ * Wt x γ χ) = ∏ b, Real.exp (if χ b = γ then θ * x b else 0) := by
    intro χ
    rw [← Real.exp_sum, Wt, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun b _ => ?_
    split_ifs <;> simp
  have e2 : ∑ χ : ι → κ, ∏ b, Real.exp (if χ b = γ then θ * x b else 0)
      = ∏ b, ∑ k : κ, Real.exp (if k = γ then θ * x b else 0) := by
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  have e3 : ∀ b, ∑ k : κ, Real.exp (if k = γ then θ * x b else 0) = ((Fintype.card κ : ℝ) - 1) + Real.exp (θ * x b) := by
    intro b
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ γ)]
    have : ∀ k ∈ (univ : Finset κ).erase γ, Real.exp (if k = γ then θ * x b else 0) = 1 := by
      intro k hk
      rw [if_neg (Finset.ne_of_mem_erase hk), Real.exp_zero]
    rw [Finset.sum_congr rfl this, if_pos rfl, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ γ), Finset.card_univ,
      nsmul_eq_mul, mul_one, Nat.cast_sub (Fintype.card_pos_iff.2 ⟨γ⟩), Nat.cast_one]
    ring
  have e4 : ∀ b, ((Fintype.card κ : ℝ) - 1) + Real.exp (θ * x b)
      ≤ (Fintype.card κ : ℝ) * Real.exp ((θ + θ ^ 2) * (x b / Fintype.card κ)) := by
    intro b
    have hy0 : 0 ≤ θ * x b := mul_nonneg h0 (hx0 b)
    have hy1 : θ * x b ≤ 1 := by nlinarith [hx0 b, hx1 b]
    have q := exp_le_quad hy0 hy1
    have q2 : (θ * x b) ^ 2 ≤ θ ^ 2 * x b := by
      have : x b ^ 2 ≤ x b := by nlinarith [hx0 b, hx1 b]
      calc (θ * x b) ^ 2 = θ ^ 2 * x b ^ 2 := by ring
        _ ≤ θ ^ 2 * x b := by gcongr
    have q3 := Real.add_one_le_exp ((θ + θ ^ 2) * (x b / Fintype.card κ))
    calc ((Fintype.card κ : ℝ) - 1) + Real.exp (θ * x b) ≤ (Fintype.card κ : ℝ) + (θ + θ ^ 2) * x b := by nlinarith
      _ = (Fintype.card κ : ℝ) * ((θ + θ ^ 2) * (x b / Fintype.card κ) + 1) := by field_simp; ring
      _ ≤ _ := by gcongr
  simp_rw [e1]
  rw [e2]
  simp_rw [e3]
  calc ∏ b, (((Fintype.card κ : ℝ) - 1) + Real.exp (θ * x b))
      ≤ ∏ b, ((Fintype.card κ : ℝ) * Real.exp ((θ + θ ^ 2) * (x b / Fintype.card κ))) := by
        refine Finset.prod_le_prod (fun b _ => ?_) fun b _ => e4 b
        have : (1 : ℝ) ≤ Fintype.card κ := by exact_mod_cast Fintype.card_pos_iff.2 ⟨γ⟩
        have := Real.exp_pos (θ * x b)
        linarith
    _ = _ := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, ← Real.exp_sum, ← Finset.mul_sum, Finset.sum_div]

/-- The tail, as a count: at most K^g·exp(−δ²s/4) colourings put at least mean + δ·s into the class
γ, where s is any upper bound for the mean. -/
theorem card_tail_le (x : ι → ℝ) (hx0 : ∀ b, 0 ≤ x b) (hx1 : ∀ b, x b ≤ 1) (γ : κ) {δ s : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hs : (∑ b, x b) / Fintype.card κ ≤ s) :
    (#{χ : ι → κ | (∑ b, x b) / Fintype.card κ + δ * s ≤ Wt x γ χ} : ℝ)
      ≤ (Fintype.card κ : ℝ) ^ Fintype.card ι * Real.exp (-(δ ^ 2 * s / 4)) := by
  set μ : ℝ := (∑ b, x b) / Fintype.card κ with hμ
  have hθ0 : (0 : ℝ) ≤ δ / 2 := by linarith
  have hθ1 : δ / 2 ≤ 1 := by linarith
  have h := sum_exp_le x hx0 hx1 γ hθ0 hθ1
  have m : (#{χ : ι → κ | μ + δ * s ≤ Wt x γ χ} : ℝ) * Real.exp (δ / 2 * (μ + δ * s)) ≤ ∑ χ : ι → κ, Real.exp (δ / 2 * Wt x γ χ) := by
    calc (#{χ : ι → κ | μ + δ * s ≤ Wt x γ χ} : ℝ) * Real.exp (δ / 2 * (μ + δ * s))
        = ∑ χ ∈ ({χ : ι → κ | μ + δ * s ≤ Wt x γ χ} : Finset (ι → κ)), Real.exp (δ / 2 * (μ + δ * s)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ χ ∈ ({χ : ι → κ | μ + δ * s ≤ Wt x γ χ} : Finset (ι → κ)), Real.exp (δ / 2 * Wt x γ χ) := by
          refine Finset.sum_le_sum fun χ hχ => Real.exp_le_exp.2 ?_
          exact mul_le_mul_of_nonneg_left (Finset.mem_filter.1 hχ).2 hθ0
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ => (Real.exp_pos _).le
  have hpos := Real.exp_pos (δ / 2 * (μ + δ * s))
  have key : (#{χ : ι → κ | μ + δ * s ≤ Wt x γ χ} : ℝ)
      ≤ (Fintype.card κ : ℝ) ^ Fintype.card ι * (Real.exp ((δ / 2 + (δ / 2) ^ 2) * μ) * Real.exp (-(δ / 2 * (μ + δ * s)))) := by
    rw [Real.exp_neg, ← mul_assoc, ← div_eq_mul_inv, le_div_iff₀ hpos]
    exact m.trans h
  refine key.trans ?_
  rw [← Real.exp_add]
  gcongr
  nlinarith [mul_le_mul_of_nonneg_left hs (sq_nonneg (δ / 2))]


omit [DecidableEq ι] [DecidableEq κ] in
/-- If x ≤ 1 pointwise, the mean is at most g/K. -/
theorem mean_le (x : ι → ℝ) (hx1 : ∀ b, x b ≤ 1) [Nonempty κ] :
    (∑ b, x b) / (Fintype.card κ : ℝ) ≤ (Fintype.card ι : ℝ) / Fintype.card κ := by
  have hK : (0 : ℝ) < Fintype.card κ := by exact_mod_cast Fintype.card_pos
  gcongr
  calc ∑ b, x b ≤ ∑ _b : ι, (1 : ℝ) := Finset.sum_le_sum fun b _ => hx1 b
    _ = Fintype.card ι := by simp

/-- Finitely many families of weights at once: if the number of (weight, colour) pairs times
exp(−δ²s/4) is below 1, one colouring is good for all. -/
theorem exists_all_good [Nonempty κ] {T : Type*} [Fintype T] (x : T → ι → ℝ) (hx0 : ∀ t b, 0 ≤ x t b) (hx1 : ∀ t b, x t b ≤ 1)
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (h : (Fintype.card T : ℝ) * Fintype.card κ * Real.exp (-(δ ^ 2 * ((Fintype.card ι : ℝ) / Fintype.card κ) / 4)) < 1) :
    ∃ χ : ι → κ, ∀ t γ, Wt (x t) γ χ < (∑ b, x t b) / Fintype.card κ + δ * ((Fintype.card ι : ℝ) / Fintype.card κ) := by
  by_contra hne
  push Not at hne
  set s : ℝ := (Fintype.card ι : ℝ) / Fintype.card κ with hs
  set E : ℝ := Real.exp (-(δ ^ 2 * s / 4)) with hE
  set N : ℝ := (Fintype.card κ : ℝ) ^ Fintype.card ι with hN
  have hNpos : 0 < N := by
    have hK : (0 : ℝ) < Fintype.card κ := by exact_mod_cast Fintype.card_pos
    positivity
  let B : T × κ → Finset (ι → κ) := fun p => {χ : ι → κ | (∑ b, x p.1 b) / Fintype.card κ + δ * s ≤ Wt (x p.1) p.2 χ}
  have hcover : (univ : Finset (ι → κ)) ⊆ univ.biUnion B := by
    intro χ _
    obtain ⟨t, γ, hb⟩ := hne χ
    exact Finset.mem_biUnion.2 ⟨(t, γ), Finset.mem_univ _, Finset.mem_filter.2 ⟨Finset.mem_univ _, hb⟩⟩
  have h1 : (N : ℝ) ≤ ∑ p : T × κ, (#(B p) : ℝ) := by
    have c1 : #(univ : Finset (ι → κ)) ≤ ∑ p : T × κ, #(B p) := (Finset.card_le_card hcover).trans Finset.card_biUnion_le
    have c2 : (#(univ : Finset (ι → κ)) : ℝ) = N := by
      rw [Finset.card_univ, Fintype.card_fun, hN]; push_cast; rfl
    rw [← c2]
    exact_mod_cast c1
  have h2 : ∑ p : T × κ, (#(B p) : ℝ) ≤ ∑ _p : T × κ, N * E :=
    Finset.sum_le_sum fun p _ => card_tail_le (x p.1) (hx0 p.1) (hx1 p.1) p.2 hδ0 hδ1 (mean_le (x p.1) (hx1 p.1))
  have h3 : ∑ _p : T × κ, N * E = N * ((Fintype.card T : ℝ) * Fintype.card κ * E) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, nsmul_eq_mul]; push_cast; ring
  have h4 : N * ((Fintype.card T : ℝ) * Fintype.card κ * E) < N * 1 := mul_lt_mul_of_pos_left h hNpos
  linarith


omit [DecidableEq ι] [Fintype κ] in
/-- The weight of a class as a sum over the class. -/
theorem Wt_eq (x : ι → ℝ) (γ : κ) (χ : ι → κ) : Wt x γ χ = ∑ b with χ b = γ, x b := by
  rw [Wt, Finset.sum_filter]

/-- **The colouring lemma with a bound M on the bits between two points.** g points, K ≥ 1 colours,
c a b ≤ M, δ = 1/D. If (g+2)·K·exp(−δ²·(g/K)/4) < 1, some
colouring has classes of fewer than 2g/K points, and from any class to any class at most U/K² +
3g²M/(DK²) bits, where U = Σ_{a,b} c a b. -/
theorem exists_colouring_cap [Nonempty κ] (c : ι → ι → ℕ) (M D : ℕ) (hM0 : 0 < M) (hD : 1 ≤ D) (hM : ∀ a b, c a b ≤ M)
    (hg : ((Fintype.card ι : ℝ) + 2) * Fintype.card κ *
      Real.exp (-((1 / (D : ℝ)) ^ 2 * ((Fintype.card ι : ℝ) / Fintype.card κ) / 4)) < 1) :
    ∃ χ : ι → κ, (∀ γ, Fintype.card κ * #{a | χ a = γ} < 2 * Fintype.card ι) ∧
      ∀ γ γ', D * Fintype.card κ ^ 2 * ∑ a with χ a = γ, ∑ b with χ b = γ', c a b
        ≤ D * (∑ a, ∑ b, c a b) + 3 * Fintype.card ι ^ 2 * M := by
  have hK1 : (1 : ℝ) ≤ Fintype.card κ := by exact_mod_cast Fintype.card_pos
  have hgpos : 0 < Fintype.card ι := by
    by_contra h0
    have h0' : Fintype.card ι = 0 := by omega
    rw [h0'] at hg
    simp at hg
    linarith
  obtain ⟨g, hgdef⟩ : ∃ g : ℝ, g = Fintype.card ι := ⟨_, rfl⟩
  obtain ⟨K, hKdef⟩ : ∃ K : ℝ, K = Fintype.card κ := ⟨_, rfl⟩
  obtain ⟨Mr, hMdef⟩ : ∃ Mr : ℝ, Mr = M := ⟨_, rfl⟩
  obtain ⟨Dr, hDdef⟩ : ∃ Dr : ℝ, Dr = D := ⟨_, rfl⟩
  have hg0 : 0 < g := by rw [hgdef]; exact_mod_cast hgpos
  have hK0 : 0 < K := by rw [hKdef]; linarith
  have hMr : 0 < Mr := by rw [hMdef]; exact_mod_cast hM0
  have hDr : 1 ≤ Dr := by rw [hDdef]; exact_mod_cast hD
  have hδ0 : 0 ≤ 1 / Dr := by positivity
  have hδ1 : 1 / Dr ≤ 1 := by rw [div_le_one (by linarith)]; exact hDr
  let Pr : ι → ℝ := fun a => ∑ b, (c a b : ℝ)
  have hP0 : ∀ a, 0 ≤ Pr a := fun a => Finset.sum_nonneg fun b _ => Nat.cast_nonneg _
  have hcM : ∀ a b, (c a b : ℝ) ≤ Mr := fun a b => by rw [hMdef]; exact_mod_cast hM a b
  have hPle : ∀ a, Pr a ≤ g * Mr := fun a => by
    calc Pr a ≤ ∑ _b : ι, Mr := Finset.sum_le_sum fun b _ => hcM a b
      _ = g * Mr := by simp [hgdef]
  let x : Unit ⊕ ι ⊕ Unit → ι → ℝ := fun t => match t with
    | .inl _ => fun _ => 1
    | .inr (.inl a) => fun b => (c a b : ℝ) / Mr
    | .inr (.inr _) => fun a => Pr a / (g * Mr)
  have hx0 : ∀ t b, 0 ≤ x t b := by
    rintro (_ | a | _) b
    · exact zero_le_one
    · exact div_nonneg (Nat.cast_nonneg _) hMr.le
    · exact div_nonneg (hP0 b) (by positivity)
  have hx1 : ∀ t b, x t b ≤ 1 := by
    rintro (_ | a | _) b
    · exact le_refl _
    · exact (div_le_one hMr).2 (hcM a b)
    · exact (div_le_one (by positivity)).2 (hPle b)
  have hcard : ((Fintype.card (Unit ⊕ ι ⊕ Unit) : ℕ) : ℝ) = g + 2 := by
    simp [Fintype.card_sum, hgdef]; ring
  obtain ⟨χ, hχ⟩ := exists_all_good (κ := κ) x hx0 hx1 hδ0 hδ1 (by rw [hcard, hgdef, hDdef]; exact hg)
  rw [← hgdef, ← hKdef] at hχ
  obtain ⟨s, hsdef⟩ : ∃ s : ℝ, s = g / K := ⟨_, rfl⟩
  rw [← hsdef] at hχ
  have hs0 : 0 < s := by rw [hsdef]; positivity
  -- the three kinds of facts
  have f1 : ∀ γ, ((#{a | χ a = γ} : ℕ) : ℝ) < 2 * s := by
    intro γ
    have h := hχ (.inl ()) γ
    have e1 : Wt (x (.inl ())) γ χ = ((#{a | χ a = γ} : ℕ) : ℝ) := by
      rw [Wt_eq]; simp [x]
    have e2 : (∑ b, x (.inl ()) b) / K = s := by
      rw [hsdef]; simp [x, hgdef]
    rw [e1, e2] at h
    nlinarith
  have f2 : ∀ a γ', ∑ b with χ b = γ', (c a b : ℝ) ≤ Pr a / K + Mr * (1 / Dr * s) := by
    intro a γ'
    have h := hχ (.inr (.inl a)) γ'
    have e1 : Wt (x (.inr (.inl a))) γ' χ = (∑ b with χ b = γ', (c a b : ℝ)) / Mr := by
      rw [Wt_eq, Finset.sum_div]
    have e2 : (∑ b, x (.inr (.inl a)) b) / K = Pr a / K / Mr := by
      have : ∑ b, x (.inr (.inl a)) b = Pr a / Mr := by
        change ∑ b, (c a b : ℝ) / Mr = _
        rw [← Finset.sum_div]
      rw [this]; ring
    rw [e1, e2, div_lt_iff₀ hMr] at h
    have : (Pr a / K / Mr + 1 / Dr * s) * Mr = Pr a / K + Mr * (1 / Dr * s) := by field_simp
    linarith
  have f3 : ∀ γ, ∑ a with χ a = γ, Pr a ≤ (∑ a, Pr a) / K + g * Mr * (1 / Dr * s) := by
    intro γ
    have h := hχ (.inr (.inr ())) γ
    have hgM : 0 < g * Mr := by positivity
    have e1 : Wt (x (.inr (.inr ()))) γ χ = (∑ a with χ a = γ, Pr a) / (g * Mr) := by
      rw [Wt_eq, Finset.sum_div]
    have e2 : (∑ b, x (.inr (.inr ())) b) / K = (∑ a, Pr a) / K / (g * Mr) := by
      have : ∑ b, x (.inr (.inr ())) b = (∑ a, Pr a) / (g * Mr) := by
        change ∑ b, Pr b / (g * Mr) = _
        rw [← Finset.sum_div]
      rw [this]; ring
    rw [e1, e2, div_lt_iff₀ hgM] at h
    have : ((∑ a, Pr a) / K / (g * Mr) + 1 / Dr * s) * (g * Mr) = (∑ a, Pr a) / K + g * Mr * (1 / Dr * s) := by field_simp
    linarith
  refine ⟨χ, fun γ => ?_, fun γ γ' => ?_⟩
  · have h := f1 γ
    rw [hsdef, mul_div_assoc', lt_div_iff₀ hK0, hKdef, hgdef] at h
    have h' : ((Fintype.card κ * #{a | χ a = γ} : ℕ) : ℝ) < ((2 * Fintype.card ι : ℕ) : ℝ) := by
      push_cast; linarith
    exact_mod_cast h'
  · have y1 : ∑ a with χ a = γ, ∑ b with χ b = γ', (c a b : ℝ)
        ≤ (∑ a with χ a = γ, Pr a) / K + ((#{a | χ a = γ} : ℕ) : ℝ) * (Mr * (1 / Dr * s)) := by
      calc ∑ a with χ a = γ, ∑ b with χ b = γ', (c a b : ℝ)
          ≤ ∑ a with χ a = γ, (Pr a / K + Mr * (1 / Dr * s)) := Finset.sum_le_sum fun a _ => f2 a γ'
        _ = _ := by rw [Finset.sum_add_distrib, Finset.sum_div, Finset.sum_const, nsmul_eq_mul]
    have y2 : (∑ a with χ a = γ, Pr a) / K ≤ ((∑ a, Pr a) / K + g * Mr * (1 / Dr * s)) / K := by
      gcongr; exact f3 γ
    have y3 : ((#{a | χ a = γ} : ℕ) : ℝ) * (Mr * (1 / Dr * s)) ≤ 2 * s * (Mr * (1 / Dr * s)) := by
      gcongr; exact (f1 γ).le
    have y4 : Dr * K ^ 2 * (((∑ a, Pr a) / K + g * Mr * (1 / Dr * s)) / K + 2 * s * (Mr * (1 / Dr * s)))
        = Dr * (∑ a, Pr a) + 3 * g ^ 2 * Mr := by
      rw [hsdef]; field_simp; ring
    have y5 : Dr * K ^ 2 * ∑ a with χ a = γ, ∑ b with χ b = γ', (c a b : ℝ) ≤ Dr * (∑ a, Pr a) + 3 * g ^ 2 * Mr := by
      rw [← y4]
      have : 0 ≤ Dr * K ^ 2 := by positivity
      exact mul_le_mul_of_nonneg_left (by linarith) this
    rw [hDdef, hKdef, hgdef, hMdef] at y5
    have y6 : (∑ a, Pr a) = ((∑ a, ∑ b, c a b : ℕ) : ℝ) := by
      simp only [Pr]; push_cast; rfl
    rw [y6] at y5
    exact_mod_cast y5

/-- 2^m ≤ exp m. -/
theorem two_pow_le_exp (m : ℕ) : (2 : ℝ) ^ m ≤ Real.exp m := by
  rw [← Real.exp_one_pow]
  have : (2 : ℝ) ≤ Real.exp 1 := by have := Real.exp_one_gt_d9; linarith
  gcongr

/-- The same lemma for `Fin g`, `Fin K`, with a hypothesis in natural numbers: 4·D²·m·K ≤ g and
(g+2)·K < 2^m for some m. -/
theorem exists_colouring_cap_nat {K g : ℕ} (hK : 1 ≤ K) (c : Fin g → Fin g → ℕ) (M D m : ℕ) (hM0 : 0 < M) (hD : 1 ≤ D)
    (hM : ∀ a b, c a b ≤ M) (h1 : 4 * D ^ 2 * m * K ≤ g) (h2 : (g + 2) * K < 2 ^ m) :
    ∃ χ : Fin g → Fin K, (∀ G, K * #{a | χ a = G} < 2 * g) ∧
      ∀ G G', D * K ^ 2 * ∑ a with χ a = G, ∑ b with χ b = G', c a b ≤ D * (∑ a, ∑ b, c a b) + 3 * g ^ 2 * M := by
  have : Nonempty (Fin K) := ⟨⟨0, hK⟩⟩
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  have key : ((Fintype.card (Fin g) : ℝ) + 2) * Fintype.card (Fin K) *
      Real.exp (-((1 / (D : ℝ)) ^ 2 * ((Fintype.card (Fin g) : ℝ) / Fintype.card (Fin K)) / 4)) < 1 := by
    simp only [Fintype.card_fin]
    have a1 : (m : ℝ) ≤ (1 / (D : ℝ)) ^ 2 * ((g : ℝ) / K) / 4 := by
      have h1r : (4 : ℝ) * D ^ 2 * m * K ≤ g := by exact_mod_cast h1
      have e : (1 / (D : ℝ)) ^ 2 * ((g : ℝ) / K) / 4 = g / (4 * D ^ 2 * K) := by field_simp
      rw [e, le_div_iff₀ (by positivity)]
      linarith
    have a2 : Real.exp (-((1 / (D : ℝ)) ^ 2 * ((g : ℝ) / K) / 4)) ≤ 1 / 2 ^ m := by
      calc Real.exp (-((1 / (D : ℝ)) ^ 2 * ((g : ℝ) / K) / 4)) ≤ Real.exp (-(m : ℝ)) := Real.exp_le_exp.2 (by linarith)
        _ = 1 / Real.exp m := by rw [Real.exp_neg, one_div]
        _ ≤ 1 / 2 ^ m := by
            apply one_div_le_one_div_of_le (by positivity) (two_pow_le_exp m)
    have a3 : ((g : ℝ) + 2) * K < 2 ^ m := by exact_mod_cast h2
    calc ((g : ℝ) + 2) * K * Real.exp (-((1 / (D : ℝ)) ^ 2 * ((g : ℝ) / K) / 4)) ≤ ((g : ℝ) + 2) * K * (1 / 2 ^ m) := by gcongr
      _ = ((g : ℝ) + 2) * K / 2 ^ m := by ring
      _ < 1 := by rw [div_lt_one (by positivity)]; exact a3
  simpa only [Fintype.card_fin] using exists_colouring_cap (ι := Fin g) (κ := Fin K) c M D hM0 hD hM key

end PaddedDescent.Col

