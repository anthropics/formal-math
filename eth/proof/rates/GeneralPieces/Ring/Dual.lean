/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import GeneralPieces.Ring.Op
public import ClauseBound.Boson.Dual

/-! # Lemma 10 of Appendix B, along its proof

a^μ[−h]·b^ν = h!·[μ = ν] for partitions μ, ν of h, on the ring ℚ[t₁, t₂, …] with the operators a[r]
of display (47). The six sentences of the proof are named theorems, in the order of the text:
the numbers ϑ_n(k); the display for (∏ y_{μ_i})[−h]·b; Vandermonde's identity and the two values of
ϑ; a nonzero term has k_i = μ_i; a^μ[−h]·b = ∏ ∇_{μ_i} b; the value at b = t^ν.
The facts about display (47) and (O3) that the proof uses, and Vandermonde's identity, are taken
from the files on the ring (`opFacts`, `o3`, `binomRules`).
A partition is handled as a list of its parts. The sum over the tuples (k_i) of positive integers
with sum h is a sum over the finite set `posTuples` of the lists of the right length with entries in
{1, …, h} and sum h. The fact that z_μ divides h! is taken from
`ClauseBound.Boson.zz_dvd_factorial`. -/

@[expose] public section

namespace GeneralPieces.Dual

open Finset MvPolynomial AppHalfPieces

/-! ## The numbers ϑ_n(k) -/

/-- «Let ϑ_n(k) = Σ_{j=1}^{n} C(n, n−j)·C(−k−1, j−1).» -/
def theta (n : ℕ+) (k : ℤ) : ℤ := ∑ j ∈ Icc 1 (n : ℕ), binom n ((n : ℤ) - j) * binom (-k - 1) ((j : ℤ) - 1)

/-- «By Vandermonde's identity ϑ_n(k) = C(n−k−1, n−1)». -/
theorem theta_eq (n : ℕ+) (k : ℤ) : theta n k = binom ((n : ℤ) - k - 1) ((n : ℤ) - 1) := by
  obtain ⟨p, hp⟩ : ∃ p : ℕ, (n : ℕ) = p + 1 := ⟨(n : ℕ) - 1, by have := n.pos; omega⟩
  have h := binomRules.vandermonde (n : ℤ) (-k - 1) p
  have hn : ((n : ℕ) : ℤ) = (p : ℤ) + 1 := by exact_mod_cast hp
  have hI : Icc 1 (n : ℕ) = Ico (0 + 1) (p + 1 + 1) := by ext j; simp only [mem_Icc, mem_Ico]; omega
  rw [theta, hI, ← sum_Ico_add' _ 0 (p + 1) 1, ← range_eq_Ico]
  rw [show (n : ℤ) - k - 1 = (n : ℤ) + (-k - 1) by ring, show ((n : ℕ) : ℤ) - 1 = (p : ℤ) by omega, ← h]
  refine sum_congr rfl fun j _ => ?_
  congr 2 <;> push_cast <;> omega

/-- C(−1, m) = (−1)^m. -/
theorem choose_neg_one (m : ℕ) : Ring.choose (-1 : ℤ) m = (-1) ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h := Ring.choose_succ_succ (-1 : ℤ) m
    rw [show (-1 : ℤ) + 1 = 0 by norm_num, Ring.choose_zero_succ, ih] at h
    rw [pow_succ]; linarith

/-- «… which is 0 for 1 ≤ k < n». -/
theorem theta_of_lt (n : ℕ+) (k : ℤ) (h1 : 1 ≤ k) (h2 : k < n) : theta n k = 0 := by
  rw [theta_eq, binom, if_pos (by have := n.pos; omega)]
  obtain ⟨a, ha⟩ : ∃ a : ℕ, (n : ℤ) - k - 1 = a := ⟨((n : ℤ) - k - 1).toNat, by omega⟩
  rw [ha, Ring.choose_natCast, Nat.choose_eq_zero_of_lt (by omega)]
  rfl

/-- «… and (−1)^{n−1} for k = n.» -/
theorem theta_self (n : ℕ+) : theta n n = (-1) ^ ((n : ℕ) - 1) := by
  rw [theta_eq, binom, if_pos (by have := n.pos; omega), show (n : ℤ) - n - 1 = -1 by ring, choose_neg_one]
  congr 1
  omega

/-! ## Lists with one entry from each of given finite sets -/

/-- The lists with one entry from each of the given finite sets, in their order. -/
def tuples {α : Type} [DecidableEq α] : List (Finset α) → Finset (List α)
  | [] => {[]}
  | s :: r => (s ×ˢ tuples r).image fun p => p.1 :: p.2

/-- A sum over such lists, sorted by the first entry. -/
theorem sum_tuples_cons {α M : Type} [DecidableEq α] [AddCommMonoid M] (s : Finset α) (r : List (Finset α)) (F : List α → M) :
    ∑ x ∈ tuples (s :: r), F x = ∑ a ∈ s, ∑ x ∈ tuples r, F (a :: x) := by
  rw [tuples, sum_image, sum_product]
  intro p _ q _ h
  simp only [List.cons.injEq] at h
  exact Prod.ext h.1 h.2

/-- Membership. -/
theorem mem_tuples {α : Type} [DecidableEq α] (L : List (Finset α)) (x : List α) : x ∈ tuples L ↔ List.Forall₂ (fun a s => a ∈ s) x L := by
  induction L generalizing x with
  | nil => simp [tuples]
  | cons s r ih =>
    simp only [tuples, mem_image, mem_product, Prod.exists]
    constructor
    · rintro ⟨a, y, ⟨ha, hy⟩, rfl⟩
      exact List.Forall₂.cons ha ((ih y).1 hy)
    · intro h
      cases h with
      | cons ha hy => exact ⟨_, _, ⟨ha, (ih _).2 hy⟩, rfl⟩

/-- Multiplying out a product of sums. -/
theorem prod_map_sum {ι α R : Type} [DecidableEq α] [CommSemiring R] (L : List ι) (S : ι → Finset α) (f : ι → α → R) :
    (L.map fun i => ∑ a ∈ S i, f i a).prod = ∑ x ∈ tuples (L.map S), (List.zipWith f L x).prod := by
  induction L with
  | nil => simp [tuples]
  | cons i L ih =>
    rw [List.map_cons, List.prod_cons, ih, List.map_cons, sum_tuples_cons, sum_mul_sum]
    simp only [List.zipWith_cons_cons, List.prod_cons]

/-! ## The display -/

/-- ∏_i ∇_{k_i}, applied to f. -/
noncomputable def nablas (ks : List ℤ) (f : V) : V := ks.foldr nabla f

/-- The tuples (k_i) of r positive integers with sum h: a finite set. -/
noncomputable def posTuples (r h : ℕ) : Finset (List ℤ) := (tuples (List.replicate r (Icc (1 : ℤ) h))).filter fun ks => ks.sum = h

theorem forall₂_replicate {α : Type} (S : Finset α) (r : ℕ) (x : List α) :
    List.Forall₂ (fun a s => a ∈ s) x (List.replicate r S) ↔ x.length = r ∧ ∀ a ∈ x, a ∈ S := by
  induction r generalizing x with
  | zero => cases x <;> simp
  | succ r ih =>
    cases x with
    | nil => simp [List.replicate_succ]
    | cons a x => simp [List.replicate_succ, ih, and_left_comm]

/-- These are the lists of r integers k_i ≥ 1 with sum h. -/
theorem mem_posTuples (r h : ℕ) (ks : List ℤ) : ks ∈ posTuples r h ↔ ks.length = r ∧ (∀ k ∈ ks, 1 ≤ k) ∧ ks.sum = h := by
  rw [posTuples, mem_filter, mem_tuples, forall₂_replicate]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨h1, fun k hk => (mem_Icc.1 (h2 k hk)).1, h3⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨⟨h1, fun k hk => mem_Icc.2 ⟨h2 k hk, ?_⟩⟩, h3⟩
    rw [← h3]
    exact List.single_le_sum (fun x hx => by have := h2 x hx; omega) k hk

/-- A term of display (47) with all k_i positive: there are only differentiations. -/
theorem term_pos (μ : List ℕ+) (ks : List ℤ) (f : V) (h : ∀ k ∈ ks, 1 ≤ k) :
    term μ ks f = (((List.zipWith (fun (m : ℕ+) (k : ℤ) => binom (-k - 1) ((m : ℤ) - 1)) μ ks).prod : ℤ) : ℚ) • nablas ks f := by
  have h1 : ks.filter (· < 0) = [] := by
    rw [List.filter_eq_nil_iff]; intro k hk; have := h k hk; simp only [decide_eq_true_eq]; omega
  have h2 : ks.filter (0 < ·) = ks := by
    rw [List.filter_eq_self]; intro k hk; have := h k hk; simp only [decide_eq_true_eq]; omega
  rw [term, h1, h2]; rfl

/-- «… using (47) and (O3) for each monomial»: on b ∈ V_h, the operator a[−h] of a monomial a is the
sum of the terms of (47) with all k_i positive. -/
theorem opMon_eq_sum (h : ℕ) (μ : List ℕ+) (b : V) (hb : b ∈ VE h) :
    opMon μ (-(h : ℤ)) b = ∑ ks ∈ posTuples μ.length h, term μ ks b := by
  unfold opMon
  apply finsum_mem_eq_sum_of_inter_support_eq
  ext ks
  simp only [Set.mem_inter_iff, Function.mem_support, mem_coe, mem_posTuples, Choices, Set.mem_ofPred_eq, neg_neg]
  constructor
  · rintro ⟨⟨hl, hne, hs⟩, ht⟩
    refine ⟨⟨hl, fun k hk => ?_, hs⟩, ht⟩
    by_contra hc
    have hk0 := hne k hk
    exact ht (o3.positive h μ b ks hb ⟨hl, hne, by rw [hs, neg_neg]⟩ ⟨k, hk, by omega⟩)
  · rintro ⟨⟨hl, hpos, hs⟩, ht⟩
    exact ⟨⟨hl, fun k hk => by have := hpos k hk; omega, hs⟩, ht⟩

/-- t^μ for a list with a first part. -/
theorem tpow_cons (a : ℕ+) (l : List ℕ+) : tpow ((a :: l : List ℕ+) : Multiset ℕ+) = X a * tpow (l : Multiset ℕ+) := by
  unfold tpow
  rw [← Multiset.cons_coe, ← Multiset.singleton_add, Multiset.toFinsupp_add, Multiset.toFinsupp_singleton, X, monomial_mul, one_mul]

theorem prod_zip_smul (c : ℕ+ → ℕ → ℚ) (g : ℕ → ℕ+) (μ : List ℕ+) (js : List ℕ) (hl : js.length = μ.length) :
    (List.zipWith (fun n j => c n j • (X (g j) : V)) μ js).prod = (List.zipWith c μ js).prod • tpow ((js.map g : List ℕ+) : Multiset ℕ+) := by
  induction μ generalizing js with
  | nil =>
    have : js = [] := List.length_eq_zero_iff.1 hl
    subst this
    simp [tpow]
  | cons n μ ih =>
    cases js with
    | nil => simp at hl
    | cons j js =>
      simp only [List.zipWith_cons_cons, List.prod_cons, List.map_cons]
      rw [ih js (by simpa using hl), smul_mul_smul_comm, tpow_cons]

/-- «Multiplying out ∏ y_{μ_i}»: the sum over all choices of j_i ∈ {1, …, μ_i} of ∏ C(μ_i, j_i)
times the monomial ∏ t_{j_i}. -/
theorem prod_y (μ : List ℕ+) : (μ.map y).prod = ∑ js ∈ tuples (μ.map fun n : ℕ+ => Icc 1 (n : ℕ)),
    (List.zipWith (fun (n : ℕ+) (j : ℕ) => ((n : ℕ).choose j : ℚ)) μ js).prod • tpow ((js.map Nat.toPNat' : List ℕ+) : Multiset ℕ+) := by
  have h := prod_map_sum μ (fun n : ℕ+ => Icc 1 (n : ℕ)) (fun (n : ℕ+) (j : ℕ) => ((n : ℕ).choose j : ℚ) • (X j.toPNat' : V))
  have h0 : (μ.map y) = μ.map fun n : ℕ+ => ∑ j ∈ Icc 1 (n : ℕ), ((n : ℕ).choose j : ℚ) • (X j.toPNat' : V) := rfl
  rw [h0, h]
  refine sum_congr rfl fun js hjs => ?_
  have hl : js.length = μ.length := by
    have := ((mem_tuples _ _).1 hjs).length_eq
    simpa using this
  exact prod_zip_smul _ _ μ js hl

/-- a[r] is linear in a, for finite sums. -/
theorem op_sum {ι : Type} (s : Finset ι) (c : ι → ℚ) (g : ι → V) (r : ℤ) (f : V) :
    op (∑ x ∈ s, c x • g x) r f = ∑ x ∈ s, c x • op (g x) r f := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [op]
  | insert a s ha ih => rw [sum_insert ha, sum_insert ha, opFacts.add_left, opFacts.smul_left, ih]

/-- C(n, n−j) is the binomial coefficient of natural numbers C(n, j), for j ≤ n. -/
theorem binom_symm (n j : ℕ) (h : j ≤ n) : binom n ((n : ℤ) - j) = (n.choose j : ℤ) := by
  rw [binom, if_pos (by omega), Ring.choose_natCast, show ((n : ℤ) - j).toNat = n - j by omega, Nat.choose_symm h]

/-- The sum over the j_i of the coefficients is ∏ ϑ_{μ_i}(k_i). -/
theorem sum_coeff (μ : List ℕ+) (ks : List ℤ) (hl : ks.length = μ.length) :
    ∑ js ∈ tuples (μ.map fun n : ℕ+ => Icc 1 (n : ℕ)), (List.zipWith (fun (n : ℕ+) (j : ℕ) => ((n : ℕ).choose j : ℚ)) μ js).prod *
      (((List.zipWith (fun (m : ℕ+) (k : ℤ) => binom (-k - 1) ((m : ℤ) - 1)) (js.map Nat.toPNat') ks).prod : ℤ) : ℚ) =
    (((List.zipWith theta μ ks).prod : ℤ) : ℚ) := by
  induction μ generalizing ks with
  | nil => simp [tuples]
  | cons n μ ih =>
    cases ks with
    | nil => simp at hl
    | cons k ks =>
      rw [List.map_cons, sum_tuples_cons]
      simp only [List.zipWith_cons_cons, List.map_cons, List.prod_cons]
      rw [Int.cast_mul, ← ih ks (by simpa using hl), theta, Int.cast_sum, sum_mul]
      refine sum_congr rfl fun j hj => ?_
      rw [mul_sum]
      refine sum_congr rfl fun js _ => ?_
      obtain ⟨hj1, hj2⟩ := mem_Icc.1 hj
      have e1 : ((j.toPNat' : ℕ+) : ℤ) = j := by
        have : ((j.toPNat' : ℕ+) : ℕ) = j := by rw [Nat.toPNat'_coe, if_pos (by omega)]
        exact_mod_cast this
      rw [e1, binom_symm _ _ hj2]
      push_cast
      ring

/-- The display in the proof: for b ∈ V_h, (∏_i y_{μ_i})[−h]·b = Σ over the tuples (k_i) with Σ k_i =
h and k_i ≥ 1 of ∏_i ϑ_{μ_i}(k_i)·∏_i ∇_{k_i} b. -/
theorem display (h : ℕ) (μ : List ℕ+) (b : V) (hb : b ∈ VE h) :
    op (μ.map y).prod (-(h : ℤ)) b = ∑ ks ∈ posTuples μ.length h, (((List.zipWith theta μ ks).prod : ℤ) : ℚ) • nablas ks b := by
  rw [prod_y, op_sum]
  have h1 : ∀ js ∈ tuples (μ.map fun n : ℕ+ => Icc 1 (n : ℕ)),
      (List.zipWith (fun (n : ℕ+) (j : ℕ) => ((n : ℕ).choose j : ℚ)) μ js).prod • op (tpow ((js.map Nat.toPNat' : List ℕ+) : Multiset ℕ+)) (-(h : ℤ)) b =
      ∑ ks ∈ posTuples μ.length h, ((List.zipWith (fun (n : ℕ+) (j : ℕ) => ((n : ℕ).choose j : ℚ)) μ js).prod *
        (((List.zipWith (fun (m : ℕ+) (k : ℤ) => binom (-k - 1) ((m : ℤ) - 1)) (js.map Nat.toPNat') ks).prod : ℤ) : ℚ)) • nablas ks b := by
    intro js hjs
    have hl : js.length = μ.length := by
      have := ((mem_tuples _ _).1 hjs).length_eq
      simpa using this
    rw [opFacts.mono, opMon_eq_sum h _ b hb, List.length_map, hl, smul_sum]
    refine sum_congr rfl fun ks hks => ?_
    rw [term_pos _ _ _ ((mem_posTuples _ _ _).1 hks).2.1, smul_smul]
  rw [sum_congr rfl h1, sum_comm]
  refine sum_congr rfl fun ks hks => ?_
  rw [← sum_smul, sum_coeff μ ks ((mem_posTuples _ _ _).1 hks).1]

/-! ## Only one term is not zero -/

/-- «So a nonzero term has k_i ≥ μ_i for all i». -/
theorem le_of_prod_ne_zero (μ : List ℕ+) (ks : List ℤ) (hl : ks.length = μ.length) (hpos : ∀ k ∈ ks, 1 ≤ k)
    (h : (List.zipWith theta μ ks).prod ≠ 0) : List.Forall₂ (fun (n : ℕ+) (k : ℤ) => (n : ℤ) ≤ k) μ ks := by
  induction μ generalizing ks with
  | nil =>
    have : ks = [] := List.length_eq_zero_iff.1 hl
    subst this
    exact List.Forall₂.nil
  | cons n μ ih =>
    cases ks with
    | nil => simp at hl
    | cons k ks =>
      rw [List.zipWith_cons_cons, List.prod_cons] at h
      refine List.Forall₂.cons ?_ (ih ks (by simpa using hl) (fun x hx => hpos x (List.mem_cons_of_mem _ hx)) (right_ne_zero_of_mul h))
      by_contra hc
      exact left_ne_zero_of_mul h (theta_of_lt n k (hpos k List.mem_cons_self) (by omega))

theorem sum_le_of_forall₂ (μ : List ℕ+) (ks : List ℤ) (h : List.Forall₂ (fun (n : ℕ+) (k : ℤ) => (n : ℤ) ≤ k) μ ks) :
    (μ.map fun n : ℕ+ => (n : ℤ)).sum ≤ ks.sum := by
  induction h with
  | nil => simp
  | cons h1 _ ih => simp only [List.map_cons, List.sum_cons]; omega

/-- «… hence k_i = μ_i, because both add up to h.» -/
theorem eq_of_forall₂_le (μ : List ℕ+) (ks : List ℤ) (h : List.Forall₂ (fun (n : ℕ+) (k : ℤ) => (n : ℤ) ≤ k) μ ks)
    (hs : ks.sum = (μ.map fun n : ℕ+ => (n : ℤ)).sum) : ks = μ.map fun n : ℕ+ => (n : ℤ) := by
  induction h with
  | nil => rfl
  | cons h1 h2 ih =>
    have h3 := sum_le_of_forall₂ _ _ h2
    rw [List.map_cons, List.sum_cons, List.sum_cons] at hs
    rw [List.map_cons, ← ih (by omega)]
    congr 1
    omega

/-- |μ| as a sum of integers. -/
theorem sum_cast (μ : List ℕ+) : (μ.map fun n : ℕ+ => (n : ℤ)).sum = (wt (μ : Multiset ℕ+) : ℤ) := by
  induction μ with
  | nil => simp [wt]
  | cons n μ ih =>
    have : wt ((n :: μ : List ℕ+) : Multiset ℕ+) = (n : ℕ) + wt (μ : Multiset ℕ+) := by simp [wt]
    rw [List.map_cons, List.sum_cons, ih, this]; push_cast; rfl

/-- The product of the signs (−1)^{μ_i−1}. -/
def sgn (μ : List ℕ+) : ℤ := (μ.map fun n : ℕ+ => (-1 : ℤ) ^ ((n : ℕ) - 1)).prod

theorem sgn_mul_self (μ : List ℕ+) : sgn μ * sgn μ = 1 := by
  induction μ with
  | nil => simp [sgn]
  | cons n μ ih =>
    have h1 : sgn (n :: μ) = (-1 : ℤ) ^ ((n : ℕ) - 1) * sgn μ := by simp [sgn]
    have h2 : ((-1 : ℤ) ^ ((n : ℕ) - 1)) * ((-1 : ℤ) ^ ((n : ℕ) - 1)) = 1 := by rw [← mul_pow]; simp
    calc sgn (n :: μ) * sgn (n :: μ) = (((-1 : ℤ) ^ ((n : ℕ) - 1)) * ((-1 : ℤ) ^ ((n : ℕ) - 1))) * (sgn μ * sgn μ) := by rw [h1]; ring
      _ = 1 := by rw [h2, ih]; norm_num

/-- At k_i = μ_i the coefficient is the product of the signs. -/
theorem prod_theta_self (μ : List ℕ+) : (List.zipWith theta μ (μ.map fun n : ℕ+ => (n : ℤ))).prod = sgn μ := by
  induction μ with
  | nil => simp [sgn]
  | cons n μ ih =>
    have h1 : sgn (n :: μ) = (-1 : ℤ) ^ ((n : ℕ) - 1) * sgn μ := by simp [sgn]
    rw [List.map_cons, List.zipWith_cons_cons, List.prod_cons, ih, theta_self, h1]

/-- The display has one term: (∏_i y_{μ_i})[−h]·b = ∏_i (−1)^{μ_i−1}·∏_i ∇_{μ_i} b, for a partition
μ of h and b ∈ V_h. -/
theorem display_single (h : ℕ) (μ : List ℕ+) (hμ : wt (μ : Multiset ℕ+) = h) (b : V) (hb : b ∈ VE h) :
    op (μ.map y).prod (-(h : ℤ)) b = (sgn μ : ℚ) • nablas (μ.map fun n : ℕ+ => (n : ℤ)) b := by
  rw [display h μ b hb, sum_eq_single (μ.map fun n : ℕ+ => (n : ℤ)), prod_theta_self]
  · intro ks hks hne
    obtain ⟨hl, hpos, hs⟩ := (mem_posTuples _ _ _).1 hks
    have h0 : (List.zipWith theta μ ks).prod = 0 := by
      by_contra hc
      exact hne (eq_of_forall₂_le μ ks (le_of_prod_ne_zero μ ks hl hpos hc) (by rw [hs, sum_cast, hμ]))
    rw [h0]; simp
  · intro hn
    exfalso
    apply hn
    rw [mem_posTuples]
    refine ⟨by simp, ?_, by rw [sum_cast, hμ]⟩
    intro k hk
    obtain ⟨n, _, rfl⟩ := List.mem_map.1 hk
    exact_mod_cast n.pos

/-- a^μ is the product of the signs times ∏ y_{μ_i}. -/
theorem aFam_eq (μ : List ℕ+) : aFam (μ : Multiset ℕ+) = (sgn μ : ℚ) • (μ.map y).prod := by
  unfold aFam
  rw [Multiset.map_coe, Multiset.prod_coe]
  induction μ with
  | nil => simp [sgn]
  | cons n μ ih =>
    have h1 : sgn (n :: μ) = (-1 : ℤ) ^ ((n : ℕ) - 1) * sgn μ := by simp [sgn]
    rw [List.map_cons, List.prod_cons, ih, List.map_cons, List.prod_cons, smul_mul_smul_comm, h1]
    push_cast
    rfl

/-- «Therefore a^μ[−h]·b = ∏_i ∇_{μ_i} b.» -/
theorem aFam_op (h : ℕ) (μ : List ℕ+) (hμ : wt (μ : Multiset ℕ+) = h) (b : V) (hb : b ∈ VE h) :
    op (aFam (μ : Multiset ℕ+)) (-(h : ℤ)) b = nablas (μ.map fun n : ℕ+ => (n : ℤ)) b := by
  rw [aFam_eq, opFacts.smul_left, display_single h μ hμ b hb, smul_smul]
  have : (sgn μ : ℚ) * (sgn μ : ℚ) = 1 := by exact_mod_cast sgn_mul_self μ
  rw [this, one_smul]

/-! ## The value at b = t^ν -/

theorem pn_coe (n : ℕ+) : pn (n : ℤ) = n := by simp [pn]

/-- ∇_n t^ν = n·m_n(ν)·t^{ν−n}, where ν − n is ν without one part n. -/
theorem nabla_tpow (n : ℕ+) (ν : Ptn) : nabla (n : ℤ) (tpow ν) = (((n : ℕ) : ℚ) * (ν.count n : ℚ)) • tpow (ν.erase n) := by
  have hpos : (0 : ℤ) < (n : ℤ) := by exact_mod_cast n.pos
  have e : Multiset.toFinsupp ν - Finsupp.single n 1 = Multiset.toFinsupp (ν.erase n) := by
    ext a
    rw [Finsupp.tsub_apply, Multiset.toFinsupp_apply, Multiset.toFinsupp_apply, Finsupp.single_apply]
    by_cases h : n = a
    · subst h; simp
    · rw [if_neg h, Multiset.count_erase_of_ne (Ne.symm h)]; simp
  rw [nabla, if_neg (by omega), if_pos hpos, pn_coe, tpow, pderiv_monomial, e, tpow, smul_monomial, smul_monomial, Multiset.toFinsupp_apply]
  congr 1
  simp

/-- ∇_k is linear. -/
theorem nabla_smul (k : ℤ) (q : ℚ) (f : V) : nabla k (q • f) = q • nabla k f := by
  unfold nabla
  split_ifs
  · rw [mul_smul_comm]
  · rw [Derivation.map_smul, smul_comm]
  · simp

theorem nablas_smul (ks : List ℤ) (q : ℚ) (f : V) : nablas ks (q • f) = q • nablas ks f := by
  induction ks with
  | nil => rfl
  | cons k ks ih => simp only [nablas, List.foldr_cons] at ih ⊢; rw [ih, nabla_smul]

/-- The differentiation that is listed last is applied first. -/
theorem nablas_snoc_tpow (μ : List ℕ+) (n : ℕ+) (ν : Ptn) : nablas ((μ ++ [n]).map fun n : ℕ+ => (n : ℤ)) (tpow ν) =
    (((n : ℕ) : ℚ) * (ν.count n : ℚ)) • nablas (μ.map fun n : ℕ+ => (n : ℤ)) (tpow (ν.erase n)) := by
  rw [← nablas_smul, ← nabla_tpow]
  simp [nablas, List.foldr_append]

theorem coe_snoc (μ : List ℕ+) (n : ℕ+) : ((μ ++ [n] : List ℕ+) : Multiset ℕ+) = n ::ₘ (μ : Multiset ℕ+) := by
  rw [← Multiset.coe_add, Multiset.coe_singleton, add_comm, Multiset.singleton_add]

/-- «For b = t^ν this is 0 if m_k(μ) > m_k(ν) for some k». -/
theorem nablas_tpow_eq_zero (μ : List ℕ+) (ν : Ptn) (k : ℕ+) (h : ν.count k < (μ : Multiset ℕ+).count k) :
    nablas (μ.map fun n : ℕ+ => (n : ℤ)) (tpow ν) = 0 := by
  induction μ using List.reverseRecOn generalizing ν with
  | nil => simp at h
  | append_singleton μ n ih =>
    rw [nablas_snoc_tpow]
    by_cases hn : n ∈ ν
    · rw [ih (ν.erase n) ?_, smul_zero]
      rw [coe_snoc, Multiset.count_cons] at h
      by_cases hkn : k = n
      · subst hkn
        have := Multiset.count_pos.2 hn
        rw [Multiset.count_erase_self]
        simp only [if_true] at h
        omega
      · rw [Multiset.count_erase_of_ne hkn]
        simpa [hkn] using h
    · rw [Multiset.count_eq_zero_of_notMem hn]; simp

/-- «… otherwise μ = ν, because |μ| = |ν|». -/
theorem eq_of_count_le (μ ν : Ptn) (hc : ∀ k, μ.count k ≤ ν.count k) (hw : wt μ = wt ν) : μ = ν := by
  obtain ⟨ρ, rfl⟩ := Multiset.le_iff_exists_add.1 (Multiset.le_iff_count.2 hc)
  rcases Multiset.empty_or_exists_mem ρ with rfl | ⟨a, ha⟩
  · simp
  · obtain ⟨t, rfl⟩ := Multiset.exists_cons_of_mem ha
    have := a.pos
    simp only [wt, Multiset.map_add, Multiset.sum_add, Multiset.map_cons, Multiset.sum_cons] at hw
    omega

theorem zz_eq_prod {ν : Ptn} {S : Finset ℕ+} (h : ν.toFinset ⊆ S) : zz ν = ∏ k ∈ S, (k : ℕ) ^ ν.count k * (ν.count k).factorial := by
  unfold zz
  refine prod_subset h fun k _ hk => ?_
  rw [Multiset.count_eq_zero_of_notMem fun h' => hk (Multiset.mem_toFinset.2 h')]
  simp

/-- z_ν = n·m_n(ν)·z_{ν−n}. -/
theorem zz_erase {ν : Ptn} {n : ℕ+} (hn : n ∈ ν) : zz ν = (n : ℕ) * ν.count n * zz (ν.erase n) := by
  have hS : (ν.erase n).toFinset ⊆ ν.toFinset := fun k hk =>
    Multiset.mem_toFinset.2 (Multiset.mem_of_mem_erase (Multiset.mem_toFinset.1 hk))
  have hn' := Multiset.mem_toFinset.2 hn
  rw [zz_eq_prod hS, zz, ← mul_prod_erase _ _ hn', ← mul_prod_erase _ (fun k : ℕ+ => (k : ℕ) ^ (ν.erase n).count k * ((ν.erase n).count k).factorial) hn']
  have h1 : ∏ k ∈ ν.toFinset.erase n, (k : ℕ) ^ (ν.erase n).count k * ((ν.erase n).count k).factorial
      = ∏ k ∈ ν.toFinset.erase n, (k : ℕ) ^ ν.count k * (ν.count k).factorial :=
    prod_congr rfl fun k hk => by rw [Multiset.count_erase_of_ne (ne_of_mem_erase hk)]
  obtain ⟨c, hc⟩ : ∃ c, ν.count n = c + 1 := ⟨ν.count n - 1, by have := Multiset.count_pos.2 hn; omega⟩
  rw [h1, Multiset.count_erase_self, hc, Nat.add_sub_cancel, pow_succ, Nat.factorial_succ]
  ring

/-- «… and it is z_μ.» -/
theorem nablas_tpow_self (μ : List ℕ+) : nablas (μ.map fun n : ℕ+ => (n : ℤ)) (tpow (μ : Multiset ℕ+)) = C (zz (μ : Multiset ℕ+) : ℚ) := by
  induction μ using List.reverseRecOn with
  | nil => simp [nablas, tpow, zz]
  | append_singleton μ n ih =>
    rw [nablas_snoc_tpow, coe_snoc, Multiset.erase_cons_head, ih, zz_erase (Multiset.mem_cons_self n _), Multiset.erase_cons_head,
      smul_eq_C_mul, ← C_mul]
    push_cast
    rfl

/-- The last sentence of the proof: for partitions μ, ν of the same number, ∏_i ∇_{μ_i} t^ν = z_μ·[μ =
ν]. -/
theorem nablas_tpow (μ : List ℕ+) (ν : Ptn) (hw : wt (μ : Multiset ℕ+) = wt ν) :
    nablas (μ.map fun n : ℕ+ => (n : ℤ)) (tpow ν) = C (if (μ : Multiset ℕ+) = ν then (zz (μ : Multiset ℕ+) : ℚ) else 0) := by
  by_cases h : ∃ k, ν.count k < (μ : Multiset ℕ+).count k
  · obtain ⟨k, hk⟩ := h
    have hne : (μ : Multiset ℕ+) ≠ ν := fun he => by rw [he] at hk; omega
    rw [nablas_tpow_eq_zero μ ν k hk, if_neg hne, C_0]
  · have he : (μ : Multiset ℕ+) = ν := eq_of_count_le _ _ (fun k => not_lt.1 fun hk => h ⟨k, hk⟩) hw
    rw [if_pos he, ← he, nablas_tpow_self]

/-! ## The lemma -/

/-- The weight of the monomial t^ν is |ν|. -/
theorem weight_toFinsupp (ν : Ptn) : Finsupp.weight (fun k : ℕ+ => (k : ℕ)) (Multiset.toFinsupp ν) = wt ν := by
  induction ν using Multiset.induction_on with
  | empty => simp [wt]
  | cons a s ih =>
    rw [← Multiset.singleton_add, Multiset.toFinsupp_add, map_add, ih, Multiset.toFinsupp_singleton]
    simp [wt, Finsupp.weight_apply]

/-- t^ν ∈ V_{|ν|}. -/
theorem tpow_mem (ν : Ptn) : tpow ν ∈ VE (wt ν) := by
  rw [VE, if_pos (Int.natCast_nonneg _), Int.toNat_natCast, mem_weightedHomogeneousSubmodule]
  exact isWeightedHomogeneous_monomial _ _ _ (weight_toFinsupp ν)

theorem zz_pos (μ : Ptn) : 0 < zz μ :=
  prod_pos fun k _ => Nat.mul_pos (pow_pos k.pos _) (Nat.factorial_pos _)

/-- Lemma 10: a^μ[−h]·b^ν = h!·[μ = ν] for all partitions μ, ν of h. -/
theorem lemmaDual : LemmaDual := by
  intro h μ ν hμ hν
  obtain ⟨l, rfl⟩ : ∃ l : List ℕ+, (l : Multiset ℕ+) = μ := ⟨μ.toList, Multiset.coe_toList μ⟩
  have hb : bFam ν ∈ VE h := by rw [← hν]; exact Submodule.smul_mem _ _ (tpow_mem ν)
  rw [aFam_op h l hμ _ hb, bFam, nablas_smul, nablas_tpow l ν (by rw [hμ, hν]), smul_eq_C_mul, ← C_mul]
  congr 1
  split_ifs with he
  · rw [← he, hμ]
    exact div_mul_cancel₀ _ (by exact_mod_cast (zz_pos _).ne')
  · simp

/-- z_μ equals `ClauseBound.Boson.zz`, the number of that name where the parts are natural numbers. -/
theorem zz_eq (μ : Ptn) : zz μ = ClauseBound.Boson.zz (μ.map fun k : ℕ+ => (k : ℕ)) := by
  unfold zz ClauseBound.Boson.zz
  rw [Multiset.toFinset_map, prod_image PNat.coe_injective.injOn]
  refine prod_congr rfl fun k _ => ?_
  rw [Multiset.count_map_eq_count' _ _ PNat.coe_injective]

/-- «Here h!/z_μ is an integer»: z_μ divides |μ|!. The paper cites this; the proof here is
`ClauseBound.Boson.zz_dvd_factorial`. -/
theorem zDvd : ZDvd := fun μ => by
  rw [zz_eq]
  exact ClauseBound.Boson.zz_dvd_factorial (h := wt μ)
    ⟨μ.map fun k : ℕ+ => (k : ℕ), fun {i} hi => by obtain ⟨k, _, rfl⟩ := Multiset.mem_map.1 hi; exact k.pos, rfl⟩

end GeneralPieces.Dual
