/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Price.BorderSum

/-!
# The choice among a few terms

A spectral point at a sum of |J| terms, exact or up to ε: the choice of the term costs |J| only to the exponent of
the unit tensor on the parties that hold legs. Proof: tensor powers, types of words, N-th roots.
-/

namespace Nc.Price

open Ov Ov.Ten Finset Polynomial

variable {K : Type} [Field K] {I A κ : Type} [Fintype I] [DecidableEq I] [Fintype A] [DecidableEq A] [Fintype κ]

/-- The exponent of a unit tensor is not negative. -/
theorem few_hexp_nonneg [Nonempty I] (F : Spec K I) (π : A → I) : 0 ≤ hexp F π :=
  Real.logb_nonneg (by norm_num) (F.one_le_unit π (by norm_num))

/-- The number of times a word uses each letter. -/
noncomputable def wordType {N : ℕ} (w : Fin N → κ) : κ → Fin (N + 1) :=
  open Classical in fun k => ⟨#{i | w i = k}, Nat.lt_succ_of_le ((card_le_univ _).trans_eq (Fintype.card_fin N))⟩

omit [Fintype κ] in
/-- Words of one type differ by a permutation of the places. -/
theorem exists_perm_of_wordType {N : ℕ} {w w₀ : Fin N → κ} (h : wordType w = wordType w₀) :
    ∃ σ : Equiv.Perm (Fin N), w₀ ∘ σ = w := by
  classical
  have hc : ∀ k, Fintype.card {i // w i = k} = Fintype.card {i // w₀ i = k} := fun k => by
    rw [Fintype.card_subtype, Fintype.card_subtype]
    exact congrArg Fin.val (congr_fun h k)
  exact ⟨Equiv.ofFiberEquiv fun k => Fintype.equivOfCardEq (hc k),
    funext fun i => Equiv.ofFiberEquiv_map _ i⟩

/-- For r orders ρ m of the places, the sum over m of the images of a
product, with the places in the order ρ m, is one image of the product times the unit tensor of size r on the
parties that hold legs. So a spectral point is at most (E + 1) ^ #parties · r ^ g · ∏ at the coefficient of ε ^ E. -/
theorem le_type_bound (F : Spec K I) [Nonempty A] (π : A → I) (t : Ten K I)
    (ht : ∀ q, q ∉ Set.range π → Subsingleton (t.ι q)) {N E r : ℕ} (hr : 1 ≤ r) (c : Fin N → Ten K I)
    (L : ∀ j p, t.ι p → (c j).ι p → Polynomial K) (ρ : Fin r → Equiv.Perm (Fin N))
    (v : (∀ p, Fin N → t.ι p) → K)
    (hv : ∀ x, v x = (∑ m, ∏ j, polyApp (c j) (L j) fun p => x p (ρ m j)).coeff E) :
    F.F ((Ten.kpow t N).withVal v) ≤
      ((E : ℝ) + 1) ^ Fintype.card I * ((r : ℝ) ^ hexp F π * ∏ j, F.F (c j)) := by
  classical
  have hI : Nonempty I := ⟨π (Classical.arbitrary A)⟩
  let pick : ∀ q, ({a : A // π a = q} → Fin r) → Equiv.Perm (Fin N) := fun q u =>
    if h : ∃ a, π a = q then ρ (u ⟨h.choose, h.choose_spec⟩) else 1
  let z : Ten K I := Ten.push π (unit K A r) * Ten.prod c
  let Φ : ∀ q, (Fin N → t.ι q) → z.ι q → Polynomial K := fun q a y =>
    ∏ j, L j q (a (pick q y.1 j)) (y.2 j)
  have key : ∀ x, ∑ m, ∏ j, polyApp (c j) (L j) (fun p => x p (ρ m j)) = polyApp z Φ x := by
    intro x
    let f : (A → Fin r) → Polynomial K := fun u =>
      C ((unit K A r).val u) * ∏ j, polyApp (c j) (L j) fun q => x q (pick q (fun a => u a.1) j)
    have e1 : polyApp z Φ x = ∑ u, f u := by
      have e : ∀ u, f u = ∑ y : ∀ q, (Ten.prod c).ι q,
          (∏ q, ∏ j, L j q (x q (pick q (fun a => u a.1) j)) (y q j)) *
            C ((unit K A r).val u * (Ten.prod c).val y) := by
        intro u
        show C _ * _ = _
        rw [← polyApp_prod (α := fun _ q => t.ι q) c L fun q j => x q (pick q (fun a => u a.1) j), polyApp,
          Finset.mul_sum]
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [map_mul]
        exact mul_left_comm _ _ _
      simp only [e]
      rw [← Fintype.sum_prod_type']
      refine Fintype.sum_equiv
        ((Equiv.arrowProdEquivProdArrow (α := I) (fun q => {a : A // π a = q} → Fin r)
          fun q => (Ten.prod c).ι q).trans
          (Equiv.prodCongr (pushEquiv π fun _ : A => Fin r) (Equiv.refl _))) _ _ fun y => ?_
      have hfib : ∀ q, (fun a : {a : A // π a = q} => (y (π a.1)).1 ⟨a.1, rfl⟩) = (y q).1 := by
        intro q
        funext a
        obtain ⟨a, rfl⟩ := a
        rfl
      show (∏ q, ∏ j, L j q (x q (pick q (y q).1 j)) ((y q).2 j)) * C _ =
        (∏ q, ∏ j, L j q (x q (pick q (fun a => (y (π a.1)).1 ⟨a.1, rfl⟩) j)) ((y q).2 j)) * C _
      simp only [hfib]
      rfl
    rw [e1]
    refine Finset.sum_of_injOn (fun m _ => m) (fun m _ m' _ h => congr_fun h (Classical.arbitrary A))
      (fun _ _ => by simp) (fun u _ hu => ?_) fun m _ => ?_
    · show C _ * _ = 0
      rw [unit_val_not, map_zero, zero_mul]
      intro h
      exact hu ⟨u (Classical.arbitrary A), by simp, funext fun a => h _ _⟩
    · show _ = C _ * _
      rw [unit_val_of (fun _ _ => rfl), map_one, one_mul]
      refine Finset.prod_congr rfl fun j _ => congr_arg _ (funext fun q => ?_)
      by_cases hq : ∃ a, π a = q
      · simp only [pick, dif_pos hq]
      · have := ht q fun ⟨a, ha⟩ => hq ⟨a, ha⟩
        exact Subsingleton.elim _ _
  refine (le_coeff F (s := (Ten.kpow t N).withVal v) (D := E) Φ fun x =>
    (hv x).trans (congr_arg (fun P => Polynomial.coeff P E) (key x))).trans (le_of_eq ?_)
  rw [F.mul, F.prod, F.unit_eq π hr]
  rfl

/-- A bound for all powers with a factor polynomial in N holds without the
factor. -/
theorem le_of_pow_le_poly {x B C : ℝ} (a : ℕ) (hB : 0 ≤ B)
    (h : ∀ N : ℕ, x ^ N ≤ C * ((N : ℝ) + 1) ^ a * B ^ N) : x ≤ B := by
  by_contra hlt
  rw [not_le] at hlt
  have hx : 0 < x := hB.trans_lt hlt
  have hr : B / x < 1 := (div_lt_one hx).2 hlt
  have hr0 : 0 ≤ B / x := by positivity
  have hlim : Filter.Tendsto (fun N : ℕ => C * 2 ^ a * ((N : ℝ) ^ a * (B / x) ^ N)) Filter.atTop (nhds 0) := by
    simpa using (tendsto_pow_const_mul_const_pow_of_lt_one a hr0 hr).const_mul (C * 2 ^ a)
  obtain ⟨N, hN, hN1⟩ := ((hlim.eventually (eventually_lt_nhds one_pos)).and (Filter.eventually_ge_atTop 1)).exists
  have hC : 0 ≤ C := by
    have := h 0
    simp only [pow_zero, Nat.cast_zero, zero_add, one_pow, mul_one] at this
    linarith
  have h1 : (1 : ℝ) ≤ C * ((N : ℝ) + 1) ^ a * (B / x) ^ N := by
    rw [div_pow, mul_div_assoc', le_div_iff₀ (pow_pos hx N), one_mul]
    exact h N
  have h2 : C * ((N : ℝ) + 1) ^ a * (B / x) ^ N ≤ C * 2 ^ a * ((N : ℝ) ^ a * (B / x) ^ N) := by
    have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
    rw [← mul_assoc, mul_assoc C (2 ^ a) _, ← mul_pow]
    gcongr
    linarith
  linarith

/-- The N-th power of the value at t is at most the number of types times the
factor of the extraction times (|κ| ^ g · M) ^ N. -/
theorem pow_le_few (F : Spec K I) [Nonempty A] [Nonempty κ] (π : A → I) (t : Ten K I)
    (ht : ∀ q, q ∉ Set.range π → Subsingleton (t.ι q)) {b : κ → Ten K I} {D : ℕ} (h : BSum D t b) {M : ℝ}
    (hM : ∀ k, F.F (b k) ≤ M) (N : ℕ) :
    F.F t ^ N ≤ ((N : ℝ) + 1) ^ Fintype.card κ * (((N * D : ℕ) : ℝ) + 1) ^ Fintype.card I *
      ((Fintype.card κ : ℝ) ^ hexp F π * M) ^ N := by
  classical
  have hI : Nonempty I := ⟨π (Classical.arbitrary A)⟩
  have hM0 : 0 ≤ M := (F.nonneg _).trans (hM (Classical.arbitrary κ))
  obtain ⟨L₁, hL₁⟩ := h
  set B := (Fintype.card κ : ℝ) ^ hexp F π * M with hB
  let G : (Fin N → κ) → (∀ p, Fin N → t.ι p) → Polynomial K := fun w x =>
    ∏ i, polyApp (b (w i)) (L₁ (w i)) fun p => x p i
  let v : (κ → Fin (N + 1)) → (∀ p, Fin N → t.ι p) → K := fun τ x =>
    (∑ w : {w : Fin N → κ // wordType w = τ}, G w x).coeff (N * D)
  have hsum : ∀ x, (Ten.kpow t N).val x = ∑ τ, v τ x := by
    intro x
    refine ((coeff_sum_words hL₁ N x le_rfl).trans (if_pos rfl)).symm.trans ?_
    show _ = ∑ τ, (∑ w : {w : Fin N → κ // wordType w = τ}, G w x).coeff (N * D)
    rw [← Polynomial.finsetSum_coeff]
    exact congr_arg (fun P => Polynomial.coeff P _)
      (Fintype.sum_fiberwise (wordType (N := N) (κ := κ)) fun w => G w x).symm
  rw [← F.kpow]
  refine (F.le_sum_val _ v hsum).trans ?_
  refine (Finset.sum_le_card_nsmul _ _ ((((N * D : ℕ) : ℝ) + 1) ^ Fintype.card I * B ^ N) fun τ _ => ?_).trans
    (le_of_eq ?_)
  · rcases isEmpty_or_nonempty {w : Fin N → κ // wordType w = τ} with he | ⟨⟨w₀, hw₀⟩⟩
    · have h0 : ∀ x, v τ x = 0 := fun x => by
        show Polynomial.coeff (∑ w : {w : Fin N → κ // wordType w = τ}, G w x) (N * D) = 0
        rw [Finset.univ_eq_empty, Finset.sum_empty, coeff_zero]
      rw [F.zero h0]
      positivity
    let W := {w : Fin N → κ // wordType w = τ}
    let num := Fintype.equivFin W
    have hσ : ∀ m, ∃ σ : Equiv.Perm (Fin N), w₀ ∘ σ = (num.symm m).1 := fun m =>
      exists_perm_of_wordType ((num.symm m).2.trans hw₀.symm)
    choose σ hσ using hσ
    have hr : 1 ≤ Fintype.card W := Fintype.card_pos_iff.2 ⟨⟨w₀, hw₀⟩⟩
    have hv : ∀ x, v τ x =
        (∑ m, ∏ j, polyApp (b (w₀ j)) (L₁ (w₀ j)) fun p => x p ((σ m).symm j)).coeff (N * D) := by
      intro x
      refine congr_arg (fun P => Polynomial.coeff P _) (Fintype.sum_equiv num _ _ fun w => ?_)
      refine Fintype.prod_equiv (σ (num w)) _ _ fun i => ?_
      have := congr_fun (hσ (num w)) i
      simp only [Function.comp_apply, Equiv.symm_apply_apply] at this ⊢
      rw [this]
    refine (le_type_bound F π t ht hr (fun j => b (w₀ j)) (fun j => L₁ (w₀ j)) (fun m => (σ m).symm) _
      hv).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [hB, mul_pow, ← Real.rpow_natCast ((Fintype.card κ : ℝ) ^ hexp F π), ← Real.rpow_mul (by positivity),
      mul_comm (hexp F π), Real.rpow_mul (by positivity), Real.rpow_natCast]
    refine mul_le_mul (Real.rpow_le_rpow (by positivity) ?_ (few_hexp_nonneg F π)) ?_
      (Finset.prod_nonneg fun _ _ => F.nonneg _) (by positivity)
    · exact_mod_cast (Fintype.card_subtype_le _).trans_eq (by simp)
    · exact (Finset.prod_le_prod (fun _ _ => F.nonneg _) fun j _ => hM _).trans (by simp)
  · rw [nsmul_eq_mul, Finset.card_univ, Fintype.card_fun, Fintype.card_fin]
    push_cast
    ring

/-- The choice among |κ| terms, exact or up to ε, costs only the exponent of the unit tensor on
the parties that hold legs: if t is a sum of restrictions of the b k up to ε, every b k has value at most M, and
outside the range of π all legs of t are trivial, then t has value at most |κ| ^ g · M. -/
theorem few (F : Spec K I) [Nonempty I] [Nonempty κ] (π : A → I) (t : Ten K I)
    (ht : ∀ q, q ∉ Set.range π → Subsingleton (t.ι q))
    {b : κ → Ten K I} {D : ℕ} (h : BSum D t b) {M : ℝ} (hM : ∀ k, F.F (b k) ≤ M) :
    F.F t ≤ (Fintype.card κ : ℝ) ^ hexp F π * M := by
  have hM0 : 0 ≤ M := (F.nonneg _).trans (hM (Classical.arbitrary κ))
  have hB : 0 ≤ (Fintype.card κ : ℝ) ^ hexp F π * M := by positivity
  rcases isEmpty_or_nonempty A with hA | hA
  · have hsub : ∀ q, Subsingleton (t.ι q) := fun q => ht q (by simp [Set.range_eq_empty])
    by_cases h0 : ∀ x, t.val x = 0
    · rw [F.zero h0]
      exact hB
    obtain ⟨x, hx⟩ := not_forall.1 h0
    have h1 : F.F t ≤ 1 := by
      refine (F.le_card t).trans ?_
      exact_mod_cast Fintype.card_le_one_iff_subsingleton.2 (@Pi.instSubsingleton I t.ι hsub)
    obtain ⟨L, hL⟩ := h
    have hk : ∃ k y, (b k).val y ≠ 0 := by
      by_contra hne
      push Not at hne
      exact hx (by have := (hL x D le_rfl).trans (if_pos rfl); simpa [hne] using this.symm)
    obtain ⟨k, y, hy⟩ := hk
    refine h1.trans (one_le_mul_of_one_le_of_one_le ?_ ((F.one_le hy).trans (hM k)))
    exact Real.one_le_rpow (by exact_mod_cast Fintype.card_pos) (few_hexp_nonneg F π)
  · refine le_of_pow_le_poly (C := ((D : ℝ) + 1) ^ Fintype.card I)
      (Fintype.card κ + Fintype.card I) hB fun N => ?_
    refine (pow_le_few F π t ht h hM N).trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
    have h2 : ((N * D : ℕ) : ℝ) + 1 ≤ ((D : ℝ) + 1) * ((N : ℝ) + 1) := by
      push_cast
      nlinarith [Nat.cast_nonneg (α := ℝ) N, Nat.cast_nonneg (α := ℝ) D]
    calc ((N : ℝ) + 1) ^ Fintype.card κ * (((N * D : ℕ) : ℝ) + 1) ^ Fintype.card I
        ≤ ((N : ℝ) + 1) ^ Fintype.card κ * (((D : ℝ) + 1) * ((N : ℝ) + 1)) ^ Fintype.card I := by gcongr
      _ = ((D : ℝ) + 1) ^ Fintype.card I * ((N : ℝ) + 1) ^ (Fintype.card κ + Fintype.card I) := by
        rw [mul_pow, pow_add]
        ring

/-- An exact sum of restrictions is a sum up to ε with denominators 1. -/
theorem BSum.of_sumRestr {t : Ten K I} {b : κ → Ten K I} (h : SumRestr t b) : BSum 0 t b := by
  obtain ⟨L, hL⟩ := h
  refine ⟨fun k p a c => C (L k p a c), fun x i hi => ?_⟩
  obtain rfl : i = 0 := Nat.le_zero.1 hi
  simp [hL x, app, Polynomial.coeff_zero_prod]

end Nc.Price
