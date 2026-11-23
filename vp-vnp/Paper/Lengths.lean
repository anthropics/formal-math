/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Paper.Alternative
import Nc.Flag.Main
import Nc.Flag.Words

/-!
# The paper, subsection "Lengths": the remark on maps into price spaces, polynomial growth and rank one

The third lemma of the subsection (lem:first) is in Paper/Groups.lean.
-/

namespace Paper

open Finset Nc.Flag Nc.Price
open Nc.Tower (U x lo hi)

/-- The mean of f² over the matrices of rank r. -/
noncomputable def rankMean {k : ℕ} (f : Mt k → ℝ) (r : ℕ) : ℝ :=
  (∑ W ∈ (univ : Finset (Mt k)).filter (fun W => W.rank = r), f W ^ 2) /
    ((univ : Finset (Mt k)).filter (fun W => W.rank = r)).card

theorem rankMean_nonneg {k : ℕ} (f : Mt k → ℝ) (r : ℕ) : 0 ≤ rankMean f r :=
  div_nonneg (sum_nonneg fun _ _ => sq_nonneg _) (Nat.cast_nonneg _)

theorem DM_eq_rankMean {k : ℕ} (f : Mt k → ℝ) (S : Finset (Fin k)) :
    DM f (dg S) = (Fintype.card (GLM (Fin k)) : ℝ) ^ 2 * rankMean f S.card := by
  have hn : (0 : ℝ) < ((univ : Finset (Mt k)).filter fun W => W.rank = S.card).card := by
    exact_mod_cast card_pos.2 ⟨dg S, mem_filter.2 ⟨mem_univ _, rank_dg S⟩⟩
  rw [rankMean, ← mul_div_assoc, eq_div_iff hn.ne', mul_comm]
  exact card_mul_DM f S

/-- A length contracts: "for every homomorphism τ from the additive group Mat_μ(F₂) into the group, the mean of |τW|²
over rank μ is at most s² times that over rank 1". It is the project's Contr. -/
theorem contracts_iff {G : Type} [Group G] (l : Len G) {μ : ℕ} (hμ : 1 ≤ μ) (s : ℝ) :
    Contr l μ s ↔ ∀ τ : Mt μ → G, (∀ M N, τ (M + N) = τ M * τ N) →
      rankMean (fun W => l.val (τ W)) μ ≤ s ^ 2 * rankMean (fun W => l.val (τ W)) 1 := by
  have hg : (0 : ℝ) < (Fintype.card (GLM (Fin μ)) : ℝ) ^ 2 := by
    have : (0 : ℝ) < Fintype.card (GLM (Fin μ)) := by exact_mod_cast Fintype.card_pos
    positivity
  have key : ∀ (f : Mt μ → ℝ) (i : Fin μ),
      DM f (dg univ) ≤ s ^ 2 * DM f (dg {i}) ↔ rankMean f μ ≤ s ^ 2 * rankMean f 1 := fun f i => by
    rw [DM_eq_rankMean, DM_eq_rankMean, card_singleton, card_univ, Fintype.card_fin, mul_left_comm,
      mul_le_mul_iff_right₀ hg]
  exact ⟨fun h τ hτ => (key _ ⟨0, hμ⟩).1 (h τ hτ _), fun h τ hτ i => (key _ i).2 (h τ hτ)⟩

/-- A multiple of a contracting length contracts. -/
theorem contracts_smul {G : Type} [Group G] (l l' : Len G) {μ : ℕ} (hμ : 1 ≤ μ) {s : ℝ} {c : ℝ}
    (h : ∀ g, l'.val g = c * l.val g) (hl : Contr l μ s) : Contr l' μ s := by
  refine (contracts_iff l' hμ s).2 fun τ hτ => ?_
  have e : ∀ r, rankMean (fun W => l'.val (τ W)) r = c ^ 2 * rankMean (fun W => l.val (τ W)) r := fun r => by
    simp only [rankMean, h, mul_pow, ← Finset.mul_sum, mul_div_assoc]
  rw [e, e, mul_left_comm (s ^ 2)]
  exact mul_le_mul_of_nonneg_left ((contracts_iff l hμ s).1 hl τ hτ) (sq_nonneg c)

/-- The remark after the definition of contracting lengths: "If a map f sends a finite group into a price space, then
|g| = (E_a|f(a)f(ga)|²)^(1/2) contracts: pull the price back along W ↦ f(τ(W)a) and average over a." -/
theorem lengths_of_maps {K : Type} [Field K] {μ : ℕ} {s : ℝ} (hμ : 1 ≤ μ) (hs : 0 ≤ s)
    (hcase : ∀ w : Mt μ → Mt μ → ℝ, IsPrice K w → distAtRank w μ ≤ s * distAtRank w 1)
    {G : Type} [Group G] [Fintype G] {Y : Type} [MetricSpace Y] (hY : IsPrice K fun a b : Y => dist a b)
    (f : G → Y) :
    ∃ l : Len G, (∀ g, l.val g = √((∑ a, dist (f a) (f (g * a)) ^ 2) / Fintype.card G)) ∧ Contr l μ s := by
  have hc : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  set l0 : Len G := (transAct G Y).len (WithLp.toLp 2 f) with hl0
  have hl : ∀ g, l0.val g ^ 2 = ∑ a, dist (f a) (f (g * a)) ^ 2 := fun g => by
    rw [hl0, IsoAct.len_val, transAct_dist]
    exact sum_congr rfl fun a _ => by rw [dist_comm]
  let l : Len G :=
    { val := fun g => l0.val g / √(Fintype.card G : ℝ)
      one' := by simp [l0.one']
      inv' := fun g => by rw [l0.inv']
      mul' := fun g g' => by
        rw [← add_div]
        exact div_le_div_of_nonneg_right (l0.mul' g g') (Real.sqrt_nonneg _) }
  refine ⟨l, fun g => ?_, (contracts_iff l hμ s).2 fun τ hτ => ?_⟩
  · rw [Real.sqrt_div' _ hc.le, ← hl, Real.sqrt_sq (l0.nonneg g)]
  have e : ∀ r, rankMean (fun W => l.val (τ W)) r =
      (∑ k : G, meanSq (fun a b => dist (f (τ a * k)) (f (τ b * k))) r) / Fintype.card G := by
    intro r
    have h1 : ∀ W, l.val (τ W) ^ 2 = l0.val (τ W) ^ 2 / Fintype.card G := fun W => by
      show (l0.val (τ W) / √(Fintype.card G : ℝ)) ^ 2 = _
      rw [div_pow, Real.sq_sqrt hc.le]
    have h2 : ∀ (W a : Mt μ), ∑ k : G, dist (f (τ a * k)) (f (τ (a + W) * k)) ^ 2 = l0.val (τ W) ^ 2 := by
      intro W a
      rw [hl, ← Equiv.sum_comp (Equiv.mulLeft (τ a)) (fun k => dist (f k) (f (τ W * k)) ^ 2)]
      refine sum_congr rfl fun k _ => ?_
      rw [add_comm a W, hτ, mul_assoc]
      rfl
    simp only [rankMean, meanSq, h1, ← Finset.sum_div]
    rw [Finset.sum_comm, sum_congr rfl fun a _ => Finset.sum_comm]
    simp only [h2, sum_const, card_univ, nsmul_eq_mul]
    have hM : (Fintype.card (Mt μ) : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    field_simp
  have h3 : ∀ k : G, meanSq (fun a b => dist (f (τ a * k)) (f (τ b * k))) μ ≤
      s ^ 2 * meanSq (fun a b => dist (f (τ a * k)) (f (τ b * k))) 1 := fun k => by
    have := hcase _ (hY.comp fun a => f (τ a * k))
    rwa [distAtRank, distAtRank, Real.sqrt_le_left (mul_nonneg hs (Real.sqrt_nonneg _)), mul_pow,
      Real.sq_sqrt (meanSq_nonneg _ _)] at this
  rw [e, e, ← mul_div_assoc]
  exact div_le_div_of_nonneg_right ((sum_le_sum fun k _ => h3 k).trans_eq (mul_sum _ _ _).symm) hc.le

/-- The proof of Lemma lem:growth: "Compose τ with Z ↦ α(Z ⊗ 1_i)α′ … and average: D(μi) ≤ sD(i) if μi ≤ k." -/
theorem lem_growth_digit {G : Type} [Group G] (l : Len G) {μ : ℕ} {s : ℝ} (hμ : 1 ≤ μ) (hs : 0 ≤ s)
    (hl : Contr l μ s) {k : ℕ} (τ : Mt k → G) (hτ : ∀ M N, τ (M + N) = τ M * τ N) {i : ℕ} (hi : μ * i ≤ k) :
    √(rankMean (fun W => l.val (τ W)) (μ * i)) ≤ s * √(rankMean (fun W => l.val (τ W)) i) := by
  set f : Mt k → ℝ := fun W => l.val (τ W)
  have hg : (0 : ℝ) < (Fintype.card (GLM (Fin k)) : ℝ) ^ 2 := by
    have : (0 : ℝ) < Fintype.card (GLM (Fin k)) := by exact_mod_cast Fintype.card_pos
    positivity
  obtain ⟨S, -, hS⟩ := exists_subset_card_eq (s := (univ : Finset (Fin k))) (n := μ * i) (by simpa using hi)
  let e : Fin μ × Fin i ↪ Fin k := (finProdFinEquiv.trans (Fintype.equivOfCardEq (α := Fin (μ * i))
    (β := {j // j ∈ S}) (by simp [hS]))).toEmbedding.trans (Function.Embedding.subtype _)
  have h := (good_of_contr l hl τ hτ).digit i e ⟨0, hμ⟩
  rw [DM_eq_rankMean, DM_eq_rankMean, card_map, card_map, card_univ, card_product, card_singleton, card_univ,
    Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, one_mul, mul_left_comm] at h
  rw [← Real.sqrt_sq hs, ← Real.sqrt_mul (sq_nonneg s)]
  exact Real.sqrt_le_sqrt (le_of_mul_le_mul_left h hg)

/-- The proof of Lemma lem:growth: "By Minkowski's inequality D(i+i′) ≤ D(i) + D(i′)." -/
theorem lem_growth_minkowski {G : Type} [Group G] (l : Len G) {k : ℕ} (τ : Mt k → G)
    (hτ : ∀ M N, τ (M + N) = τ M * τ N) {i i' : ℕ} (hi : i + i' ≤ k) :
    √(rankMean (fun W => l.val (τ W)) (i + i')) ≤
      √(rankMean (fun W => l.val (τ W)) i) + √(rankMean (fun W => l.val (τ W)) i') := by
  set f : Mt k → ℝ := fun W => l.val (τ W)
  have hg : (0 : ℝ) < Fintype.card (GLM (Fin k)) := by exact_mod_cast Fintype.card_pos
  obtain ⟨U, -, hU⟩ := exists_subset_card_eq (s := (univ : Finset (Fin k))) (n := i + i') (by simpa using hi)
  obtain ⟨S, hSU, hS⟩ := exists_subset_card_eq (s := U) (n := i) (by omega)
  have h := DM_dg_le f (fun _ => l.nonneg _) (fun M N => by simp only [f, hτ]; exact l.mul' _ _)
    (S := S) (T := U \ S) disjoint_sdiff
  rw [union_sdiff_of_subset hSU, DM_eq_rankMean, DM_eq_rankMean, DM_eq_rankMean, card_sdiff_of_subset hSU, hU, hS,
    Nat.add_sub_cancel_left, Real.sqrt_mul (sq_nonneg _), Real.sqrt_mul (sq_nonneg _), Real.sqrt_mul (sq_nonneg _),
    Real.sqrt_sq hg.le, ← mul_add] at h
  exact le_of_mul_le_mul_left h hg

/-- **Paper: Lemma lem:growth.** "Let 1 ≤ r ≤ k, let τ be a homomorphism from Mat_{k×k}(F₂) into a group with a
contracting length, and let D(r) be the quadratic mean of |τW| over rank r. Then D(r) ≤ μ(j+1)s^j D(1), where
j = ⌊log_μ r⌋." (r = 0 is allowed too.) -/
theorem lem_growth {G : Type} [Group G] (l : Len G) {μ : ℕ} {s : ℝ} (hμ : 2 ≤ μ) (hs : 1 ≤ s) (hl : Contr l μ s)
    {k : ℕ} (τ : Mt k → G) (hτ : ∀ M N, τ (M + N) = τ M * τ N) {r : ℕ} (hr : r ≤ k) :
    √(rankMean (fun W => l.val (τ W)) r) ≤
      (μ : ℝ) * (Nat.log μ r + 1) * s ^ Nat.log μ r * √(rankMean (fun W => l.val (τ W)) 1) := by
  set D : ℕ → ℝ := fun r => √(rankMean (fun W => l.val (τ W)) r) with hD
  show D r ≤ (μ : ℝ) * (Nat.log μ r + 1) * s ^ Nat.log μ r * D 1
  have hD0 : D 0 = 0 := by
    have h := (good_of_contr l hl τ hτ).dg_zero
    have hg : ((Fintype.card (GLM (Fin k)) : ℝ)) ^ 2 ≠ 0 :=
      pow_ne_zero 2 (Nat.cast_ne_zero.2 Fintype.card_ne_zero)
    rw [DM_eq_rankMean, card_empty, mul_eq_zero, or_iff_right hg] at h
    simp only [hD, h, Real.sqrt_zero]
  have hD1 : 0 ≤ D 1 := Real.sqrt_nonneg _
  have hsmall : ∀ t, t ≤ k → D t ≤ t * D 1 := by
    intro t
    induction t with
    | zero => intro _; simp [hD0]
    | succ t ih =>
      intro ht
      refine (lem_growth_minkowski l τ hτ ht).trans ?_
      have := ih (by omega)
      push_cast
      linarith
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    by_cases hrm : r < μ
    · refine (hsmall r hr).trans ?_
      rw [Nat.log_of_lt hrm]
      have : (r : ℝ) ≤ μ := by exact_mod_cast hrm.le
      simp only [CharP.cast_eq_zero, zero_add, mul_one, pow_zero]
      gcongr
    · push Not at hrm
      have hq : r / μ < r := Nat.div_lt_self (by omega) (by omega)
      have hm : r % μ ≤ μ := (Nat.mod_lt r (by omega)).le
      have h1 : D r ≤ D (μ * (r / μ)) + D (r % μ) := by
        have := lem_growth_minkowski l τ hτ (i := μ * (r / μ)) (i' := r % μ) (by rw [Nat.div_add_mod]; exact hr)
        rwa [Nat.div_add_mod] at this
      have h2 : D (μ * (r / μ)) ≤ s * D (r / μ) :=
        lem_growth_digit l (by omega) (by linarith) hl τ hτ ((Nat.mul_div_le r μ).trans hr)
      have h3 := mul_le_mul_of_nonneg_left (ih _ hq (by omega)) (show 0 ≤ s by linarith)
      have hmR : ((r % μ : ℕ) : ℝ) ≤ μ := by exact_mod_cast hm
      have h4 : D (r % μ) ≤ μ * D 1 :=
        (hsmall _ (by have := Nat.mod_le r μ; omega)).trans (mul_le_mul_of_nonneg_right hmR hD1)
      have hlog : Nat.log μ r = Nat.log μ (r / μ) + 1 := Nat.log_of_one_lt_of_le (by omega) hrm
      have hp : 1 ≤ s ^ (Nat.log μ (r / μ) + 1) := one_le_pow₀ hs
      have h5 : (μ : ℝ) * D 1 ≤ μ * D 1 * s ^ (Nat.log μ (r / μ) + 1) := le_mul_of_one_le_right (by positivity) hp
      rw [hlog]
      push_cast
      refine (h1.trans (add_le_add (h2.trans h3) (h4.trans h5))).trans (le_of_eq ?_)
      ring

/-- **Paper: Lemma lem:words.** "For 1 ≤ k < n and nonzero ξ, ω the element of U_n with upper right block ξωᵀ and unit
diagonal blocks has, in every length on U_n, length at most 18 ∑_j |x_j|." -/
theorem lem_words {n : ℕ} (l : Len (U n)) (k : ℕ) (u φ : Fin n → F2) (hu : ∀ i, u i ≠ 0 → i.1 < k)
    (hφk : ∀ j, φ j ≠ 0 → k ≤ j.1) (A : U n) (hA : mat A = 1 + Matrix.vecMulVec u φ) :
    l.val A ≤ 18 * ∑ j : Fin (n - 1), l.val (x n j) := by
  show l.val A ≤ 18 * l.S
  have hs : ∀ i j, u i ≠ 0 → φ j ≠ 0 → i < j := fun i j hi hj =>
    Fin.lt_def.2 (by have := hu i hi; have := hφk j hj; omega)
  have hS := l.S_nonneg
  have f2 : ∀ a : F2, a ≠ 0 → a = 1 := by decide
  by_cases h0 : (∃ i, u i ≠ 0) ∧ ∃ j, φ j ≠ 0
  · obtain ⟨⟨i0, hi0⟩, j0, hj0⟩ := h0
    obtain ⟨a, ha, hmax⟩ := exists_max_image (univ.filter fun i => u i ≠ 0) id
      ⟨i0, by simpa using hi0⟩
    have ha0 : u a ≠ 0 := by simpa using ha
    have ha1 : ∀ i, a < i → u i = 0 := by
      intro i hi
      by_contra h
      exact absurd (hmax i (by simpa using h)) (not_le.2 hi)
    have haj := hs a j0 ha0 hj0
    rw [Fin.lt_def] at haj
    have hj0n := j0.2
    set j : Fin (n - 1) := ⟨a.1, by omega⟩ with hj
    have hlo : lo j = a := rfl
    have hφ : ∀ i, i < hi j → φ i = 0 := by
      intro i hi
      by_contra h
      have h1 := hs a i ha0 h
      rw [Fin.lt_def] at h1 hi
      simp only [Nc.Tower.hi, hj] at hi
      omega
    by_cases hb : φ (hi j) = 0
    · have huhi : ∀ i, u i ≠ 0 → i < hi j := by
        intro i hi
        have h1 : i ≤ a := not_lt.1 fun h => hi (ha1 i h)
        exact lt_of_le_of_lt h1 (hlo ▸ Nc.Tower.lo_lt_hi j)
      have key : ∀ ψ : Fin n → F2, (∀ i, i < hi j → ψ i = 0) → ψ (hi j) = 1 →
          ∃ B : U n, mat B = 1 + Matrix.vecMulVec u ψ ∧ l.val B ≤ 9 * l.S := by
        intro ψ h1 h2
        have hz : ∀ i k, k ≤ i → u i * ψ k = 0 := by
          intro i k hki
          by_cases hi : u i = 0
          · rw [hi, zero_mul]
          · rw [h1 k (lt_of_le_of_lt hki (huhi i hi)), mul_zero]
        let B : U n := mk (1 + Matrix.vecMulVec u ψ)
          (fun i k hki => by
            rw [Matrix.add_apply, Matrix.one_apply_ne hki.ne', Matrix.vecMulVec_apply, hz i k hki.le,
              add_zero])
          (fun i => by
            rw [Matrix.add_apply, Matrix.one_apply_eq, Matrix.vecMulVec_apply, hz i i le_rfl,
              add_zero])
        exact ⟨B, rfl, lead_le l j u ψ (f2 _ ha0) ha1 h2 h1 B rfl⟩
      obtain ⟨B, hB, hlB⟩ := key (Pi.single (hi j) 1) (fun i hi => Pi.single_eq_of_ne hi.ne _)
        (Pi.single_eq_same _ _)
      obtain ⟨C, hC, hlC⟩ := key (φ + Pi.single (hi j) 1)
        (fun i hi => by rw [Pi.add_apply, hφ i hi, Pi.single_eq_of_ne hi.ne, add_zero])
        (by rw [Pi.add_apply, hb, Pi.single_eq_same, zero_add])
      have hABC : A = B * C := by
        apply mat_inj
        rw [mat_mul, hA, hB, hC, Matrix.add_mul, Matrix.one_mul, Matrix.mul_add, Matrix.mul_one,
          Matrix.vecMulVec_add]
        have : Matrix.vecMulVec u (Pi.single (hi j) (1 : F2)) *
            (Matrix.vecMulVec u φ + Matrix.vecMulVec u (Pi.single (hi j) 1)) = 0 := by
          rw [← Matrix.vecMulVec_add]
          ext i m
          rw [Matrix.mul_apply]
          refine sum_eq_zero fun c _ => ?_
          simp only [Matrix.vecMulVec_apply]
          by_cases hc : c = hi j
          · have : u c = 0 := by
              by_contra h
              exact absurd (huhi c h) (by rw [hc]; exact lt_irrefl _)
            rw [this]; simp
          · rw [Pi.single_eq_of_ne hc]; simp
        rw [this, add_zero]
        ext i m
        simp only [Matrix.add_apply, Matrix.vecMulVec_apply]
        have := f2_add_self (u i * (Pi.single (hi j) 1 : Fin n → F2) m)
        linear_combination (-1 : F2) * this
      rw [hABC]
      have := l.mul' B C
      linarith
    · have := lead_le l j u φ (f2 _ ha0) ha1 (f2 _ hb) hφ A hA
      linarith
  · have : mat A = 1 := by
      rw [hA]
      ext i k
      rw [Matrix.add_apply, Matrix.vecMulVec_apply]
      by_cases h1 : u i = 0
      · rw [h1, zero_mul, add_zero]
      · have : φ k = 0 := by
          by_contra h
          exact h0 ⟨⟨i, h1⟩, k, h⟩
        rw [this, mul_zero, add_zero]
    have hA1 : A = 1 := mat_inj (this.trans mat_one.symm)
    rw [hA1, l.one']
    linarith

end Paper
