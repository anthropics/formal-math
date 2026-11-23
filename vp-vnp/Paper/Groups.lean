/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Paper.Lengths
import Nc.Flag.Main
import Nc.Vp.Gen

/-!
# The paper, section "The contracting case: unitriangular groups", from the first estimate on
-/

namespace Paper

open Finset Filter Nc.Flag
open Nc.Tower (U x lo hi)

/-- The constant κ_n of the first estimate. -/
noncomputable def kappa (μ : ℕ) (s : ℝ) (n : ℕ) : ℝ := 18 * Nat.clog 2 n * grow μ s (2 ^ Nat.clog 2 n)

theorem kappa_nonneg (μ : ℕ) {s : ℝ} (hs : 1 ≤ s) (n : ℕ) : 0 ≤ kappa μ s n :=
  mul_nonneg (by positivity) (grow_nonneg μ hs _)

/-- The proof of Lemma lem:first, rank one in the upper right block (Lemma lem:words). -/
theorem lem_first_rank_one {a : ℕ} (l : Len (U (a + a))) (u φ : Fin a → F2) :
    l.val (up (Matrix.vecMulVec u φ)) ≤ 18 * l.S := by
  refine lem_words l a (fun i => if h : i.1 < a then u ⟨i.1, h⟩ else 0)
    (fun i => if h : a ≤ i.1 then φ ⟨i.1 - a, by omega⟩ else 0) (fun i hi => ?_) (fun j hj => ?_) _ ?_
  · by_contra h1
    simp [h1] at hi
  · by_contra h1
    simp [h1] at hj
  · rw [mat_up]
    congr 1
    ext i j
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_apply, wi, Matrix.of_apply, Matrix.transpose_apply,
      Matrix.vecMulVec_apply]
    by_cases h1 : i.1 < a
    · have e1 : ∀ c, i = we (hl (a := a) (b := a)) c ↔ ⟨i.1, h1⟩ = c := by
        intro c
        simp [we, Fin.ext_iff]
      simp only [e1, h1, dif_pos, ite_mul, one_mul, zero_mul, sum_ite_eq, mem_univ, if_true]
      by_cases h2 : a ≤ j.1
      · have e2 : ∀ c, j = we (hr (a := a) (b := a)) c ↔ ⟨j.1 - a, by omega⟩ = c := by
          intro c
          simp only [we, Fin.ext_iff]
          omega
        simp [e2, h2]
      · have e2 : ∀ c, j ≠ we (hr (a := a) (b := a)) c := by
          intro c
          simp only [we, ne_eq, Fin.ext_iff]
          omega
        simp [e2, h2]
    · have e1 : ∀ c, i ≠ we (hl (a := a) (b := a)) c := by
        intro c
        simp only [we, ne_eq, Fin.ext_iff]
        omega
      simp [e1, h1]

/-- The proof of Lemma lem:first: "By Lemmas lem:growth and lem:words the first [the upper right block] contributes at
most 18μ(d+1)s^d ∑_j |x_j|." Here the mean square over the block is bounded, with the sum in place of the mean. -/
theorem lem_first_block {a m : ℕ} {s : ℝ} (l : Len (U (a + a))) (hm : 2 ≤ m) (hs : 1 ≤ s) (hl : Contr l m s) :
    ∑ M : Mt a, l.val (up M) ^ 2 ≤ (Fintype.card (Mt a) : ℝ) * (grow m s a * (18 * l.S)) ^ 2 := by
  have hS := l.S_nonneg
  have h1 : rankMean (fun M : Mt a => l.val (up M)) 1 ≤ (18 * l.S) ^ 2 := by
    rw [rankMean]
    refine div_le_of_le_mul₀ (Nat.cast_nonneg _) (sq_nonneg _) ?_
    rw [mul_comm, ← nsmul_eq_mul]
    refine sum_le_card_nsmul _ _ _ fun W hW => pow_le_pow_left₀ (l.nonneg _) ?_ 2
    obtain ⟨p, q, T, rfl⟩ := exists_factor W
    rw [mem_filter, rank_units, rank_dg] at hW
    obtain ⟨i, rfl⟩ := card_eq_one.1 hW.2
    have e : (p : Mt a) * dg {i} * (q : Mt a) =
        Matrix.vecMulVec (fun r => (p : Mt a) r i) (fun c => (q : Mt a) i c) := by
      ext r c
      simp [Matrix.mul_apply, dg, Matrix.diagonal_apply, Matrix.vecMulVec_apply]
    rw [e]
    exact lem_first_rank_one l _ _
  have h2 : ∀ r, r ≤ a → rankMean (fun M : Mt a => l.val (up M)) r ≤ (grow m s a * (18 * l.S)) ^ 2 := by
    intro r hr
    have h := lem_growth l hm hs hl (fun M : Mt a => up M) up_add hr
    rw [← Real.sq_sqrt (rankMean_nonneg _ r)]
    refine pow_le_pow_left₀ (Real.sqrt_nonneg _) (h.trans ?_) 2
    have h3 : √(rankMean (fun M : Mt a => l.val (up M)) 1) ≤ 18 * l.S :=
      (Real.sqrt_le_left (by positivity)).2 h1
    exact mul_le_mul (grow_mono m hs hr) h3 (Real.sqrt_nonneg _) (grow_nonneg m hs a)
  have hmap : ∀ M ∈ (univ : Finset (Mt a)), M.rank ∈ range (a + 1) := fun M _ => by
    rw [mem_range, Nat.lt_succ_iff]
    exact (Matrix.rank_le_card_width M).trans (le_of_eq (Fintype.card_fin a))
  rw [← sum_fiberwise_of_maps_to hmap, ← card_univ, card_eq_sum_card_fiberwise hmap, Nat.cast_sum, Finset.sum_mul]
  refine sum_le_sum fun r hr => ?_
  rcases ((univ : Finset (Mt a)).filter fun M => M.rank = r).eq_empty_or_nonempty with he | he
  · simp [he]
  · have hc : (0 : ℝ) < ((univ : Finset (Mt a)).filter fun M => M.rank = r).card := by exact_mod_cast he.card_pos
    have h := h2 r (Nat.lt_succ_iff.1 (mem_range.1 hr))
    rw [rankMean, div_le_iff₀ hc] at h
    linarith

/-- The proof of Lemma lem:first, the step of the induction: "A uniform element is a product of a uniform element of
the abelian upper right block and uniform elements of the two diagonal blocks", and these "use disjoint sets of
generators". -/
theorem lem_first_double {m : ℕ} {s : ℝ} (hm : 2 ≤ m) (hs : 1 ≤ s) {a : ℕ} {κ : ℝ} (h : Bd m s a κ)
    (hκ : 0 ≤ κ) : Bd m s (a + a) (18 * grow m s a + κ) := by
  intro l hC
  set A := l.comap (win (hl (a := a) (b := a))) with hA
  set B := l.comap (win (hr (a := a) (b := a))) with hB
  have hAr : A.rms ≤ κ * A.S := h A (hC.comap _)
  have hBr : B.rms ≤ κ * B.S := h B (hC.comap _)
  have hS := S_add_le l
  rw [← hA, ← hB] at hS
  have hS0 := l.S_nonneg
  have hM := lem_first_block l hm hs hC (a := a)
  set cM : ℝ := (Fintype.card (Matrix (Fin a) (Fin a) F2) : ℝ) with hcM
  set cU : ℝ := (Fintype.card (U a) : ℝ) with hcU
  have hcM0 : 0 < cM := by rw [hcM]; exact_mod_cast Fintype.card_pos
  have hcU0 : 0 < cU := by rw [hcU]; exact_mod_cast Fintype.card_pos
  have hcard : (Fintype.card (U (a + a)) : ℝ) = cU * (cM * cU) := by
    have := Fintype.card_of_bijective (blk_bijective (a := a) (b := a))
    rw [← this, Fintype.card_prod, Fintype.card_prod]
    push_cast
    rfl
  have hsum : ∀ f : U (a + a) → ℝ, ∑ g, f g = ∑ t, f (blk t) := fun f =>
    (Function.Bijective.sum_comp blk_bijective f).symm
  have key : √(∑ g : U (a + a), l.val g ^ 2) ≤
      √(∑ t : U a × Matrix (Fin a) (Fin a) F2 × U a, B.val t.2.2 ^ 2) +
      (√(∑ t : U a × Matrix (Fin a) (Fin a) F2 × U a, l.val (up t.2.1) ^ 2) +
      √(∑ t : U a × Matrix (Fin a) (Fin a) F2 × U a, A.val t.1 ^ 2)) := by
    rw [hsum]
    refine three_le (fun t => l.val (blk t)) (fun t => B.val t.2.2) (fun t => l.val (up t.2.1))
      (fun t => A.val t.1) (fun _ => l.nonneg _) (fun _ => B.nonneg _) (fun _ => l.nonneg _)
      (fun _ => A.nonneg _) fun t => ?_
    have h1 := l.mul' (win hr t.2.2 * up t.2.1) (win hl t.1)
    have h2 := l.mul' (win hr t.2.2) (up t.2.1)
    have h3 : B.val t.2.2 = l.val (win hr t.2.2) := rfl
    have h4 : A.val t.1 = l.val (win hl t.1) := rfl
    rw [h3, h4]
    exact h1.trans (by linarith)
  have s1 : ∑ t : U a × Matrix (Fin a) (Fin a) F2 × U a, B.val t.2.2 ^ 2 =
      cU * (cM * cU) * B.rms ^ 2 := by
    rw [Len.rms_sq, Fintype.sum_prod_type, ← hcU]
    simp only [Fintype.sum_prod_type, sum_const, card_univ, nsmul_eq_mul, ← hcU, ← hcM]
    field_simp
  have s2 : ∑ t : U a × Matrix (Fin a) (Fin a) F2 × U a, l.val (up t.2.1) ^ 2 ≤
      cU * (cM * cU) * (grow m s a * (18 * l.S)) ^ 2 := by
    simp only [Fintype.sum_prod_type, sum_const, card_univ, nsmul_eq_mul, ← hcU, ← mul_sum]
    calc _ ≤ cU * (cU * (cM * (grow m s a * (18 * l.S)) ^ 2)) := by gcongr
      _ = _ := by ring
  have s3 : ∑ t : U a × Matrix (Fin a) (Fin a) F2 × U a, A.val t.1 ^ 2 =
      cU * (cM * cU) * A.rms ^ 2 := by
    rw [Len.rms_sq, Fintype.sum_prod_type, ← hcU]
    simp only [sum_const, card_univ, nsmul_eq_mul, Fintype.card_prod, Nat.cast_mul, ← hcU, ← hcM,
      ← mul_sum]
    field_simp
  have hc0 : 0 ≤ cU * (cM * cU) := by positivity
  have hg0 := grow_nonneg m hs a
  have t2 : √(∑ t : U a × Matrix (Fin a) (Fin a) F2 × U a, l.val (up t.2.1) ^ 2) ≤
      √(cU * (cM * cU)) * (grow m s a * (18 * l.S)) := by
    refine (Real.sqrt_le_sqrt s2).trans (le_of_eq ?_)
    rw [Real.sqrt_mul hc0, Real.sqrt_sq (by positivity)]
  rw [s1, s3, Real.sqrt_mul hc0, Real.sqrt_mul hc0, Real.sqrt_sq A.rms_nonneg,
    Real.sqrt_sq B.rms_nonneg] at key
  have hsq : 0 < √(cU * (cM * cU)) := Real.sqrt_pos.2 (by positivity)
  have hr : l.rms = √(∑ g : U (a + a), l.val g ^ 2) / √(cU * (cM * cU)) := by
    rw [Len.rms, hcard, Real.sqrt_div' _ hc0]
  rw [hr, div_le_iff₀ hsq]
  have hκS : κ * A.S + κ * B.S ≤ κ * l.S := by rw [← mul_add]; exact mul_le_mul_of_nonneg_left hS hκ
  calc √(∑ g : U (a + a), l.val g ^ 2)
      ≤ √(cU * (cM * cU)) * B.rms + (√(cU * (cM * cU)) * (grow m s a * (18 * l.S)) +
        √(cU * (cM * cU)) * A.rms) := key.trans (add_le_add le_rfl (add_le_add t2 le_rfl))
    _ = √(cU * (cM * cU)) * (B.rms + grow m s a * (18 * l.S) + A.rms) := by ring
    _ ≤ √(cU * (cM * cU)) * ((18 * grow m s a + κ) * l.S) := by
        apply mul_le_mul_of_nonneg_left _ hsq.le
        linarith
    _ = _ := by ring

/-- κ_n² n = o(n²). -/
theorem kappa_small {μ : ℕ} {s : ℝ} (hμ : 2 ≤ μ) (hs : 1 ≤ s) (hsm : s ^ 2 < μ) :
    Tendsto (fun n : ℕ => kappa μ s n ^ 2 * n / (n : ℝ) ^ 2) atTop (nhds 0) := by
  have hm0 : (0 : ℝ) < μ := by exact_mod_cast (by omega : 0 < μ)
  set ρ : ℝ := s ^ 2 / μ with hρ
  have hρ0 : 0 < ρ := by positivity
  have hρ1 : ρ < 1 := by rw [hρ, div_lt_one hm0]; exact hsm
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨L₀, hL₀⟩ := exists_log_large hρ0 hρ1 (show (0 : ℝ) < ε / (2 * (324 * 2 * (μ : ℝ) ^ 4)) by positivity)
  refine ⟨μ ^ L₀ + 2, fun n hn => ?_⟩
  set i := Nat.clog 2 n with hi
  set L := Nat.log μ (2 ^ i) with hL
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.2 (by omega)
  have hni : n ≤ 2 ^ i := Nat.le_pow_clog one_lt_two n
  have hi2 : 2 ^ i ≤ 2 * n := by
    obtain ⟨j, hj⟩ : ∃ j, i = j + 1 := ⟨i - 1, by have := Nat.clog_pos one_lt_two (show 2 ≤ n by omega); omega⟩
    have h : 2 ^ i.pred < n := Nat.pow_pred_clog_lt_self one_lt_two (by omega)
    rw [hj, Nat.pred_succ] at h
    rw [hj, pow_succ]
    omega
  have hLL : L₀ ≤ L := Nat.le_log_of_pow_le (by omega) (by omega)
  have hiL : (i : ℝ) ≤ μ * ((L : ℝ) + 1) := by
    have h1 : 2 ^ i < 2 ^ (μ * (L + 1)) := by
      calc 2 ^ i < μ ^ (L + 1) := Nat.lt_pow_succ_log_self (by omega) _
        _ ≤ (2 ^ μ) ^ (L + 1) := Nat.pow_le_pow_left Nat.lt_two_pow_self.le _
        _ = 2 ^ (μ * (L + 1)) := by rw [← pow_mul]
    have h2 : i < μ * (L + 1) := (Nat.pow_lt_pow_iff_right (by norm_num)).1 h1
    exact_mod_cast h2.le
  have hmL : (μ : ℝ) ^ L ≤ 2 * n := by
    exact_mod_cast (Nat.pow_log_le_self μ (Nat.two_pow_pos i).ne').trans hi2
  have e0 : (s ^ L) ^ 2 = ρ ^ L * (μ : ℝ) ^ L := by
    rw [← mul_pow, hρ, div_mul_cancel₀ _ hm0.ne', ← pow_mul, ← pow_mul, mul_comm]
  have h5 : kappa μ s n ^ 2 ≤ 324 * 2 * (μ : ℝ) ^ 4 * (((L : ℝ) + 1) ^ 4 * ρ ^ L) * n := by
    have e : kappa μ s n ^ 2 = 324 * (i : ℝ) ^ 2 * ((μ : ℝ) ^ 2 * ((L : ℝ) + 1) ^ 2 * (ρ ^ L * (μ : ℝ) ^ L)) := by
      rw [kappa, grow, ← hi, ← hL, ← e0]
      ring
    rw [e]
    calc _ ≤ 324 * ((μ : ℝ) * ((L : ℝ) + 1)) ^ 2 * ((μ : ℝ) ^ 2 * ((L : ℝ) + 1) ^ 2 * (ρ ^ L * (2 * n))) := by
          gcongr
      _ = _ := by ring
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity), div_lt_iff₀ (by positivity)]
  calc kappa μ s n ^ 2 * n ≤ 324 * 2 * (μ : ℝ) ^ 4 * (ε / (2 * (324 * 2 * (μ : ℝ) ^ 4))) * n * n := by
        gcongr
        refine h5.trans ?_
        gcongr
        exact hL₀ L hLL
    _ = ε / 2 * (n : ℝ) ^ 2 := by field_simp
    _ < ε * (n : ℝ) ^ 2 := by
        have : 0 < ε * (n : ℝ) ^ 2 := by positivity
        linarith

/-- **Paper: Lemma lem:first.** "There are κ_n with κ_n² n = o(n²) such that every contracting length on U_n satisfies
(E_g|g|²)^(1/2) ≤ κ_n ∑_j|x_j|." Here κ_n is the explicit kappa μ s n. -/
theorem lem_first {μ : ℕ} {s : ℝ} (hμ : 2 ≤ μ) (hs : 1 ≤ s) (hsm : s ^ 2 < μ) :
    Tendsto (fun n : ℕ => kappa μ s n ^ 2 * n / (n : ℝ) ^ 2) atTop (nhds 0) ∧
      ∀ (n : ℕ) (l : Len (U n)), Contr l μ s →
        √((∑ g : U n, l.val g ^ 2) / Fintype.card (U n)) ≤ kappa μ s n * ∑ j : Fin (n - 1), l.val (x n j) := by
  refine ⟨kappa_small hμ hs hsm, fun n => ?_⟩
  have hpow : ∀ i : ℕ, Bd μ s (2 ^ i) (18 * i * grow μ s (2 ^ i)) := by
    intro i
    induction i with
    | zero => simpa using bd_one μ s
    | succ i ih =>
      have h := lem_first_double hμ hs ih (by have := grow_nonneg μ hs (2 ^ i); positivity)
      rw [← two_mul, ← pow_succ'] at h
      intro l hl
      refine (h l hl).trans (mul_le_mul_of_nonneg_right ?_ l.S_nonneg)
      have h1 := grow_mono μ hs (Nat.pow_le_pow_right (n := 2) (by norm_num) (Nat.le_succ i))
      have : 18 * (i : ℝ) * grow μ s (2 ^ i) ≤ 18 * i * grow μ s (2 ^ (i + 1)) := by gcongr
      push_cast
      linarith
  exact bd_mono (Nat.le_pow_clog one_lt_two n) (kappa_nonneg μ hs n) (hpow _)

/-- C(n) = κ_n² n. -/
noncomputable def windowConst (μ : ℕ) (s : ℝ) (n : ℕ) : ℝ := kappa μ s n ^ 2 * n

theorem windowConst_nonneg (μ : ℕ) (s : ℝ) (n : ℕ) : 0 ≤ windowConst μ s n :=
  mul_nonneg (sq_nonneg _) (Nat.cast_nonneg _)

/-! ### Windows -/

section Fixed

variable {G Z : Type} [Group G] [MetricSpace Z] [Cat.CN Z]

open Cat in
/-- A point of a segment between fixed points is fixed: the point in Lemma lem:toolkit(a) is the only one with these
distances. -/
theorem segment_fixed (A : IsoAct G Z) {x v q : Z} {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) (hx : A.Fix x) (hv : A.Fix v)
    (e1 : dist x q = t * dist x v) (e2 : dist q v = (1 - t) * dist x v) : A.Fix q := by
  intro g
  obtain ⟨γ, -, huniq, -⟩ := (lem_toolkit (Y := Z)).1 x v t h0 h1
  rw [huniq q e1 e2]
  refine huniq _ ?_ ?_
  · rw [← huniq q e1 e2]
    conv_lhs => rw [← hx g]
    rw [A.iso', e1]
  · rw [← huniq q e1 e2]
    conv_lhs => rw [← hv g]
    rw [A.iso', e2]

variable [Fintype G]

/-- "These form a closed convex set, which contains the barycenter of every orbit." In the project P z is that
barycenter; projection_var shows that it is the nearest point. -/
theorem fixed_closed_convex (A : IsoAct G Z) :
    IsClosed {y : Z | A.Fix y} ∧
      (∀ x, A.Fix x → ∀ v, A.Fix v → ∀ q, dist x q = dist x v / 2 → dist q v = dist x v / 2 → A.Fix q) ∧
      ∀ z, A.Fix (A.P z) := by
  refine ⟨?_, fun x hx v hv q e1 e2 => segment_fixed A (t := 1 / 2) (by norm_num) (by norm_num) hx hv
    (by rw [e1]; ring) (by rw [e2]; ring), A.P_fix⟩
  have : {y : Z | A.Fix y} = ⋂ g, {y | A.act g y = y} := Set.ofPred_forall _
  rw [this]
  exact isClosed_iInter fun g => isClosed_eq (A.isometry g).continuous continuous_id

/-- Lemma lem:toolkit(d) for the fixed set: |z Pz|² + |Pz q|² ≤ |zq|² for every fixed q. -/
theorem projection_var (A : IsoAct G Z) {q : Z} (hq : A.Fix q) (z : Z) :
    dist z (A.P z) ^ 2 + dist (A.P z) q ^ 2 ≤ dist z q ^ 2 := by
  obtain ⟨hcl, hconv, hP⟩ := fixed_closed_convex A
  obtain ⟨P₀, hP₀, -, hvar⟩ := (lem_toolkit (Y := Z)).2.2.2.1 {y | A.Fix y} hcl ⟨_, hP z⟩ hconv z
  have h1 := hvar _ (hP z)
  have h2 := A.P_spec z P₀
  have e1 : ∀ g, dist (A.P z) (A.act g z) = dist z (A.P z) := fun g => by
    conv_lhs => rw [← A.P_fix z g]
    rw [A.iso', dist_comm]
  have e2 : ∀ g, dist P₀ (A.act g z) = dist z P₀ := fun g => by
    conv_lhs => rw [← hP₀ g]
    rw [A.iso', dist_comm]
  simp only [e1, e2, one_mul, sum_const, card_univ, nsmul_eq_mul, mul_one, ← mul_add] at h2
  have h3 := le_of_mul_le_mul_left h2 (by exact_mod_cast Fintype.card_pos)
  have h4 : dist P₀ (A.P z) ^ 2 ≤ 0 := by linarith [sq_nonneg (dist P₀ (A.P z))]
  rw [← dist_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 (le_antisymm h4 (sq_nonneg _)))]
  exact hvar q hq

/-- The P of the windows is the nearest-point projection to the fixed set: P z is fixed, is at least as near to z as every
fixed point, and is the only fixed point with this property. -/
theorem projection_nearest [DecidableEq G] (A : IsoAct G Z) (z : Z) :
    A.Fix (A.P z) ∧ (∀ y, A.Fix y → dist z (A.P z) ≤ dist z y) ∧
      ∀ y, A.Fix y → dist z y ≤ dist z (A.P z) → y = A.P z := by
  refine ⟨A.P_fix z, fun y hy => ?_, fun y hy h => ?_⟩
  · refine (abs_le_of_sq_le_sq' (show dist z (A.P z) ^ 2 ≤ dist z y ^ 2 from ?_) dist_nonneg).2
    linarith [projection_var A hy z, sq_nonneg (dist (A.P z) y)]
  · have h1 := projection_var A hy z
    have h2 : dist z y ^ 2 ≤ dist z (A.P z) ^ 2 := pow_le_pow_left₀ dist_nonneg h 2
    have h3 : dist (A.P z) y ^ 2 ≤ 0 := by linarith
    exact (dist_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 (le_antisymm h3 (sq_nonneg _)))).symm

/-- "So |z Pz|² ≤ E_g|z,gz|²." -/
theorem projection_sq_le (A : IsoAct G Z) (z : Z) :
    dist z (A.P z) ^ 2 ≤ (∑ g : G, dist z (A.act g z) ^ 2) / Fintype.card G := by
  have h := A.P_spec z z
  simp only [one_mul, sum_const, card_univ, nsmul_eq_mul, mul_one] at h
  rw [le_div_iff₀ (by exact_mod_cast Fintype.card_pos)]
  linarith [show 0 ≤ ∑ g : G, dist (A.P z) (A.act g z) ^ 2 from sum_nonneg fun _ _ => sq_nonneg _]

/-- "q projects to v": a point between v = Pa and a has the projection v. -/
theorem projection_segment [DecidableEq G] (A : IsoAct G Z) {a q : Z} {σ : ℝ}
    (e1 : dist (A.P a) q = σ * dist (A.P a) a) (e2 : dist q a = (1 - σ) * dist (A.P a) a) : A.P q = A.P a := by
  refine (projection_nearest A a).2.2 _ (A.P_fix q) ?_
  have h1 := dist_triangle a q (A.P q)
  have h2 := (projection_nearest A q).2.1 _ (A.P_fix a)
  rw [dist_comm a q] at h1
  rw [dist_comm q (A.P a)] at h2
  rw [dist_comm a (A.P a)]
  linarith

end Fixed

section Windows

variable {μ : ℕ} {s : ℝ} {h : ℕ} {Z : Type} [MetricSpace Z] [Cat.CN Z] (A : IsoAct (U h) Z)

/-- "For disjoint windows the projection of one maps the fixed set of the other into itself, as the two groups
commute." -/
theorem windows_commute {p n p' n' : ℕ} (hd : p + n ≤ p') (hp' : p' + n' ≤ h) :
    (∀ z, (A.W p n).Fix z → (A.W p n).Fix ((A.W p' n').P z)) ∧
      ∀ z, (A.W p' n').Fix z → (A.W p' n').Fix ((A.W p n).P z) := by
  refine ⟨fun z hz a => ?_, fun z hz b => ?_⟩
  · have h1 := (A.W p' n').P_comm (A.act (wh h p n a)) (A.isometry _) (A.surj _)
      (fun b z => by
        show A.act _ (A.act (wh h p' n' b) z) = A.act (wh h p' n' b) (A.act _ z)
        rw [← A.mul', ← A.mul', IsoAct.wh_comm hd hp']) z
    show A.act (wh h p n a) _ = _
    rw [h1, show A.act (wh h p n a) z = z from hz a]
  · have h1 := (A.W p n).P_comm (A.act (wh h p' n' b)) (A.isometry _) (A.surj _)
      (fun a z => by
        show A.act _ (A.act (wh h p n a) z) = A.act (wh h p n a) (A.act _ z)
        rw [← A.mul', ← A.mul', IsoAct.wh_comm hd hp']) z
    show A.act (wh h p' n' b) _ = _
    rw [h1, show A.act (wh h p' n' b) z = z from hz b]

/-- The inequality (eq:window) of the paper: |z Pz|² ≤ C(n) ∑ e_j(z)² over the generators of the window. "By Lemma
lem:first and the Cauchy–Schwarz inequality." -/
theorem eq_window (hμ : 2 ≤ μ) (hs : 1 ≤ s) (hsm : s ^ 2 < μ) (hA : ∀ z, Contr (A.len z) μ s) {n p : ℕ}
    (hp : p + n ≤ h) (z : Z) :
    dist z ((A.W p n).P z) ^ 2 ≤ windowConst μ s n * ∑ j ∈ Ico p (p + n - 1), A.e j z ^ 2 := by
  have hC : Contr ((A.W p n).len z) μ s := (hA z).comap (wh h p n)
  have h1 : ((A.W p n).len z).rms ≤ kappa μ s n * ((A.W p n).len z).S := (lem_first hμ hs hsm).2 n _ hC
  have h2 := projection_sq_le (A.W p n) z
  have h3 : (∑ g : U n, dist z ((A.W p n).act g z) ^ 2) / Fintype.card (U n) = ((A.W p n).len z).rms ^ 2 := by
    rw [Len.rms_sq]
    simp only [IsoAct.len_val]
  rw [h3] at h2
  have h4 : ((A.W p n).len z).rms ^ 2 ≤ (kappa μ s n * ((A.W p n).len z).S) ^ 2 :=
    pow_le_pow_left₀ (Len.rms_nonneg _) h1 2
  have h5 : ((A.W p n).len z).S = ∑ j : Fin (n - 1), A.e (p + j.1) z := by
    unfold Len.S
    refine sum_congr rfl fun j _ => ?_
    have hj : p + j.1 < h - 1 := by have := j.2; omega
    have e1 : wh h p n (x n j) = x h ⟨p + j.1, hj⟩ := by rw [wh_eq hp, win_x]; rfl
    have e2 : ((A.W p n).len z).val (x n j) = dist z (A.act (wh h p n (x n j)) z) := rfl
    rw [e2, e1]
    unfold IsoAct.e
    rw [dif_pos hj]
  have h6 : (((A.W p n).len z).S) ^ 2 ≤ n * ∑ j ∈ Ico p (p + n - 1), A.e j z ^ 2 := by
    have h7 : ∑ j ∈ Ico p (p + n - 1), A.e j z ^ 2 = ∑ j : Fin (n - 1), A.e (p + j.1) z ^ 2 := by
      rw [sum_Ico_eq_sum_range, ← Fin.sum_univ_eq_sum_range (fun j => A.e (p + j) z ^ 2)]
      rw [show p + n - 1 - p = n - 1 by omega]
    rw [h5, h7]
    have h8 := sq_sum_le_card_mul_sum_sq (s := univ) (f := fun j : Fin (n - 1) => A.e (p + j.1) z)
    rw [card_univ, Fintype.card_fin] at h8
    refine h8.trans (mul_le_mul_of_nonneg_right ?_ (sum_nonneg fun _ _ => sq_nonneg _))
    exact_mod_cast Nat.sub_le n 1
  calc _ ≤ kappa μ s n ^ 2 * (((A.W p n).len z).S) ^ 2 := by rw [← mul_pow]; exact h2.trans h4
    _ ≤ kappa μ s n ^ 2 * (n * ∑ j ∈ Ico p (p + n - 1), A.e j z ^ 2) := mul_le_mul_of_nonneg_left h6 (sq_nonneg _)
    _ = _ := by rw [windowConst]; ring

/-- The proof of Lemma lem:tele: "By Lemma lem:toolkit(c) each generator moves the barycenter by at most 1/n times
the sum of what it moves the n points." -/
theorem lem_tele_generator {n : ℕ} {y : Fin n → Z} {b : Z}
    (hb : ∀ w, (n : ℝ) * dist w b ^ 2 + ∑ i, dist b (y i) ^ 2 ≤ ∑ i, dist w (y i) ^ 2) (j : ℕ) :
    (n : ℝ) * A.e j b ≤ ∑ i, A.e j (y i) := by
  unfold IsoAct.e
  split_ifs with hj
  · refine (lem_toolkit (Y := Z)).2.2.1.2 n y (fun i => A.act (x h ⟨j, hj⟩) (y i)) b (A.act (x h ⟨j, hj⟩) b) hb
      fun w => ?_
    obtain ⟨w, rfl⟩ := A.surj (x h ⟨j, hj⟩) w
    simp only [A.iso']
    exact hb w
  · simp

/-- **Paper: Lemma lem:tele.** "Let u ≥ 2, p+3u ≤ h, ζ ≥ 0 and 4C(3u) ≤ ζ²(u−1)². If a is fixed by [p,p+2u), then
|a, P_{[p+u,p+3u)}a| ≥ (1−ζ)R, where R = |a, P_{[p,p+3u)}a|." -/
theorem lem_tele (hμ : 2 ≤ μ) (hs : 1 ≤ s) (hsm : s ^ 2 < μ) (hA : ∀ z, Contr (A.len z) μ s) {u p : ℕ} {ζ : ℝ}
    (hu : 2 ≤ u) (hp : p + 3 * u ≤ h) (hζ : 0 ≤ ζ)
    (hC : 4 * windowConst μ s (3 * u) ≤ ζ ^ 2 * ((u : ℝ) - 1) ^ 2) {a : Z} (ha : (A.W p (2 * u)).Fix a) :
    (1 - ζ) * dist a ((A.W p (3 * u)).P a) ≤ dist a ((A.W (p + u) (2 * u)).P a) := by
  set R := dist a ((A.W p (3 * u)).P a) with hR
  set B : ℕ → Z := fun k => (A.W (p + k) (3 * u - k)).P a with hB
  have hBfix : ∀ k, (A.W (p + k) (3 * u - k)).Fix (B k) := fun k => IsoAct.P_fix _ a
  have hBu : B u = (A.W (p + u) (2 * u)).P a := by
    show (A.W (p + u) (3 * u - u)).P a = _
    rw [show 3 * u - u = 2 * u by omega]
  have hu1 : (0 : ℝ) < (u : ℝ) - 1 := by
    have : (2 : ℝ) ≤ u := by exact_mod_cast hu
    linarith
  -- Lemma lem:toolkit (d)
  have hstep : ∀ k, k < 3 * u → dist (B k) (B (k + 1)) ^ 2 ≤ dist a (B k) ^ 2 - dist a (B (k + 1)) ^ 2 := by
    intro k hk
    have h1 := projection_var (A.W (p + (k + 1)) (3 * u - (k + 1)))
      ((hBfix k).sub A (by omega) (by omega) (by omega)) a
    rw [dist_comm ((A.W (p + (k + 1)) (3 * u - (k + 1))).P a) (B k)] at h1
    show dist (B k) ((A.W (p + (k + 1)) (3 * u - (k + 1))).P a) ^ 2 ≤
      dist a (B k) ^ 2 - dist a ((A.W (p + (k + 1)) (3 * u - (k + 1))).P a) ^ 2
    linarith
  have hφR : dist a (B u) ≤ R :=
    (projection_nearest (A.W (p + u) (3 * u - u)) a).2.1 _
      (((A.W p (3 * u)).P_fix a).sub A (by omega) (by omega) hp)
  have hφ : ∀ k, u ≤ k → k ≤ 3 * u → dist a (B k) ≤ dist a (B u) := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => intro _; exact le_rfl
    | succ k hk ih =>
      intro hk3
      refine le_trans ?_ (ih (by omega))
      exact (abs_le_of_sq_le_sq' (show dist a (B (k + 1)) ^ 2 ≤ dist a (B k) ^ 2 by
        linarith [hstep k (by omega), sq_nonneg (dist (B k) (B (k + 1)))]) dist_nonneg).2
  -- the barycenter of the u-1 points
  obtain ⟨b, hb⟩ := (lem_toolkit (Y := Z)).2.2.1.1 (u - 1) (fun i => B (u + 1 + i.1)) (by omega)
  have hw : ((u - 1 : ℕ) : ℝ) = (u : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ u), Nat.cast_one]
  have hab : dist a b ≤ dist a (B u) := by
    refine (abs_le_of_sq_le_sq' (show dist a b ^ 2 ≤ dist a (B u) ^ 2 from ?_) dist_nonneg).2
    have h1 := hb a
    have h2 : ∑ i : Fin (u - 1), dist a (B (u + 1 + i.1)) ^ 2 ≤ ((u : ℝ) - 1) * dist a (B u) ^ 2 := by
      have : ((u : ℝ) - 1) * dist a (B u) ^ 2 = ∑ _i : Fin (u - 1), dist a (B u) ^ 2 := by simp [hw]
      rw [this]
      refine sum_le_sum fun i _ => pow_le_pow_left₀ dist_nonneg ?_ 2
      exact hφ _ (by omega) (by have := i.2; omega)
    rw [hw] at h1
    have h3 : 0 ≤ ∑ i : Fin (u - 1), dist b (B (u + 1 + i.1)) ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
    exact le_of_mul_le_mul_left (by linarith) hu1
  -- for u < k < 2u all generators of the window fix b_k, apart from one
  have he : ∀ t, t < 3 * u - 1 → ∀ k, u + 1 ≤ k → k < 2 * u → k ≠ t + 1 → A.e (p + t) (B k) = 0 := by
    intro t ht k hk1 hk2 hkt
    by_cases htk : k ≤ t
    · exact A.e_zero (hBfix k) (by omega) (by omega) (by omega)
    · have h1 : (A.W (p + t) 2).Fix a := ha.sub A (by omega) (by omega) (by omega)
      exact A.e_zero ((windows_commute A (by omega) (by omega)).1 a h1) le_rfl le_rfl (by omega)
  have he2 : ∀ t, u ≤ t → t + 1 < 2 * u → A.e (p + t) (B (t + 1)) ≤ 2 * dist (B t) (B (t + 1)) := by
    intro t h1 h2
    rw [dist_comm]
    exact A.e_le (hBfix t) (by omega) (by omega) (by omega) _
  have hde : ∀ t, t < 3 * u - 1 → (((u : ℝ) - 1) * A.e (p + t) b) ^ 2 ≤
      if u ≤ t ∧ t + 1 < 2 * u then 4 * (dist a (B t) ^ 2 - dist a (B (t + 1)) ^ 2) else 0 := by
    intro t ht
    have h1 := lem_tele_generator A hb (p + t)
    rw [hw] at h1
    have h0 : 0 ≤ ((u : ℝ) - 1) * A.e (p + t) b := mul_nonneg hu1.le (A.e_nonneg _ _)
    split_ifs with hc
    · have h2 : ∑ i : Fin (u - 1), A.e (p + t) (B (u + 1 + i.1)) = A.e (p + t) (B (t + 1)) := by
        rw [sum_eq_single (⟨t - u, by omega⟩ : Fin (u - 1))]
        · congr 2
          simp only
          omega
        · intro i _ hi
          have := i.2
          refine he t ht _ (by omega) (by omega) ?_
          intro h3
          apply hi
          apply Fin.ext
          simp only
          omega
        · intro h3
          exact absurd (mem_univ _) h3
      rw [h2] at h1
      calc (((u : ℝ) - 1) * A.e (p + t) b) ^ 2 ≤ (2 * dist (B t) (B (t + 1))) ^ 2 :=
            pow_le_pow_left₀ h0 (h1.trans (he2 t hc.1 hc.2)) 2
        _ = 4 * dist (B t) (B (t + 1)) ^ 2 := by ring
        _ ≤ _ := by
          have := hstep t (by omega)
          linarith
    · have h2 : ∑ i : Fin (u - 1), A.e (p + t) (B (u + 1 + i.1)) = 0 := by
        refine sum_eq_zero fun i _ => ?_
        have := i.2
        refine he t ht _ (by omega) (by omega) ?_
        intro h3
        exact hc ⟨by omega, by omega⟩
      rw [h2] at h1
      rw [le_antisymm h1 h0]
      norm_num
  have hsum : ((u : ℝ) - 1) ^ 2 * ∑ j ∈ Ico p (p + 3 * u - 1), A.e j b ^ 2 ≤ 4 * R ^ 2 := by
    have h1 : ∑ j ∈ Ico p (p + 3 * u - 1), A.e j b ^ 2 = ∑ t ∈ range (3 * u - 1), A.e (p + t) b ^ 2 := by
      rw [sum_Ico_eq_sum_range, show p + 3 * u - 1 - p = 3 * u - 1 by omega]
    rw [h1, mul_sum]
    have h2 : ∀ t ∈ range (3 * u - 1), ((u : ℝ) - 1) ^ 2 * A.e (p + t) b ^ 2 ≤
        if u ≤ t ∧ t + 1 < 2 * u then 4 * (dist a (B t) ^ 2 - dist a (B (t + 1)) ^ 2) else 0 := by
      intro t ht
      rw [← mul_pow]
      exact hde t (mem_range.1 ht)
    refine (sum_le_sum h2).trans ?_
    rw [← sum_filter]
    have h3 : (range (3 * u - 1)).filter (fun t => u ≤ t ∧ t + 1 < 2 * u) = Ico u (2 * u - 1) := by
      ext t
      simp only [mem_filter, mem_range, mem_Ico]
      omega
    rw [h3, ← mul_sum]
    have h4 : ∀ m, u ≤ m → ∑ t ∈ Ico u m, (dist a (B t) ^ 2 - dist a (B (t + 1)) ^ 2) =
        dist a (B u) ^ 2 - dist a (B m) ^ 2 := by
      intro m hm
      induction m, hm using Nat.le_induction with
      | base => simp
      | succ m hm ih => rw [sum_Ico_succ_top hm, ih]; ring
    rw [h4 _ (by omega)]
    have := sq_nonneg (dist a (B (2 * u - 1)))
    have := pow_le_pow_left₀ dist_nonneg hφR 2
    linarith
  -- by (eq:window) b is within ζR of a fixed point of the window
  have hR0 : 0 ≤ R := dist_nonneg
  have hbP : dist b ((A.W p (3 * u)).P b) ≤ ζ * R := by
    refine (abs_le_of_sq_le_sq' (show dist b ((A.W p (3 * u)).P b) ^ 2 ≤ (ζ * R) ^ 2 from ?_)
      (mul_nonneg hζ hR0)).2
    have h2 : ((u : ℝ) - 1) ^ 2 * dist b ((A.W p (3 * u)).P b) ^ 2 ≤ ((u : ℝ) - 1) ^ 2 * (ζ * R) ^ 2 := by
      calc _ ≤ ((u : ℝ) - 1) ^ 2 * (windowConst μ s (3 * u) * ∑ j ∈ Ico p (p + 3 * u - 1), A.e j b ^ 2) :=
            mul_le_mul_of_nonneg_left (eq_window A hμ hs hsm hA hp b) (sq_nonneg _)
        _ = windowConst μ s (3 * u) * (((u : ℝ) - 1) ^ 2 * ∑ j ∈ Ico p (p + 3 * u - 1), A.e j b ^ 2) := by ring
        _ ≤ windowConst μ s (3 * u) * (4 * R ^ 2) := mul_le_mul_of_nonneg_left hsum (windowConst_nonneg μ s _)
        _ = 4 * windowConst μ s (3 * u) * R ^ 2 := by ring
        _ ≤ ζ ^ 2 * ((u : ℝ) - 1) ^ 2 * R ^ 2 := mul_le_mul_of_nonneg_right hC (sq_nonneg _)
        _ = _ := by ring
    exact le_of_mul_le_mul_left h2 (by positivity)
  have h1 := (projection_nearest (A.W p (3 * u)) a).2.1 _ ((A.W p (3 * u)).P_fix b)
  rw [← hR] at h1
  have h2 := dist_triangle a b ((A.W p (3 * u)).P b)
  rw [← hBu]
  linarith

end Windows

open Cat in
/-- The proof of Lemma lem:angle for any two fixed sets with a common point v. If every point q that divides [v,a], a the
first projection of z, is at squared distance at least (1−c²)|qv|² from the second fixed set, then
|aa′|² ≤ |za|² + |za′|² + 2c|za||za′|. -/
theorem lem_angle_projections {G₁ G₂ Z : Type} [Group G₁] [Fintype G₁] [DecidableEq G₁] [Group G₂] [Fintype G₂]
    [DecidableEq G₂] [MetricSpace Z] [CN Z] (A₁ : IsoAct G₁ Z) (A₂ : IsoAct G₂ Z) {c : ℝ} (hc : 0 < c) (z v : Z)
    (hv1 : A₁.Fix v) (hv2 : A₂.Fix v)
    (hq : ∀ (q : Z) (σ : ℝ), 0 < σ → σ ≤ 1 → dist v q = σ * dist v (A₁.P z) →
      dist q (A₁.P z) = (1 - σ) * dist v (A₁.P z) → (1 - c ^ 2) * dist v q ^ 2 ≤ dist q (A₂.P q) ^ 2) :
    dist (A₁.P z) (A₂.P z) ^ 2 ≤
      dist z (A₁.P z) ^ 2 + dist z (A₂.P z) ^ 2 + 2 * c * (dist z (A₁.P z) * dist z (A₂.P z)) := by
  set a := A₁.P z with ha
  set a' := A₂.P z with ha'
  have hA1 := projection_var A₁ hv1 z
  have hA2 := projection_var A₂ hv2 z
  rw [← ha] at hA1
  rw [← ha'] at hA2
  rcases (dist_nonneg (x := z) (y := a)).eq_or_lt with h0 | hr
  · rw [← h0, ← dist_eq_zero.1 h0.symm]
    simp
  rcases (dist_nonneg (x := z) (y := a')).eq_or_lt with h0 | hr'
  · rw [← h0, ← dist_eq_zero.1 h0.symm, dist_comm a z]
    simp
  have hpos : 0 ≤ 2 * c * (dist z a * dist z a') := by positivity
  rcases (dist_nonneg (x := v) (y := a)).eq_or_lt with h0 | hα
  · rw [dist_eq_zero.1 h0.symm, dist_comm a' a] at hA2
    linarith [sq_nonneg (dist z a')]
  rcases (dist_nonneg (x := v) (y := a')).eq_or_lt with h0 | hβ
  · rw [dist_eq_zero.1 h0.symm] at hA1
    linarith [sq_nonneg (dist z a)]
  rw [dist_comm a v] at hA1
  rw [dist_comm a' v] at hA2
  -- q, q′ divide [v,a], [v,a′] in ratios σ, τ with τβ = cσα
  set α := dist v a with hαd
  set β := dist v a' with hβd
  have hQ : α ^ 2 + β ^ 2 - 2 * c * (α * β) ≤ dist a a' ^ 2 := by
    set N := β + c * α with hN
    have hN0 : 0 < N := by positivity
    set σ := β / N with hσ
    set τ := c * α / N with hτ
    have hσ0 : 0 < σ := by positivity
    have hτ0 : 0 < τ := by positivity
    have hσ1 : σ ≤ 1 := by
      rw [hσ, div_le_one hN0, hN]
      linarith [mul_nonneg hc.le hα.le]
    have hτ1 : τ ≤ 1 := by
      rw [hτ, div_le_one hN0, hN]
      linarith
    obtain ⟨q, ⟨q1, q2⟩, -, q3⟩ := (lem_toolkit (Y := Z)).1 v a σ hσ0.le hσ1
    obtain ⟨q', ⟨p1, p2⟩, -, p3⟩ := (lem_toolkit (Y := Z)).1 v a' τ hτ0.le hτ1
    have h2 := hq q σ hσ0 hσ1 q1 q2
    have f2 : A₂.Fix q' := segment_fixed A₂ hτ0.le hτ1 hv2 (A₂.P_fix z) p1 p2
    have h4 : dist q (A₂.P q) ^ 2 ≤ dist q q' ^ 2 :=
      pow_le_pow_left₀ dist_nonneg ((projection_nearest A₂ q).2.1 _ f2) 2
    have h5 := p3 q
    have h6 := q3 a'
    rw [dist_comm a' q, dist_comm a' v, dist_comm a' a] at h6
    rw [dist_comm q v] at h5
    rw [q1] at h2 h5
    simp only [← hαd, ← hβd] at h2 h5 h6
    have h8 := mul_le_mul_of_nonneg_left h6 hτ0.le
    have e1 : τ * β = c * (σ * α) := by rw [hτ, hσ]; ring
    have e2 : (τ * β) ^ 2 = c ^ 2 * (σ * α) ^ 2 := by rw [e1]; ring
    have e3 : (τ * β) ^ 2 = c * (σ * α) * (τ * β) := by rw [sq, ← e1]
    have h7 : (σ * τ) * (α ^ 2 + β ^ 2 - dist a a' ^ 2) ≤ (σ * τ) * (2 * c * (α * β)) := by
      nlinarith
    linarith [le_of_mul_le_mul_left h7 (by positivity)]
  refine angle_num (α := α) (β := β) (A := dist z v ^ 2) hr hr' hα hβ (by linarith) (by linarith) hQ ?_
  -- Lemma lem:toolkit (a) twice, for the points at η on [a,a′] and at t on [z,v]
  intro η t hη0 hη1 ht0 ht1
  obtain ⟨m, -, -, hm⟩ := (lem_toolkit (Y := Z)).1 a a' η hη0 hη1
  obtain ⟨g, -, -, hg⟩ := (lem_toolkit (Y := Z)).1 z v t ht0 ht1
  have h1 := mul_le_mul_of_nonneg_left (hm z) (show 0 ≤ 1 - t by linarith)
  have h2 := mul_le_mul_of_nonneg_left (hm v) ht0
  have h3 := hg m
  rw [dist_comm m z, dist_comm m v] at h3
  simp only [← hαd, ← hβd] at h2 ⊢
  linarith [sq_nonneg (dist m g)]

/-- **Paper: Lemma lem:angle.** "Let u, p, ζ be as in Lemma lem:tele, 0 ≤ ζ ≤ 1, and 1−c² ≤ (1−ζ)², c > 0. If a, a′
are the projections of z for [p,p+2u) and [p+u,p+3u), then |aa′|² ≤ |za|² + |za′|² + 2c|za||za′|." -/
theorem lem_angle {μ : ℕ} {s : ℝ} {h : ℕ} {Z : Type} [MetricSpace Z] [Cat.CN Z] (A : IsoAct (U h) Z)
    (hμ : 2 ≤ μ) (hs : 1 ≤ s) (hsm : s ^ 2 < μ) (hA : ∀ z, Contr (A.len z) μ s) {u p : ℕ} {ζ c : ℝ}
    (hu : 2 ≤ u) (hp : p + 3 * u ≤ h) (hζ : 0 ≤ ζ)
    (hC : 4 * windowConst μ s (3 * u) ≤ ζ ^ 2 * ((u : ℝ) - 1) ^ 2) (hζ1 : ζ ≤ 1)
    (hcζ : 1 - c ^ 2 ≤ (1 - ζ) ^ 2) (hc : 0 < c) (z : Z) :
    dist ((A.W p (2 * u)).P z) ((A.W (p + u) (2 * u)).P z) ^ 2 ≤
      dist z ((A.W p (2 * u)).P z) ^ 2 + dist z ((A.W (p + u) (2 * u)).P z) ^ 2 +
        2 * c * (dist z ((A.W p (2 * u)).P z) * dist z ((A.W (p + u) (2 * u)).P z)) := by
  set a := (A.W p (2 * u)).P z with ha
  set v := (A.W p (3 * u)).P a with hv
  have hvf : (A.W p (3 * u)).Fix v := IsoAct.P_fix _ a
  have hv1 : (A.W p (2 * u)).Fix v := hvf.sub A le_rfl (by omega) hp
  refine lem_angle_projections _ _ hc z v hv1 (hvf.sub A (by omega) (by omega) hp) fun q σ hσ0 hσ1 q1 q2 => ?_
  have hqf : (A.W p (2 * u)).Fix q := segment_fixed _ hσ0.le hσ1 hv1 (IsoAct.P_fix _ z) q1 q2
  have hqv : (A.W p (3 * u)).P q = v := projection_segment _ q1 q2
  have h1 := lem_tele A hμ hs hsm hA hu hp hζ hC hqf
  rw [hqv] at h1
  rw [dist_comm v q]
  calc (1 - c ^ 2) * dist q v ^ 2 ≤ ((1 - ζ) * dist q v) ^ 2 := by
        rw [mul_pow]
        exact mul_le_mul_of_nonneg_right hcζ (sq_nonneg _)
    _ ≤ _ := pow_le_pow_left₀ (mul_nonneg (by linarith) dist_nonneg) h1 2

/-- The proof of Theorem thm:poincare: "If the windows of i, i′ do not meet and y is fixed by that of i, then the
point nearest to y among those fixed by that of i′ is fixed by both. So this point can serve as v in the proof of Lemma
lem:angle, with ζ = 0 and any c > 0, and gives |Q_iz Q_{i′}z|² ≤ r_i² + r_{i′}²." -/
theorem thm_poincare_far {h : ℕ} {Z : Type} [MetricSpace Z] [Cat.CN Z] (A : IsoAct (U h) Z) {p n p' n' : ℕ}
    (hd : p + n ≤ p') (hp' : p' + n' ≤ h) (z : Z) :
    dist ((A.W p n).P z) ((A.W p' n').P z) ^ 2 ≤
      dist z ((A.W p n).P z) ^ 2 + dist z ((A.W p' n').P z) ^ 2 := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  set r := dist z ((A.W p n).P z) * dist z ((A.W p' n').P z) with hr
  have hr0 : 0 ≤ r := mul_nonneg dist_nonneg dist_nonneg
  have hc : 0 < ε / (2 * r + 1) := by positivity
  set v := (A.W p' n').P ((A.W p n).P z) with hv
  have hv1 : (A.W p n).Fix v := (windows_commute A hd hp').1 _ (IsoAct.P_fix _ z)
  refine (lem_angle_projections _ _ hc z v hv1 (IsoAct.P_fix _ _) fun q σ hσ0 hσ1 q1 q2 => ?_).trans ?_
  · rw [projection_segment _ q1 q2, ← hv, dist_comm q v]
    exact mul_le_of_le_one_left (sq_nonneg _) (by linarith [sq_nonneg (ε / (2 * r + 1))])
  · rw [← hr]
    have : 2 * (ε / (2 * r + 1)) * r ≤ ε := by
      rw [mul_div_assoc', div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith
    linarith

section Poincare

variable {μ : ℕ} {s : ℝ} {h : ℕ} {Z : Type} [MetricSpace Z] [Cat.CN Z] (A : IsoAct (U h) Z)

/-- F(z) = ∑_i r_i², r_i = |z Q_iz|, Q_i the projection for the window [iu, iu+2u), i < L. -/
noncomputable def windowSum (u L : ℕ) (z : Z) : ℝ := ∑ i : Fin L, dist z ((A.W (i.1 * u) (2 * u)).P z) ^ 2

theorem windowSum_nonneg (u L : ℕ) (z : Z) : 0 ≤ windowSum A u L z := sum_nonneg fun _ _ => sq_nonneg _

theorem window_le {u L : ℕ} (hh : (L + 1) * u = h) (a : Fin L) : a.1 * u + 2 * u ≤ h := by
  rw [← hh]
  calc a.1 * u + 2 * u = (a.1 + 2) * u := by ring
    _ ≤ (L + 1) * u := Nat.mul_le_mul_right u (by omega)

/-- The proof of Theorem thm:poincare: "For neighbours Lemma lem:angle allows c(r_i²+r_{i′}²) more", so
∑_{i,i′} |Q_iz Q_{i′}z|² ≤ 2(L−1+2c)F(z). -/
theorem thm_poincare_pairs (hμ : 2 ≤ μ) (hs : 1 ≤ s) (hsm : s ^ 2 < μ) (hA : ∀ z, Contr (A.len z) μ s) {u L : ℕ}
    {ζ c : ℝ} (hu : 2 ≤ u) (hh : (L + 1) * u = h) (hζ : 0 ≤ ζ)
    (hC : 4 * windowConst μ s (3 * u) ≤ ζ ^ 2 * ((u : ℝ) - 1) ^ 2) (hζ1 : ζ ≤ 1)
    (hcζ : 1 - c ^ 2 ≤ (1 - ζ) ^ 2) (hc0 : 0 < c) (z : Z) :
    ∑ a : Fin L, ∑ b : Fin L, dist ((A.W (a.1 * u) (2 * u)).P z) ((A.W (b.1 * u) (2 * u)).P z) ^ 2 ≤
      2 * ((L : ℝ) - (1 - 2 * c)) * windowSum A u L z := by
  set Q : Fin L → Z → Z := fun a z => (A.W (a.1 * u) (2 * u)).P z with hQ
  show ∑ a, ∑ b, dist (Q a z) (Q b z) ^ 2 ≤ _
  have hwin := window_le hh (L := L)
  have hpair : ∀ (z : Z) (a b : Fin L), a.1 < b.1 → dist (Q a z) (Q b z) ^ 2 ≤
      dist z (Q a z) ^ 2 + dist z (Q b z) ^ 2 +
        if b.1 = a.1 + 1 then c * (dist z (Q a z) ^ 2 + dist z (Q b z) ^ 2) else 0 := by
    intro z a b hab
    split_ifs with hb
    · have h3 : a.1 * u + 3 * u ≤ h := by
        have := hwin b
        rw [hb] at this
        nlinarith
      have h1 := lem_angle A hμ hs hsm hA hu h3 hζ hC hζ1 hcζ hc0 z
      rw [show a.1 * u + u = b.1 * u by rw [hb]; ring] at h1
      have h2 : 2 * c * (dist z (Q a z) * dist z (Q b z)) ≤
          c * (dist z (Q a z) ^ 2 + dist z (Q b z) ^ 2) := by
        nlinarith [sq_nonneg (dist z (Q a z) - dist z (Q b z))]
      exact h1.trans (by linarith)
    · have h3 : a.1 * u + 2 * u ≤ b.1 * u := by
        calc a.1 * u + 2 * u = (a.1 + 2) * u := by ring
          _ ≤ b.1 * u := Nat.mul_le_mul_right u (by omega)
      rw [add_zero]
      exact thm_poincare_far A h3 (hwin b) z
  have hpair2 : ∀ (z : Z) (a b : Fin L), dist (Q a z) (Q b z) ^ 2 ≤
      (if a = b then 0 else dist z (Q a z) ^ 2 + dist z (Q b z) ^ 2) +
        ((if b.1 = a.1 + 1 then c * (dist z (Q a z) ^ 2 + dist z (Q b z) ^ 2) else 0) +
          if a.1 = b.1 + 1 then c * (dist z (Q a z) ^ 2 + dist z (Q b z) ^ 2) else 0) := by
    intro z a b
    rcases lt_trichotomy a.1 b.1 with hab | hab | hab
    · rw [if_neg (fun h => by rw [h] at hab; exact lt_irrefl _ hab),
        if_neg (show ¬ a.1 = b.1 + 1 by omega), add_zero]
      exact hpair z a b hab
    · have : a = b := Fin.ext hab
      subst this
      simp
    · rw [if_neg (fun h => by rw [h] at hab; exact lt_irrefl _ hab),
        if_neg (show ¬ b.1 = a.1 + 1 by omega), zero_add, dist_comm]
      have := hpair z b a hab
      rw [add_comm (dist z (Q b z) ^ 2)] at this
      exact this
  have hnb : ∀ (r : Fin L → ℝ) (_ : ∀ a, 0 ≤ r a), ∑ a : Fin L, ∑ b : Fin L,
      (if b.1 = a.1 + 1 then c * (r a + r b) else 0) ≤ 2 * c * ∑ a, r a := by
    intro r hr
    have e1 : ∀ a : Fin L, ∑ b : Fin L, (if b.1 = a.1 + 1 then c * r a else 0) ≤ c * r a := by
      intro a
      by_cases ha : a.1 + 1 < L
      · rw [sum_eq_single (⟨a.1 + 1, ha⟩ : Fin L)]
        · simp
        · intro b _ hb
          rw [if_neg]
          intro h1
          exact hb (Fin.ext h1)
        · simp
      · rw [sum_eq_zero]
        · exact mul_nonneg hc0.le (hr a)
        · intro b _
          rw [if_neg]
          have := b.2
          omega
    have e2 : ∀ b : Fin L, ∑ a : Fin L, (if b.1 = a.1 + 1 then c * r b else 0) ≤ c * r b := by
      intro b
      by_cases hb : 1 ≤ b.1
      · rw [sum_eq_single (⟨b.1 - 1, by omega⟩ : Fin L)]
        · rw [if_pos (by simp only; omega)]
        · intro a _ ha
          rw [if_neg]
          intro h1
          apply ha
          apply Fin.ext
          simp only
          omega
        · simp
      · rw [sum_eq_zero]
        · exact mul_nonneg hc0.le (hr b)
        · intro a _
          rw [if_neg]
          omega
    have e3 : ∀ a b : Fin L, (if b.1 = a.1 + 1 then c * (r a + r b) else 0) =
        (if b.1 = a.1 + 1 then c * r a else 0) + if b.1 = a.1 + 1 then c * r b else 0 := by
      intro a b
      split_ifs
      · ring
      · simp
    simp only [e3, sum_add_distrib]
    rw [sum_comm (f := fun a b : Fin L => if b.1 = a.1 + 1 then c * r b else 0)]
    have e4 := sum_le_sum fun a (_ : a ∈ univ) => e1 a
    have e5 := sum_le_sum fun b (_ : b ∈ univ) => e2 b
    rw [← mul_sum] at e4 e5
    linarith
  set r : Fin L → ℝ := fun a => dist z (Q a z) ^ 2 with hr
  have hr0 : ∀ a, 0 ≤ r a := fun a => sq_nonneg _
  have h1 : ∑ a : Fin L, ∑ b : Fin L, (if a = b then (0 : ℝ) else r a + r b) =
      2 * ((L : ℝ) - 1) * ∑ a, r a := by
    have e1 : ∀ a b : Fin L, (if a = b then (0 : ℝ) else r a + r b) =
        (r a + r b) - if a = b then 2 * r a else 0 := by
      intro a b
      split_ifs with hab
      · rw [hab]; ring
      · ring
    simp only [e1, sum_sub_distrib, sum_add_distrib, sum_const, card_univ, Fintype.card_fin,
      nsmul_eq_mul, sum_ite_eq, mem_univ, if_true, ← mul_sum]
    ring
  have h2 := hnb r hr0
  have h3 : ∑ a : Fin L, ∑ b : Fin L, (if a.1 = b.1 + 1 then c * (r a + r b) else 0) ≤
      2 * c * ∑ a, r a := by
    rw [sum_comm]
    refine le_trans (le_of_eq ?_) h2
    refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
    rw [add_comm (r b)]
  calc ∑ a, ∑ b, dist (Q a z) (Q b z) ^ 2 ≤ _ :=
        sum_le_sum fun a _ => sum_le_sum fun b _ => hpair2 z a b
    _ = ∑ a : Fin L, ∑ b : Fin L, (if a = b then (0 : ℝ) else r a + r b) +
        (∑ a : Fin L, ∑ b : Fin L, (if b.1 = a.1 + 1 then c * (r a + r b) else 0) +
          ∑ a : Fin L, ∑ b : Fin L, (if a.1 = b.1 + 1 then c * (r a + r b) else 0)) := by
        simp only [sum_add_distrib]
        rfl
    _ ≤ _ := by
        rw [h1]
        show _ ≤ 2 * ((L : ℝ) - (1 - 2 * c)) * ∑ a, r a
        linarith

/-- The proof of Theorem thm:poincare: for the barycenter b of the points Q_iz, "F(b) ≤ ∑_i|b Q_iz|² ≤ (1 − (1−2c)/L)F(z)
and L|zb|² ≤ F(z) − F(b)", by Lemma lem:toolkit(c). -/
theorem thm_poincare_step (hμ : 2 ≤ μ) (hs : 1 ≤ s) (hsm : s ^ 2 < μ) (hA : ∀ z, Contr (A.len z) μ s) {u L : ℕ}
    {ζ c : ℝ} (hu : 2 ≤ u) (hL : 1 ≤ L) (hh : (L + 1) * u = h) (hζ : 0 ≤ ζ)
    (hC : 4 * windowConst μ s (3 * u) ≤ ζ ^ 2 * ((u : ℝ) - 1) ^ 2) (hζ1 : ζ ≤ 1)
    (hcζ : 1 - c ^ 2 ≤ (1 - ζ) ^ 2) (hc0 : 0 < c) (z : Z) :
    ∃ b, windowSum A u L b ≤ (1 - (1 - 2 * c) / L) * windowSum A u L z ∧
      (L : ℝ) * dist z b ^ 2 ≤ windowSum A u L z - windowSum A u L b := by
  set Q : Fin L → Z := fun a => (A.W (a.1 * u) (2 * u)).P z with hQ
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  obtain ⟨b, hb⟩ := (lem_toolkit (Y := Z)).2.2.1.1 L Q hL
  have h1 : 2 * ((L : ℝ) * ∑ i, dist b (Q i) ^ 2) ≤ ∑ i, ∑ j, dist (Q i) (Q j) ^ 2 := by
    refine le_trans (le_of_eq ?_) (sum_le_sum fun i _ => hb (Q i))
    rw [sum_add_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_sum,
      sum_congr rfl fun i _ => congrArg (· ^ 2) (dist_comm (Q i) b)]
    ring
  have h2 := h1.trans (thm_poincare_pairs A hμ hs hsm hA hu hh hζ hC hζ1 hcζ hc0 z)
  have h3 : ∑ i, dist b (Q i) ^ 2 ≤ (1 - (1 - 2 * c) / L) * windowSum A u L z := by
    refine le_of_mul_le_mul_left ?_ hLr
    have e : (L : ℝ) * ((1 - (1 - 2 * c) / L) * windowSum A u L z) = (L - (1 - 2 * c)) * windowSum A u L z := by
      field_simp
    rw [e]
    linarith
  have h4 : windowSum A u L b ≤ ∑ i, dist b (Q i) ^ 2 :=
    sum_le_sum fun a _ => pow_le_pow_left₀ dist_nonneg
      ((projection_nearest _ b).2.1 _ (IsoAct.P_fix _ z)) 2
  refine ⟨b, h4.trans h3, ?_⟩
  have h5 := hb z
  have e : windowSum A u L z = ∑ i, dist z (Q i) ^ 2 := rfl
  linarith

/-- The proof of Theorem thm:poincare: "Iterate: F decreases geometrically and the steps add up to at most
2√(F(z)/(1−2c)), so the points converge to one fixed by every window, hence by U_h. So |z P_{[0,h)}z|² ≤ 4F(z)/(1−2c)." -/
theorem thm_poincare_limit (hμ : 2 ≤ μ) (hs : 1 ≤ s) (hsm : s ^ 2 < μ) (hA : ∀ z, Contr (A.len z) μ s) {u L : ℕ}
    {ζ c : ℝ} (hu : 2 ≤ u) (hL : 1 ≤ L) (hh : (L + 1) * u = h) (hζ : 0 ≤ ζ)
    (hC : 4 * windowConst μ s (3 * u) ≤ ζ ^ 2 * ((u : ℝ) - 1) ^ 2) (hζ1 : ζ ≤ 1)
    (hcζ : 1 - c ^ 2 ≤ (1 - ζ) ^ 2) (hc0 : 0 < c) (hc : c < 1 / 2) (z : Z) :
    ∃ y, A.Fix y ∧ dist z y ^ 2 ≤ 4 / (1 - 2 * c) * windowSum A u L z := by
  choose b hb1 hb2 using thm_poincare_step A hμ hs hsm hA hu hL hh hζ hC hζ1 hcζ hc0
  set F := windowSum A u L with hF
  have hF0 : ∀ z, 0 ≤ F z := windowSum_nonneg A u L
  set δ := 1 - 2 * c with hδ
  have hδ0 : 0 < δ := by linarith
  have hLr : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hq0 : 0 ≤ 1 - δ / L := by
    have : δ / L ≤ 1 := (div_le_one (by linarith)).2 (by linarith)
    linarith
  have hq1 : 1 - δ / L < 1 := by
    have : 0 < δ / L := by positivity
    linarith
  set y : ℕ → Z := fun n => b^[n] z with hy
  have hys : ∀ n, y (n + 1) = b (y n) := fun n => Function.iterate_succ_apply' b n z
  set X : ℕ → ℝ := fun n => 2 / √δ * √(F (y n)) with hX
  have hstep : ∀ n, dist (y n) (y (n + 1)) ≤ X n - X (n + 1) := by
    intro n
    rw [hys, hX]
    simp only [hys, ← mul_sub]
    exact step_num (L := (L : ℝ)) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hLr hδ0
      (by rw [Real.sq_sqrt (hF0 _), Real.sq_sqrt (hF0 _)]; exact hb1 _)
      (by rw [Real.sq_sqrt (hF0 _), Real.sq_sqrt (hF0 _)]; exact hb2 _)
  have htot : ∀ n m, n ≤ m → dist (y n) (y m) ≤ X n - X m := by
    intro n m hnm
    induction m, hnm using Nat.le_induction with
    | base => simp
    | succ m _ ih =>
      have := dist_triangle (y n) (y m) (y (m + 1))
      linarith [hstep m]
  have hX0 : ∀ n, 0 ≤ X n := fun n => mul_nonneg (by positivity) (Real.sqrt_nonneg _)
  have hgeo : ∀ n, F (y n) ≤ (1 - δ / L) ^ n * F z := by
    intro n
    induction n with
    | zero => simp [hy]
    | succ n ih =>
      rw [hys, pow_succ']
      refine (hb1 _).trans ?_
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left ih hq0
  have hF0lim : Tendsto (fun n => F (y n)) atTop (nhds 0) := by
    refine squeeze_zero (fun n => hF0 _) hgeo ?_
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).mul_const (F z)
  have hX0lim : Tendsto X atTop (nhds 0) := by
    simpa using (hF0lim.sqrt).const_mul (2 / √δ)
  have hcauchy : CauchySeq y :=
    cauchySeq_of_le_tendsto_0' X (fun n m hnm => (htot n m hnm).trans (by linarith [hX0 m])) hX0lim
  obtain ⟨y₀, hy₀⟩ := cauchySeq_tendsto_of_complete hcauchy
  refine ⟨y₀, ?_, ?_⟩
  · -- F is continuous, so the limit is fixed by every window
    have hcont : Continuous F := by
      rw [hF]
      unfold windowSum
      refine continuous_finsetSum _ fun a _ => Continuous.pow ?_ 2
      refine (LipschitzWith.of_le_add fun x w => ?_).continuous
      have h1 := (projection_nearest (A.W (a.1 * u) (2 * u)) x).2.1 _ (IsoAct.P_fix _ w)
      have h2 := dist_triangle x w ((A.W (a.1 * u) (2 * u)).P w)
      linarith
    have hlim : F y₀ = 0 := tendsto_nhds_unique ((hcont.tendsto y₀).comp hy₀) hF0lim
    have hfix : ∀ a : Fin L, (A.W (a.1 * u) (2 * u)).Fix y₀ := fun a => by
      have h1 : dist y₀ ((A.W (a.1 * u) (2 * u)).P y₀) ^ 2 = 0 :=
        (sum_eq_zero_iff_of_nonneg fun _ _ => sq_nonneg _).1 hlim a (mem_univ a)
      rw [dist_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h1)]
      exact IsoAct.P_fix _ _
    let H : Subgroup (U h) :=
      { carrier := {g | A.act g y₀ = y₀}
        one_mem' := A.one' y₀
        mul_mem' := fun {g g'} hg hg' => by
          show A.act (g * g') y₀ = y₀
          rw [A.mul', show A.act g' y₀ = y₀ from hg', show A.act g y₀ = y₀ from hg]
        inv_mem' := fun {g} hg => by
          show A.act g⁻¹ y₀ = y₀
          conv_lhs => rw [← show A.act g y₀ = y₀ from hg]
          rw [← A.mul', inv_mul_cancel, A.one'] }
    refine fun g => mem_of_x H (fun j => ?_) g
    show A.act (x h j) y₀ = y₀
    have hjlt := j.2
    obtain ⟨j, hj⟩ := j
    simp only at hjlt ⊢
    have h3 : ∃ a : Fin L, a.1 * u ≤ j ∧ j + 2 ≤ a.1 * u + 2 * u := by
      by_cases hj2 : j < u
      · refine ⟨⟨0, by omega⟩, by simp, ?_⟩
        simp only [zero_mul, zero_add]
        omega
      · have hdiv := Nat.div_add_mod (j - (u - 1)) u
        have hmod := Nat.mod_lt (j - (u - 1)) (show 0 < u by omega)
        refine ⟨⟨(j - (u - 1)) / u, ?_⟩, ?_, ?_⟩
        · rw [Nat.div_lt_iff_lt_mul (by omega)]
          have : (L + 1) * u = L * u + u := by ring
          omega
        · simp only
          rw [mul_comm]
          omega
        · simp only
          rw [mul_comm]
          omega
    obtain ⟨a, ha1, ha2⟩ := h3
    have he := A.e_zero (hfix a) ha1 ha2 (window_le hh a)
    unfold IsoAct.e at he
    rw [dif_pos hj] at he
    exact (dist_eq_zero.1 he).symm
  · have h1 : dist z y₀ ≤ X 0 := le_of_tendsto' ((tendsto_const_nhds (x := z)).dist hy₀) fun n => by
      have := htot 0 n (Nat.zero_le n)
      simp only [hy, Function.iterate_zero, id_eq] at this
      linarith [hX0 n]
    calc dist z y₀ ^ 2 ≤ X 0 ^ 2 := pow_le_pow_left₀ dist_nonneg h1 2
      _ = 4 / δ * F z := by
        simp only [hX, hy, Function.iterate_zero, id_eq]
        rw [mul_pow, div_pow, Real.sq_sqrt hδ0.le, Real.sq_sqrt (hF0 z)]
        norm_num

/-- The proof of Theorem thm:poincare: "(eq:window) for n = 2u, each generator lying in at most two windows, bounds
F(z) by 2C(2u) ∑_j e_j(z)²." -/
theorem thm_poincare_windows (hμ : 2 ≤ μ) (hs : 1 ≤ s) (hsm : s ^ 2 < μ) (hA : ∀ z, Contr (A.len z) μ s) {u L : ℕ}
    (hu : 2 ≤ u) (hh : (L + 1) * u = h) (z : Z) :
    windowSum A u L z ≤ 2 * windowConst μ s (2 * u) * ∑ j ∈ range (h - 1), A.e j z ^ 2 := by
  set Q : Fin L → Z → Z := fun a z => (A.W (a.1 * u) (2 * u)).P z with hQ
  set F : Z → ℝ := windowSum A u L with hF
  set C₂ := windowConst μ s (2 * u) with hC₂d
  have hwin := window_le hh (L := L)
  have h1 : ∀ a : Fin L, dist z (Q a z) ^ 2 ≤ C₂ * ∑ j ∈ range (h - 1),
      if a.1 * u ≤ j ∧ j + 1 < a.1 * u + 2 * u then A.e j z ^ 2 else 0 := by
    intro a
    refine (eq_window A hμ hs hsm hA (hwin a) z).trans (le_of_eq ?_)
    rw [← sum_filter]
    congr 1
    refine sum_congr ?_ fun _ _ => rfl
    have := hwin a
    ext j
    simp only [mem_Ico, mem_filter, mem_range]
    omega
  have h2 : F z ≤ C₂ * ∑ j ∈ range (h - 1), ∑ a : Fin L,
      if a.1 * u ≤ j ∧ j + 1 < a.1 * u + 2 * u then A.e j z ^ 2 else 0 := by
    rw [sum_comm, mul_sum]
    exact sum_le_sum fun a _ => h1 a
  refine h2.trans ?_
  rw [mul_comm 2 C₂, mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (windowConst_nonneg μ s _)
  rw [mul_sum]
  refine sum_le_sum fun j _ => ?_
  rw [← sum_filter, sum_const, nsmul_eq_mul]
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  have h3 : (univ.filter fun a : Fin L => a.1 * u ≤ j ∧ j + 1 < a.1 * u + 2 * u).card ≤ 2 := by
    have hsub : (univ.filter fun a : Fin L => a.1 * u ≤ j ∧ j + 1 < a.1 * u + 2 * u).image
        (fun a => a.1) ⊆ {j / u - 1, j / u} := by
      intro k hk
      simp only [mem_image, mem_filter, mem_univ, true_and] at hk
      obtain ⟨a, ⟨ha1, ha2⟩, rfl⟩ := hk
      have h4 : a.1 ≤ j / u := (Nat.le_div_iff_mul_le (by omega)).2 ha1
      have h5 : j / u < a.1 + 2 := by
        rw [Nat.div_lt_iff_lt_mul (by omega)]
        calc j < a.1 * u + 2 * u := by omega
          _ = (a.1 + 2) * u := by ring
      simp only [mem_insert, mem_singleton]
      omega
    calc _ = ((univ.filter fun a : Fin L => a.1 * u ≤ j ∧ j + 1 < a.1 * u + 2 * u).image
        (fun a => a.1)).card := (card_image_of_injective _ Fin.val_injective).symm
      _ ≤ ({j / u - 1, j / u} : Finset ℕ).card := card_le_card hsub
      _ ≤ 2 := card_le_two
  exact_mod_cast h3

/-- The Poincaré bound for every isometric action of U_h, h = lu, on a CAT(0) space with contracting lengths, from the
proof of Theorem thm:poincare, with ζ = 1/32 and c = 1/4: "|z,gz| ≤ 2|z P_{[0,h)}z|", so E_g|z,gz|² ≤ 32C(2u)/(1−2c) ∑_j e_j(z)². -/
theorem thm_poincare_action (hμ : 2 ≤ μ) (hs : 1 ≤ s) (hsm : s ^ 2 < μ) (hA : ∀ z, Contr (A.len z) μ s) {u l : ℕ}
    (hu : 2 ≤ u) (hl : 2 ≤ l) (hh : l * u = h)
    (hC : 4 * windowConst μ s (3 * u) ≤ (1 / 32) ^ 2 * ((u : ℝ) - 1) ^ 2) (z : Z) :
    (∑ g, dist z (A.act g z) ^ 2) / Fintype.card (U h) ≤
      32 * windowConst μ s (2 * u) / (1 - 2 * (1 / 4)) * ∑ j, dist z (A.act (x h j) z) ^ 2 := by
  obtain ⟨L, rfl⟩ : ∃ L, l = L + 1 := ⟨l - 1, by omega⟩
  obtain ⟨y, hy, hy2⟩ := thm_poincare_limit A hμ hs hsm hA hu (by omega) hh (by norm_num) hC (by norm_num)
    (c := 1 / 4) (by norm_num) (by norm_num) (by norm_num) z
  have hw := thm_poincare_windows A hμ hs hsm hA hu hh z
  have hd : ∀ g, dist z (A.act g z) ^ 2 ≤ 4 * dist z y ^ 2 := fun g => by
    have h1 := dist_triangle z y (A.act g z)
    have h2 : dist y (A.act g z) = dist z y := by
      conv_lhs => rw [← hy g]
      rw [A.iso', dist_comm]
    rw [h2] at h1
    calc dist z (A.act g z) ^ 2 ≤ (2 * dist z y) ^ 2 := pow_le_pow_left₀ dist_nonneg (by linarith) 2
      _ = _ := by ring
  have hsum : ∑ j ∈ range (h - 1), A.e j z ^ 2 = ∑ j, dist z (A.act (x h j) z) ^ 2 := by
    rw [← Fin.sum_univ_eq_sum_range (fun j => A.e j z ^ 2)]
    refine sum_congr rfl fun j _ => ?_
    unfold IsoAct.e
    rw [dif_pos j.2]
  rw [hsum] at hw
  rw [div_le_iff₀ (by exact_mod_cast Fintype.card_pos)]
  refine (sum_le_card_nsmul univ _ _ fun g _ => hd g).trans ?_
  rw [card_univ, nsmul_eq_mul, mul_comm]
  refine mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg _)
  norm_num at hy2 ⊢
  linarith

end Poincare

/-- The proof of Theorem thm:poincare: "Since C(n) = o(n²), some u has 4C(3u) ≤ (u−1)²/32²; fix it." -/
theorem thm_poincare_size {μ : ℕ} {s : ℝ} (hμ : 2 ≤ μ) (hs : 1 ≤ s) (hsm : s ^ 2 < μ) :
    ∃ u : ℕ, 2 ≤ u ∧ 4 * windowConst μ s (3 * u) ≤ (1 / 32) ^ 2 * ((u : ℝ) - 1) ^ 2 := by
  obtain ⟨n₀, hn⟩ := eventually_atTop.1
    ((lem_first hμ hs hsm).1.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / (36 * 4096) by norm_num)))
  refine ⟨n₀ + 2, by omega, ?_⟩
  have h1 := hn (3 * (n₀ + 2)) (by omega)
  have hpos : (0 : ℝ) < ((3 * (n₀ + 2) : ℕ) : ℝ) ^ 2 := by positivity
  rw [div_lt_iff₀ hpos] at h1
  rw [windowConst]
  push_cast at h1 ⊢
  nlinarith [show (0 : ℝ) ≤ n₀ from Nat.cast_nonneg _]

/-- **Paper: Theorem thm:poincare.** "There are u ≥ 2 and C₀ such that for every l ≥ 2, h = lu, and every price on U_h,
E_{g,k}|k,gk|² ≤ C₀ ∑_{j<h−1} E_k|k,x_jk|²." In the proof Z = L²(U_h,Y) has the sum for the mean; this scales all
distances by one factor. C₀ = 32C(2u)/(1−2c). -/
theorem thm_poincare {K : Type} [Field K] (hK : Contracting K) :
    ∃ u : ℕ, 2 ≤ u ∧ ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ l : ℕ, 2 ≤ l → ∀ w : U (l * u) → U (l * u) → ℝ, Nc.Price.IsPrice K w →
      (∑ g, ∑ k, w k (g * k) ^ 2) / (Fintype.card (U (l * u)) : ℝ) ^ 2 ≤
        C₀ * ∑ j, (∑ k, w k (x (l * u) j * k) ^ 2) / (Fintype.card (U (l * u)) : ℝ) := by
  obtain ⟨μ, s, hμ, hs, hsm, hcase⟩ := hK
  obtain ⟨u, hu, hC⟩ := thm_poincare_size hμ hs hsm
  refine ⟨u, hu, 32 * windowConst μ s (2 * u) / (1 - 2 * (1 / 4)),
    div_nonneg (by have := windowConst_nonneg μ s (2 * u); linarith) (by norm_num), fun l hl w hw => ?_⟩
  have hb : (0 : ℝ) < Fintype.card (U (l * u)) := by exact_mod_cast Fintype.card_pos
  obtain ⟨Y, hYm, hYc, f, hY, hf⟩ := prop_space hw
  have hCN : Cat.CN (PiLp 2 fun _ : U (l * u) => Y) := (lem_toolkit (Y := Y)).2.2.2.2.1 _
  have hA : ∀ z : PiLp 2 fun _ : U (l * u) => Y, Contr ((transAct (U (l * u)) Y).len z) μ s := by
    intro z
    obtain ⟨len, hlen, hcon⟩ := lengths_of_maps (by omega) (by linarith) hcase hY (fun k => z k)
    refine contracts_smul len _ (by omega) (c := √(Fintype.card (U (l * u)) : ℝ)) (fun g => ?_) hcon
    rw [hlen, Real.sqrt_div' _ hb.le, mul_div_cancel₀ _ (Real.sqrt_pos.2 hb).ne', IsoAct.len_val,
      ← Real.sqrt_sq (dist_nonneg (x := z) (y := (transAct (U (l * u)) Y).act g z)), transAct_dist]
    exact congrArg _ (sum_congr rfl fun k _ => by rw [dist_comm])
  have h1 := thm_poincare_action (transAct (U (l * u)) Y) hμ hs hsm hA hu hl rfl hC (WithLp.toLp 2 f)
  have h2 : ∀ g : U (l * u), dist (WithLp.toLp 2 f : PiLp 2 fun _ : U (l * u) => Y)
      ((transAct (U (l * u)) Y).act g (WithLp.toLp 2 f)) ^ 2 = ∑ k, w k (g * k) ^ 2 := by
    intro g
    rw [transAct_dist]
    refine sum_congr rfl fun k _ => ?_
    show dist (f (g * k)) (f k) ^ 2 = _
    rw [dist_comm, hf]
  simp only [h2] at h1
  rw [pow_two, ← div_div, ← Finset.sum_div, ← mul_div_assoc]
  exact div_le_div_of_nonneg_right h1 hb.le

/-- The inequality of Theorem thm:poincare for the numbers u and C₀: for every l ≥ 2, h = lu, and every price on U_h,
E_{g,k}|k,gk|² ≤ C₀ ∑_j E_k|k,x_jk|². -/
def PoincareBound (K : Type) [Field K] (u : ℕ) (C₀ : ℝ) : Prop :=
  ∀ l : ℕ, 2 ≤ l → ∀ w : U (l * u) → U (l * u) → ℝ, Nc.Price.IsPrice K w →
    (∑ g, ∑ k, w k (g * k) ^ 2) / (Fintype.card (U (l * u)) : ℝ) ^ 2 ≤
      C₀ * ∑ j, (∑ k, w k (x (l * u) j * k) ^ 2) / (Fintype.card (U (l * u)) : ℝ)

end Paper
