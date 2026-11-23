/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Cat.Core
import Nc.Cat.Prod

/-!
# The paper, section "Prices are nonpositively curved": CAT(0) spaces

The definition of CAT(0) spaces and Lemma lem:toolkit, part by part. All of it rests on the inequality (CN) alone, which is
the class Cat.CN. Two predicates of the library are used in the proofs: Cat.IsPt x v t b says that b satisfies the inequality
of part (a), and Cat.IsBary w x b that b satisfies the inequality of part (c), for weights w.
-/

namespace Paper

open Finset Filter Topology Cat

/-- The paper's definition: "A complete metric space is CAT(0) if any two points x, v have a midpoint and (CN) holds
for it." -/
theorem cat0_iff (X : Type) [MetricSpace X] : Cat.CN X ↔ CompleteSpace X ∧ ∀ x v : X, ∃ m,
    dist x m = dist x v / 2 ∧ dist m v = dist x v / 2 ∧
      ∀ z, dist z m ^ 2 ≤ 1 / 2 * dist z x ^ 2 + 1 / 2 * dist z v ^ 2 - (dist x v / 2) ^ 2 := by
  constructor
  · intro h
    refine ⟨h.toCompleteSpace, fun x v => ⟨Cat.mid x v, Cat.dist_mid_left x v, Cat.dist_mid_right x v, fun z => ?_⟩⟩
    linarith [Cat.cn x v z]
  · rintro ⟨hc, h⟩
    refine { hc with exists_mid := fun x v => ?_ }
    obtain ⟨m, -, -, hm⟩ := h x v
    exact ⟨m, fun z => by linarith [hm z]⟩

section Toolkit

variable {Y : Type*} [MetricSpace Y] [CN Y]

/-- The minimization behind parts (a), (c) and (d): "Strict convexity of the functions to be minimized, from (CN), makes
minimizing sequences converge; comparing the minimum with points close to it on [b,y], respectively [Py,q], gives the
inequalities." Let C be nonempty, closed and convex, and let Θ ≥ 0 be continuous with
Θ(m) ≤ ½Θ(x) + ½Θ(v) − (c/4)|xv|² for the midpoint m of x, v ∈ C, where c > 0. Then some b ∈ C has Θ(y) ≥ Θ(b) + c|yb|² for all
y ∈ C. -/
theorem lem_toolkit_minimization (C : Set Y) (hC : IsClosed C) (hne : C.Nonempty)
    (hmem : ∀ x ∈ C, ∀ v ∈ C, mid x v ∈ C) (Θ : Y → ℝ) (hF : Continuous Θ)
    (hF0 : ∀ x, 0 ≤ Θ x) {c : ℝ} (hc : 0 < c)
    (hconv : ∀ x ∈ C, ∀ v ∈ C, Θ (mid x v) ≤ (Θ x + Θ v) / 2 - c / 4 * dist x v ^ 2) :
    ∃ b ∈ C, ∀ y ∈ C, Θ b + c * dist y b ^ 2 ≤ Θ y := by
  set I := sInf (Θ '' C) with hI
  have hbdd : BddBelow (Θ '' C) := ⟨0, by rintro _ ⟨x, -, rfl⟩; exact hF0 x⟩
  have hle : ∀ y ∈ C, I ≤ Θ y := fun y hy => csInf_le hbdd ⟨y, hy, rfl⟩
  have hseq : ∀ n : ℕ, ∃ y ∈ C, Θ y < I + 1 / ((n : ℝ) + 1) := by
    intro n
    obtain ⟨_, ⟨y, hy, rfl⟩, h⟩ := Real.lt_sInf_add_pos (hne.image Θ)
      (show (0 : ℝ) < 1 / ((n : ℝ) + 1) by positivity)
    exact ⟨y, hy, h⟩
  choose u huC hu using hseq
  have hcauchy : CauchySeq u := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt (show 0 < c / 4 * ε ^ 2 by positivity)
    refine ⟨N, fun m hm n hn => ?_⟩
    have h1 := hconv _ (huC m) _ (huC n)
    have h2 := hle _ (hmem _ (huC m) _ (huC n))
    have hmono : ∀ k : ℕ, N ≤ k → 1 / ((k : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) := by
      intro k hk
      apply one_div_le_one_div_of_le (by positivity)
      have : (N : ℝ) ≤ k := by exact_mod_cast hk
      linarith
    have h3 := hu m
    have h4 := hu n
    have h5 := hmono m hm
    have h6 := hmono n hn
    have h7 : c / 4 * dist (u m) (u n) ^ 2 < c / 4 * ε ^ 2 := by linarith
    have h8 : dist (u m) (u n) ^ 2 < ε ^ 2 := lt_of_mul_lt_mul_left h7 (by positivity)
    exact lt_of_pow_lt_pow_left₀ 2 hε.le h8
  obtain ⟨b, hb⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hbC : b ∈ C := hC.mem_of_tendsto hb (Eventually.of_forall huC)
  have hFb : Θ b ≤ I := by
    have h1 : Tendsto (fun n => Θ (u n)) atTop (𝓝 (Θ b)) := (hF.tendsto b).comp hb
    have h2 : Tendsto (fun n : ℕ => I + 1 / ((n : ℝ) + 1)) atTop (𝓝 (I + 0)) :=
      tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat
    rw [add_zero] at h2
    exact le_of_tendsto_of_tendsto' h1 h2 fun n => (hu n).le
  refine ⟨b, hbC, ?_⟩
  have key : ∀ k : ℕ, ∀ y ∈ C, Θ b + c * (1 - (1 / 2) ^ k) * dist y b ^ 2 ≤ Θ y := by
    intro k
    induction k with
    | zero => intro y hy; simpa using hFb.trans (hle y hy)
    | succ k ih =>
      intro y hy
      have h1 := ih _ (hmem b hbC y hy)
      have h2 := hconv b hbC y hy
      rw [dist_comm _ b, dist_mid_left] at h1
      rw [dist_comm y b, pow_succ]
      nlinarith
  intro y hy
  have h1 : Tendsto (fun k : ℕ => Θ b + c * (1 - (1 / 2 : ℝ) ^ k) * dist y b ^ 2) atTop
      (𝓝 (Θ b + c * (1 - 0) * dist y b ^ 2)) := by
    apply Tendsto.const_add
    apply Tendsto.mul_const
    apply Tendsto.const_mul
    exact (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).const_sub 1
  rw [sub_zero, mul_one] at h1
  exact le_of_tendsto' h1 fun k => key k y hy

/-- The first half of part (c) with weights: points x_i with weights w_i ≥ 0 have a barycenter b, with
∑ w_i|yx_i|² ≥ (∑ w_i)|yb|² + ∑ w_i|bx_i|² for all y. It is the minimizer of y ↦ ∑ w_i|yx_i|² given by lem_toolkit_minimization. -/
theorem lem_toolkit_c_exists {ι : Type*} [Fintype ι] [Nonempty Y] (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (x : ι → Y) :
    ∃ b, IsBary w x b := by
  rcases (Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) => hw i).eq_or_lt with h0 | h0
  · have h : ∀ i, w i = 0 := by
      intro i
      have := (Finset.sum_eq_zero_iff_of_nonneg fun i (_ : i ∈ Finset.univ) => hw i).1 h0.symm
      exact this i (Finset.mem_univ i)
    exact ⟨Classical.arbitrary Y, fun y => by simp [h]⟩
  · obtain ⟨b, -, hb⟩ := lem_toolkit_minimization (Y := Y) Set.univ isClosed_univ Set.univ_nonempty
      (fun _ _ _ _ => Set.mem_univ _) (fun y => ∑ i, w i * dist y (x i) ^ 2) (by fun_prop)
      (fun y => Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (sq_nonneg _)) h0
      (by
        intro y _ y' _
        have h : ∀ i, w i * dist (mid y y') (x i) ^ 2 ≤
            w i * dist y (x i) ^ 2 / 2 + w i * dist y' (x i) ^ 2 / 2
              - w i * (dist y y' ^ 2 / 4) := by
          intro i
          have h1 := mul_le_mul_of_nonneg_left (cn y y' (x i)) (hw i)
          rw [dist_comm (x i), dist_comm (x i), dist_comm (x i)] at h1
          linarith
        calc ∑ i, w i * dist (mid y y') (x i) ^ 2
            ≤ ∑ i, (w i * dist y (x i) ^ 2 / 2 + w i * dist y' (x i) ^ 2 / 2
              - w i * (dist y y' ^ 2 / 4)) := Finset.sum_le_sum fun i _ => h i
          _ = _ := by
            rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.sum_div,
              ← Finset.sum_div, ← Finset.sum_mul]
            ring)
    exact ⟨b, fun y => hb y (Set.mem_univ y)⟩

/-- **Paper: Lemma lem:toolkit (a).** "For x, v and t ∈ [0,1] exactly one point γ(t) has distances t|xv|, (1−t)|xv| from
them, and |zγ(t)|² ≤ (1−t)|zx|² + t|zv|² − t(1−t)|xv|²." The point is the barycenter of x and v with the weights 1−t and t. -/
theorem lem_toolkit_a (x v : Y) (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) : ∃ γ : Y,
    (dist x γ = t * dist x v ∧ dist γ v = (1 - t) * dist x v) ∧
    (∀ γ', dist x γ' = t * dist x v → dist γ' v = (1 - t) * dist x v → γ' = γ) ∧
    ∀ z, dist z γ ^ 2 ≤ (1 - t) * dist z x ^ 2 + t * dist z v ^ 2 - t * (1 - t) * dist x v ^ 2 := by
  have : Nonempty Y := ⟨x⟩
  obtain ⟨b, hb⟩ := lem_toolkit_c_exists (Y := Y) (ι := Bool) (fun i => cond i t (1 - t))
    (by intro i; cases i <;> simp <;> linarith) (fun i => cond i v x)
  have hpt : IsPt x v t b := by
    intro z
    have h := hb z
    simp only [Fintype.sum_bool, cond_true, cond_false] at h
    have h2 := dist_triangle x b v
    rw [dist_comm x b] at h2
    have h3 : t * (1 - t) * dist x v ^ 2 ≤ t * (1 - t) * (dist b x + dist b v) ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg h0 (by linarith))
      exact pow_le_pow_left₀ dist_nonneg h2 2
    have h4 : 0 ≤ ((1 - t) * dist b x - t * dist b v) ^ 2 := sq_nonneg _
    nlinarith
  exact ⟨b, ⟨hpt.dist_left h0 h1, hpt.dist_right h0 h1⟩, fun _ e1 e2 => hpt.eq_of_dist e1 e2, hpt⟩

/-- Part (a) in the words of the library. -/
theorem lem_toolkit_a_isPt (x v : Y) {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) : ∃ b, IsPt x v t b := by
  obtain ⟨γ, -, -, h⟩ := lem_toolkit_a x v t h0 h1
  exact ⟨γ, h⟩

/-- A point with the distances of part (a) satisfies its inequality. -/
theorem lem_toolkit_a_of_dist {x v c : Y} {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) (e1 : dist x c = t * dist x v)
    (e2 : dist c v = (1 - t) * dist x v) : IsPt x v t c := by
  obtain ⟨γ, -, hu, h⟩ := lem_toolkit_a x v t h0 h1
  rw [hu c e1 e2]
  exact h

/-- The first step of the proof of part (b): for the point q at s on [p,p′], insert (a) twice into
t(1−t)|xv|² ≤ (1−t)|xq|² + t|qv|². -/
theorem lem_toolkit_b_box (x v p p' : Y) {s t : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    t * (1 - t) * dist x v ^ 2 + s * (1 - s) * dist p p' ^ 2 ≤
      (1 - t) * (1 - s) * dist x p ^ 2 + (1 - t) * s * dist x p' ^ 2
        + t * (1 - s) * dist v p ^ 2 + t * s * dist v p' ^ 2 := by
  obtain ⟨q, -, -, hq⟩ := lem_toolkit_a p p' s hs0 hs1
  have h1 := mul_le_mul_of_nonneg_left (hq x) (show 0 ≤ 1 - t by linarith)
  have h2 := mul_le_mul_of_nonneg_left (hq v) ht0
  have h3 := dist_triangle x q v
  rw [dist_comm q v] at h3
  have h4 : t * (1 - t) * dist x v ^ 2 ≤ t * (1 - t) * (dist x q + dist v q) ^ 2 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ dist_nonneg h3 2)
      (mul_nonneg ht0 (by linarith))
  have h5 : 0 ≤ ((1 - t) * dist x q - t * dist v q) ^ 2 := sq_nonneg _
  nlinarith

/-- The second step of the proof of part (b), the choice of the parameter: it gives the first inequality of (b), here as
|x₁x₃|² + |x₂x₄|² ≤ |x₁x₂|² + |x₃x₄|² + 2|x₂x₃||x₁x₄|. -/
theorem lem_toolkit_b_first (x₁ x₂ x₃ x₄ : Y) :
    dist x₁ x₃ ^ 2 + dist x₂ x₄ ^ 2 ≤
      dist x₁ x₂ ^ 2 + dist x₃ x₄ ^ 2 + 2 * dist x₂ x₃ * dist x₁ x₄ := by
  have key : dist x₁ x₃ ^ 2 + dist x₂ x₄ ^ 2 - dist x₁ x₂ ^ 2 - dist x₃ x₄ ^ 2 ≤
      2 * dist x₁ x₄ * dist x₂ x₃ := by
    apply le_two_mul_of_forall dist_nonneg dist_nonneg
    intro τ hτ
    have hs0 : 0 ≤ τ / (1 + τ) := by positivity
    have hs1 : τ / (1 + τ) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
    have h := lem_toolkit_b_box x₁ x₃ x₄ x₂ hs0 hs1 hs0 hs1
    have e1 : 1 - τ / (1 + τ) = 1 / (1 + τ) := by field_simp; ring
    rw [e1] at h
    have hpos : 0 < (1 + τ) ^ 2 / τ := by positivity
    have h2 := mul_le_mul_of_nonneg_left h hpos.le
    have e2 : (1 + τ) ^ 2 / τ * (τ / (1 + τ) * (1 / (1 + τ)) * dist x₁ x₃ ^ 2 +
        τ / (1 + τ) * (1 / (1 + τ)) * dist x₄ x₂ ^ 2) =
        dist x₁ x₃ ^ 2 + dist x₄ x₂ ^ 2 := by field_simp
    have e3 : (1 + τ) ^ 2 / τ * (1 / (1 + τ) * (1 / (1 + τ)) * dist x₁ x₄ ^ 2 +
        1 / (1 + τ) * (τ / (1 + τ)) * dist x₁ x₂ ^ 2 +
        τ / (1 + τ) * (1 / (1 + τ)) * dist x₃ x₄ ^ 2 +
        τ / (1 + τ) * (τ / (1 + τ)) * dist x₃ x₂ ^ 2) =
        dist x₁ x₄ ^ 2 / τ + dist x₁ x₂ ^ 2 + dist x₃ x₄ ^ 2 + τ * dist x₃ x₂ ^ 2 := by
      field_simp
    rw [e2, e3, dist_comm x₄ x₂, dist_comm x₃ x₂] at h2
    linarith
  linarith

/-- **Paper: Lemma lem:toolkit (b).** "|xv|² + |yu|² ≤ |xu|² + |yv|² + 2|xy||uv|; in particular the squared diagonals of a
quadrangle add up to at most its squared sides, and if there is equality, opposite sides are equal." -/
theorem lem_toolkit_b (x v y u : Y) :
    dist x v ^ 2 + dist y u ^ 2 ≤ dist x u ^ 2 + dist y v ^ 2 + 2 * dist x y * dist u v ∧
    dist x v ^ 2 + dist y u ^ 2 ≤ dist x y ^ 2 + dist y v ^ 2 + dist v u ^ 2 + dist x u ^ 2 ∧
    (dist x v ^ 2 + dist y u ^ 2 = dist x y ^ 2 + dist y v ^ 2 + dist v u ^ 2 + dist x u ^ 2 →
      dist x y = dist v u ∧ dist y v = dist x u) := by
  have h1 : dist x v ^ 2 + dist y u ^ 2 ≤ dist x u ^ 2 + dist y v ^ 2 + 2 * dist x y * dist u v := by
    have h := lem_toolkit_b_first x u v y
    rw [dist_comm u y, dist_comm v y] at h
    linarith
  have h2 : dist x v ^ 2 + dist y u ^ 2 ≤ dist x y ^ 2 + dist v u ^ 2 + 2 * dist y v * dist x u :=
    lem_toolkit_b_first x y v u
  refine ⟨h1, by nlinarith [sq_nonneg (dist y v - dist x u)], fun he => ⟨?_, ?_⟩⟩
  · have h3 : (dist x y - dist v u) ^ 2 ≤ 0 := by
      rw [dist_comm u v] at h1
      nlinarith
    have h4 := pow_eq_zero_iff two_ne_zero |>.1 (le_antisymm h3 (sq_nonneg _))
    linarith
  · have h3 : (dist y v - dist x u) ^ 2 ≤ 0 := by nlinarith
    have h4 := pow_eq_zero_iff two_ne_zero |>.1 (le_antisymm h3 (sq_nonneg _))
    linarith

/-- The second half of part (c) with weights: (∑ w_i)|bb′| ≤ ∑ w_i|x_ix′_i|. "Adding the inequality of (c) for (b,x) at b′
and for (b′,x′) at b, and applying (b) to every b, b′, x_i, x′_i". -/
theorem lem_toolkit_c_contract {ι : Type*} [Fintype ι] {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) {x x' : ι → Y} {b b' : Y}
    (h : IsBary w x b) (h' : IsBary w x' b') :
    (∑ i, w i) * dist b b' ≤ ∑ i, w i * dist (x i) (x' i) := by
  rcases (dist_nonneg (x := b) (y := b')).eq_or_lt with h0 | h0
  · rw [← h0, mul_zero]
    exact Finset.sum_nonneg fun i _ => mul_nonneg (hw i) dist_nonneg
  have h1 := h b'
  have h2 := h' b
  rw [dist_comm b' b] at h1
  have h3 : ∀ i, w i * dist b' (x i) ^ 2 + w i * dist b (x' i) ^ 2 ≤
      w i * dist b (x i) ^ 2 + w i * dist b' (x' i) ^ 2
        + 2 * dist b b' * (w i * dist (x i) (x' i)) := by
    intro i
    have h4 := mul_le_mul_of_nonneg_left (lem_toolkit_b b' (x i) b (x' i)).1 (hw i)
    rw [dist_comm (x' i) (x i), dist_comm b' b] at h4
    linarith
  have h5 := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => h3 i
  simp only [Finset.sum_add_distrib] at h5
  rw [← Finset.mul_sum] at h5
  have h6 : dist b b' * ((∑ i, w i) * dist b b') ≤
      dist b b' * ∑ i, w i * dist (x i) (x' i) := by nlinarith
  exact le_of_mul_le_mul_left h6 h0

/-- **Paper: Lemma lem:toolkit (c).** "Points x₁, …, x_n, n ≥ 1, have a barycenter b, the minimizer of y ↦ ∑|yx_i|², with
∑|yx_i|² ≥ n|yb|² + ∑|bx_i|² for all y; if b′ is that of x′₁, …, x′_n, then n|bb′| ≤ ∑|x_ix′_i|." Here a barycenter is a
point with the displayed inequality; by lem_toolkit_c_minimizer this is the same as being the minimizer, and there is exactly
one. -/
theorem lem_toolkit_c :
    (∀ (n : ℕ) (x : Fin n → Y), 0 < n → ∃ b, ∀ y,
      (n : ℝ) * dist y b ^ 2 + ∑ i, dist b (x i) ^ 2 ≤ ∑ i, dist y (x i) ^ 2) ∧
    ∀ (n : ℕ) (x x' : Fin n → Y) (b b' : Y),
      (∀ y, (n : ℝ) * dist y b ^ 2 + ∑ i, dist b (x i) ^ 2 ≤ ∑ i, dist y (x i) ^ 2) →
      (∀ y, (n : ℝ) * dist y b' ^ 2 + ∑ i, dist b' (x' i) ^ 2 ≤ ∑ i, dist y (x' i) ^ 2) →
      (n : ℝ) * dist b b' ≤ ∑ i, dist (x i) (x' i) := by
  constructor
  · intro n x hn
    have : Nonempty Y := ⟨x ⟨0, hn⟩⟩
    obtain ⟨b, hb⟩ := lem_toolkit_c_exists (fun _ : Fin n => (1 : ℝ)) (fun _ => zero_le_one) x
    refine ⟨b, fun y => ?_⟩
    have := hb y
    simp only [one_mul, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at this
    linarith
  · intro n x x' b b' hb hb'
    have conv : ∀ (x : Fin n → Y) (b : Y),
        (∀ y, (n : ℝ) * dist y b ^ 2 + ∑ i, dist b (x i) ^ 2 ≤ ∑ i, dist y (x i) ^ 2) →
          IsBary (fun _ => (1 : ℝ)) x b := by
      intro x b h y
      simp only [one_mul, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
      linarith [h y]
    simpa using lem_toolkit_c_contract (fun _ => zero_le_one) (conv x b hb) (conv x' b' hb')

/-- Part (c): the barycenter is "the minimizer of y ↦ ∑|yx_i|²". For n ≥ 1 there is exactly one minimizer, and a point is the
minimizer if and only if it satisfies the inequality of (c), by which lem_toolkit_c describes the barycenter. -/
theorem lem_toolkit_c_minimizer {n : ℕ} (hn : 0 < n) (x : Fin n → Y) :
    (∃! b, ∀ y, ∑ i, dist b (x i) ^ 2 ≤ ∑ i, dist y (x i) ^ 2) ∧
    ∀ b, (∀ y, (n : ℝ) * dist y b ^ 2 + ∑ i, dist b (x i) ^ 2 ≤ ∑ i, dist y (x i) ^ 2) ↔
      ∀ y, ∑ i, dist b (x i) ^ 2 ≤ ∑ i, dist y (x i) ^ 2 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨b₀, h₀⟩ := lem_toolkit_c.1 n x hn
  have hmin : ∀ b, (∀ y, (n : ℝ) * dist y b ^ 2 + ∑ i, dist b (x i) ^ 2 ≤ ∑ i, dist y (x i) ^ 2) →
      ∀ y, ∑ i, dist b (x i) ^ 2 ≤ ∑ i, dist y (x i) ^ 2 := fun b h y => by
    nlinarith [h y, sq_nonneg (dist y b)]
  have huniq : ∀ b, (∀ y, ∑ i, dist b (x i) ^ 2 ≤ ∑ i, dist y (x i) ^ 2) → b = b₀ := fun b h => by
    have h1 : (n : ℝ) * dist b b₀ ^ 2 ≤ 0 := by linarith [h₀ b, h b₀]
    have h2 : dist b b₀ ^ 2 ≤ 0 := by nlinarith
    exact dist_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 (le_antisymm h2 (sq_nonneg _)))
  exact ⟨⟨b₀, hmin b₀ h₀, huniq⟩, fun b => ⟨hmin b, fun h => (huniq b h).symm ▸ h₀⟩⟩

/-- **Paper: Lemma lem:toolkit (d).** "A nonempty closed convex F has nearest points Py, with |yq|² ≥ |yPy|² + |Py,q|² for
q ∈ F." A set is convex if it contains the midpoints of its points. -/
theorem lem_toolkit_d (F : Set Y) (hF : IsClosed F) (hne : F.Nonempty)
    (hconv : ∀ x ∈ F, ∀ v ∈ F, ∀ m, dist x m = dist x v / 2 → dist m v = dist x v / 2 → m ∈ F) (y : Y) :
    ∃ P ∈ F, (∀ q ∈ F, dist y P ≤ dist y q) ∧ ∀ q ∈ F, dist y P ^ 2 + dist P q ^ 2 ≤ dist y q ^ 2 := by
  obtain ⟨P, hP, h⟩ := lem_toolkit_minimization F hF hne
    (fun x hx v hv => hconv x hx v hv _ (dist_mid_left x v) (dist_mid_right x v))
    (fun q => dist y q ^ 2) (by fun_prop) (fun _ => sq_nonneg _) one_pos
    (fun x _ v _ => by linarith [cn x v y])
  have h' : ∀ q ∈ F, dist y P ^ 2 + dist P q ^ 2 ≤ dist y q ^ 2 := fun q hq => by
    have := h q hq
    rw [dist_comm P q]
    linarith
  exact ⟨P, hP, fun q hq => (abs_le_of_sq_le_sq' (by nlinarith [h' q hq]) dist_nonneg).2, h'⟩

/-- Part (e) for factors that may differ. -/
theorem lem_toolkit_e_general {ι : Type*} [Fintype ι] {X : ι → Type*} [∀ i, MetricSpace (X i)] [∀ i, CN (X i)] :
    CN (PiLp 2 X) where
  exists_mid x v := by
    refine ⟨WithLp.toLp 2 fun i => mid (x i) (v i), fun z => ?_⟩
    simp only [piLp_dist_sq]
    calc ∑ i, dist (z i) (mid (x i) (v i)) ^ 2
        ≤ ∑ i, ((dist (z i) (x i) ^ 2 + dist (z i) (v i) ^ 2) / 2
          - dist (x i) (v i) ^ 2 / 4) := Finset.sum_le_sum fun i _ => cn _ _ _
      _ = _ := by
        rw [Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.sum_div, Finset.sum_add_distrib]

/-- **Paper: Lemma lem:toolkit (e).** "Finite L² products of copies of Y are CAT(0)." -/
theorem lem_toolkit_e (ι : Type) [Fintype ι] : CN (PiLp 2 fun _ : ι => Y) := lem_toolkit_e_general

/-! Part (f). The letters are those of the paper: |xy| = |uv| = δ, |xu| = |yv| = h, a is the point at s on [x,u] and b the
point at t on [y,v]. The steps before the last one ask only that the squared diagonals add up to at least 2h² + 2δ² (a flat
parallelogram). The form Φ(p,p′;r,r′) = |pr′|² + |p′r|² − |pr|² − |p′r′|² is at most 2|pp′||rr′| by (b), and it is additive when
[p,p′] and [r,r′] are cut; so equality for the whole is inherited by the parts. -/

/-- Φ(p,p′;r,r′) ≤ 2|pp′||rr′|, by part (b). -/
theorem lem_toolkit_f_form (p p' r r' : Y) :
    dist p r' ^ 2 + dist p' r ^ 2 - dist p r ^ 2 - dist p' r' ^ 2 ≤ 2 * dist p p' * dist r r' := by
  linarith [(lem_toolkit_b p r' p' r).1]

/-- The form is additive, Φ(x,u;y,v) = Φ(x,a;y,b) + Φ(x,a;b,v) + Φ(a,u;y,b) + Φ(a,u;b,v), and the four bounds of
lem_toolkit_f_form add up to 2h², which is at most Φ(x,u;y,v) by hypothesis. So all four are equalities; the first one says
|xb|² + |ay|² − δ² − |ab|² = 2sth². -/
theorem lem_toolkit_f_parts {x u v y a b : Y} {h δ s t : ℝ} (hp : dist x u = h) (hp' : dist y v = h)
    (hq : dist u v = δ) (hq' : dist x y = δ)
    (hd : 2 * h ^ 2 + 2 * δ ^ 2 ≤ dist x v ^ 2 + dist u y ^ 2)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (ha : IsPt x u s a) (hb : IsPt y v t b) :
    dist x b ^ 2 + dist a y ^ 2 - δ ^ 2 - dist a b ^ 2 = 2 * s * t * h ^ 2 := by
  have e1 := ha.dist_left hs0 hs1
  have e2 := ha.dist_right hs0 hs1
  have e3 := hb.dist_left ht0 ht1
  have e4 := hb.dist_right ht0 ht1
  rw [hp] at e1 e2
  rw [hp'] at e3 e4
  have f1 := lem_toolkit_f_form x a y b
  have f2 := lem_toolkit_f_form x a b v
  have f3 := lem_toolkit_f_form a u y b
  have f4 := lem_toolkit_f_form a u b v
  rw [e1, e3, hq'] at f1
  rw [e1, e4] at f2
  rw [e2, e3] at f3
  rw [e2, e4, hq] at f4
  nlinarith

/-- The case s = t: then |ab| = δ, and |xb|² and |ay|² have the values that the inequality of (a) allows at most. -/
theorem lem_toolkit_f_same {x u v y a b : Y} {h δ s : ℝ} (hp : dist x u = h) (hp' : dist y v = h)
    (hq : dist u v = δ) (hq' : dist x y = δ)
    (hd : 2 * h ^ 2 + 2 * δ ^ 2 ≤ dist x v ^ 2 + dist u y ^ 2)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ha : IsPt x u s a) (hb : IsPt y v s b) :
    dist a b = δ ∧ dist x b ^ 2 = (1 - s) * δ ^ 2 + s * dist x v ^ 2 - s * (1 - s) * h ^ 2 ∧
      dist a y ^ 2 = (1 - s) * δ ^ 2 + s * dist u y ^ 2 - s * (1 - s) * h ^ 2 := by
  have h1 := lem_toolkit_f_parts hp hp' hq hq' hd hs0 hs1 hs0 hs1 ha hb
  have h2 := lem_toolkit_b_first x a b y
  have e1 := ha.dist_left hs0 hs1
  have e3 := hb.dist_left hs0 hs1
  rw [hp] at e1
  rw [hp'] at e3
  rw [dist_comm b y, e1, e3, hq'] at h2
  have h3 : (dist a b - δ) ^ 2 ≤ 0 := by nlinarith
  have h4 : dist a b = δ := by
    have : dist a b - δ = 0 := pow_eq_zero_iff two_ne_zero |>.1 (le_antisymm h3 (sq_nonneg _))
    linarith
  have h5 := hb x
  have h6 := ha y
  rw [hp', hq'] at h5
  rw [hp, dist_comm y a, dist_comm y x, dist_comm y u, hq'] at h6
  have h7 := (lem_toolkit_b x v u y).2.1
  rw [hp, hq, hq', dist_comm v y, hp'] at h7
  rw [h4] at h1
  have h8 : dist x v ^ 2 + dist u y ^ 2 = 2 * h ^ 2 + 2 * δ ^ 2 := le_antisymm (by linarith) hd
  have h9 : s * dist x v ^ 2 + s * dist u y ^ 2 = s * (2 * h ^ 2 + 2 * δ ^ 2) := by
    rw [← mul_add, h8]
  refine ⟨h4, ?_, ?_⟩ <;> nlinarith

/-- The values of |xb|² and |ay|² from lem_toolkit_f_same, inserted into lem_toolkit_f_parts: the formula for |ab|², still in
terms of the two diagonals. -/
theorem lem_toolkit_f_parallelogram {x u v y a b : Y} {h δ s t : ℝ} (hp : dist x u = h) (hp' : dist y v = h)
    (hq : dist u v = δ) (hq' : dist x y = δ)
    (hd : 2 * h ^ 2 + 2 * δ ^ 2 ≤ dist x v ^ 2 + dist u y ^ 2)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (ha : IsPt x u s a) (hb : IsPt y v t b) :
    dist a b ^ 2 = (1 - s - t) * δ ^ 2 + t * dist x v ^ 2 + s * dist u y ^ 2
      - s * (1 - s) * h ^ 2 - t * (1 - t) * h ^ 2 - 2 * s * t * h ^ 2 := by
  have h1 := lem_toolkit_f_parts hp hp' hq hq' hd hs0 hs1 ht0 ht1 ha hb
  obtain ⟨a', ha'⟩ := lem_toolkit_a_isPt x u ht0 ht1
  obtain ⟨b', hb'⟩ := lem_toolkit_a_isPt y v hs0 hs1
  have h2 := (lem_toolkit_f_same hp hp' hq hq' hd ht0 ht1 ha' hb).2.1
  have h3 := (lem_toolkit_f_same hp hp' hq hq' hd hs0 hs1 ha hb').2.2
  rw [h2, h3] at h1
  linarith

/-- Part (f), with a ∈ [x,u] and b ∈ [y,v] given by the inequality of (a) (Cat.IsPt), and with lower bounds for the diagonals. -/
theorem lem_toolkit_f_isPt {x u v y a b : Y} {h δ s t : ℝ} (hp : dist x u = h) (hp' : dist y v = h)
    (hq : dist u v = δ) (hq' : dist x y = δ)
    (hd : h ^ 2 + δ ^ 2 ≤ dist x v ^ 2) (hd' : h ^ 2 + δ ^ 2 ≤ dist u y ^ 2)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (ha : IsPt x u s a) (hb : IsPt y v t b) :
    dist a b ^ 2 = δ ^ 2 + (s - t) ^ 2 * h ^ 2 := by
  have hab := lem_toolkit_f_parallelogram hp hp' hq hq' (by linarith) hs0 hs1 ht0 ht1 ha hb
  have h7 := (lem_toolkit_b x v u y).2.1
  rw [hp, hq, hq', dist_comm v y, hp'] at h7
  have h8 : dist x v ^ 2 = h ^ 2 + δ ^ 2 := by linarith
  have h9 : dist u y ^ 2 = h ^ 2 + δ ^ 2 := by linarith
  rw [hab, h8, h9]
  ring

/-- **Paper: Lemma lem:toolkit (f).** "Flat rectangles: if |xy| = |uv| = δ, |xu| = |yv| = h and both diagonals have squared
length δ² + h², and a ∈ [x,u], b ∈ [y,v] have |xa| = sh, |yb| = th, then |ab|² = δ² + h²(s−t)²." -/
theorem lem_toolkit_f (x y u v a b : Y) (δ h s t : ℝ) (hxy : dist x y = δ) (huv : dist u v = δ) (hxu : dist x u = h)
    (hyv : dist y v = h) (d1 : dist x v ^ 2 = δ ^ 2 + h ^ 2) (d2 : dist y u ^ 2 = δ ^ 2 + h ^ 2) (hs0 : 0 ≤ s)
    (hs1 : s ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (a1 : dist x a = s * dist x u) (a2 : dist a u = (1 - s) * dist x u)
    (b1 : dist y b = t * dist y v) (b2 : dist b v = (1 - t) * dist y v) :
    dist a b ^ 2 = δ ^ 2 + h ^ 2 * (s - t) ^ 2 := by
  have := lem_toolkit_f_isPt (x := x) (u := u) (y := y) (v := v) (a := a) (b := b) hxu hyv huv hxy
    (by linarith) (by rw [dist_comm u y]; linarith) hs0 hs1 ht0 ht1 (lem_toolkit_a_of_dist hs0 hs1 a1 a2)
    (lem_toolkit_a_of_dist ht0 ht1 b1 b2)
  linarith

end Toolkit

open Cat in
/-- **Paper: Lemma lem:toolkit.** "Let Y be CAT(0). (a) For x, v and t ∈ [0,1] exactly one point γ(t) has distances t|xv|,
(1−t)|xv| from them, and |zγ(t)|² ≤ (1−t)|zx|² + t|zv|² − t(1−t)|xv|². (b) |xv|² + |yu|² ≤ |xu|² + |yv|² + 2|xy||uv|; in
particular the squared diagonals of a quadrangle add up to at most its squared sides, and if there is equality, opposite sides
are equal. (c) Points x₁, …, x_n, n ≥ 1, have a barycenter b, the minimizer of y ↦ ∑|yx_i|², with
∑|yx_i|² ≥ n|yb|² + ∑|bx_i|² for all y; if b′ is that of x′₁, …, x′_n, then n|bb′| ≤ ∑|x_ix′_i|. (d) A nonempty closed
convex F has nearest points Py, with |yq|² ≥ |yPy|² + |Py,q|² for q ∈ F. (e) Finite L² products of copies of Y are CAT(0).
(f) Flat rectangles: if |xy| = |uv| = δ, |xu| = |yv| = h and both diagonals have squared length δ² + h², and a ∈ [x,u],
b ∈ [y,v] have |xa| = sh, |yb| = th, then |ab|² = δ² + h²(s−t)²." In (c) a barycenter is a point with the displayed
inequality; by lem_toolkit_c_minimizer this is the same as being the minimizer, and there is exactly one. -/
theorem lem_toolkit {Y : Type} [MetricSpace Y] [CN Y] :
    (∀ (x v : Y) (t : ℝ), 0 ≤ t → t ≤ 1 → ∃ γ : Y,
      (dist x γ = t * dist x v ∧ dist γ v = (1 - t) * dist x v) ∧
      (∀ γ', dist x γ' = t * dist x v → dist γ' v = (1 - t) * dist x v → γ' = γ) ∧
      ∀ z, dist z γ ^ 2 ≤ (1 - t) * dist z x ^ 2 + t * dist z v ^ 2 - t * (1 - t) * dist x v ^ 2) ∧
    (∀ x v y u : Y,
      dist x v ^ 2 + dist y u ^ 2 ≤ dist x u ^ 2 + dist y v ^ 2 + 2 * dist x y * dist u v ∧
      dist x v ^ 2 + dist y u ^ 2 ≤ dist x y ^ 2 + dist y v ^ 2 + dist v u ^ 2 + dist x u ^ 2 ∧
      (dist x v ^ 2 + dist y u ^ 2 = dist x y ^ 2 + dist y v ^ 2 + dist v u ^ 2 + dist x u ^ 2 →
        dist x y = dist v u ∧ dist y v = dist x u)) ∧
    ((∀ (n : ℕ) (x : Fin n → Y), 0 < n → ∃ b, ∀ y,
        (n : ℝ) * dist y b ^ 2 + ∑ i, dist b (x i) ^ 2 ≤ ∑ i, dist y (x i) ^ 2) ∧
      ∀ (n : ℕ) (x x' : Fin n → Y) (b b' : Y),
        (∀ y, (n : ℝ) * dist y b ^ 2 + ∑ i, dist b (x i) ^ 2 ≤ ∑ i, dist y (x i) ^ 2) →
        (∀ y, (n : ℝ) * dist y b' ^ 2 + ∑ i, dist b' (x' i) ^ 2 ≤ ∑ i, dist y (x' i) ^ 2) →
        (n : ℝ) * dist b b' ≤ ∑ i, dist (x i) (x' i)) ∧
    (∀ F : Set Y, IsClosed F → F.Nonempty →
      (∀ x ∈ F, ∀ v ∈ F, ∀ m, dist x m = dist x v / 2 → dist m v = dist x v / 2 → m ∈ F) →
      ∀ y, ∃ P ∈ F, (∀ q ∈ F, dist y P ≤ dist y q) ∧ ∀ q ∈ F, dist y P ^ 2 + dist P q ^ 2 ≤ dist y q ^ 2) ∧
    (∀ (ι : Type) [Fintype ι], CN (PiLp 2 fun _ : ι => Y)) ∧
    ∀ (x y u v a b : Y) (δ h s t : ℝ), dist x y = δ → dist u v = δ → dist x u = h → dist y v = h →
      dist x v ^ 2 = δ ^ 2 + h ^ 2 → dist y u ^ 2 = δ ^ 2 + h ^ 2 → 0 ≤ s → s ≤ 1 → 0 ≤ t → t ≤ 1 →
      dist x a = s * dist x u → dist a u = (1 - s) * dist x u →
      dist y b = t * dist y v → dist b v = (1 - t) * dist y v →
      dist a b ^ 2 = δ ^ 2 + h ^ 2 * (s - t) ^ 2 :=
  ⟨lem_toolkit_a, lem_toolkit_b, lem_toolkit_c, lem_toolkit_d, fun ι _ => lem_toolkit_e ι, lem_toolkit_f⟩

end Paper
