/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.TimeClaims.Sec3.Arithmetic
public import ThreeSumApsp.Util.Asymptotics.LogU

/-!
# Running-time claims of Section 3.4: Theorems 21 and 22

All lemmas are about an arbitrary interpretation `M : DetTimeModel` of "is solved in time T".  They
are deductions between running-time sentences: those of the paper for Theorem 22, and for
Theorem 21, which the paper cites, those of the route taken here.

* Theorem 21(a) from two reductions, [CH20, Theorem 5.1] followed by [VW13, Theorem 4.3]:
  `Theorem21a.of_CH20_VW13`.  The sizes, numbers of instances and extra times compose
  by the rules for `n^{a+o(1)}`.
* Theorem 21(b) for the (min,+)-product from [VW13, Theorem 3.3] and [VW18, Theorem 4.2]:
  `Theorem21b.minPlus_of_VW13_VW18`.  The time of the first reduction is again a good
  time (`GoodTime.mul_logU`), and `log (cU) = O(log U)` (`dominated_logU_mul`).
* Theorem 21(b) for APSP by repeated squaring: `Theorem21b.apsp_of_minPlus`, whose
  arithmetic is `dominated_repeatedSquaring`.
* "Plug Theorem 19 into Theorem 21": `threeSum_of_uniform_theorem_21a`,
  `minPlus_of_uniform_theorem_21b`, `apsp_of_uniform_theorem_21b`.
* Theorem 22: the roundings such as `n^{2-1/1296+o(1)} ≤ O(n^{1.99923})`
  (`Claim.SolvedAlongPow.mono`).
-/

@[expose] public section

namespace ThreeSumApsp

/-! ## Theorem 21(a) -/

/-- Theorem 21(a) from two reductions: [CH20, Theorem 5.1] followed by [VW13, Theorem 4.3]. -/
theorem Theorem21a.of_CH20_VW13 (M : DetTimeModel) (hCH : Claim.CH20_Theorem_5_1 M)
    (hVW : Claim.VW13_Theorem_4_3 M) : Claim.Theorem_21a M := by
  obtain ⟨c, E₂, Num₂, size₂, hc, hE₂, hNum₂, hsize₂, hsize₂_pos, hVW⟩ := hVW
  intro κ hκ
  obtain ⟨E₁, Num₁, mag₁, N, c', κ', hE₁, hNum₁, hN, hpos, hCH⟩ := hCH κ hκ
  have hN' := hN.isPowLittleO
  have hwords : IsPowLittleO (fun n : ℕ => 1 + logU (mag₁ n)) 0 :=
    ((isPowPolylog_const 1).add (isPowPolylog_logU_of_le fun n hn => (hpos n hn).2)).isPowLittleO
  refine ⟨fun n => E₁ n + Num₁ n * (E₂ (N n) * (1 + logU (mag₁ n))), fun n => Num₁ n * Num₂ (N n),
    fun n => c * mag₁ n, fun n => size₂ (N n), c * c', κ', ?_, ?_, ?_, fun n hn => ?_,
    fun T hT => ?_⟩
  · -- the extra time: `Õ(n^{3/2}) + Õ(1) · N^{3/2+o(1)} · Õ(1)`
    exact hE₁.isPowLittleO.add ((hNum₁.isPowLittleO.mul
      ((hE₂.comp hN' (by norm_num) (by norm_num)).mul hwords)).mono (by norm_num))
  · -- the number of instances: `Õ(1) · O(N^{1/2})`
    exact (hNum₁.isPowLittleO.mul
      (hNum₂.isPowLittleO.comp hN' (by norm_num) (by norm_num))).mono (by norm_num)
  · -- their size: `O(N^{1/2})`
    exact (hsize₂.isPowLittleO.comp hN' (by norm_num) (by norm_num)).mono (by norm_num)
  · obtain ⟨hN1, hmag1, hmag⟩ := hpos n hn
    refine ⟨hsize₂_pos _ hN1, one_le_mul_of_one_le_of_one_le hc hmag1, ?_⟩
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left hmag (zero_le_one.trans hc)
  · obtain ⟨T', hT', hb⟩ := hCH _ (hVW T hT)
    exact ⟨T', hT', fun n hn => (hb n hn).trans (le_of_eq (by ring))⟩

/-! ## Theorem 21(b): the (min,+)-product -/

/-- A good time is at least `1 + log u`. -/
theorem GoodTime.one_add_logU_le {T : ℕ → ℝ → ℝ} (hT : GoodTime T) {s : ℕ} (hs : 1 ≤ s) (u : ℝ) :
    1 + logU u ≤ T s u :=
  (le_mul_of_one_le_left (zero_le_one.trans (one_le_one_add_logU u))
    (one_le_pow₀ (Nat.one_le_cast.2 hs))).trans (hT.1 s u hs)

/-- A good time is nonnegative. -/
theorem GoodTime.nonneg {T : ℕ → ℝ → ℝ} (hT : GoodTime T) {s : ℕ} (hs : 1 ≤ s) (u : ℝ) :
    0 ≤ T s u :=
  (zero_le_one.trans (one_le_one_add_logU u)).trans (hT.one_add_logU_le hs u)

/-- The time `C T(s) log U` that [VW13, Theorem 3.3] gives for Negative Triangle is again a good
time. -/
theorem GoodTime.mul_logU {T : ℕ → ℝ → ℝ} (hT : GoodTime T) {c C : ℝ} (hc : 1 ≤ c) (hC : 2 ≤ C) :
    GoodTime fun s U => C * (T s (c * U) * logU U) := by
  refine ⟨fun s u hs => ?_, fun u s₁ s₂ hs₁ hs => ?_⟩
  · have hT0 := hT.nonneg hs (c * u)
    have hhalf : 1 / 2 ≤ logU u := Real.one_half_lt_log_two.le.trans (log_two_le_logU u)
    calc (s : ℝ) ^ 2 * (1 + logU u) ≤ (s : ℝ) ^ 2 * (1 + logU (c * u)) := by
          gcongr
          exact logU_le_logU_mul hc u
      _ ≤ T s (c * u) := hT.1 s _ hs
      _ = 2 * (T s (c * u) * (1 / 2)) := by ring
      _ ≤ C * (T s (c * u) * logU u) := by gcongr
  · calc C * (T s₁ (c * u) * logU u) / s₁ = C * logU u * (T s₁ (c * u) / s₁) := by ring
      _ ≤ C * logU u * (T s₂ (c * u) / s₂) :=
          mul_le_mul_of_nonneg_left (hT.2 (c * u) s₁ s₂ hs₁ hs)
            (mul_nonneg (zero_le_two.trans hC) (logU_pos u).le)
      _ = C * (T s₂ (c * u) * logU u) / s₂ := by ring

/-- Theorem 21(b), (min,+)-product, from two reductions: [VW13, Theorem 3.3] followed by
[VW18, Theorem 4.2]. -/
theorem Theorem21b.minPlus_of_VW13_VW18 (M : DetTimeModel)
    (h33 : Claim.VW13_Theorem_3_3 M) (h42 : Claim.VW18_Theorem_4_2 M) :
    Claim.Theorem_21b_minPlus M := by
  obtain ⟨c₁, C₁, hc₁, hC₁, h33⟩ := h33
  obtain ⟨c₂, C₂, hc₂, hC₂, h42⟩ := h42
  obtain ⟨B, hB0, hB⟩ := dominated_logU_mul hc₂
  refine ⟨c₁ * c₂, C₂ * (C₁ * B), one_le_mul_of_one_le_of_one_le hc₁ hc₂, fun T hT hex => ?_⟩
  obtain ⟨T'', hT'', hb⟩ := h42 _ (hT.mul_logU hc₁ hC₁) (h33 T hT hex)
  refine ⟨T'', hT'', fun n U hn hU => ?_⟩
  have hT0 := hT.nonneg (one_le_cbrtCeil hn) (c₁ * (c₂ * U))
  have hC₁0 : 0 ≤ C₁ := zero_le_two.trans hC₁
  have hlogU := (logU_pos U).le
  have hlogcU := (logU_pos (c₂ * U)).le
  calc T'' n U
      ≤ C₂ * ((n : ℝ) ^ 2 * (C₁ * (T (cbrtCeil n) (c₁ * (c₂ * U)) * logU (c₂ * U))) * logU U) :=
        hb n U hn hU
    _ ≤ C₂ * ((n : ℝ) ^ 2 * (C₁ * (T (cbrtCeil n) (c₁ * (c₂ * U)) * (B * logU U))) * logU U) := by
        gcongr
        exact hB U trivial
    _ = C₂ * (C₁ * B) * ((n : ℝ) ^ 2 * T (cbrtCeil n) (c₁ * c₂ * U) * logU U ^ 2) := by
        rw [mul_assoc c₁ c₂ U]
        ring

/-! ## Theorem 21(b): APSP -/

/-- The quantities in the arithmetic of repeated squaring. -/
private structure Squaring where
  /-- The number of vertices. -/
  n : ℕ
  /-- Stands for the time `T(⌈n^{1/3}⌉)`. -/
  V : ℝ
  /-- Stands for `log U`, where `U` bounds the entries. -/
  W : ℝ

/-- The arithmetic of repeated squaring:
`(⌈log₂ n⌉ + 1) (C n² V W² + C₀ n² (1 + W)) = O(n² V log³ n)`, if `0 ≤ W ≤ B log n` and
`V ≥ 1 + W`. -/
private theorem dominated_repeatedSquaring (C C₀ : ℝ) {B : ℝ} (hB : 0 ≤ B) :
    Dominated (fun p : Squaring => 2 ≤ p.n ∧ 0 ≤ p.W ∧ p.W ≤ B * Real.log p.n ∧ 1 + p.W ≤ p.V)
      (fun p => ((Nat.clog 2 p.n : ℝ) + 1) *
        (C * ((p.n : ℝ) ^ 2 * p.V * p.W ^ 2) + C₀ * ((p.n : ℝ) ^ 2 * (1 + p.W))))
      fun p => (p.n : ℝ) ^ 2 * p.V * Real.log p.n ^ 3 := by
  set dom : Squaring → Prop := fun p =>
    2 ≤ p.n ∧ 0 ≤ p.W ∧ p.W ≤ B * Real.log p.n ∧ 1 + p.W ≤ p.V
  have hV0 : ∀ p, dom p → 0 ≤ (p.n : ℝ) ^ 2 * p.V := fun p ⟨_, hW0, _, hV⟩ =>
    mul_nonneg (by positivity) ((add_nonneg zero_le_one hW0).trans hV)
  have hrounds : Dominated dom (fun p => (Nat.clog 2 p.n : ℝ) + 1) fun p => Real.log p.n :=
    (dominated_clog_add_one_log 2).comp Squaring.n fun _ hp => hp.1
  have hW : Dominated dom Squaring.W fun p => Real.log p.n :=
    .of_le_const_mul hB fun _ hp => hp.2.2.1
  have hone : Dominated dom (fun _ => (1 : ℝ)) fun p => Real.log p.n ^ 2 :=
    .of_le_const_mul (C := 4) (by norm_num) fun p hp => by
      nlinarith [Real.one_half_le_log_of_two_le (Nat.ofNat_le_cast.2 hp.1 : (2 : ℝ) ≤ p.n)]
  -- one product: `C n² V W² = O(n² V log² n)`
  have hproduct : Dominated dom (fun p => C * ((p.n : ℝ) ^ 2 * p.V * p.W ^ 2))
      fun p => (p.n : ℝ) ^ 2 * p.V * Real.log p.n ^ 2 :=
    ((hW.pow (fun _ hp => hp.2.1) 2).mul_left hV0).const_mul_of_nonneg C fun p hp =>
      mul_nonneg (hV0 p hp) (by positivity)
  -- writing a matrix: `C₀ n² (1 + W) ≤ C₀ n² V = O(n² V log² n)`
  have hwrite : Dominated dom (fun p => C₀ * ((p.n : ℝ) ^ 2 * (1 + p.W)))
      fun p => (p.n : ℝ) ^ 2 * p.V * Real.log p.n ^ 2 :=
    (((hone.mul_left hV0).congr (fun _ _ => mul_one _) fun _ _ => rfl).mono_left fun p hp =>
      mul_le_mul_of_nonneg_left hp.2.2.2 (by positivity)).const_mul_of_nonneg C₀ fun p hp =>
        mul_nonneg (by positivity) (add_nonneg zero_le_one hp.2.1)
  -- `⌈log₂ n⌉ + 1 = O(log n)` rounds
  exact (((hproduct.add hwrite).mul_left fun p _ => by positivity).trans
    (hrounds.mul_right fun p hp => mul_nonneg (hV0 p hp) (by positivity))).congr
      (fun _ _ => rfl) fun _ _ => by ring

/-- Theorem 21(b), APSP: repeated squaring on top of the
(min,+)-product. -/
theorem Theorem21b.apsp_of_minPlus (M : DetTimeModel) (h21 : Claim.Theorem_21b_minPlus M)
    (hsq : Claim.ApspFromMinPlus M) : Claim.Theorem_21b_apsp M := by
  obtain ⟨c, C, hc, h21⟩ := h21
  obtain ⟨ca, C₀, hca, hsq⟩ := hsq
  intro κ hκ
  obtain ⟨B, hB0, hB⟩ := dominated_logU_mul_rpow hca (by linarith : 0 ≤ κ + 1)
  obtain ⟨K, -, hK⟩ := dominated_repeatedSquaring C C₀ hB0
  refine ⟨c * ca, K, one_le_mul_of_one_le_of_one_le hc hca, fun T hT hex => ?_⟩
  obtain ⟨T', hT', hb⟩ := h21 T hT hex
  refine ⟨_, hsq T' hT', fun n hn => ?_⟩
  have hn1 : 1 ≤ n := one_le_two.trans hn
  have hpow : (n : ℝ) * (n : ℝ) ^ κ = (n : ℝ) ^ (κ + 1) := by
    rw [Real.rpow_add_one (Nat.cast_pos.2 hn1).ne', mul_comm]
  -- the finite entries are at most n^{κ+1} in absolute value
  have hproduct := hb n (ca * (n : ℝ) ^ (κ + 1)) hn1 (one_le_mul_of_one_le_of_one_le hca
    (Real.one_le_rpow (Nat.one_le_cast.2 hn1) (by linarith)))
  have hV : 1 + logU (ca * (n : ℝ) ^ (κ + 1)) ≤ T (cbrtCeil n) (c * (ca * (n : ℝ) ^ (κ + 1))) :=
    (add_le_add_right (logU_le_logU_mul hc _) 1).trans
      (hT.one_add_logU_le (one_le_cbrtCeil hn1) _)
  have htotal := hK ⟨n, T (cbrtCeil n) (c * (ca * (n : ℝ) ^ (κ + 1))), _⟩
    ⟨hn, (logU_pos _).le, hB n hn, hV⟩
  rw [hpow, mul_assoc c ca]
  exact (mul_le_mul_of_nonneg_left (add_le_add_left hproduct _) (by positivity)).trans htotal

/-! ## "Plug Theorem 19 into Theorem 21"

The time of Theorem 19 is `uniformTime K δ e s u = K s^{3-δ} (log s + 1)^e (1 + log u)²`.
Theorem 21 evaluates it at sizes `s(n)` and bounds `u(n) ≤ c n^κ` on the numbers, and multiplies it
by powers of `n` and logarithms.  So each bound is a product of functions of known classes. -/

/-- The running time `K s^{3-δ} (log s + 1)^e (1 + log u)²` satisfies the requirements of
Theorem 21(b) as rendered by `GoodTime`: it is at least `s² (1 + log u)`, and divided by `s` it is
nondecreasing in `s` ("for which T(s)/s is nondecreasing"). -/
theorem goodTime_uniformTime {K δ : ℝ} (e : ℕ) (hK : 1 ≤ K) (hδ1 : δ ≤ 1) :
    GoodTime (uniformTime K δ e) := by
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  refine ⟨fun s u hs => ?_, fun u s₁ s₂ hs₁ hs => ?_⟩
  · have hs1 : (1 : ℝ) ≤ s := Nat.one_le_cast.2 hs
    have hwords := one_le_one_add_logU u
    have hpow : (s : ℝ) ^ 2 ≤ (s : ℝ) ^ (3 - δ) := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le hs1 (by push_cast; linarith)
    have hlog := one_le_log_add_one_pow s e
    calc (s : ℝ) ^ 2 * (1 + logU u) = 1 * ((s : ℝ) ^ 2 * 1 * (1 + logU u) ^ 1) := by ring
      _ ≤ K * ((s : ℝ) ^ (3 - δ) * (Real.log s + 1) ^ e * (1 + logU u) ^ 2) := by
          gcongr
          norm_num
  · -- `T(s)/s = K s^{2-δ} (log s + 1)^e (1 + log u)²`, and every factor is nondecreasing
    have hdiv : ∀ s : ℕ, 1 ≤ s → uniformTime K δ e s u / s
        = K * ((s : ℝ) ^ (2 - δ) * (Real.log s + 1) ^ e * (1 + logU u) ^ 2) := fun s hs => by
      have hs0 : (s : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.one_le_iff_ne_zero.1 hs)
      rw [uniformTime, show 3 - δ = 2 - δ + 1 by ring, Real.rpow_add_one hs0]
      field_simp
    have hs₁' : (0 : ℝ) < s₁ := Nat.cast_pos.2 hs₁
    have hlog : 0 ≤ Real.log s₁ + 1 := add_nonneg (Real.log_natCast_nonneg s₁) zero_le_one
    rw [hdiv _ hs₁, hdiv _ (hs₁.trans hs)]
    gcongr
    linarith

/-- The time of Theorem 19 on `⌈n^{1/3}⌉` vertices per part, with weights up to `c n^κ`, is
`Õ(n^{1-δ/3})`. -/
theorem isPowPolylog_uniformTime_cbrtCeil (K : ℝ) {δ : ℝ} (e : ℕ) (hδ : δ ≤ 3) {c κ : ℝ}
    (hc : 1 ≤ c) (hκ : 0 ≤ κ) :
    IsPowPolylog (fun n : ℕ => uniformTime K δ e (cbrtCeil n) (c * (n : ℝ) ^ κ)) (1 - δ / 3) := by
  have hsize := (isPowPolylog_rpow_mul_log_add_one_pow (3 - δ) e).comp
    (isBigOPow_ceil_rpow (μ := 1 / 3) (by norm_num)) (by linarith) (by norm_num)
  have hwords := ((isPowPolylog_const 1).add (isPowPolylog_logU_mul_rpow hc hκ)).pow 2
  exact ((hsize.mul hwords).const_mul K).mono (le_of_eq (by push_cast; ring))

/-- "Plug Theorem 19 into Theorem 21", 3SUM, in general form: with exponent `3 - δ` for Exact
Triangle the time for 3SUM is `n^{2-δ/2+o(1)}`. -/
theorem threeSum_of_uniform_theorem_21a (M : DetTimeModel) {δ : ℝ} (e : ℕ) (hδ1 : δ ≤ 1)
    (hu : Claim.ExactTriangleUniform M δ e) (h21 : Claim.Theorem_21a M) :
    Claim.ThreeSumInLittleO M (2 - δ / 2) := by
  obtain ⟨K, -, hex⟩ := hu
  intro κ hκ
  obtain ⟨E, Num, mag, size, c', κ', hE, hNum, hsize, hpos, h⟩ := h21 κ hκ
  obtain ⟨T', hT', hb⟩ := h _ hex
  have hsizes := (isPowPolylog_rpow_mul_log_add_one_pow (3 - δ) e).isPowLittleO.comp hsize
    (by linarith) (by norm_num)
  have hwords := (((isPowPolylog_const 1).add
    (isPowPolylog_logU_of_le fun n hn => (hpos n hn).2)).pow 2).isPowLittleO
  have htotal : IsPowLittleO (fun n => E n + Num n * uniformTime K δ e (size n) (mag n))
      (2 - δ / 2) :=
    (hE.mono (by linarith)).add
      ((hNum.mul ((hsizes.mul hwords).const_mul K)).mono (le_of_eq (by push_cast; ring)))
  exact ⟨T', hT', htotal.upperPowLittleO.mono_left (Filter.eventually_atTop.2 ⟨1, hb⟩)⟩

/-- "Plug Theorem 19 into Theorem 21", (min,+)-product, in general form: with exponent `3 - δ` for
Exact Triangle the time is `O(n^{3-δ/3} (log n)^{O(1)})`. -/
theorem minPlus_of_uniform_theorem_21b (M : DetTimeModel) {δ : ℝ} (e : ℕ) (hδ1 : δ ≤ 1)
    (hu : Claim.ExactTriangleUniform M δ e) (h21 : Claim.Theorem_21b_minPlus M) :
    Claim.MinPlusInPolylog M (3 - δ / 3) := by
  obtain ⟨K, hK, hex⟩ := hu
  obtain ⟨c, C, hc, h21⟩ := h21
  intro κ hκ
  obtain ⟨T', hT', hb⟩ := h21 _ (goodTime_uniformTime e hK hδ1) hex
  have hone : ∀ n : ℕ, 1 ≤ n → 1 ≤ (n : ℝ) ^ κ := fun n hn =>
    Real.one_le_rpow (Nat.one_le_cast.2 hn) hκ
  have htotal := ((((isBigOPow_natCast_pow 2).isPowPolylog.mul
    (isPowPolylog_uniformTime_cbrtCeil K (δ := δ) e (by linarith) hc hκ)).mul
    ((isPowPolylog_logU_of_le (c := 1) fun n hn => ⟨hone n hn, (one_mul _).ge⟩).pow 2)).const_mul
    C).mono (b := 3 - δ / 3) (le_of_eq (by push_cast; ring))
  exact ⟨T', hT', htotal.upperPowPolylog.mono_left
    (Filter.eventually_atTop.2 ⟨1, fun n hn => hb n _ hn (hone n hn)⟩)⟩

/-- "Plug Theorem 19 into Theorem 21", APSP, in general form. -/
theorem apsp_of_uniform_theorem_21b (M : DetTimeModel) {δ : ℝ} (e : ℕ) (hδ1 : δ ≤ 1)
    (hu : Claim.ExactTriangleUniform M δ e) (h21 : Claim.Theorem_21b_apsp M) :
    Claim.ApspInPolylog M (3 - δ / 3) := by
  obtain ⟨K, hK, hex⟩ := hu
  intro κ hκ
  obtain ⟨c, C, hc, h21⟩ := h21 κ hκ
  obtain ⟨T', hT', hb⟩ := h21 _ (goodTime_uniformTime e hK hδ1) hex
  have htotal := ((((isBigOPow_natCast_pow 2).isPowPolylog.mul
    (isPowPolylog_uniformTime_cbrtCeil K (δ := δ) e (by linarith) hc (by linarith : 0 ≤ κ + 1))).mul
    (isPowPolylog_log_pow 3)).const_mul C).mono (b := 3 - δ / 3) (le_of_eq (by push_cast; ring))
  exact ⟨T', hT', htotal.upperPowPolylog.mono_left (Filter.eventually_atTop.2 ⟨2, hb⟩)⟩

/-! ## Theorem 22 -/

/-- The roundings of Theorem 22, such as "n^{2-1/1296+o(1)} ≤ O(n^{1.99923})", at the level of
claims: an inclusion between two classes of running times carries over to the claims. -/
theorem Claim.SolvedAlongPow.mono {S : (ℕ → ℝ → ℝ) → Prop} {Cls Cls' : (ℕ → ℝ) → ℝ → Prop}
    {a b : ℝ} (h : Claim.SolvedAlongPow S Cls a) (hCls : ∀ f, Cls f a → Cls' f b) :
    Claim.SolvedAlongPow S Cls' b := fun κ hκ =>
  let ⟨T, hT, hb⟩ := h κ hκ
  ⟨T, hT, hCls _ hb⟩

end ThreeSumApsp
