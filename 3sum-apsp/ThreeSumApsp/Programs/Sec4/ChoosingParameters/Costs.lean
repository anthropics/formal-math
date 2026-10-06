/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec4.ChoosingParameters.Limits
public import ThreeSumApsp.Programs.Sec4.ChoosingParameters.Offline

/-!
# Section 4.4: the costs of the programs with rational parameters

Bounds for the time and the space of the preprocessing and for the time of a query. `CostsWithin`
says of two bounds tp and tq that they dominate the two costs of Theorem 30. A quantity that is
bounded for m < m₀ and within a constant times a cost for m ≥ m₀ is then within a constant times the
bound (`exists_le_of_small_of_large`). The overheads are absorbed by the cost expression (8) of
Theorem 30: padding, copying and filling cost O(N 4^m), and N 4^m ≤ N 10^L/(√K N₀), because K N₀ 4^m
≤ 7^L (`N_mul_pow_le_cost8`); computing L and t costs O(L). For m < m₀ everything is bounded by a
constant. This gives the results that the end theorems use: `exists_tPre31_le`,
`exists_tQuery31_le`, `exists_tOffline32_le`, `exists_structEnd_sub_le`, `exists_lim31_depth_le`.
-/

@[expose] public section

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.Spec ThreeSumApsp.WordRam

section
variable (G : RatParams)

/-- **The two bounds dominate the two costs**, at the sizes N and D: sizes and bounds are at least
1, D ≤ N, and from the threshold on the hypotheses of Theorem 30 hold and its two cost expressions,
(8) and L ∑ α_d, are at most C tp and C tq. -/
structure CostsWithin (C : ℝ) (N D₀ : ℕ) (tp tq : ℝ) : Prop where
  one_le_N : 1 ≤ N
  one_le_D : 1 ≤ D₀
  D_le_N : D₀ ≤ N
  one_le_pre : 1 ≤ tp
  one_le_query : 1 ≤ tq
  above : G.m₀ ≤ logFour D₀ → Hyp30 (parOf G N D₀) (switchOf31 G D₀) ∧
    cost8 (G.L (logFour D₀)) (logFour D₀) (switchOf31 G D₀) N ≤ C * tp ∧
    costQuery (G.L (logFour D₀)) (logFour D₀) (switchOf31 G D₀) ≤ C * tq

variable {G} in
/-- For m ≥ m₀ the hypotheses of Theorem 30 hold. -/
theorem CostsWithin.hyp {C : ℝ} {N D₀ : ℕ} {tp tq : ℝ} (h : CostsWithin G C N D₀ tp tq)
    (hm : G.m₀ ≤ logFour D₀) : G.Hyp N D₀ :=
  (h.above hm).1

variable {G} in
/-- For m ≥ m₀ the cost (8) is at most C tp. -/
theorem CostsWithin.pre_le {C : ℝ} {N D₀ : ℕ} {tp tq : ℝ} (h : CostsWithin G C N D₀ tp tq)
    (hm : G.m₀ ≤ logFour D₀) : G.preCost N D₀ ≤ C * tp :=
  (h.above hm).2.1

variable {G} in
/-- For m ≥ m₀ the cost of a query is at most C tq. -/
theorem CostsWithin.query_le {C : ℝ} {N D₀ : ℕ} {tp tq : ℝ} (h : CostsWithin G C N D₀ tp tq)
    (hm : G.m₀ ≤ logFour D₀) : G.queryCost D₀ ≤ C * tq :=
  (h.above hm).2.2

/-- A quantity that is bounded below the threshold, and at most a constant times a cost from the
threshold on, is at most a constant times every bound t ≥ 1 that dominates the cost. -/
theorem exists_le_of_small_of_large {C : ℝ} (hC : 0 ≤ C) {S K : ℝ} (hS : 0 ≤ S) (hK : 0 ≤ K) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (D₀ : ℕ) (cost t z : ℝ), 1 ≤ t → (G.m₀ ≤ logFour D₀ → cost ≤ C * t) →
      (logFour D₀ < G.m₀ → z ≤ S) → (G.m₀ ≤ logFour D₀ → z ≤ K * cost + S) → z ≤ A * t := by
  refine ⟨S + K * C, by positivity, fun D₀ cost t z ht hcost hsmall hlarge => ?_⟩
  have hsplit : (S + K * C) * t = S * t + K * (C * t) := by ring
  have hSt : S ≤ S * t := le_mul_of_one_le_right hS ht
  rw [hsplit]
  by_cases hm : logFour D₀ < G.m₀
  · linarith [hsmall hm, mul_nonneg hK (mul_nonneg hC (by linarith : (0 : ℝ) ≤ t))]
  · linarith [hlarge (by omega), mul_le_mul_of_nonneg_left (hcost (by omega)) hK]

/-! ### The preprocessing -/

/-- Setting up takes O(L + N 4^m) steps. -/
theorem exists_tPre31_le_setup : ∃ k : ℕ, ∀ c0 N D₀ : ℕ, G.m₀ ≤ logFour D₀ →
    tPre31 c0 G N D₀ ≤ k * (G.L (logFour D₀) + 1 + N * 4 ^ logFour D₀ + N)
      + tPreCore c0 (parOf G N D₀) (switchOf31 G D₀) := by
  refine ⟨20 + 20 * G.b + 20 * G.q + 352, fun c0 N D₀ hm => ?_⟩
  have ham := G.am_le (logFour D₀)
  have hpm := G.pm_le (logFour D₀)
  have hmL : logFour D₀ ≤ G.L (logFour D₀) := by have := G.ten_le_L (logFour D₀); omega
  have hDF : D₀ ≤ 4 ^ logFour D₀ := le_D_logFour D₀
  unfold tPre31
  rw [if_neg (not_lt.2 hm)]
  simp only [tLog4, tCeilMul, tPadX, tCopy, tFill, D]
  generalize tPreCore c0 (parOf G N D₀) (switchOf31 G D₀) = tp
  generalize G.L (logFour D₀) = L at *
  generalize logFour D₀ = m at *
  generalize 4 ^ m = F at *
  have hcopy : D₀ * N ≤ N * F := by rw [Nat.mul_comm]; exact Nat.mul_le_mul_left _ hDF
  have hfill : (F - D₀) * N ≤ N * F := by
    rw [Nat.mul_comm]; exact Nat.mul_le_mul_left _ (Nat.sub_le _ _)
  have hqL : G.q * m ≤ G.q * L := Nat.mul_le_mul_left _ hmL
  have hpad : N * (16 * F + 80) = 16 * (N * F) + 80 * N := by ring
  have hk : (20 + 20 * G.b + 20 * G.q + 352) * (L + 1 + N * F + N)
      = 20 * L + 20 * (G.b * L) + 20 * (G.q * L) + (20 + 20 * G.b + 20 * G.q) * (1 + N * F + N)
        + 352 * (L + 1 + N * F + N) := by ring
  have := Nat.zero_le ((20 + 20 * G.b + 20 * G.q) * (1 + N * F + N))
  omega

/-- From the threshold on the preprocessing takes O((8)) steps. -/
theorem exists_tPre31_le_cost8 (c0 : ℕ) : ∃ K : ℝ, 0 ≤ K ∧ ∀ N D₀ : ℕ, 1 ≤ N → G.m₀ ≤ logFour D₀ →
    G.Hyp N D₀ → (tPre31 c0 G N D₀ : ℝ) ≤ K * G.preCost N D₀ := by
  obtain ⟨k, hk⟩ := exists_tPre31_le_setup G
  obtain ⟨Cp, hCp0, hCp⟩ := exists_tPreCore_le c0
  refine ⟨k * 7 + Cp, by positivity, fun N D₀ hN hm h => ?_⟩
  have hN' : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hL0 : (0 : ℝ) ≤ (G.L (logFour D₀) : ℝ) := by positivity
  have hcore : (tPreCore c0 (parOf G N D₀) (switchOf31 G D₀) : ℝ)
      ≤ Cp * G.preCost N D₀ := hCp (parOf G N D₀) (switchOf31 G D₀) h
  have hNF : (N : ℝ) * (4 : ℝ) ^ logFour D₀ ≤ G.preCost N D₀ := N_mul_pow_le_cost8 h
  have hNL : (N : ℝ) * ((G.L (logFour D₀) : ℝ) + 1) ≤ 3 * G.preCost N D₀ := N_mul_le_cost8 h
  have hsetup : (tPre31 c0 G N D₀ : ℝ)
      ≤ k * ((G.L (logFour D₀) : ℝ) + 1 + N * (4 : ℝ) ^ logFour D₀ + N)
        + (tPreCore c0 (parOf G N D₀) (switchOf31 G D₀) : ℝ) := by exact_mod_cast hk c0 N D₀ hm
  -- L + 1 ≤ N (L + 1) and N ≤ N (L + 1), so that the sum is at most 7 times (8)
  have hL : (G.L (logFour D₀) : ℝ) + 1 ≤ (N : ℝ) * ((G.L (logFour D₀) : ℝ) + 1) :=
    le_mul_of_one_le_left (by positivity) hN'
  have hNle : (N : ℝ) ≤ (N : ℝ) * ((G.L (logFour D₀) : ℝ) + 1) :=
    le_mul_of_one_le_right (by positivity) (by linarith)
  have hsum : (k : ℝ) * ((G.L (logFour D₀) : ℝ) + 1 + N * (4 : ℝ) ^ logFour D₀ + N)
      ≤ k * (7 * G.preCost N D₀) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  linarith

/-- **The time of the preprocessing** is at most a constant times every bound tp ≥ 1 that, from the
threshold on, dominates the cost (8) of Theorem 30. -/
theorem exists_tPre31_le {C : ℝ} (hC : 0 ≤ C) (c0 : ℕ) : ∃ A : ℝ, 0 ≤ A ∧
    ∀ {N D₀ : ℕ} {tp tq : ℝ}, CostsWithin G C N D₀ tp tq → (tPre31 c0 G N D₀ : ℝ) ≤ A * tp := by
  obtain ⟨K, hK0, hK⟩ := exists_tPre31_le_cost8 G c0
  obtain ⟨A, hA0, hA⟩ := exists_le_of_small_of_large G hC
    (S := ((20 * G.m₀ + 50 : ℕ) : ℝ)) (by positivity) hK0
  refine ⟨A, hA0, fun {N D₀ tp tq} h =>
    hA D₀ _ tp _ h.one_le_pre h.pre_le (fun hm => ?_) fun hm => ?_⟩
  · have hsmall : tPre31 c0 G N D₀ ≤ 20 * G.m₀ + 50 := by
      unfold tPre31 tLog4
      rw [if_pos hm]
      omega
    exact_mod_cast hsmall
  · have := hK N D₀ h.one_le_N hm (h.hyp hm)
    have : (0 : ℝ) ≤ ((20 * G.m₀ + 50 : ℕ) : ℝ) := by positivity
    linarith

/-! ### A query -/

/-- **The time of a query** is at most a constant times every bound tq ≥ 1 that, from the threshold
on, dominates the cost L ∑ α_d of Theorem 30. -/
theorem exists_tQuery31_le {C : ℝ} (hC : 0 ≤ C) : ∃ A : ℝ, 0 ≤ A ∧
    ∀ {N D₀ : ℕ} {tp tq : ℝ}, CostsWithin G C N D₀ tp tq → (tQuery31 G D₀ : ℝ) ≤ A * tq := by
  obtain ⟨K, hK0, hK⟩ := exists_tQueryAt_le
  obtain ⟨A, hA0, hA⟩ := exists_le_of_small_of_large G hC
    (S := ((40 * 4 ^ G.m₀ + 40 : ℕ) : ℝ)) (by positivity) hK0
  refine ⟨A, hA0, fun {N D₀ tp tq} h =>
    hA D₀ _ tq _ h.one_le_query h.query_le (fun hm => ?_) fun hm => ?_⟩
  · -- an inner product of D ≤ 4^m₀ summands
    have hD := (Nat.clog_le_iff_le_pow (by norm_num)).1 hm.le
    have hsmall : tQuery31 G D₀ ≤ 40 * 4 ^ G.m₀ + 40 := by
      unfold tQuery31 tIpAt
      rw [if_pos hm]
      omega
    exact_mod_cast hsmall
  · have hquery : (tQueryAt (G.L (logFour D₀)) (logFour D₀) (switchOf31 G D₀) : ℝ)
        ≤ K * G.queryCost D₀ :=
      hK (parOf G N D₀) (switchOf31 G D₀) (h.hyp hm)
    have htime :
        tQuery31 G D₀ = tQueryAt (G.L (logFour D₀)) (logFour D₀) (switchOf31 G D₀) + 20 := by
      unfold tQuery31
      rw [if_neg (not_lt.2 hm)]
    have h40 : (20 : ℝ) ≤ ((40 * 4 ^ G.m₀ + 40 : ℕ) : ℝ) := by exact_mod_cast (by omega)
    rw [htime]
    push_cast at h40 ⊢
    linarith

end

/-- **The time of the offline routine**, with k further steps, is at most a constant times tp + w
tq, for all bounds tp, tq ≥ 1 that dominate the two costs of Theorem 30. -/
theorem exists_tOffline32_le (G : RatParams) {C : ℝ} (hC : 0 ≤ C) (c0 k : ℕ) : ∃ A : ℝ,
    ∀ {N D₀ : ℕ} {tp tq : ℝ} (w : ℕ), CostsWithin G C N D₀ tp tq →
      (tOffline32 c0 G N D₀ w : ℝ) + k ≤ A * (tp + w * tq) := by
  obtain ⟨Ap, hAp0, hAp⟩ := exists_tPre31_le G hC c0
  obtain ⟨Aq, hAq0, hAq⟩ := exists_tQuery31_le G hC
  refine ⟨(Ap + 20 + k) + (Aq + 30), fun {N D₀ tp tq} w h => ?_⟩
  have hpre := hAp h
  have hquery := hAq h
  have htp := h.one_le_pre
  have htq := h.one_le_query
  have hw : (0 : ℝ) ≤ (w : ℝ) := by positivity
  have hk : (0 : ℝ) ≤ (k : ℝ) := by positivity
  have hwtq : 0 ≤ (w : ℝ) * tq := mul_nonneg hw (by linarith)
  have htime : (tOffline32 c0 G N D₀ w : ℝ)
      = (tPre31 c0 G N D₀ : ℝ) + (w : ℝ) * ((tQuery31 G D₀ : ℝ) + 30) + 20 := by
    simp only [tOffline32]
    push_cast
    ring
  -- the preprocessing and the k + 20 further steps against tp, the w queries against w tq
  have hfirst : (tPre31 c0 G N D₀ : ℝ) + 20 + k ≤ (Ap + 20 + k) * tp := by
    linarith [le_mul_of_one_le_right (by positivity : (0 : ℝ) ≤ 20 + (k : ℝ)) htp]
  have hsecond : (w : ℝ) * ((tQuery31 G D₀ : ℝ) + 30) ≤ (Aq + 30) * ((w : ℝ) * tq) := by
    calc (w : ℝ) * ((tQuery31 G D₀ : ℝ) + 30) ≤ (w : ℝ) * ((Aq + 30) * tq) :=
          mul_le_mul_of_nonneg_left (by linarith) hw
      _ = (Aq + 30) * ((w : ℝ) * tq) := by ring
  have hcross₁ : 0 ≤ (Ap + 20 + k) * ((w : ℝ) * tq) := mul_nonneg (by positivity) hwtq
  have hcross₂ : 0 ≤ (Aq + 30) * tp := mul_nonneg (by positivity) (by linarith)
  rw [htime]
  linarith

/-! ### Space and the nesting of calls -/

/-- **The number of cells** of a structure at fr is at most a constant times every bound tp ≥ 1
that, from the threshold on, dominates the cost (8) of Theorem 30. -/
theorem exists_structEnd_sub_le (G : RatParams) {C : ℝ} (hC : 0 ≤ C) : ∃ A : ℝ, 0 ≤ A ∧
    ∀ {N D₀ : ℕ} {tp tq : ℝ} (fr : ℕ), CostsWithin G C N D₀ tp tq →
      ((structEnd G N D₀ fr - fr : ℕ) : ℝ) ≤ A * tp := by
  obtain ⟨K, hK0, hK⟩ := exists_top_sub_le
  obtain ⟨A, hA0, hA⟩ := exists_le_of_small_of_large G hC (S := 3) (by norm_num)
    (by positivity : (0 : ℝ) ≤ K + 2)
  refine ⟨A, hA0, fun {N D₀ tp tq} fr hc =>
    hA D₀ _ tp _ hc.one_le_pre hc.pre_le (fun hm => ?_) fun hm => ?_⟩
  · have hsmall : structEnd G N D₀ fr - fr = 3 := by rw [structEnd_small hm]; omega
    rw [hsmall]
    norm_num
  · -- three cells, the two padded matrices, and the block of Theorem 30
    have h := hc.hyp hm
    have hblock : ((G.blockEnd N D₀ fr - blockAt N D₀ fr : ℕ) : ℝ) ≤ K * G.preCost N D₀ :=
      hK (parOf G N D₀) (switchOf31 G D₀) _ h
    have hNF : (N : ℝ) * (4 : ℝ) ^ logFour D₀ ≤ G.preCost N D₀ := N_mul_pow_le_cost8 h
    have hle := (G.blockAt_lt_blockEnd N D₀ fr).le
    have hb0 : blockAt N D₀ fr = fr + (3 + 2 * (N * 4 ^ logFour D₀)) := by
      change fr + 3 + N * 4 ^ logFour D₀ + N * 4 ^ logFour D₀ = _
      ring
    have hcells : structEnd G N D₀ fr - fr = (3 + 2 * (N * 4 ^ logFour D₀))
        + (G.blockEnd N D₀ fr - blockAt N D₀ fr) := by
      rw [structEnd_large hm]
      omega
    rw [hcells]
    push_cast
    linarith

/-- The same for a structure at the address 0. -/
theorem exists_structEnd_le (G : RatParams) {C : ℝ} (hC : 0 ≤ C) : ∃ A : ℝ, 0 ≤ A ∧
    ∀ {N D₀ : ℕ} {tp tq : ℝ}, CostsWithin G C N D₀ tp tq →
      ((structEnd G N D₀ 0 : ℕ) : ℝ) ≤ A * tp := by
  obtain ⟨A, hA0, hA⟩ := exists_structEnd_sub_le G hC
  exact ⟨A, hA0, fun h => hA 0 h⟩

/-- **The nesting of calls** that the limits allow is at most a constant times every bound tp ≥ 1
that, from the threshold on, dominates the cost (8) of Theorem 30. -/
theorem exists_lim31_depth_le (G : RatParams) {C : ℝ} (hC : 0 ≤ C) : ∃ A : ℝ, 0 ≤ A ∧
    ∀ {N D₀ : ℕ} {tp tq : ℝ} (fr c : ℕ), CostsWithin G C N D₀ tp tq →
      ((lim31 G N D₀ fr c).depth : ℝ) ≤ A * tp := by
  obtain ⟨A, hA0, hA⟩ := exists_le_of_small_of_large G hC
    (S := ((G.L G.m₀ + 10 : ℕ) : ℝ)) (K := 3) (by positivity) (by norm_num)
  refine ⟨A, hA0, fun {N D₀ tp tq} fr c h =>
    hA D₀ _ tp _ h.one_le_pre h.pre_le (fun hm => ?_) fun hm => ?_⟩
  · rw [lim31_small hm]
  · -- L + 1 ≤ N (L + 1), which is at most 3 times (8)
    have hNL : (N : ℝ) * ((G.L (logFour D₀) : ℝ) + 1) ≤ 3 * G.preCost N D₀ := N_mul_le_cost8
            (h.hyp hm)
    have hL : (G.L (logFour D₀) : ℝ) + 1 ≤ (N : ℝ) * ((G.L (logFour D₀) : ℝ) + 1) :=
      le_mul_of_one_le_left (by positivity) (by exact_mod_cast h.one_le_N)
    have h10 : (10 : ℝ) ≤ ((G.L G.m₀ + 10 : ℕ) : ℝ) := by exact_mod_cast (by omega)
    rw [lim31_large (not_lt.2 hm)]
    push_cast at h10 ⊢
    linarith

end Light.Sec4
