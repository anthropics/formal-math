/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec4.ChoosingParameters.Costs
public import ThreeSumApsp.Programs.Sec4.ChoosingParameters.Layout
public import ThreeSumApsp.Programs.Sec4.Theorem30.ThinLayout

/-!
# Section 4.4, the data structure as a light program

Section 4.4. The programs hold rational parameters c = a/b, θ = p/q and a threshold m₀. They are a
data structure for the entries of a thin matrix product (`programIsDataStructure_of_costsWithin`),
on every domain of inputs and for all bounds Tp (preprocessing time and space) and Tq (query time)
that dominate the two cost expressions (8) and L ∑ α_d of Theorem 30 at these parameters. The regime
and the bounds are parameters, so that the statements of Section 4 about data structures
(Corollaries 26 and 31, Theorem 24) are instances; the compiler takes the statement to the word RAM
in `isDataStructure_of_costsWithin`.
-/

public section

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.Spec ThreeSumApsp.WordRam

/-- A quantity that is at most a t + 40 is at most A t, if a + 40 ≤ A and t ≥ 1. -/
private theorem le_mul_of_le_mul_add {A a z t : ℝ} (ht : 1 ≤ t) (ha : a + 40 ≤ A)
    (hz : z ≤ a * t + 40) : z ≤ A * t := by
  have h1 : (a + 40) * t ≤ A * t := mul_le_mul_of_nonneg_right ha (by linarith)
  linarith

/-- **Word size**: with the free pointer behind the input, the limits are polynomial in N, and N and
all numbers of the input fit in a word. -/
theorem lim31_thinPair (G : RatParams) {C tp tq : ℝ} {e : ℕ} {x : ThinPair} (hU : x.U = x.N ^ e)
    (hc : CostsWithin G C x.N x.D tp tq) :
    Small (slopeExp31 G) (20 + 2 * e) [x.N, x.D] (lim31 G x.N x.D (inputEnd x.N x.D) e) ∧
      (x.N : ℤ) ≤ (lim31 G x.N x.D (inputEnd x.N x.D) e).word ∧
      ∀ v ∈ x.input [], |v| ≤ (lim31 G x.N x.D (inputEnd x.N x.D) e).word := by
  have hN1 := hc.one_le_N
  have hD := hc.one_le_D
  have hDN := hc.D_le_N
  have hfr : inputEnd x.N x.D = 2 + x.N * x.D + x.N * x.D := rfl
  have hb0 : blockAt x.N x.D (inputEnd x.N x.D) ≤ 10 * (x.N + 1) ^ 3 := by
    refine le_trans ?_ (blockAt_le (w := 0) hD hDN (Nat.zero_le _))
    unfold blockAt
    omega
  have hNfr : x.N ≤ inputEnd x.N x.D := by have := Nat.le_mul_of_pos_right x.N hD; omega
  have hDfr : x.D ≤ inputEnd x.N x.D := by have := Nat.le_mul_of_pos_left x.D hN1; omega
  have hUe : (x.U : ℤ) = (x.N : ℤ) ^ e := by rw [hU]; push_cast; rfl
  exact ⟨small_lim31 e hD hDN hb0 hc.hyp, lim31_natCast_le G _ _ _ _ hNfr,
    abs_thinPair_input_le (lim31_natCast_le G _ _ _ _ hNfr) (lim31_natCast_le G _ _ _ _ hDfr)
      (hUe ▸ (lim31_facts G x.N x.D _ e).2) (by simp)⟩

/-- **The programs with rational parameters are a data structure**, on every domain and for all
bounds that dominate the costs of Theorem 30. -/
theorem programIsDataStructure_of_costsWithin {P : Program} {c0 : ℕ} (G : RatParams) {C : ℝ}
    (hC : 0 ≤ C) (e : ℕ) (dom : ThinPair → Prop) (Tp Tq : ThinPair → ℝ)
    (hdom : ∀ x, dom x → x.U = x.N ^ e ∧ CostsWithin G C x.N x.D (Tp x) (Tq x))
    (hpreMain : P[Proc.preMain31]? = some preMain31Body)
    (hqueryMain : P[Proc.queryMain31]? = some queryMain31Body)
    (hpre : ∀ lim, PreSpec31 lim P c0 G) (hq : ∀ lim, QuerySpec31 lim P G) :
    ∃ (A : ℝ) (s k : ℕ), ProgramIsDataStructure P Proc.preMain31 Proc.queryMain31 s k [] dom
      (fun x => A * Tp x) (fun x => A * Tp x) (fun x => A * Tq x) := by
  obtain ⟨Ap, hAp0, hAp⟩ := exists_tPre31_le G hC c0
  obtain ⟨Aq, hAq0, hAq⟩ := exists_tQuery31_le G hC
  obtain ⟨As, hAs0, hAs⟩ := exists_structEnd_sub_le G hC
  obtain ⟨Ad, hAd0, hAd⟩ := exists_lim31_depth_le G hC
  refine ⟨Ap + Aq + As + Ad + 40, slopeExp31 G, 20 + 2 * e, fun x hx => ?_⟩
  obtain ⟨hU, hc⟩ := hdom x hx
  have hN1 := hc.one_le_N
  have hD := hc.one_le_D
  have hTp := hc.one_le_pre
  have hTq := hc.one_le_query
  obtain ⟨hsmall, hNword, hinput⟩ := lim31_thinPair G hU hc
  beta_reduce
  have hlim := lim31_ok G x.N x.D (inputEnd x.N x.D) e
  have hdepth := (lim31_facts G x.N x.D (inputEnd x.N x.D) e).1
  have hUe : (x.U : ℤ) = (x.N : ℤ) ^ e := by rw [hU]; push_cast; rfl
  have bX : ∀ i j, |x.X i j| ≤ (x.N : ℤ) ^ e := fun i j => hUe ▸ x.boundX i j
  have bY : ∀ i j, |x.Y i j| ≤ (x.N : ℤ) ^ e := fun i j => hUe ▸ x.boundY i j
  refine ⟨lim31 G x.N x.D (inputEnd x.N x.D) e, InputReady31 G x.X x.Y, hsmall, hNword, hinput,
    mul_nonneg (by positivity) (by linarith), ?_, ?_, ?_, ?_⟩
  · -- space: the cells of the structure behind the input
    have hcells := hAs (inputEnd x.N x.D) hc
    have hfr3 := add_three_le_structEnd G x.N x.D (inputEnd x.N x.D)
    have hlen : (x.input []).length = inputEnd x.N x.D := length_thinPair_input x []
    rw [hlen, lim31_space, show structEnd G x.N x.D (inputEnd x.N x.D)
      = inputEnd x.N x.D + (structEnd G x.N x.D (inputEnd x.N x.D) - inputEnd x.N x.D) by omega]
    push_cast
    linarith [le_mul_of_le_mul_add (A := Ap + Aq + As + Ad + 40) (a := As) hTp (by linarith)
      (hcells.trans (by linarith))]
  · -- depth
    exact le_mul_of_le_mul_add (a := Ad) hTp (by linarith)
      ((hAd (inputEnd x.N x.D) e hc).trans (by linarith))
  · -- the preprocessing
    exact (preMain31_meets hpreMain (hpre _) hD hN1 x.X x.Y ((x.N : ℤ) ^ e) bX bY hlim (by omega) _
      (thinPair_cellN x []) (thinPair_cellD x []) (thinPair_matAt_X x [])
      (thinPair_matAt_Y x [])).main (by omega)
        (le_mul_of_le_mul_add (a := Ap) hTp (by linarith) (by push_cast; linarith [hAp hc]))
  · -- a query
    exact AnswersQueries.of_meets (by omega)
      (le_mul_of_le_mul_add (a := Aq) hTq (by linarith) (by push_cast; linarith [hAq hc]))
      fun μ' hM I J => queryMain31_meets hqueryMain (hq _) hD x.X x.Y ((x.N : ℤ) ^ e) bX bY hlim
        (by omega) μ' hM I J

end Light.Sec4
