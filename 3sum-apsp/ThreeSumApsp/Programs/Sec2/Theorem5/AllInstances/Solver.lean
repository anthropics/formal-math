/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.LightModel
public import ThreeSumApsp.Programs.Sec2.Theorem5.AllInstances.BruteForce
public import ThreeSumApsp.Programs.Sec2.Theorem5.AllInstances.RegimeTest
public import ThreeSumApsp.Programs.Sec2.Theorem5.Solver

/-!
# The thin matrix product, on all instances

The task thinTask: given an N × D matrix X and a D × N matrix Y with entries of absolute value at
most U, and w positions (rows at wi, columns at wj), write the entries of XY at these positions to
the cells from out on. Theorem 5 is about instances with D ≥ 4 a power of four, N ≥ D^18
and at most N²/√D wanted positions. A solver that other procedures call has to be right on every
instance. thin(N, D, w, U, x, y, wi, wj, out, fr) tests the regime, calls the solver of Theorem 5 in
the regime and the brute force outside it.

The file proves that thin solves the task thinTask (thin_solves), within a need that is polynomial
in the parameters (thinNeed_poly) and covers what the solver of Theorem 5 asks of the limits
(thin_limits5, "Word size" in Section 2.4.4), and within the time of Theorem 5 in the regime
(thin_shape_le, thinTimeBound_le). Together these are the running-time claim "Theorem 5" for the
light model (thin_claim).
-/

@[expose] public section

namespace Light.Sec2

open ThreeSumApsp

/-- Local 10 of thin: the result of the test of the regime. -/
abbrev Thin.Expo : ℕ := 10

open ThinArg Thin in
/-- thin(N, D, w, U, x, y, wi, wj, out, fr). -/
def thinBody : Stmt :=
  .call pRegime [v Rows, v Cols, v Wanted] Expo ;;
  .ite (k 0 <' v Expo)
    (.call pThm5
      [v Rows, v Cols, v Wanted, v Bound, v AdrX, v AdrY, v AdrWI, v AdrWJ, v AdrOut, v Free] 0)
    (.call pThinBrute
      [v Rows, v Cols, v Wanted, v Bound, v AdrX, v AdrY, v AdrWI, v AdrWJ, v AdrOut, v Free] 0)

/-- The largest number that thin forms. -/
def thinWord (N D w U : ℕ) : ℕ :=
  N ^ 6 * U ^ 2 + N ^ 3 * U + N ^ 4 + (4 * D + N * D + w * D + N * N + 100) + D * (U * U)

/-- What thin needs, for the parameters N, D, w, U: the largest number formed, the cells from the
free pointer on, the levels of calls. -/
def thinNeed : List ℕ → Need
  | [N, D, w, U] => ⟨thinWord N D w U, N ^ 4 + N + 1, 19 * D + 8⟩
  | _ => ⟨0, 0, 0⟩

/-- The bound of Theorem 5, without its constant. -/
noncomputable def bound5 (N D : ℕ) : ℝ := (N : ℝ) ^ 2 * Real.log D ^ 2 / (D : ℝ) ^ (1 / 18 : ℝ)

open Classical in
/-- The time of thin on sizes N, D, w, if the solver of Theorem 5 takes at most K · thm5Shape
steps. -/
noncomputable def thinSteps (K N D w : ℕ) : ℕ :=
  cRegime * (D + 1) + 30
    + (if InRegime N D w then ⌈(K : ℝ) * 6000 * bound5 N D⌉₊ else 40 * ((w + 1) * (D + 1)))

/-- The time of thin, for the parameters N, D, w, U. -/
noncomputable def thinTime (K : ℕ) : List ℕ → ℕ
  | [N, D, w, _] => thinSteps K N D w
  | _ => 0

open Classical in
/-- The time as a function of N, D and of upper bounds on w and U; it is monotone in the bound on
w. -/
noncomputable def thinTimeBound (K : ℕ) (N D w : ℕ) (_u : ℝ) : ℝ :=
  ((cRegime * (D + 1) + 30 : ℕ) : ℝ)
    + (if InRegime N D 0 then (K : ℝ) * 6000 * bound5 N D + 1 else 0)
    + (if InRegime N D w then 0 else ((40 * ((w + 1) * (D + 1)) : ℕ) : ℝ))

/-! ## The need -/

/-- Each factor of a product of four positive numbers is at most the product. -/
private theorem le_prod_four {a b c e : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (he : 0 < e) :
    a ≤ a * (b * (c * e)) ∧ b ≤ a * (b * (c * e)) ∧ c ≤ a * (b * (c * e))
      ∧ e ≤ a * (b * (c * e)) := by
  have hce : c * e ≤ b * (c * e) := Nat.le_mul_of_pos_left _ hb
  have hbce : b * (c * e) ≤ a * (b * (c * e)) := Nat.le_mul_of_pos_left _ ha
  exact ⟨Nat.le_mul_of_pos_right a (Nat.mul_pos hb (Nat.mul_pos hc he)),
    (Nat.le_mul_of_pos_right b (Nat.mul_pos hc he)).trans hbce,
    ((Nat.le_mul_of_pos_right c he).trans hce).trans hbce,
    ((Nat.le_mul_of_pos_left e hc).trans hce).trans hbce⟩

/-- The need is polynomial in the parameters: each of them is at most
Q = (N + 1) (D + 1) (w + 1) (U + 1), and the three numbers are polynomials of degree at most 8. -/
theorem thinNeed_poly : PolyNeedN thinNeed := by
  refine ⟨7, 8, fun ps => ?_⟩
  rcases ps with _ | ⟨N, _ | ⟨D, _ | ⟨w, _ | ⟨U, _ | ⟨z, t⟩⟩⟩⟩⟩
  case cons.cons.cons.cons.nil =>
    have hbound : polyBound 7 8 [N, D, w, U]
        = 128 * ((N + 1) * ((D + 1) * ((w + 1) * (U + 1)))) ^ 8 := by
      simp only [polyBound, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, Nat.mul_one]
      norm_num
    rw [hbound]
    obtain ⟨kN, kD, kw, kU⟩ := le_prod_four (Nat.succ_pos N) (Nat.succ_pos D) (Nat.succ_pos w)
      (Nat.succ_pos U)
    generalize (N + 1) * ((D + 1) * ((w + 1) * (U + 1))) = Q at *
    have hN : N ≤ Q := by omega
    have hD : D ≤ Q := by omega
    have hw : w ≤ Q := by omega
    have hU : U ≤ Q := by omega
    have up : ∀ i, i ≤ 8 → Q ^ i ≤ Q ^ 8 := fun i hi => Nat.pow_le_pow_right (by omega) hi
    have hword : thinWord N D w U ≤ thinWord Q Q Q Q := by
      unfold thinWord
      gcongr
    have hQ : thinWord Q Q Q Q = Q ^ 8 + 2 * Q ^ 4 + Q ^ 3 + 3 * Q ^ 2 + 4 * Q + 100 := by
      unfold thinWord
      ring
    have hcells : N ^ 4 ≤ Q ^ 4 := Nat.pow_le_pow_left hN 4
    have h0 : 1 ≤ Q ^ 8 := Nat.one_le_pow _ _ (by omega)
    have h1 := up 1 (by norm_num)
    have h2 := up 2 (by norm_num)
    have h3 := up 3 (by norm_num)
    have h4 := up 4 (by norm_num)
    rw [pow_one] at h1
    refine ⟨?_, ?_, ?_⟩
    · change thinWord N D w U ≤ _
      omega
    · change N ^ 4 + N + 1 ≤ _
      omega
    · change 19 * D + 8 ≤ _
      omega
  all_goals exact ⟨Nat.zero_le _, Nat.zero_le _, Nat.zero_le _⟩

/-! ## The regime -/

/-- The regime is closed under taking fewer wanted positions. -/
theorem InRegime.mono {N D w w' : ℕ} (h : InRegime N D w') (hw : w ≤ w') : InRegime N D w := by
  obtain ⟨m, h⟩ := h
  exact ⟨m, { h with hw := (Nat.mul_le_mul_right _ hw).trans h.hw }⟩

/-- The bound of Theorem 5 is not negative. -/
theorem bound5_nonneg (N D : ℕ) : 0 ≤ bound5 N D := by
  unfold bound5
  positivity

/-- In the regime, D is at most the bound of Theorem 5: D ≤ N ≤ N² / D^{1/18}, and log D ≥ 1. -/
theorem le_bound5 {N m : ℕ} (hm : 1 ≤ m) (hN : (4 ^ m) ^ 18 ≤ N) :
    ((4 ^ m : ℕ) : ℝ) ≤ bound5 N (4 ^ m) := by
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hlog : 1 ≤ Real.log (D m) := by linarith [levels_le_log m hm]
  have hDN : (D m : ℝ) ≤ N := by exact_mod_cast D_le_of_D_pow_le (m := m) hN
  calc ((4 ^ m : ℕ) : ℝ) ≤ 1 * ((N : ℝ) ^ 2 / (D m : ℝ) ^ (1 / 18 : ℝ)) := by
        rw [one_mul]
        exact hDN.trans (le_rate hN)
    _ ≤ Real.log (D m) ^ 2 * ((N : ℝ) ^ 2 / (D m : ℝ) ^ (1 / 18 : ℝ)) :=
        mul_le_mul_of_nonneg_right (one_le_pow₀ hlog) (by positivity)
    _ = bound5 N (4 ^ m) := by
        unfold bound5 D
        ring

/-! ## The time -/

open Classical in
/-- The time for w and U is at most the time for upper bounds on them. -/
theorem thinTime_le (K : ℕ) (N D w w' U : ℕ) (u : ℝ) (hw : w ≤ w') :
    (thinTime K [N, D, w, U] : ℝ) ≤ thinTimeBound K N D w' u := by
  have hB : 0 ≤ (K : ℝ) * 6000 * bound5 N D := by
    have := bound5_nonneg N D
    positivity
  change ((thinSteps K N D w : ℕ) : ℝ) ≤ _
  unfold thinSteps thinTimeBound
  by_cases h : InRegime N D w
  · have h0 : InRegime N D 0 := h.mono (Nat.zero_le _)
    rw [if_pos h, if_pos h0]
    have hc := (Nat.ceil_lt_add_one hB).le
    have h3 : (0 : ℝ) ≤ if InRegime N D w' then 0 else ((40 * ((w' + 1) * (D + 1)) : ℕ) : ℝ) := by
      split_ifs
      · exact le_rfl
      · positivity
    push_cast at hc h3 ⊢
    linarith
  · have h' : ¬ InRegime N D w' := fun hh => h (hh.mono hw)
    rw [if_neg h, if_neg h']
    have h2 : (0 : ℝ) ≤ if InRegime N D 0 then (K : ℝ) * 6000 * bound5 N D + 1 else 0 := by
      split_ifs
      · linarith
      · exact le_rfl
    have h3 : ((40 * ((w + 1) * (D + 1)) : ℕ) : ℝ) ≤ ((40 * ((w' + 1) * (D + 1)) : ℕ) : ℝ) := by
      exact_mod_cast Nat.mul_le_mul_left 40 (Nat.mul_le_mul_right _ (by omega))
    push_cast at h2 h3 ⊢
    linarith

/-- In the regime the time is within the bound of Theorem 5. -/
theorem thinTimeBound_le (K : ℕ) :
    ∃ C : ℝ, ∀ (N D w : ℕ) (u : ℝ), (∃ k : ℕ, D = 4 ^ k) → 4 ≤ D → D ^ 18 ≤ N →
      (w : ℝ) ≤ (N : ℝ) ^ 2 / Real.sqrt D → thinTimeBound K N D w u ≤ C * bound5 N D := by
  refine ⟨(K : ℝ) * 6000 + (2 * cRegime + 31 : ℕ), ?_⟩
  rintro N D w u ⟨m, rfl⟩ h4 hN hw
  have hm : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · norm_num at h4
    · exact hm
  have hreg : InRegime N (4 ^ m) w := ⟨m, hm, rfl, hN, (le_sq_div_sqrt_D_iff m N w).1 hw⟩
  have h0 : InRegime N (4 ^ m) 0 := hreg.mono (Nat.zero_le _)
  have hD := le_bound5 hm hN
  have hD1 : (1 : ℝ) ≤ ((4 ^ m : ℕ) : ℝ) := by exact_mod_cast Nat.one_le_pow _ _ (by norm_num)
  unfold thinTimeBound
  rw [if_pos h0, if_pos hreg]
  generalize bound5 N (4 ^ m) = B at *
  have hc : (0 : ℝ) ≤ (cRegime : ℝ) := Nat.cast_nonneg _
  push_cast at hD hD1 ⊢
  generalize (4 : ℝ) ^ m = Dr at *
  nlinarith [mul_le_mul_of_nonneg_left hD hc, mul_le_mul_of_nonneg_left (hD1.trans hD) hc]

/-! ## The solver of Theorem 5 may be called -/

/-- The set ThinW x of the wanted positions has x.w elements. -/
theorem card_thinW_of_pre {x : ThinInst} {μ : ℕ → ℤ} {fr : ℕ} (hpre : x.Pre μ fr) :
    (ThinW x).card = x.w := by
  have hinj : Function.Injective (fun q : Fin x.N × Fin x.N => ((q.1 : ℕ), (q.2 : ℕ))) :=
    fun a b h => by
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (Fin.ext h.1) (Fin.ext h.2)
  have himg : (ThinW x).image (fun q : Fin x.N × Fin x.N => ((q.1 : ℕ), (q.2 : ℕ))) =
    (x.WI.zip x.WJ).toFinset := by
    ext ⟨i, j⟩
    simp only [Finset.mem_image, ThinW, Finset.mem_filter, Finset.mem_univ, true_and,
      List.mem_toFinset]
    constructor
    · rintro ⟨q, hq, h⟩
      rw [← h]
      exact hq
    · intro h
      have hi := hpre.ltWI i (List.of_mem_zip h).1
      have hj := hpre.ltWJ j (List.of_mem_zip h).2
      exact ⟨(⟨i, hi⟩, ⟨j, hj⟩), h, rfl⟩
  rw [← Finset.card_image_of_injective _ hinj, himg, List.toFinset_card_of_nodup hpre.nodup,
    List.length_zip, hpre.lenWI,
    hpre.lenWJ, min_self]

/-- **The limits that thin asks for are those that the solver of Theorem 5 asks for**, in the
regime; the encoded numbers are at most N² U. -/
theorem thin_limits5 {lim : Limits} {x : ThinInst} {m fr d : ℕ} {μ : ℕ → ℤ} (hpre : x.Pre μ fr)
    (reg : Regime5 x m)
    (hok : (thinNeed [x.N, x.D, x.w, x.U]).Ok lim fr d) : SolverLimits lim x m fr (d + 1)
      ((x.N ^ 2 * x.U : ℕ) : ℤ) := by
  have hm := reg.hm
  have hN := reg.pow_le
  have hW : ((thinWord x.N x.D x.w x.U : ℕ) : ℤ) ≤ lim.word := hok.word
  have hC : fr + (x.N ^ 4 + x.N + 1) ≤ lim.space := hok.cells
  have hDp : d + (19 * x.D + 8) ≤ lim.depth := hok.depth
  have le : ∀ n : ℕ, n ≤ thinWord x.N x.D x.w x.U → (n : ℤ) ≤ lim.word := fun n hn =>
    le_trans (by exact_mod_cast hn) hW
  have hmD : m < x.D := by
    rw [reg.hD]
    exact Nat.lt_pow_self (by norm_num)
  have h7 := seven_pow_levels_le_sq hN
  have hU0 : (0 : ℤ) ≤ (x.U : ℤ) := Nat.cast_nonneg _
  have henc : (7 : ℤ) ^ (19 * m) * (x.U : ℤ) ≤ ((x.N ^ 2 * x.U : ℕ) : ℤ) := by
    exact_mod_cast Nat.mul_le_mul_right x.U h7
  have hspace := cells_le_pow_four hm hN reg.hw
  have hseven := Nat.mul_le_mul_right x.U (pow_succ_le_cube hm hN (show 7 ≤ 10 by norm_num))
  have hten := ten_pow_succ_le_cube hm hN
  have hcube : x.N ^ 3 ≤ x.N ^ 4 := pow_le_pow_of_D_pow_le hN (by norm_num)
  have hbands : (numBands (19 * m) m x.N + 1) * (numBands (19 * m) m x.N + 1) ≤ x.N ^ 4 :=
    numBands_succ_sq_le hm hN
  have hroom : 10 ^ (19 * m) * (x.N ^ 2 * x.U * (x.N ^ 2 * x.U)) ≤ x.N ^ 6 * x.U ^ 2 :=
    (Nat.mul_le_mul_right _ (ten_pow_levels_le_sq hN)).trans_eq (by ring)
  exact
    { depth := show d + 1 + 19 * m + 5 ≤ lim.depth by omega
      space := by rw [end5_eq]; omega
      seven := by exact_mod_cast le _ (show 7 ^ (19 * m + 1) * x.U ≤ _ by unfold thinWord; omega)
      ten := le (10 ^ (19 * m + 1)) (by unfold thinWord; omega)
      bands := le _ (hbands.trans (by unfold thinWord; omega))
      encA := fun β e he => by
        obtain ⟨k, -, rfl⟩ := List.mem_map.1 he
        exact (abs_encodingL_le (abs_bandArrayL_le _ hU0 (abs_thinX_le hpre) β) _).trans henc
      encB := fun β e he => by
        obtain ⟨k, -, rfl⟩ := List.mem_map.1 he
        exact (abs_encodingR_le (abs_bandArrayR_le _ hU0 (abs_thinY_le hpre) β) _).trans henc
      room := show (10 : ℤ) ^ (19 * m) * _ ≤ lim.word by
        exact_mod_cast le _ (hroom.trans (by unfold thinWord; omega)) }

/-- In the regime the time of the solver of Theorem 5 is within the bound of the theorem. -/
theorem thin_shape_le {x : ThinInst} {m fr : ℕ} {μ : ℕ → ℤ} (K : ℕ) (hpre : x.Pre μ fr)
    (reg : Regime5 x m) :
    K * thm5Shape (thm5Par m x.N) x.w (thinWork x m) ≤ ⌈(K : ℝ) * 6000 * bound5 x.N x.D⌉₊ := by
  have hcard := card_thinW_of_pre hpre
  have hs := thm5Shape_le_of_wanted (Spec.stdLayout (show m ≤ 19 * m by omega)) (ThinW x) reg.hm
    reg.pow_le (by rw [hcard]; exact reg.hw)
  rw [hcard] at hs
  have hs' : (thm5Shape (thm5Par m x.N) x.w (thinWork x m) : ℝ) ≤ 6000 * bound5 x.N x.D := by
    have e : bound5 x.N x.D = (x.N : ℝ) ^ 2 * Real.log (D m) ^ 2 / (D m : ℝ) ^ (1 / 18 : ℝ) := by
      unfold bound5
      rw [reg.hD]
      rfl
    rw [e]
    exact hs
  have hK : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg _
  have h : ((K * thm5Shape (thm5Par m x.N) x.w (thinWork x m) : ℕ) : ℝ)
      ≤ (K : ℝ) * 6000 * bound5 x.N x.D := by
    push_cast
    nlinarith [mul_le_mul_of_nonneg_left hs' hK]
  exact_mod_cast h.trans (Nat.le_ceil _)

open Classical in
/-- **thin solves the task on all instances**, in the program P5 ++ [regime, thinBrute, thin], where
P5 is a program of 26 procedures whose number pThm5 is the solver of Theorem 5, which does its task
within K · thm5Shape steps also after more procedures are appended. -/
theorem thin_solves {P5 : Program} {K : ℕ} (hlen : P5.length = 26)
    (hthm5At : P5[pThm5]? = some thm5Body) (hsolver : ∀ R : Program, Solver5 (P5 ++ R) K) :
    SolvesN thinTask (P5 ++ [regimeBody, thinBruteBody, thinBody]) pThin (thinTime K) thinNeed := by
  have at26 : ∀ (i : ℕ) (body : Stmt), [regimeBody, thinBruteBody, thinBody][i]? = some body →
      (P5 ++ [regimeBody, thinBruteBody, thinBody])[26 + i]? = some body := fun i body h => by
    rw [List.getElem?_append_right (by omega), hlen, Nat.add_sub_cancel_left]
    exact h
  refine ⟨thinBody, at26 2 _ rfl, fun R lim d (x : ThinInst) μ fr (hpre : x.Pre μ fr) hok => ?_⟩
  have hok' : (thinNeed [x.N, x.D, x.w, x.U]).Ok lim fr d := hok
  have hcells : fr + (x.N ^ 4 + x.N + 1) ≤ lim.space := hok'.cells
  have hdepth : d + (19 * x.D + 8) ≤ lim.depth := hok'.depth
  have le : ∀ n : ℕ, n ≤ thinWord x.N x.D x.w x.U → (n : ℤ) ≤ lim.word := fun n hn =>
    le_trans (by exact_mod_cast hn) hok'.word
  have std : Std lim := ⟨hok'.space, by exact_mod_cast le 100 (by unfold thinWord; omega)⟩
  have h100 := std.const_le
  have hregime : (P5 ++ [regimeBody, thinBruteBody, thinBody] ++ R)[pRegime]? = some regimeBody :=
    getElem?_append_of_eq_some (at26 0 _ rfl) R
  have hbrute : (P5 ++ [regimeBody, thinBruteBody, thinBody] ++ R)[pThinBrute]?
      = some thinBruteBody := getElem?_append_of_eq_some (at26 1 _ rfl) R
  have hthm5 : (P5 ++ [regimeBody, thinBruteBody, thinBody] ++ R)[pThm5]? = some thm5Body :=
    getElem?_append_of_eq_some (getElem?_append_of_eq_some hthm5At _) R
  have hsol : Solver5 (P5 ++ [regimeBody, thinBruteBody, thinBody] ++ R) K := by
    rw [List.append_assoc]
    exact hsolver _
  change Ends lim _ d thinBody ⟨frame [(x.N : ℤ), (x.D : ℤ), (x.w : ℤ), (x.U : ℤ), (x.x : ℤ),
    (x.y : ℤ), (x.wi : ℤ), (x.wj : ℤ), (x.out : ℤ), (fr : ℤ)], μ⟩ (thinSteps K x.N x.D x.w)
    fun σ' => thinTask.Post x μ fr (σ'.loc 0) σ'.mem
  generalize P5 ++ [regimeBody, thinBruteBody, thinBody] ++ R = P at *
  unfold thinBody thinSteps
  -- r := regime(N, D, w)
  light_call (regime_entry hregime x.N x.D x.w μ (le _ (by unfold thinWord; omega)))
    with r μ' ⟨rfl, hr⟩
  rcases hr with ⟨m, reg, rfl⟩ | ⟨rfl, hno⟩
  · -- in the regime: thm5(N, D, w, U, x, y, wi, wj, out, fr)
    have hm := reg.hm
    have htime := thin_shape_le K hpre reg
    rw [if_pos (show InRegime x.N x.D x.w from ⟨m, reg⟩)]
    refine Ends.iteLast (fun _ => ?_) (fun h => absurd (by simp; omega) h)
    exact Ends.callTo (Meets.of_body hthm5
      (hsol lim std (d + 1) m x μ' fr _ x.U hpre reg (thin_limits5 hpre reg hok')))
      fun r μ'' h => by simpa using h
  · -- outside the regime: thinBrute(N, D, w, U, x, y, wi, wj, out, fr)
    rw [if_neg hno]
    refine Ends.iteLast (fun h => absurd h (by simp)) (fun _ => ?_)
    exact Ends.callTo (Meets.of_body hbrute
      (thinBrute_spec std x μ' fr x.U hpre (by omega) (le _ (by unfold thinWord; omega))))
      fun r μ'' h => by simpa using h

/-- **The running-time claim "Theorem 5" for programs of the light language**, from a program as in
thin_solves. -/
theorem thin_claim {P5 : Program} {K : ℕ} (hlen : P5.length = 26)
    (hthm5At : P5[pThm5]? = some thm5Body) (hsolver : ∀ R : Program, Solver5 (P5 ++ R) K) :
    Claim.Theorem_5 lightModel := by
  intro _
  obtain ⟨C, hC⟩ := thinTimeBound_le K
  exact ⟨C, thinTimeBound K,
    ⟨_, pThin, thinTime K, thinNeed, thinNeed_poly, thin_solves hlen hthm5At hsolver,
      fun N D w w' U u _ _ _ hw _ => thinTime_le K N D w w' U u hw⟩,
    fun N D w u hpow h4 hN hw _ => hC N D w u hpow h4 hN hw⟩

end Light.Sec2
