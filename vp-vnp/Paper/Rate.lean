/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Paper.Scales
import Paper.Flat
import Paper.Convex
import Paper.Ryser
import Nc.CaseI.Hub

/-!
# The paper, section "The main theorem", and the results of the introduction
-/

namespace Paper

open Finset Nc Nc.Price Nc.CaseI Ov

/-! ### The geometry of the proof of Proposition prop:flat-rate -/

/-- "So |t_S| ≥ (2/9)k^(3/2) by the Cauchy–Schwarz inequality." Here hubDir A is the direction t_S. -/
theorem prop_flat_rate_direction {k : ℕ} (hk : 1 ≤ k) (A : Finset (Fin k)) (h1 : k ≤ 3 * A.card) (h2 : 3 * A.card ≤ 2 * k) :
    2 / 9 * ((k : ℝ) * √k) ≤ ‖hubDir A‖ := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hs1 : (k : ℝ) ≤ 3 * A.card := by exact_mod_cast h1
  have hs2 : 3 * (A.card : ℝ) ≤ 2 * k := by exact_mod_cast h2
  set w : EuclideanSpace ℝ (Fin k) := WithLp.toLp 2 (sideSign A) with hw
  have hwn : ‖w‖ = √k := by
    rw [EuclideanSpace.norm_eq]
    congr 1
    have : ∀ a, ‖w a‖ ^ 2 = 1 := by
      intro a
      simp only [hw, sideSign]
      split_ifs <;> simp
    simp only [this, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  have hin : inner ℝ (hubDir A) w = (A.card : ℝ) * ((k : ℝ) - A.card) := by
    rw [inner_hubDir, ← sum_sep]
    refine Finset.sum_congr rfl fun e _ => ?_
    by_cases h : CaseI.Sep A e
    · rw [if_pos h, if_pos h]
      simp only [hw, sideSign]
      split_ifs <;> norm_num
    · rw [if_neg h, if_neg h]
  have hcs := real_inner_le_norm (hubDir A) w
  rw [hwn, hin] at hcs
  have hp : 2 / 9 * (k : ℝ) ^ 2 ≤ (A.card : ℝ) * ((k : ℝ) - A.card) := by nlinarith
  have hsq : √(k : ℝ) * √k = k := Real.mul_self_sqrt hk0.le
  have hs0 : 0 < √(k : ℝ) := Real.sqrt_pos.2 hk0
  refine le_of_mul_le_mul_right ?_ hs0
  calc 2 / 9 * ((k : ℝ) * √k) * √k = 2 / 9 * (k : ℝ) ^ 2 := by rw [mul_assoc, mul_assoc, hsq]; ring
    _ ≤ _ := hp.trans hcs

/-- "Leading every end to the hub of its side gives total length at most N − (4/81)k", with hubs ±o of length 2/(9√k). -/
theorem prop_flat_rate_lengths {k : ℕ} (hk : 1 ≤ k) (A : Finset (Fin k)) (h1 : k ≤ 3 * A.card) (h2 : 3 * A.card ≤ 2 * k) :
    ∃ x : EuclideanSpace ℝ (Fin k), ‖x‖ = 2 / (9 * √k) ∧
      ∑ e : Pr k, (dist (endPos e 0) (if e.1.1 ∈ A then x else -x) + dist (endPos e 1) (if e.1.2 ∈ A then x else -x)) ≤
        (k : ℝ) * (k - 1) / 2 - 4 / 81 * k := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hs0 : 0 < √(k : ℝ) := Real.sqrt_pos.2 hk0
  have hsq : √(k : ℝ) ^ 2 = k := Real.sq_sqrt hk0.le
  have hv := prop_flat_rate_direction hk A h1 h2
  have hv0 : 0 < ‖hubDir A‖ := lt_of_lt_of_le (by positivity) hv
  set γ : ℝ := 2 / (9 * √k) with hγ
  have hγ0 : 0 < γ := by positivity
  set z : ℝ := γ / ‖hubDir A‖ with hz
  have hz0 : 0 < z := by positivity
  have hn : ‖z • hubDir A‖ = γ := by
    rw [norm_smul, Real.norm_of_nonneg hz0.le, hz]
    exact div_mul_cancel₀ _ hv0.ne'
  refine ⟨z • hubDir A, hn, ?_⟩
  set x := z • hubDir A with hx
  have hterm : ∀ e : Pr k,
      dist (endPos e 0) (if e.1.1 ∈ A then x else -x) + dist (endPos e 1) (if e.1.2 ∈ A then x else -x) ≤
        (1 + 2 * γ ^ 2) - 2 * (if CaseI.Sep A e then sideSign A e.1.1 * x e.1.1 else 0) := by
    intro e
    have hu : ‖(EuclideanSpace.single e.1.1 (1 : ℝ) : EuclideanSpace ℝ (Fin k))‖ = 1 := by simp
    have hu' : ‖-(EuclideanSpace.single e.1.1 (1 : ℝ) : EuclideanSpace ℝ (Fin k))‖ = 1 := by simp
    rw [endPos_zero, endPos_one]
    have a1 := dist_half_le hu (if e.1.1 ∈ A then x else -x)
    have a2 := dist_half_le hu' (if e.1.2 ∈ A then x else -x)
    refine (add_le_add a1 a2).trans (le_of_eq ?_)
    by_cases ha : e.1.1 ∈ A <;> by_cases hb : e.1.2 ∈ A <;>
      simp [CaseI.Sep, sideSign, ha, hb, EuclideanSpace.inner_single_left, inner_neg_left, hn] <;> ring
  refine (Finset.sum_le_sum fun e _ => hterm e).trans ?_
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← inner_hubDir, hx, real_inner_smul_right,
    real_inner_self_eq_norm_sq]
  have hN : ∑ _e : Pr k, (1 + 2 * γ ^ 2) = (k : ℝ) * (k - 1) / 2 * (1 + 2 * γ ^ 2) := by
    rw [← sum_pairs_one, Finset.sum_mul]
    simp
  rw [hN]
  have e1 : z * ‖hubDir A‖ ^ 2 = γ * ‖hubDir A‖ := by rw [hz]; field_simp
  rw [e1]
  have e2 : 4 / 81 * (k : ℝ) ≤ γ * ‖hubDir A‖ := by
    calc 4 / 81 * (k : ℝ) = γ * (2 / 9 * ((k : ℝ) * √k)) := by rw [hγ]; field_simp; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hv hγ0.le
  have e3 : (k : ℝ) * (k - 1) * γ ^ 2 ≤ 4 / 81 * k := by
    have : γ ^ 2 * k = 4 / 81 := by rw [hγ, div_pow, mul_pow, hsq]; field_simp; norm_num
    calc (k : ℝ) * ((k : ℝ) - 1) * γ ^ 2 = (γ ^ 2 * k) * ((k : ℝ) - 1) := by ring
      _ = 4 / 81 * ((k : ℝ) - 1) := by rw [this]
      _ ≤ _ := by linarith
  nlinarith


/-- The place of an end: (a, b), a < b, at ½e_a and (b, a) at −½e_a. -/
noncomputable def ratePos {k : ℕ} (a : End k) : EuclideanSpace ℝ (Fin k) := endPos a.1 a.2

/-- The hubs of the sets as parties. -/
def hubPt {k : ℕ} (S : Finset (Fin k)) (b : Bool) : RPt k := Sum.inr (S, b)

/-- "The push-forward of a unit tensor on all ends is that on the set of their positions." -/
theorem prop_flat_rate_pushforward (K : Type) [Field K] {A I : Type} [Fintype A] [DecidableEq A] [Fintype I]
    [DecidableEq I] (π : A → I) (q : ℕ) :
    Ten.Equi (Ten.push π (Ten.unit K A q))
      (Ten.push (Subtype.val : univ.image π → I) (Ten.unit K (univ.image π) q)) :=
  Ten.Equi.push_unit_congr π Subtype.val (by ext x; simp) q

theorem hexp_image {K : Type} [Field K] {A I : Type} [Fintype A] [DecidableEq A] [Fintype I] [DecidableEq I]
    (φ : Spec K I) (π : A → I) : hexp φ π = hexp φ (Subtype.val : univ.image π → I) := by
  rw [hexp, hexp, φ.congr (prop_flat_rate_pushforward K π 2)]

/-- The last step of Proposition prop:flat-rate: "this gives even ℓk^(3/2)/14". -/
theorem rate_numbers14 {k ℓ c ε S1 S2 S3 G lg : ℝ} (hk : 1 ≤ k) (hℓ : 100 * √k ≤ ℓ) (hc : 0 ≤ c) (hlg : 0 ≤ lg)
    (hε : ε = 1 / (1000 * k)) (hw : k * (k - 1) / 2 * (1 - ε) ≤ c * S1)
    (hh : c * S2 ≤ k * (k - 1) / 2 - 4 / 81 * k + k * (k - 1) * ε) (hm : c * S3 ≤ 4 / (9 * √k) + ε)
    (hg : c * G ≤ √k + ε) (h1 : ℓ * S1 ≤ k * G + ℓ * S2 + S3 * lg) : ℓ * (k * √k) / 14 ≤ lg := by
  have hk0 : 0 < k := by linarith
  have hs1 : 1 ≤ √k := Real.one_le_sqrt.2 hk
  have hs0 : 0 < √k := by linarith
  have hℓ0 : 0 ≤ ℓ := by linarith
  have hε0 : 0 < ε := by rw [hε]; positivity
  have h3 : ℓ * (k * (k - 1) / 2 * (1 - ε)) ≤
      k * (√k + ε) + ℓ * (k * (k - 1) / 2 - 4 / 81 * k + k * (k - 1) * ε) + (4 / (9 * √k) + ε) * lg := by
    have h2 := mul_le_mul_of_nonneg_left h1 hc
    have a1 := mul_le_mul_of_nonneg_left hw hℓ0
    have a2 := mul_le_mul_of_nonneg_left hh hℓ0
    have a3 := mul_le_mul_of_nonneg_right hm hlg
    have a4 := mul_le_mul_of_nonneg_left hg hk0.le
    nlinarith
  have e1 : k * k * ε = k / 1000 := by rw [hε]; field_simp
  have e2 : k * ε = 1 / 1000 := by rw [hε]; field_simp
  have b1 : ℓ * (k * (k - 1) * ε * (3 / 2)) ≤ ℓ * (3 * k / 2000) := by
    refine mul_le_mul_of_nonneg_left ?_ hℓ0
    nlinarith
  have b2 : k * (√k + ε) ≤ ℓ * k * (1 / 100 + 1 / 10000) := by
    have : k * √k * 100 ≤ ℓ * k := by nlinarith
    nlinarith
  have h4 : ℓ * k * (4 / 81 - 3 / 2000 - 1 / 100 - 1 / 10000) ≤ (4 / (9 * √k) + ε) * lg := by linarith
  have h5 : 4 / (9 * √k) + ε ≤ (4 / 9 + 1 / 1000) / √k := by
    have : ε * √k ≤ 1 / 1000 := by
      have : √k ≤ k := by nlinarith [Real.mul_self_sqrt hk0.le]
      nlinarith
    rw [le_div_iff₀ hs0, add_mul]
    have e3 : 4 / (9 * √k) * √k = 4 / 9 := by field_simp
    linarith
  have h6 := h4.trans (mul_le_mul_of_nonneg_right h5 hlg)
  rw [div_mul_eq_mul_div, le_div_iff₀ hs0] at h6
  nlinarith

/-- What Lemma lem:few gives: for some balanced set the choice costs k times the price of the unit tensor on all
ends, and the set what its hubs cost. -/
def SomeSetPays {K : Type} [Field K] {k : ℕ} (φ : Spec K (RPt k)) (ℓ s : ℕ) : Prop :=
  ∃ A ∈ bal (univ : Finset (Fin k)), (ℓ : ℝ) * ∑ e : Pr k, φ.e (Sum.inl ⟨e, 0⟩) (Sum.inl ⟨e, 1⟩) ≤
    k * hexp φ (Sum.inl : End k → RPt k) + hubCost φ ℓ s Sum.inl hubPt A

/-- The steps "Ends", "Hubs" and "Comparison" of the proof of Proposition prop:flat-rate, given what the lemma on sums
with few terms says. -/
theorem rate_of_someSetPays {K : Type} [Field K] (hK : Flat K) {k : ℕ} (hk : 2 ≤ k) {ℓ s : ℕ}
    (hℓ : 100 * √k ≤ (ℓ : ℝ)) (hs : 1 ≤ s) (hfew : ∀ φ : Spec K (RPt k), SomeSetPays φ ℓ s) :
    (ℓ : ℝ) * (k * √k) / 14 ≤ Real.logb 2 s := by
  classical
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
  have hhub : ∀ A : Finset (Fin k), ∃ x : EuclideanSpace ℝ (Fin k), A ∈ bal (univ : Finset (Fin k)) →
      ‖x‖ = 2 / (9 * √k) ∧
      ∑ e : Pr k, (dist (endPos e 0) (if e.1.1 ∈ A then x else -x) + dist (endPos e 1) (if e.1.2 ∈ A then x else -x)) ≤
        (k : ℝ) * (k - 1) / 2 - 4 / 81 * k := by
    intro A
    by_cases hA : A ∈ bal (univ : Finset (Fin k))
    · obtain ⟨-, h1, h2⟩ := mem_bal.1 hA
      obtain ⟨x, hx⟩ := prop_flat_rate_lengths (by omega) A h1 h2
      exact ⟨x, fun _ => hx⟩
    · exact ⟨0, fun h => absurd h hA⟩
  choose x hx using hhub
  set ε : ℝ := 1 / (1000 * k) with hε
  have hε0 : 0 < ε := by positivity
  let pos : RPt k → EuclideanSpace ℝ (Fin k) := Sum.elim ratePos fun z => if z.2 then x z.1 else -x z.1
  let e₀ : Pr k := ⟨(⟨0, by omega⟩, ⟨1, by omega⟩), by simp [Fin.lt_def]⟩
  have hPV : univ.image ratePos ⊆ univ.image pos := fun y hy => by
    obtain ⟨a, -, rfl⟩ := mem_image.1 hy
    exact mem_image.2 ⟨Sum.inl a, mem_univ _, rfl⟩
  obtain ⟨φ, c, hc, hφ, hg⟩ := prop_cube hK (univ.image pos) (univ.image ratePos) hPV
    ⟨ratePos ⟨e₀, 0⟩, mem_image_of_mem _ (mem_univ _)⟩ (fun y hy => by
      obtain ⟨a, -, rfl⟩ := mem_image.1 hy
      exact ⟨a.1.1.1, decide (a.2 = 0), rfl⟩) hε0
  -- pulled back to the ends and hubs regarded as different parties
  let place : RPt k → univ.image pos := fun z => ⟨pos z, mem_image_of_mem _ (mem_univ z)⟩
  let F := φ.pull place
  have hF : ∀ a b, |dist (pos a) (pos b) - c * F.e a b| < ε := fun a b => by
    rw [φ.pull_e, abs_sub_comm, ← Subtype.dist_eq (place a) (place b)]
    exact hφ _ _
  have hG : c * hexp F (Sum.inl : End k → RPt k) ≤ √k + ε := by
    refine le_of_eq_of_le ?_ hg
    rw [hexp_pull]
    refine congrArg _ ?_
    let atP : univ.image ratePos → univ.image pos := fun y => ⟨y.1, hPV y.2⟩
    have himg : univ.image (place ∘ (Sum.inl : End k → RPt k)) = univ.image atP := by
      ext y
      simp only [mem_image, mem_univ, true_and, Function.comp]
      constructor
      · rintro ⟨a, rfl⟩
        exact ⟨⟨ratePos a, mem_image_of_mem _ (mem_univ a)⟩, rfl⟩
      · rintro ⟨⟨z, hz⟩, rfl⟩
        obtain ⟨a, -, rfl⟩ := mem_image.1 hz
        exact ⟨a, rfl⟩
    rw [hexp_image φ (place ∘ Sum.inl), himg]
    exact (hexp_image φ atP).symm
  have hlog : 0 ≤ Real.logb 2 s := Real.logb_nonneg (by norm_num) (by exact_mod_cast hs)
  obtain ⟨A, hA, h1⟩ := hfew F
  obtain ⟨hxn, hxs⟩ := hx A hA
  refine rate_numbers14 hk1 hℓ hc hlog hε ?_ ?_ ?_ hG (by simpa only [hubCost, add_assoc] using h1)
  · rw [Finset.mul_sum]
    have e1 : (k : ℝ) * (k - 1) / 2 * (1 - ε) = ∑ _e : Pr k, (1 - ε) := by
      rw [← sum_pairs_one, Finset.sum_mul]
      simp
    rw [e1]
    refine Finset.sum_le_sum fun e _ => ?_
    have h2 := (abs_lt.1 (hF (Sum.inl ⟨e, 0⟩) (Sum.inl ⟨e, 1⟩))).2
    simp only [pos, Sum.elim_inl, ratePos, dist_endPos] at h2
    linarith
  · have h2 : ∀ (e : Pr k) (i : Fin 2), c * F.e (Sum.inl ⟨e, i⟩) (hubOf hubPt A ⟨e, i⟩) ≤
        dist (endPos e i) (if endNode e i ∈ A then x A else -x A) + ε := by
      intro e i
      have h3 := (abs_lt.1 (hF (Sum.inl ⟨e, i⟩) (hubOf hubPt A ⟨e, i⟩))).1
      simp only [pos, hubOf, hubPt, Sum.elim_inl, Sum.elim_inr, decide_eq_true_eq, ratePos] at h3
      simp only [hubOf, hubPt]
      linarith
    rw [Finset.mul_sum]
    calc ∑ e : Pr k, c * ∑ i, F.e (Sum.inl ⟨e, i⟩) (hubOf hubPt A ⟨e, i⟩) ≤
        ∑ e : Pr k, ((dist (endPos e 0) (if e.1.1 ∈ A then x A else -x A) +
          dist (endPos e 1) (if e.1.2 ∈ A then x A else -x A)) + 1 * (2 * ε)) := by
          refine Finset.sum_le_sum fun e _ => ?_
          rw [Fin.sum_univ_two, mul_add]
          refine (add_le_add (h2 e 0) (h2 e 1)).trans (le_of_eq ?_)
          simp only [endNode, if_true, Fin.one_eq_zero_iff, OfNat.ofNat_ne_one, if_false]
          ring
      _ ≤ _ := by
        rw [Finset.sum_add_distrib, ← Finset.sum_mul, sum_pairs_one]
        linarith
  · have h2 := (abs_lt.1 (hF (hubPt A true) (hubPt A false))).1
    simp only [pos, hubPt, Sum.elim_inr, if_true, Bool.false_eq_true, if_false] at h2
    have h3 : dist (x A) (-x A) = 4 / (9 * √k) := by
      rw [dist_eq_norm, sub_neg_eq_add, ← two_smul ℝ, norm_smul, hxn]
      norm_num
      ring
    rw [h3] at h2
    simp only [hubPt]
    linarith

theorem rate_pow {k ℓ s : ℕ} (hk : 2 ≤ k) (hs : 1 ≤ s) (h : (ℓ : ℝ) * (k * √k) / 14 ≤ Real.logb 2 s) :
    (2 : ℝ) ^ ((ℓ : ℝ) * (k : ℝ) ^ (3 / 2 : ℝ) / 16) ≤ s := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hk0, Real.rpow_one, ← Real.sqrt_eq_rpow,
    ← Real.le_logb_iff_rpow_le (by norm_num) (by exact_mod_cast hs)]
  have : (0 : ℝ) ≤ (ℓ : ℝ) * (k * √k) := by positivity
  linarith

/-- A finite numbering of the balanced sets, for Lemma lem:few. -/
noncomputable def balEnum (k : ℕ) : Fin (Fintype.card (bal (univ : Finset (Fin k)))) ≃ bal (univ : Finset (Fin k)) :=
  (Fintype.equivFin _).symm

/-- From the bound of the lemma on sums with few terms, with J ≤ 2^k, to the inequality for one set. -/
theorem someSetPays_of_few {K : Type} [Field K] {k : ℕ} (φ : Spec K (RPt k)) {ℓ s : ℕ} (hs : 1 ≤ s)
    [NeZero (Fintype.card (bal (univ : Finset (Fin k))))]
    (h : φ.F (Ten.push Sum.inl (fklTen K k ℓ)) ≤
      (Fintype.card (bal (univ : Finset (Fin k))) : ℝ) ^
          hexp φ (Subtype.val : (univ.image (Sum.inl : End k → RPt k)) → RPt k) *
        univ.sup' univ_nonempty fun j => φ.F (hubTen K ℓ s Sum.inl hubPt (balEnum k j).1)) :
    SomeSetPays φ ℓ s := by
  classical
  obtain ⟨j, -, hj⟩ := Finset.exists_mem_eq_sup' univ_nonempty
    fun j => φ.F (hubTen K ℓ s Sum.inl hubPt (balEnum k j).1)
  rw [hj, fklTen_price, hubTen_price φ ℓ hs, ← hexp_image] at h
  have : Nonempty (RPt k) := ⟨hubPt ∅ true⟩
  refine ⟨_, (balEnum k j).2, (Real.rpow_le_rpow_left_iff (show (1 : ℝ) < 2 by norm_num)).1 ?_⟩
  rw [Real.rpow_add (by norm_num), Real.rpow_mul (by norm_num) (k : ℝ)]
  refine h.trans (mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (Nat.cast_nonneg _) ?_ (hexp_nonneg φ _)) (by positivity))
  rw [Real.rpow_natCast]
  exact_mod_cast card_bal_le k

/-- The tensor of f_{k,ℓ}, pushed to the parties, is a tensor on the ends. -/
theorem fklTen_onEnds (K : Type) [Field K] (k ℓ : ℕ) (q : RPt k)
    (hq : q ∉ univ.image (Sum.inl : End k → RPt k)) :
    Subsingleton ((Ten.push (Sum.inl : End k → RPt k) (fklTen K k ℓ)).ι q) := by
  have : IsEmpty {a // (Sum.inl : End k → RPt k) a = q} := ⟨fun a => hq (mem_image.2 ⟨a.1, mem_univ _, a.2⟩)⟩
  exact inferInstanceAs (Subsingleton (∀ a : {a // (Sum.inl : End k → RPt k) a = q}, (fklTen K k ℓ).ι a.1))

/-- **Paper: Proposition prop:flat-rate.** "In the flat case, for k ≥ 2 and ℓ ≥ 100√k every circuit over k for f_{k,ℓ}
has at least 2^(ℓk^(3/2)/16) gates." -/
theorem prop_flat_rate {K : Type} [Field K] (hK : Flat K) {k : ℕ} (hk : 2 ≤ k) {ℓ s : ℕ}
    (hℓ : 100 * √k ≤ (ℓ : ℝ)) (hcomp : Computes (fkl K k ℓ) s) :
    (2 : ℝ) ^ ((ℓ : ℝ) * (k : ℝ) ^ (3 / 2 : ℝ) / 16) ≤ s := by
  classical
  have hs : 1 ≤ s := by
    obtain ⟨l, -, a, ha, -⟩ := hcomp
    omega
  refine rate_pow hk hs (rate_of_someSetPays hK hk hℓ hs fun φ => ?_)
  have := bal_nonempty hk
  have : NeZero (Fintype.card (bal (univ : Finset (Fin k)))) := ⟨Fintype.card_ne_zero⟩
  have : Nonempty (RPt k) := ⟨hubPt ∅ true⟩
  -- the tensor of f is a sum of at most 2^k hub tensors
  have hsum := prop_flat_lower_sum hk hcomp (Sum.inl : End k → RPt k) hubPt
  rw [show ((fklTen K k ℓ).withVal fun z => cf univ (fkl K k ℓ) (tables z)) = fklTen K k ℓ from
    congrArg _ (funext fun z => (fklTen_val K z).symm)] at hsum
  exact someSetPays_of_few φ hs (lem_few φ _ _ (fklTen_onEnds K k ℓ) _ (hsum.reindex (balEnum k)))

/-- **Paper: Proposition prop:flat-rate**, for f_{k,ℓ} with exactly the printed variables. -/
theorem prop_flat_rate_printed {K : Type} [Field K] (hK : Flat K) {k : ℕ} (hk : 2 ≤ k) {ℓ s : ℕ}
    (hℓ : 100 * √k ≤ (ℓ : ℝ)) (hcomp : Computes (fklExact K k ℓ) s) :
    (2 : ℝ) ^ ((ℓ : ℝ) * (k : ℝ) ^ (3 / 2 : ℝ) / 16) ≤ s :=
  prop_flat_rate hK hk hℓ (fklExact_computes.1 hcomp)

/-- The largest cube with 200 r³ ≤ B. -/
theorem exists_cube_root (B : ℕ) : ∃ r, 200 * r ^ 3 ≤ B ∧ B < 200 * (r + 1) ^ 3 := by
  classical
  have hex : ∃ r, B < 200 * (r + 1) ^ 3 := ⟨B, by
    have : B + 1 ≤ (B + 1) ^ 3 := Nat.le_self_pow (by norm_num) _
    omega⟩
  refine ⟨Nat.find hex, ?_, Nat.find_spec hex⟩
  rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | h0
  · simp [h0]
  · have h1 := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
    rw [Nat.sub_add_cancel h0] at h1
    omega

/-- The proof of Theorem thm:flat-rate for anything that gives circuits for f_{k,ℓ} with five times as many gates
once m ≥ κk³ℓ2^(kℓ): r is largest with 200r³ ≤ ⌊log m⌋, k = r², ℓ = 100r. -/
theorem rate_of_projection (κ : ℕ) : ∃ m₀ : ℕ, ∀ P : ℕ → ℕ → Prop,
    (∀ k ℓ m s : ℕ, 2 ≤ k → 1 ≤ ℓ → 100 * √k ≤ (ℓ : ℝ) → κ * k ^ 3 * ℓ * 2 ^ (k * ℓ) ≤ m → P m s →
      (2 : ℝ) ^ ((ℓ : ℝ) * (k : ℝ) ^ (3 / 2 : ℝ) / 16) ≤ ((5 * s : ℕ) : ℝ)) →
    ∀ m ≥ m₀, ∀ s, P m s → (2 : ℝ) ^ (Real.logb 2 m ^ (4 / 3 : ℝ) / 1600 ^ 2) < s := by
  refine ⟨2 ^ (200 * (κ + 3) ^ 3), fun P hP m hm s hs => ?_⟩
  obtain ⟨B, hB⟩ : ∃ B, B = Nat.log 2 m := ⟨_, rfl⟩
  have hm0 : m ≠ 0 := by
    have : 1 ≤ 2 ^ (200 * (κ + 3) ^ 3) := Nat.one_le_two_pow
    omega
  have hB1 : 200 * (κ + 3) ^ 3 ≤ B := hB ▸ Nat.le_log_of_pow_le (by norm_num) hm
  obtain ⟨r, hr1, hr2⟩ := exists_cube_root B
  have hr : κ + 2 ≤ r := by
    by_contra hlt
    have : (r + 1) ^ 3 ≤ (κ + 3) ^ 3 := Nat.pow_le_pow_left (by omega) 3
    omega
  have hmL : 2 ^ B ≤ m := hB ▸ Nat.pow_log_le_self 2 hm0
  have hmU : m < 2 ^ (B + 1) := hB ▸ Nat.lt_pow_succ_log_self (by norm_num) m
  have hfit : κ * (r ^ 2) ^ 3 * (100 * r) * 2 ^ (r ^ 2 * (100 * r)) ≤ 2 ^ (200 * r ^ 3) := by
    have a1 : κ ≤ 2 ^ r := (Nat.lt_two_pow_self (n := κ)).le.trans (Nat.pow_le_pow_right (by norm_num) (by omega))
    have a2 : (r ^ 2) ^ 3 ≤ 2 ^ (6 * r) := by
      rw [← pow_mul, show (2 : ℕ) * 3 = 6 from rfl, Nat.mul_comm 6 r, pow_mul]
      exact Nat.pow_le_pow_left (Nat.lt_two_pow_self (n := r)).le 6
    have a3 : 100 * r ≤ 2 ^ (100 * r) := (Nat.lt_two_pow_self).le
    have h2 : κ * (r ^ 2) ^ 3 * (100 * r) ≤ 2 ^ (100 * r ^ 3) := by
      calc κ * (r ^ 2) ^ 3 * (100 * r) ≤ 2 ^ r * 2 ^ (6 * r) * 2 ^ (100 * r) :=
            Nat.mul_le_mul (Nat.mul_le_mul a1 a2) a3
        _ = 2 ^ (107 * r) := by rw [← pow_add, ← pow_add]; congr 1; ring
        _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (by nlinarith [Nat.mul_le_mul hr hr])
    rw [show r ^ 2 * (100 * r) = 100 * r ^ 3 by ring]
    calc κ * (r ^ 2) ^ 3 * (100 * r) * 2 ^ (100 * r ^ 3) ≤ 2 ^ (100 * r ^ 3) * 2 ^ (100 * r ^ 3) :=
          Nat.mul_le_mul_right _ h2
      _ = _ := by rw [← pow_add]; congr 1; ring
  have hrR : (2 : ℝ) ≤ r := by exact_mod_cast (by omega : 2 ≤ r)
  have hsq : √((r ^ 2 : ℕ) : ℝ) = r := by push_cast; exact Real.sqrt_sq (by linarith)
  have hlow := hP (r ^ 2) (100 * r) m s (le_trans (by omega : 2 ≤ r) (Nat.le_self_pow (by norm_num) r)) (by omega)
    (by rw [hsq]; push_cast; exact le_rfl) (hfit.trans ((Nat.pow_le_pow_right (by norm_num) hr1).trans hmL)) hs
  have hs0 : (0 : ℝ) < s := by
    have := (Real.rpow_pos_of_pos (show (0 : ℝ) < 2 by norm_num) _).trans_le hlow
    push_cast at this
    linarith
  have hk0 : (0 : ℝ) < ((r ^ 2 : ℕ) : ℝ) := by push_cast; positivity
  rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hk0, Real.rpow_one, ← Real.sqrt_eq_rpow, hsq] at hlow
  push_cast at hlow
  rw [← Real.le_logb_iff_rpow_le (by norm_num) (by positivity), Real.logb_mul (by norm_num) hs0.ne'] at hlow
  have h5 : Real.logb 2 5 ≤ 3 := by
    rw [Real.logb_le_iff_le_rpow (by norm_num) (by norm_num)]
    norm_num
  have hlM : Real.logb 2 m ≤ 1600 * (r : ℝ) ^ 3 := by
    have h1 : B + 1 ≤ 1600 * r ^ 3 := by
      have h2 : (r + 1) ^ 3 ≤ (2 * r) ^ 3 := Nat.pow_le_pow_left (by omega) 3
      rw [mul_pow] at h2
      omega
    have h3 : Real.logb 2 m ≤ ((B + 1 : ℕ) : ℝ) := by
      rw [Real.logb_le_iff_le_rpow (by norm_num) (by exact_mod_cast Nat.pos_of_ne_zero hm0), Real.rpow_natCast]
      exact_mod_cast hmU.le
    exact h3.trans (by exact_mod_cast h1)
  have hl0 : 0 ≤ Real.logb 2 m := Real.logb_nonneg (by norm_num) (by exact_mod_cast Nat.pos_of_ne_zero hm0)
  have hpow : Real.logb 2 m ^ (4 / 3 : ℝ) ≤ 1600 ^ 2 * (r : ℝ) ^ 4 := by
    refine (Real.rpow_le_rpow hl0 hlM (by norm_num)).trans ?_
    rw [Real.mul_rpow (by norm_num) (by positivity)]
    refine mul_le_mul ?_ (le_of_eq ?_) (by positivity) (by norm_num)
    · calc (1600 : ℝ) ^ (4 / 3 : ℝ) ≤ (1600 : ℝ) ^ ((2 : ℕ) : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ = _ := Real.rpow_natCast _ 2
    · rw [← Real.rpow_natCast (r : ℝ) 3, ← Real.rpow_mul (by linarith)]
      norm_num
  have h4 : (16 : ℝ) ≤ (r : ℝ) ^ 4 := by
    calc (16 : ℝ) = 2 ^ 4 := by norm_num
      _ ≤ _ := pow_le_pow_left₀ (by norm_num) hrR 4
  rw [← Real.lt_logb_iff_rpow_lt (by norm_num) hs0, div_lt_iff₀ (by norm_num)]
  nlinarith

/-- **Paper: Theorem thm:flat-rate.** "In the flat case there is m₀ such that for m ≥ m₀ every circuit over k for PERM_m
has more than 2^((log m)^(4/3)/1600²) gates." -/
theorem thm_flat_rate {K : Type} [Field K] (hK : Flat K) (h2 : (2 : K) ≠ 0) :
    ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ s, Computes (genPerm K m) s →
      (2 : ℝ) ^ (Real.logb 2 m ^ (4 / 3 : ℝ) / 1600 ^ 2) < s := by
  obtain ⟨m₀, h⟩ := rate_of_projection 3
  exact ⟨m₀, h _ fun k ℓ m s hk hℓ hℓk hm hs => prop_flat_rate hK hk hℓk (lem_fkl_perm h2 hk hℓ hm hs)⟩

/-- Theorem thm:flat-rate for every family that is complete for grid sums ("the factor 3 becomes 40"). -/
theorem flat_rate_complete (κ : ℕ) : ∃ m₀ : ℕ, ∀ (K : Type) [Field K], Flat K →
    ∀ G : ∀ S : ℕ, MvPolynomial (Fin S × Fin S) K, GridComplete K G κ →
    ∀ m ≥ m₀, ∀ s : ℕ, Computes (G m) s → (2 : ℝ) ^ (Real.logb 2 m ^ (4 / 3 : ℝ) / 1600 ^ 2) < s := by
  obtain ⟨m₀, h⟩ := rate_of_projection κ
  refine ⟨m₀, fun K _ hK G hG => h _ fun k ℓ m s hk hℓ hℓk hm hs => prop_flat_rate hK hk hℓk ?_⟩
  obtain ⟨E, hE, he⟩ := fkl_complete hG hk hℓ hm
  exact he ▸ hs.aeval E hE

/-- "(log m)²/log log m ≥ (log m)^(4/3) for large m", and indeed more than any multiple: the bound of the contracting
case exceeds that of the flat case. -/
theorem thm_main_calculation (C : ℝ) : ∃ m₀ : ℕ, ∀ m ≥ m₀,
    C * Real.logb 2 m ^ (4 / 3 : ℝ) ≤ Real.logb 2 m ^ 2 / Real.logb 2 (Real.logb 2 m) := by
  have ht : Filter.Tendsto (fun m : ℕ => Real.logb 2 m) Filter.atTop Filter.atTop :=
    (Real.tendsto_logb_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  have h0 := (isLittleO_log_rpow_atTop (show (0 : ℝ) < 2 / 3 by norm_num)).bound
    (show (0 : ℝ) < Real.log 2 / (|C| + 1) by positivity)
  obtain ⟨m₀, hm₀⟩ := Filter.eventually_atTop.1 ((ht.eventually h0).and (ht.eventually_gt_atTop 2))
  refine ⟨m₀, fun m hm => ?_⟩
  obtain ⟨h1, hL⟩ := hm₀ m hm
  set L := Real.logb 2 m
  have hL0 : 0 < L := by linarith
  have hl : 0 < Real.logb 2 L := Real.logb_pos (by norm_num) (by linarith)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg (by linarith)),
    abs_of_nonneg (Real.rpow_nonneg hL0.le _)] at h1
  have h3 : (|C| + 1) * Real.logb 2 L ≤ L ^ (2 / 3 : ℝ) := by
    have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
    rw [Real.logb, ← mul_div_assoc, div_le_iff₀ hlog]
    calc (|C| + 1) * Real.log L ≤ (|C| + 1) * (Real.log 2 / (|C| + 1) * L ^ (2 / 3 : ℝ)) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = _ := by field_simp
  rw [le_div_iff₀ hl]
  calc C * L ^ (4 / 3 : ℝ) * Real.logb 2 L = L ^ (4 / 3 : ℝ) * (C * Real.logb 2 L) := by ring
    _ ≤ L ^ (4 / 3 : ℝ) * L ^ (2 / 3 : ℝ) := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hL0.le _)
        nlinarith [le_abs_self C]
    _ = L ^ 2 := by
        rw [← Real.rpow_add hL0, show (4 / 3 : ℝ) + 2 / 3 = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

theorem genPerm_eq.{u} (F : Type u) [Field F] (m : ℕ) :
    genPerm F m = ∑ σ : Equiv.Perm (Fin m), ∏ i, MvPolynomial.X (σ i, i) := by
  simp [genPerm, Matrix.permanent]

/-- **Paper: Theorem thm:simple.** "For every C there is m₀ such that for all m ≥ m₀ no circuit over ℝ with at most m^C
gates computes PERM_m." -/
theorem thm_simple (C : ℕ) : ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ s : ℕ, s ≤ m ^ C →
    ¬ Computes (∑ σ : Equiv.Perm (Fin m), ∏ i, MvPolynomial.X (σ i, i) : MvPolynomial (Fin m × Fin m) ℝ) s := by
  have h2 : (2 : ℝ) ≠ 0 := by norm_num
  obtain ⟨M₀, h⟩ : ∃ M₀, ∀ m ≥ M₀, ¬ Computes (genPerm ℝ m) (m ^ C) := by
    rcases thm_alt ℝ with hK | hK
    · exact thm_flat_simple hK h2 C
    · obtain ⟨c, hc, M₁, hlow⟩ := thm_contracting hK h2
      obtain ⟨M₂, hM₂⟩ := thm_main_calculation ((C : ℝ) / c)
      refine ⟨M₁ + M₂ + 2, fun m hm hcomp => ?_⟩
      have h1 := hlow m (by omega) _ hcomp
      have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
      have hL : 1 ≤ Real.logb 2 m := by
        rw [Real.le_logb_iff_rpow_le (by norm_num) hm0, Real.rpow_one]
        exact_mod_cast (by omega : 2 ≤ m)
      have h3 : (C : ℝ) * Real.logb 2 m ≤ c * Real.logb 2 m ^ 2 / Real.logb 2 (Real.logb 2 m) := by
        have h4 := mul_le_mul_of_nonneg_left (hM₂ m (by omega)) hc.le
        rw [← mul_assoc, mul_div_cancel₀ _ hc.ne', ← mul_div_assoc] at h4
        refine le_trans ?_ h4
        exact mul_le_mul_of_nonneg_left (Real.self_le_rpow_of_one_le hL (by norm_num)) (Nat.cast_nonneg C)
      have h5 := (Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ 2 by norm_num) h3).trans_lt h1
      rw [mul_comm, Real.rpow_mul (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) hm0,
        Real.rpow_natCast] at h5
      push_cast at h5
      exact lt_irrefl _ h5
  refine ⟨M₀, fun m hm s hs hc => h m hm ?_⟩
  rw [genPerm_eq]
  exact Computes.mono hc hs

/-- "VP is contained in VNP." -/
theorem vp_subset_vnp.{u} (F : Type u) [CommSemiring F] : VP F ⊆ VNP F := by
  rintro p ⟨C, hC⟩
  refine ⟨fun _ => 0, fun n => MvPolynomial.rename Sum.inl (p.poly n), ⟨C, fun n => ?_⟩, fun n => ?_⟩
  · obtain ⟨h1, h2, h3⟩ := hC n
    refine ⟨?_, (MvPolynomial.totalDegree_rename_le _ _).trans h2, h3.rename _⟩
    refine le_trans (le_of_eq ?_) h1
    change Fintype.card (p.X n ⊕ Fin 0) = _
    simp
  · rw [Fintype.sum_unique, bits_rename]

/-- **Paper: Corollary cor:classes.** "Over ℝ, VP is a proper subset of VNP." The witness is the permanent: it is in VNP
by Ryser's formula and not in VP by Theorem thm:simple. -/
theorem cor_classes : VP ℝ ⊂ VNP ℝ := by
  refine ⟨vp_subset_vnp ℝ, fun h => ?_⟩
  obtain ⟨C, hC⟩ := h (perm_mem_VNP ℝ)
  obtain ⟨m₀, hlow⟩ := thm_simple (C + 1)
  obtain ⟨m, hm⟩ : ∃ m, m = m₀ + C + 2 := ⟨_, rfl⟩
  refine hlow m (by omega) (m ^ C + C) ?_ ?_
  · have h1 : 1 ≤ m ^ C := Nat.one_le_pow _ _ (by omega)
    calc m ^ C + C ≤ m ^ C + m ^ C * C := Nat.add_le_add_left (Nat.le_mul_of_pos_left _ h1) _
      _ = m ^ C * (C + 1) := by ring
      _ ≤ m ^ C * m := Nat.mul_le_mul_left _ (by omega)
      _ = m ^ (C + 1) := (pow_succ m C).symm
  · rw [← genPerm_eq]
    exact (hC m).2.2

/-- m^(c(log m)^(1/3)) = 2^(c(log m)^(4/3)). -/
theorem thm_main_form {m : ℕ} (hm : 2 ≤ m) (c : ℝ) :
    (m : ℝ) ^ (c * Real.logb 2 m ^ (1 / 3 : ℝ)) = (2 : ℝ) ^ (c * Real.logb 2 m ^ (4 / 3 : ℝ)) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hL : 0 < Real.logb 2 m := Real.logb_pos (by norm_num) (by exact_mod_cast (by omega : 1 < m))
  conv_lhs => rw [← Real.rpow_logb (by norm_num : (0 : ℝ) < 2) (by norm_num) hm0, ← Real.rpow_mul (by norm_num)]
  rw [show (4 / 3 : ℝ) = 1 + 1 / 3 by norm_num, Real.rpow_add hL, Real.rpow_one, mul_left_comm]
  congr 2
  rw [Real.rpow_logb (by norm_num) (by norm_num) hm0]

/-- **Paper: Theorem thm:main.** "There are c > 0 and m₀ such that for all m ≥ m₀ every circuit over ℝ that computes
PERM_m has more than m^(c(log m)^(1/3)) gates." -/
theorem thm_main : ∃ c : ℝ, 0 < c ∧ ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ s : ℕ,
    Computes (∑ σ : Equiv.Perm (Fin m), ∏ i, MvPolynomial.X (σ i, i) : MvPolynomial (Fin m × Fin m) ℝ) s →
      (m : ℝ) ^ (c * Real.logb 2 m ^ (1 / 3 : ℝ)) < s := by
  have h2 : (2 : ℝ) ≠ 0 := by norm_num
  obtain ⟨c, hc, m₀, h⟩ : ∃ c : ℝ, 0 < c ∧ ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ s, Computes (genPerm ℝ m) s →
      (2 : ℝ) ^ (c * Real.logb 2 m ^ (4 / 3 : ℝ)) < s := by
    rcases thm_alt ℝ with hK | hK
    · obtain ⟨m₀, h⟩ := thm_flat_rate hK h2
      refine ⟨1 / 1600 ^ 2, by norm_num, m₀, fun m hm s hs => ?_⟩
      rw [one_div_mul_eq_div]
      exact h m hm s hs
    · obtain ⟨c, hc, m₁, h⟩ := thm_contracting hK h2
      obtain ⟨m₂, hm₂⟩ := thm_main_calculation 1
      refine ⟨c, hc, m₁ + m₂, fun m hm s hs => lt_of_le_of_lt ?_ (h m (by omega) s hs)⟩
      refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
      rw [mul_div_assoc]
      exact mul_le_mul_of_nonneg_left (by simpa using hm₂ m (by omega)) hc.le
  refine ⟨c, hc, m₀ + 2, fun m hm s hs => ?_⟩
  rw [thm_main_form (by omega) c]
  exact h m (by omega) s (genPerm_eq ℝ m ▸ hs)

end Paper
