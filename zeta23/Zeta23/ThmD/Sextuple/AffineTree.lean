/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.ThmD.Sextuple.PieceCert
import Zeta23.ThmD.Sextuple.Energy

open scoped BigOperators

noncomputable section

namespace Zeta23.ThmD.Sextuple

/-- An exact rational box for the five adjacent gaps. -/
structure GapBox where
  lo : Fin 5 → ℚ
  hi : Fin 5 → ℚ
  deriving DecidableEq, Repr

namespace GapBox

/-- Real membership in a rational five-gap box. Endpoints are included. -/
def Holds (box : GapBox) (g : Fin 5 → ℝ) : Prop :=
  ∀ i, ((box.lo i : ℚ) : ℝ) ≤ g i ∧ g i ≤ ((box.hi i : ℚ) : ℝ)

/-- Rational membership, used to validate compact rational witnesses. -/
def HoldsRat (box : GapBox) (z : Fin 5 → ℚ) : Prop :=
  ∀ i, box.lo i ≤ z i ∧ z i ≤ box.hi i

/-- The box has ordered endpoints in every coordinate. -/
def ordered (box : GapBox) : Bool :=
  decide (∀ i, box.lo i ≤ box.hi i)

lemma ordered_iff (box : GapBox) :
    box.ordered = true ↔ ∀ i, box.lo i ≤ box.hi i := by
  simp [ordered]

/-- Sum of the lower endpoints. -/
def lowerSpan (box : GapBox) : ℚ := ∑ i, box.lo i

/-- Exact midpoint of one coordinate. -/
def midpoint (box : GapBox) (axis : Fin 5) : ℚ :=
  (box.lo axis + box.hi axis) / 2

/-- Closed lower half of a midpoint split. -/
def lowerHalf (box : GapBox) (axis : Fin 5) : GapBox where
  lo := box.lo
  hi := Function.update box.hi axis (box.midpoint axis)

/-- Closed upper half of a midpoint split. -/
def upperHalf (box : GapBox) (axis : Fin 5) : GapBox where
  lo := Function.update box.lo axis (box.midpoint axis)
  hi := box.hi

lemma lowerHalf_holds_of_holds {box : GapBox} {axis : Fin 5} {g : Fin 5 → ℝ}
    (hg : box.Holds g) (haxis : g axis ≤ (box.midpoint axis : ℚ)) :
    (box.lowerHalf axis).Holds g := by
  intro i
  by_cases hi : i = axis
  · subst i
    simpa [lowerHalf] using And.intro (hg axis).1 haxis
  · simpa [lowerHalf, Function.update, hi] using hg i

lemma upperHalf_holds_of_holds {box : GapBox} {axis : Fin 5} {g : Fin 5 → ℝ}
    (hg : box.Holds g) (haxis : ((box.midpoint axis : ℚ) : ℝ) ≤ g axis) :
    (box.upperHalf axis).Holds g := by
  intro i
  by_cases hi : i = axis
  · subst i
    simpa [upperHalf] using And.intro haxis (hg axis).2
  · simpa [upperHalf, Function.update, hi] using hg i

/-- The two closed midpoint children cover their parent. -/
theorem holds_lowerHalf_or_upperHalf {box : GapBox} {axis : Fin 5} {g : Fin 5 → ℝ}
    (hg : box.Holds g) :
    (box.lowerHalf axis).Holds g ∨ (box.upperHalf axis).Holds g := by
  rcases le_total (g axis) (((box.midpoint axis : ℚ) : ℝ)) with h | h
  · exact Or.inl (lowerHalf_holds_of_holds hg h)
  · exact Or.inr (upperHalf_holds_of_holds hg h)

/-- A point on the splitting hyperplane belongs to both closed children. -/
theorem holds_both_halves_of_eq_midpoint {box : GapBox} {axis : Fin 5}
    {g : Fin 5 → ℝ} (hg : box.Holds g)
    (haxis : g axis = ((box.midpoint axis : ℚ) : ℝ)) :
    (box.lowerHalf axis).Holds g ∧ (box.upperHalf axis).Holds g := by
  exact ⟨lowerHalf_holds_of_holds hg haxis.le,
    upperHalf_holds_of_holds hg haxis.ge⟩

lemma midpoint_mem_interval {box : GapBox} {axis : Fin 5}
    (hordered : ∀ i, box.lo i ≤ box.hi i) :
    box.lo axis ≤ box.midpoint axis ∧ box.midpoint axis ≤ box.hi axis := by
  simp only [midpoint]
  constructor <;> linarith [hordered axis]

/-- Each closed lower child reconstructs a point of its parent. -/
theorem holds_of_lowerHalf_holds {box : GapBox} {axis : Fin 5} {g : Fin 5 → ℝ}
    (hordered : ∀ i, box.lo i ≤ box.hi i)
    (hg : (box.lowerHalf axis).Holds g) : box.Holds g := by
  intro i
  by_cases hi : i = axis
  · subst i
    have hmid : (((box.midpoint axis : ℚ) : ℝ)) ≤ ((box.hi axis : ℚ) : ℝ) := by
      exact_mod_cast (midpoint_mem_interval hordered).2
    have hga := hg axis
    simp only [lowerHalf, Function.update] at hga
    exact ⟨hga.1, hga.2.trans hmid⟩
  · simpa [lowerHalf, Function.update, hi] using hg i

/-- Each closed upper child reconstructs a point of its parent. -/
theorem holds_of_upperHalf_holds {box : GapBox} {axis : Fin 5} {g : Fin 5 → ℝ}
    (hordered : ∀ i, box.lo i ≤ box.hi i)
    (hg : (box.upperHalf axis).Holds g) : box.Holds g := by
  intro i
  by_cases hi : i = axis
  · subst i
    have hmid : (((box.lo axis : ℚ) : ℝ)) ≤ ((box.midpoint axis : ℚ) : ℝ) := by
      exact_mod_cast (midpoint_mem_interval hordered).1
    have hga := hg axis
    simp only [upperHalf, Function.update] at hga
    exact ⟨hmid.trans hga.1, hga.2⟩
  · simpa [upperHalf, Function.update, hi] using hg i

/-- Exact midpoint reconstruction: the parent is the union of its two closed children. -/
theorem holds_iff_holds_lowerHalf_or_upperHalf {box : GapBox} {axis : Fin 5}
    {g : Fin 5 → ℝ} (hordered : ∀ i, box.lo i ≤ box.hi i) :
    box.Holds g ↔ (box.lowerHalf axis).Holds g ∨ (box.upperHalf axis).Holds g := by
  constructor
  · exact holds_lowerHalf_or_upperHalf
  · rintro (hg | hg)
    · exact holds_of_lowerHalf_holds hordered hg
    · exact holds_of_upperHalf_holds hordered hg

end GapBox

/-- Left point index of the `p`-th consecutive pair, in lexicographic order. -/
def pairLeft (p : Fin 15) : Fin 6 :=
  match p.val with
  | 0 | 1 | 2 | 3 | 4 => 0
  | 5 | 6 | 7 | 8 => 1
  | 9 | 10 | 11 => 2
  | 12 | 13 => 3
  | _ => 4

/-- Right point index of the `p`-th consecutive pair, in lexicographic order. -/
def pairRight (p : Fin 15) : Fin 6 :=
  match p.val with
  | 0 => 1
  | 1 => 2
  | 2 => 3
  | 3 => 4
  | 4 => 5
  | 5 => 2
  | 6 => 3
  | 7 => 4
  | 8 => 5
  | 9 => 3
  | 10 => 4
  | 11 => 5
  | 12 => 4
  | _ => 5

@[simp] theorem pairLeft_lt_pairRight (p : Fin 15) : pairLeft p < pairRight p := by
  fin_cases p <;> decide

/-- The adjacent gaps occurring in one of the fifteen consecutive distances. -/
def gapSupport (p : Fin 15) : Finset (Fin 5) :=
  Finset.univ.filter fun k => (pairLeft p).val ≤ k.val ∧ k.val < (pairRight p).val

/-- One of the fifteen positive consecutive partial-sum distances. -/
def gapDistance (g : Fin 5 → ℝ) (p : Fin 15) : ℝ :=
  ∑ k ∈ gapSupport p, g k

/-- Exact interval image of one consecutive distance over a gap box. -/
def distanceInterval (box : GapBox) (p : Fin 15) : RatInterval where
  lo := ∑ k ∈ gapSupport p, box.lo k
  hi := ∑ k ∈ gapSupport p, box.hi k

/-- Every one of the fifteen consecutive distances lies in its exact interval image. -/
theorem distanceInterval_holds {box : GapBox} {g : Fin 5 → ℝ}
    (hg : box.Holds g) (p : Fin 15) :
    RatInterval.Holds (distanceInterval box p) (gapDistance g p) := by
  constructor
  · simpa [distanceInterval, gapDistance] using
      (Finset.sum_le_sum fun k _ => (hg k).1)
  · simpa [distanceInterval, gapDistance] using
      (Finset.sum_le_sum fun k _ => (hg k).2)

/-- The fixed index really enumerates fifteen distances. -/
@[simp] theorem card_consecutivePairs : Fintype.card (Fin 15) = 15 := by decide


@[simp] private lemma fin5_mk_two (h : (2 : ℕ) < 5) : (⟨2, h⟩ : Fin 5) = 2 := by rfl
@[simp] private lemma fin5_mk_three (h : (3 : ℕ) < 5) : (⟨3, h⟩ : Fin 5) = 3 := by rfl
@[simp] private lemma fin5_mk_four (h : (4 : ℕ) < 5) : (⟨4, h⟩ : Fin 5) = 4 := by rfl

/-- A consecutive gap sum is the difference of its two ordered positions. -/
theorem gapDistance_eq_position_sub (g : Fin 5 → ℝ) (p : Fin 15) :
    gapDistance g p =
      sextuplePosition g (pairRight p) - sextuplePosition g (pairLeft p) := by
  fin_cases p <;>
    simp only [gapDistance, gapSupport, Finset.sum_filter] <;>
    rw [Fin.sum_univ_five] <;>
    norm_num [pairLeft, pairRight, sextuplePosition, Fin.succ] <;> ring

lemma mtKernel_gapDistance_eq_pair (g : Fin 5 → ℝ) (p : Fin 15) :
    mtKernel (gapDistance g p) =
      mtKernel (sextuplePosition g (pairLeft p) - sextuplePosition g (pairRight p)) := by
  rw [gapDistance_eq_position_sub]
  symm
  simpa only [neg_sub] using
    mtKernel_neg (sextuplePosition g (pairRight p) - sextuplePosition g (pairLeft p))

/-- The fifteen positive-distance kernel terms in the sextuple energy. -/
def pairKernelEnergy (g : Fin 5 → ℝ) : ℝ :=
  ∑ p : Fin 15, 2 * mtKernel (gapDistance g p) ^ 2

/-- The fixed fifteen-term presentation agrees with `sextupleEnergy`. -/
theorem pairKernelEnergy_eq_sextupleEnergy (g : Fin 5 → ℝ) :
    pairKernelEnergy g = sextupleEnergy g := by
  simp [pairKernelEnergy, sextupleEnergy, sextupleGram,
    mtKernel_gapDistance_eq_pair, pairLeft, pairRight,
    Fin.sum_univ_succ, Finset.sum_filter]
  ring


/-- The sextuple energy is a sum of squares. -/
lemma sextupleEnergy_nonneg (g : Fin 5 → ℝ) : 0 ≤ sextupleEnergy g := by
  simp only [sextupleEnergy]
  positivity

/-- A cheap affine-span leaf. It uses only exact rational arithmetic. -/
def affineTailCheck (A B : ℚ) (box : GapBox) : Bool :=
  box.ordered && decide (0 ≤ B) && decide (A ≤ B * box.lowerSpan)

/-- An accepted affine-span leaf proves the target throughout its box. -/
theorem affineTailCheck_sound {A B : ℚ} {box : GapBox}
    (hc : affineTailCheck A B box = true) {g : Fin 5 → ℝ}
    (hg : box.Holds g) :
    ((A : ℚ) : ℝ) ≤ sextupleEnergy g + ((B : ℚ) : ℝ) * sextupleSpan g := by
  simp only [affineTailCheck, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨_hordered, hB⟩, hA⟩ := hc
  have hspan : ((box.lowerSpan : ℚ) : ℝ) ≤ sextupleSpan g := by
    simp only [GapBox.lowerSpan, sextupleSpan, Rat.cast_sum]
    exact Finset.sum_le_sum fun i _ => (hg i).1
  have hBR : (0 : ℝ) ≤ ((B : ℚ) : ℝ) := by exact_mod_cast hB
  have hmul : ((B * box.lowerSpan : ℚ) : ℝ) ≤
      ((B : ℚ) : ℝ) * sextupleSpan g := by
    simpa only [Rat.cast_mul] using mul_le_mul_of_nonneg_left hspan hBR
  have hAR : ((A : ℚ) : ℝ) ≤ ((B * box.lowerSpan : ℚ) : ℝ) := by
    exact_mod_cast hA
  nlinarith [sextupleEnergy_nonneg g, hAR.trans hmul]

/-- The concrete sextuple constants use the generic affine-span leaf. -/
theorem affineTailCheck_A6_sound {box : GapBox}
    (hc : affineTailCheck (1 / 80) (1094977 / 5000000000) box = true)
    {g : Fin 5 → ℝ} (hg : box.Holds g) :
    A6 ≤ sextupleEnergy g + B6 * sextupleSpan g := by
  simpa [A6, B6] using affineTailCheck_sound hc hg

/-- Beyond span `59`, the exact affine tail alone closes the sextuple target. -/
theorem sextuple_affine_of_span_ge_59 {g : Fin 5 → ℝ}
    (hspan : 59 ≤ sextupleSpan g) :
    A6 ≤ sextupleEnergy g + B6 * sextupleSpan g := by
  have henergy := sextupleEnergy_nonneg g
  norm_num [A6, B6] at *
  nlinarith


/-- An exact rational positive-semidefinite rank-one lower model. -/
structure RankOneModel where
  base : ℚ
  weight : ℚ
  offset : ℚ
  coeff : Fin 5 → ℚ
  deriving DecidableEq, Repr

namespace RankOneModel

/-- Rational dot product with the rank-one direction. -/
def dotRat (m : RankOneModel) (z : Fin 5 → ℚ) : ℚ :=
  ∑ i, m.coeff i * z i

/-- The rational value of `base + weight * (coeff·z+offset)^2`. -/
def valueRat (m : RankOneModel) (z : Fin 5 → ℚ) : ℚ :=
  m.base + m.weight * (m.dotRat z + m.offset) ^ 2

/-- Real dot product, with the rational direction cast exactly. -/
def dot (m : RankOneModel) (x : Fin 5 → ℝ) : ℝ :=
  ∑ i, ((m.coeff i : ℚ) : ℝ) * x i

/-- The real rank-one quadratic. -/
def value (m : RankOneModel) (x : Fin 5 → ℝ) : ℝ :=
  ((m.base : ℚ) : ℝ) + ((m.weight : ℚ) : ℝ) *
    (m.dot x + ((m.offset : ℚ) : ℝ)) ^ 2

@[simp] lemma cast_dotRat (m : RankOneModel) (z : Fin 5 → ℚ) :
    ((m.dotRat z : ℚ) : ℝ) = m.dot fun i => ((z i : ℚ) : ℝ) := by
  simp [dotRat, dot]

@[simp] lemma cast_valueRat (m : RankOneModel) (z : Fin 5 → ℚ) :
    ((m.valueRat z : ℚ) : ℝ) = m.value fun i => ((z i : ℚ) : ℝ) := by
  simp [valueRat, value]

lemma dot_sub (m : RankOneModel) (x z : Fin 5 → ℝ) :
    m.dot x - m.dot z = ∑ i, ((m.coeff i : ℚ) : ℝ) * (x i - z i) := by
  simp only [dot, mul_sub, Finset.sum_sub_distrib]

/-- Exact tangent plus square identity for one rank-one quadratic. -/
theorem value_tangent_sos (m : RankOneModel) (x z : Fin 5 → ℝ) :
    m.value x = m.value z +
      ∑ i, (2 * ((m.weight : ℚ) : ℝ) *
        (m.dot z + ((m.offset : ℚ) : ℝ)) * ((m.coeff i : ℚ) : ℝ)) * (x i - z i) +
      ((m.weight : ℚ) : ℝ) * (m.dot x - m.dot z) ^ 2 := by
  have hlin :
      (∑ i, (2 * ((m.weight : ℚ) : ℝ) *
        (m.dot z + ((m.offset : ℚ) : ℝ)) * ((m.coeff i : ℚ) : ℝ)) * (x i - z i)) =
      2 * ((m.weight : ℚ) : ℝ) * (m.dot z + ((m.offset : ℚ) : ℝ)) *
        (m.dot x - m.dot z) := by
    rw [dot_sub]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hlin]
  simp only [value]
  ring

end RankOneModel

/-- Exact rational gradient of a sum of rank-one models plus `B * span`. -/
def rankGradient {n : ℕ} (terms : Fin n → RankOneModel) (B : ℚ)
    (z : Fin 5 → ℚ) (i : Fin 5) : ℚ :=
  B + ∑ p, 2 * (terms p).weight * ((terms p).dotRat z + (terms p).offset) * (terms p).coeff i

/-- Exact rational objective at an anchor. -/
def rankObjectiveRat {n : ℕ} (terms : Fin n → RankOneModel) (B : ℚ)
    (z : Fin 5 → ℚ) : ℚ :=
  (∑ p, (terms p).valueRat z) + B * ∑ i, z i

/-- The real objective bounded by the tangent certificate. -/
def rankObjective {n : ℕ} (terms : Fin n → RankOneModel) (B : ℚ)
    (x : Fin 5 → ℝ) : ℝ :=
  (∑ p, (terms p).value x) + ((B : ℚ) : ℝ) * ∑ i, x i

/-- Minimum of one affine tangent coordinate over a rational box. -/
def affineCoordinateLower (box : GapBox) (z : Fin 5 → ℚ) (slope : ℚ)
    (i : Fin 5) : ℚ :=
  if 0 ≤ slope then slope * (box.lo i - z i)
  else slope * (box.hi i - z i)

/-- Exact rational tangent lower bound over a box. -/
def rankTangentLower {n : ℕ} (terms : Fin n → RankOneModel) (B : ℚ)
    (box : GapBox) (z : Fin 5 → ℚ) : ℚ :=
  rankObjectiveRat terms B z +
    ∑ i, affineCoordinateLower box z (rankGradient terms B z i) i

/-- Purely rational checker for a tangent/SOS lower bound on a box. -/
def rankTangentCheck {n : ℕ} (A B : ℚ) (box : GapBox) (z : Fin 5 → ℚ)
    (terms : Fin n → RankOneModel) : Bool :=
  box.ordered && decide (∀ i, box.lo i ≤ z i ∧ z i ≤ box.hi i) &&
    decide (∀ p, 0 ≤ (terms p).weight) &&
    decide (A ≤ rankTangentLower terms B box z)


@[simp] lemma cast_rankObjectiveRat {n : ℕ} (terms : Fin n → RankOneModel)
    (B : ℚ) (z : Fin 5 → ℚ) :
    ((rankObjectiveRat terms B z : ℚ) : ℝ) =
      rankObjective terms B (fun i => ((z i : ℚ) : ℝ)) := by
  simp [rankObjectiveRat, rankObjective]

@[simp] lemma cast_rankGradient {n : ℕ} (terms : Fin n → RankOneModel)
    (B : ℚ) (z : Fin 5 → ℚ) (i : Fin 5) :
    ((rankGradient terms B z i : ℚ) : ℝ) =
      ((B : ℚ) : ℝ) +
        ∑ p, 2 * (((terms p).weight : ℚ) : ℝ) *
          ((terms p).dot (fun j => ((z j : ℚ) : ℝ)) +
            (((terms p).offset : ℚ) : ℝ)) * (((terms p).coeff i : ℚ) : ℝ) := by
  simp [rankGradient]

private lemma sum_rankLinear_swap {n : ℕ} (C : Fin n → Fin 5 → ℝ)
    (d : Fin 5 → ℝ) :
    (∑ p, ∑ i, C p i * d i) = ∑ i, (∑ p, C p i) * d i := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_mul]

private lemma mul_sum_tangent (B : ℝ) (x z : Fin 5 → ℝ) :
    B * ∑ i, x i = B * ∑ i, z i + ∑ i, B * (x i - z i) := by
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

private lemma sum_rankLinear_add_span (B : ℝ) (C d : Fin 5 → ℝ) :
    (∑ i, C i * d i) + ∑ i, B * d i =
      ∑ i, (B + C i) * d i := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- A sum of nonnegative rank-one quadratics is its tangent plus an exact SOS. -/
theorem rankObjective_tangent_sos {n : ℕ} (terms : Fin n → RankOneModel)
    (B : ℚ) (x : Fin 5 → ℝ) (z : Fin 5 → ℚ) :
    rankObjective terms B x =
      rankObjective terms B (fun i => ((z i : ℚ) : ℝ)) +
        ∑ i, ((rankGradient terms B z i : ℚ) : ℝ) *
          (x i - ((z i : ℚ) : ℝ)) +
        ∑ p, (((terms p).weight : ℚ) : ℝ) *
          ((terms p).dot x -
            (terms p).dot (fun i => ((z i : ℚ) : ℝ))) ^ 2 := by
  let zR : Fin 5 → ℝ := fun i => ((z i : ℚ) : ℝ)
  let d : Fin 5 → ℝ := fun i => x i - zR i
  let C : Fin n → Fin 5 → ℝ := fun p i =>
    2 * (((terms p).weight : ℚ) : ℝ) *
      ((terms p).dot zR + (((terms p).offset : ℚ) : ℝ)) *
      (((terms p).coeff i : ℚ) : ℝ)
  let R : ℝ := ∑ p, (((terms p).weight : ℚ) : ℝ) *
    ((terms p).dot x - (terms p).dot zR) ^ 2
  have hterms :
      (∑ p, (terms p).value x) =
        (∑ p, (terms p).value zR) + (∑ p, ∑ i, C p i * d i) + R := by
    rw [show (∑ p, (terms p).value x) =
        ∑ p, ((terms p).value zR + ∑ i, C p i * d i +
          (((terms p).weight : ℚ) : ℝ) *
            ((terms p).dot x - (terms p).dot zR) ^ 2) by
      apply Finset.sum_congr rfl
      intro p _
      exact RankOneModel.value_tangent_sos (terms p) x zR]
    simp only [Finset.sum_add_distrib]
    rfl
  have hswap : (∑ p, ∑ i, C p i * d i) =
      ∑ i, (∑ p, C p i) * d i := sum_rankLinear_swap C d
  have hspan : (((B : ℚ) : ℝ) * ∑ i, x i) =
      ((B : ℚ) : ℝ) * ∑ i, zR i + ∑ i, ((B : ℚ) : ℝ) * d i := by
    exact mul_sum_tangent ((B : ℚ) : ℝ) x zR
  have hcombine :
      (∑ i, (∑ p, C p i) * d i) + ∑ i, ((B : ℚ) : ℝ) * d i =
        ∑ i, (((B : ℚ) : ℝ) + ∑ p, C p i) * d i :=
    sum_rankLinear_add_span ((B : ℚ) : ℝ) (fun i => ∑ p, C p i) d
  simp_rw [cast_rankGradient]
  change (∑ p, (terms p).value x) + ((B : ℚ) : ℝ) * ∑ i, x i =
    ((∑ p, (terms p).value zR) + ((B : ℚ) : ℝ) * ∑ i, zR i) +
      ∑ i, (((B : ℚ) : ℝ) + ∑ p, C p i) * d i + R
  rw [hterms, hswap, hspan]
  linear_combination hcombine


lemma affineCoordinateLower_sound {box : GapBox} {z : Fin 5 → ℚ}
    {slope : ℚ} {i : Fin 5} {x : Fin 5 → ℝ} (hx : box.Holds x) :
    ((affineCoordinateLower box z slope i : ℚ) : ℝ) ≤
      ((slope : ℚ) : ℝ) * (x i - ((z i : ℚ) : ℝ)) := by
  simp only [affineCoordinateLower]
  split_ifs with hs
  · have hsR : (0 : ℝ) ≤ ((slope : ℚ) : ℝ) := by exact_mod_cast hs
    simp only [Rat.cast_mul, Rat.cast_sub]
    exact mul_le_mul_of_nonneg_left (sub_le_sub_right (hx i).1 _) hsR
  · have hsR : ((slope : ℚ) : ℝ) ≤ 0 := by
      exact_mod_cast le_of_not_ge hs
    simp only [Rat.cast_mul, Rat.cast_sub]
    exact mul_le_mul_of_nonpos_left (sub_le_sub_right (hx i).2 _) hsR

/-- The exact rational tangent value is a lower bound for the PSD objective. -/
theorem rankTangentLower_sound {n : ℕ} {terms : Fin n → RankOneModel}
    {B : ℚ} {box : GapBox} {z : Fin 5 → ℚ}
    (hweight : ∀ p, 0 ≤ (terms p).weight) {x : Fin 5 → ℝ} (hx : box.Holds x) :
    ((rankTangentLower terms B box z : ℚ) : ℝ) ≤ rankObjective terms B x := by
  let zR : Fin 5 → ℝ := fun i => ((z i : ℚ) : ℝ)
  have hcoord :
      (∑ i, ((affineCoordinateLower box z (rankGradient terms B z i) i : ℚ) : ℝ)) ≤
        ∑ i, ((rankGradient terms B z i : ℚ) : ℝ) * (x i - zR i) := by
    exact Finset.sum_le_sum fun i _ => affineCoordinateLower_sound hx
  have hres : 0 ≤ ∑ p, (((terms p).weight : ℚ) : ℝ) *
      ((terms p).dot x - (terms p).dot zR) ^ 2 := by
    apply Finset.sum_nonneg
    intro p _
    have hcp : (0 : ℝ) ≤ (((terms p).weight : ℚ) : ℝ) := by exact_mod_cast hweight p
    exact mul_nonneg hcp (sq_nonneg _)
  rw [rankTangentLower, Rat.cast_add, Rat.cast_sum, cast_rankObjectiveRat]
  calc
    rankObjective terms B zR +
        ∑ i, ((affineCoordinateLower box z (rankGradient terms B z i) i : ℚ) : ℝ) ≤
      rankObjective terms B zR +
        ∑ i, ((rankGradient terms B z i : ℚ) : ℝ) * (x i - zR i) :=
      by simpa only [add_comm] using add_le_add_left hcoord (rankObjective terms B zR)
    _ ≤ rankObjective terms B x := by
      rw [rankObjective_tangent_sos terms B x z]
      exact le_add_of_nonneg_right hres

/-- Soundness of the exact rational tangent/SOS checker. -/
theorem rankTangentCheck_sound {n : ℕ} {A B : ℚ} {box : GapBox}
    {z : Fin 5 → ℚ} {terms : Fin n → RankOneModel}
    (hc : rankTangentCheck A B box z terms = true)
    {x : Fin 5 → ℝ} (hx : box.Holds x) :
    ((A : ℚ) : ℝ) ≤ rankObjective terms B x := by
  simp only [rankTangentCheck, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨_hordered, _hz⟩, hcoeff⟩, hA⟩ := hc
  have hAR : ((A : ℚ) : ℝ) ≤ ((rankTangentLower terms B box z : ℚ) : ℝ) := by
    exact_mod_cast hA
  exact hAR.trans (rankTangentLower_sound hcoeff hx)


/-- Any fifteen certified affine-square models lift termwise to the sextuple energy. -/
theorem rankObjective_le_energy_of_pairwise {B : ℚ}
    {terms : Fin 15 → RankOneModel} {g : Fin 5 → ℝ}
    (hpair : ∀ p, (terms p).value g ≤ 2 * mtKernel (gapDistance g p) ^ 2) :
    rankObjective terms B g ≤
      sextupleEnergy g + ((B : ℚ) : ℝ) * sextupleSpan g := by
  have hsum : (∑ p, (terms p).value g) ≤ pairKernelEnergy g := by
    simpa only [pairKernelEnergy] using Finset.sum_le_sum fun p _ => hpair p
  simpa only [rankObjective, pairKernelEnergy_eq_sextupleEnergy, sextupleSpan] using
    add_le_add_left hsum (((B : ℚ) : ℝ) * ∑ i, g i)

/-- Generic box leaf: rational tangent checking plus certified pointwise 1D models. -/
theorem rankTangentCheck_energy_sound {A B : ℚ} {box : GapBox}
    {z : Fin 5 → ℚ} {terms : Fin 15 → RankOneModel}
    (hc : rankTangentCheck A B box z terms = true)
    (hpair : ∀ ⦃g⦄, box.Holds g → ∀ p,
      (terms p).value g ≤ 2 * mtKernel (gapDistance g p) ^ 2) :
    ∀ ⦃g⦄, box.Holds g →
      ((A : ℚ) : ℝ) ≤ sextupleEnergy g + ((B : ℚ) : ℝ) * sextupleSpan g := by
  intro g hg
  exact (rankTangentCheck_sound hc hg).trans
    (rankObjective_le_energy_of_pairwise (hpair hg))

/-- The `0/1` rational direction for one consecutive distance. -/
def consecutiveCoeff (p : Fin 15) (i : Fin 5) : ℚ :=
  if i ∈ gapSupport p then 1 else 0

/-- A certified one-dimensional lower piece as an affine-square rank-one term. -/
def lowerPieceRankModel (pieces : Fin 15 → LowerPiece) (p : Fin 15) :
    RankOneModel where
  base := (pieces p).a
  weight := (pieces p).c
  offset := -(pieces p).q
  coeff := consecutiveCoeff p

@[simp] theorem lowerPieceRankModel_dot (pieces : Fin 15 → LowerPiece)
    (p : Fin 15) (g : Fin 5 → ℝ) :
    (lowerPieceRankModel pieces p).dot g = gapDistance g p := by
  simp only [RankOneModel.dot, lowerPieceRankModel, gapDistance]
  calc
    (∑ i, ((consecutiveCoeff p i : ℚ) : ℝ) * g i) =
        ∑ i, if i ∈ gapSupport p then g i else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : i ∈ gapSupport p <;> simp [consecutiveCoeff, hi]
    _ = ∑ i ∈ gapSupport p, g i := by
      rw [gapSupport, Finset.sum_filter]
      simp

@[simp] theorem lowerPieceRankModel_value (pieces : Fin 15 → LowerPiece)
    (p : Fin 15) (g : Fin 5 → ℝ) :
    (lowerPieceRankModel pieces p).value g = (pieces p).model (gapDistance g p) := by
  rw [RankOneModel.value]
  rw [lowerPieceRankModel_dot]
  simp only [lowerPieceRankModel, LowerPiece.model, Rat.cast_neg]
  ring

/-- Every selected one-dimensional piece contains its distance interval. -/
def lowerPiecesFit (box : GapBox) (pieces : Fin 15 → LowerPiece) : Bool :=
  decide (∀ p, (pieces p).box.lo ≤ (distanceInterval box p).lo ∧
    (distanceInterval box p).hi ≤ (pieces p).box.hi)

/-- Fast leaf check when the selected pieces have been certified once globally. -/
def lowerPieceTangentCheck (A B : ℚ) (box : GapBox) (z : Fin 5 → ℚ)
    (pieces : Fin 15 → LowerPiece) : Bool :=
  lowerPiecesFit box pieces &&
    rankTangentCheck A B box z (lowerPieceRankModel pieces)

/-- Standalone leaf check. This also replays all selected one-dimensional pieces. -/
def checkedLowerPieceTangentCheck (A B : ℚ) (box : GapBox) (z : Fin 5 → ℚ)
    (pieces : Fin 15 → LowerPiece) : Bool :=
  decide (∀ p, (pieces p).check = true) &&
    lowerPieceTangentCheck A B box z pieces

lemma distanceInterval_holds_selectedPiece {box : GapBox} {g : Fin 5 → ℝ}
    (hg : box.Holds g) {pieces : Fin 15 → LowerPiece}
    (hfit : ∀ p, (pieces p).box.lo ≤ (distanceInterval box p).lo ∧
      (distanceInterval box p).hi ≤ (pieces p).box.hi) (p : Fin 15) :
    RatInterval.Holds (pieces p).box (gapDistance g p) := by
  have hd := distanceInterval_holds hg p
  constructor
  · have hlo : (((pieces p).box.lo : ℚ) : ℝ) ≤
        (((distanceInterval box p).lo : ℚ) : ℝ) := by
      exact_mod_cast (hfit p).1
    exact hlo.trans hd.1
  · have hhi : (((distanceInterval box p).hi : ℚ) : ℝ) ≤
        (((pieces p).box.hi : ℚ) : ℝ) := by
      exact_mod_cast (hfit p).2
    exact hd.2.trans hhi

/-- The rank-one objective assembled from selected pieces is below the kernel energy. -/
theorem lowerPieceRankObjective_le_energy {B : ℚ} {box : GapBox}
    {pieces : Fin 15 → LowerPiece} (hcert : ∀ p, (pieces p).check = true)
    (hfit : ∀ p, (pieces p).box.lo ≤ (distanceInterval box p).lo ∧
      (distanceInterval box p).hi ≤ (pieces p).box.hi)
    {g : Fin 5 → ℝ} (hg : box.Holds g) :
    rankObjective (lowerPieceRankModel pieces) B g ≤
      sextupleEnergy g + ((B : ℚ) : ℝ) * sextupleSpan g := by
  have hp : ∀ p, (pieces p).model (gapDistance g p) ≤
      2 * mtKernel (gapDistance g p) ^ 2 := by
    intro p
    exact LowerPiece.check_sound (hcert p)
      (distanceInterval_holds_selectedPiece hg hfit p)
  have hsum : (∑ p, (pieces p).model (gapDistance g p)) ≤ pairKernelEnergy g := by
    simpa only [pairKernelEnergy] using Finset.sum_le_sum fun p _ => hp p
  simpa only [rankObjective, lowerPieceRankModel_value,
    pairKernelEnergy_eq_sextupleEnergy, sextupleSpan] using
      add_le_add_left hsum (((B : ℚ) : ℝ) * ∑ i, g i)

/-- A rational tangent certificate over certified one-dimensional models proves the affine bound. -/
theorem lowerPieceTangentCheck_sound {A B : ℚ} {box : GapBox}
    {z : Fin 5 → ℚ} {pieces : Fin 15 → LowerPiece}
    (hcert : ∀ p, (pieces p).check = true)
    (hc : lowerPieceTangentCheck A B box z pieces = true)
    {g : Fin 5 → ℝ} (hg : box.Holds g) :
    ((A : ℚ) : ℝ) ≤ sextupleEnergy g + ((B : ℚ) : ℝ) * sextupleSpan g := by
  simp only [lowerPieceTangentCheck, lowerPiecesFit, Bool.and_eq_true,
    decide_eq_true_eq] at hc
  obtain ⟨hfit, htangent⟩ := hc
  exact (rankTangentCheck_sound htangent hg).trans
    (lowerPieceRankObjective_le_energy hcert hfit hg)

/-- Standalone checked leaves need no analytic or table premise. -/
theorem checkedLowerPieceTangentCheck_sound {A B : ℚ} {box : GapBox}
    {z : Fin 5 → ℚ} {pieces : Fin 15 → LowerPiece}
    (hc : checkedLowerPieceTangentCheck A B box z pieces = true)
    {g : Fin 5 → ℝ} (hg : box.Holds g) :
    ((A : ℚ) : ℝ) ≤ sextupleEnergy g + ((B : ℚ) : ℝ) * sextupleSpan g := by
  simp only [checkedLowerPieceTangentCheck, Bool.and_eq_true,
    decide_eq_true_eq] at hc
  exact lowerPieceTangentCheck_sound hc.1 hc.2 hg

/-- Concrete `A6/B6` form of a standalone checked tangent leaf. -/
theorem checkedLowerPieceTangentCheck_A6_sound {box : GapBox}
    {z : Fin 5 → ℚ} {pieces : Fin 15 → LowerPiece}
    (hc : checkedLowerPieceTangentCheck (1 / 80) (1094977 / 5000000000)
      box z pieces = true)
    {g : Fin 5 → ℝ} (hg : box.Holds g) :
    A6 ≤ sextupleEnergy g + B6 * sextupleSpan g := by
  simpa [A6, B6] using checkedLowerPieceTangentCheck_sound hc hg


/-- Prefix-code token: a terminal node or a midpoint split with an explicit axis. -/
inductive AffineTreeToken where
  | terminal
  | split (axis : Fin 5)
  deriving DecidableEq, Repr

/-- A cursor-addressed finite stream. Its reader is always bounded by `length`. -/
structure CursorStream (α : Type*) where
  length : ℕ
  read : ℕ → Option α

namespace CursorStream

/-- Read one logical stream entry; out-of-range cursors fail. -/
def get? (stream : CursorStream α) (cursor : ℕ) : Option α :=
  if cursor < stream.length then stream.read cursor else none

/-- A simple stream adapter for small generated lists. -/
def ofList (xs : List α) : CursorStream α where
  length := xs.length
  read := fun cursor => xs[cursor]?

@[simp] lemma get?_ofList (xs : List α) (cursor : ℕ) :
    (ofList xs).get? cursor = xs[cursor]? := by
  by_cases hcursor : cursor < xs.length <;> simp [get?, ofList, hcursor]

end CursorStream

/-- Decoder for the six valid three-bit topology codes.
`0` is terminal and `1,...,5` split axes `0,...,4`. -/
def decodeAffineTreeToken : ℕ → Option AffineTreeToken
  | 0 => some .terminal
  | 1 => some (.split 0)
  | 2 => some (.split 1)
  | 3 => some (.split 2)
  | 4 => some (.split 3)
  | 5 => some (.split 4)
  | _ => none

/-- Twenty three-bit topology tokens packed into each natural-number word. -/
def packedTopologyRead (words : Array ℕ) (cursor : ℕ) : Option AffineTreeToken :=
  match words[cursor / 20]? with
  | none => none
  | some word =>
      decodeAffineTreeToken ((word / 2 ^ (3 * (cursor % 20))) % 8)

/-- Compact topology stream backed by 60-bit natural-number chunks. -/
def packedTopologyStream (tokenCount : ℕ) (words : Array ℕ) :
    CursorStream AffineTreeToken where
  length := tokenCount
  read := packedTopologyRead words

/-- Canonical physical layout for 20 three-bit tokens per 60-bit word. -/
def PackedTopologyLayoutValid (tokenCount : ℕ) (words : Array ℕ) : Prop :=
  words.size = (tokenCount + 19) / 20 ∧
    (∀ i : Fin words.size, words[i] < 2 ^ 60) ∧
    (tokenCount % 20 = 0 ∨
      ∃ word, words[tokenCount / 20]? = some word ∧
        word < 2 ^ (3 * (tokenCount % 20)))

/-- Reject extra words, non-60-bit words, and nonzero final padding slots. -/
def packedTopologyLayoutCheck (tokenCount : ℕ) (words : Array ℕ) : Bool :=
  decide (words.size = (tokenCount + 19) / 20 ∧
    (∀ i : Fin words.size, words[i] < 2 ^ 60) ∧
    (tokenCount % 20 = 0 ∨
      ∃ word, words[tokenCount / 20]? = some word ∧
        word < 2 ^ (3 * (tokenCount % 20))))

@[simp] theorem packedTopologyLayoutCheck_iff (tokenCount : ℕ) (words : Array ℕ) :
    packedTopologyLayoutCheck tokenCount words = true ↔
      PackedTopologyLayoutValid tokenCount words := by
  simp [packedTopologyLayoutCheck, PackedTopologyLayoutValid]

/-- Expose a packed topology stream only after canonical physical validation. -/
def checkedPackedTopologyStream (tokenCount : ℕ) (words : Array ℕ) :
    Option (CursorStream AffineTreeToken) :=
  if packedTopologyLayoutCheck tokenCount words then
    some (packedTopologyStream tokenCount words)
  else none

/-- Fuel-bounded prefix replay. Cursors, rather than nested tree constructors, carry topology.
A split consumes one topology token. A terminal also consumes one payload. -/
def replayAffineTree {α : Type*} (leafCheck : GapBox → α → Bool)
    (topology : CursorStream AffineTreeToken) (payloads : CursorStream α) :
    ℕ → ℕ → ℕ → GapBox → Option (ℕ × ℕ)
  | 0, _, _, _ => none
  | fuel + 1, topologyCursor, payloadCursor, box =>
      match topology.get? topologyCursor with
      | none => none
      | some .terminal =>
          match payloads.get? payloadCursor with
          | none => none
          | some payload =>
              if leafCheck box payload then
                some (topologyCursor + 1, payloadCursor + 1)
              else none
      | some (.split axis) =>
          match replayAffineTree leafCheck topology payloads fuel
              (topologyCursor + 1) payloadCursor (box.lowerHalf axis) with
          | none => none
          | some cursors =>
              replayAffineTree leafCheck topology payloads fuel cursors.1 cursors.2
                (box.upperHalf axis)

/-- A complete serialized tree must consume both logical streams exactly. -/
def checkAffineTree {α : Type*} (leafCheck : GapBox → α → Bool)
    (topology : CursorStream AffineTreeToken) (payloads : CursorStream α)
    (fuel : ℕ) (root : GapBox) : Bool :=
  decide (replayAffineTree leafCheck topology payloads fuel 0 0 root =
    some (topology.length, payloads.length))

/-- Pointwise goal supplied by every terminal leaf. -/
def BoxPredicate (P : (Fin 5 → ℝ) → Prop) (box : GapBox) : Prop :=
  ∀ ⦃g⦄, box.Holds g → P g

/-- Sound left and right children cover their parent, including the shared midpoint. -/
theorem boxPredicate_of_midpoint_children {P : (Fin 5 → ℝ) → Prop}
    {box : GapBox} {axis : Fin 5}
    (hleft : BoxPredicate P (box.lowerHalf axis))
    (hright : BoxPredicate P (box.upperHalf axis)) : BoxPredicate P box := by
  intro g hg
  rcases box.holds_lowerHalf_or_upperHalf hg with hgl | hgr
  · exact hleft hgl
  · exact hright hgr


/-- Soundness of every successful fuel-bounded replay. Split children jointly cover
all parent points; equality at the midpoint may be sent to either child. -/
theorem replayAffineTree_sound {α : Type*} {P : (Fin 5 → ℝ) → Prop}
    {leafCheck : GapBox → α → Bool}
    {topology : CursorStream AffineTreeToken} {payloads : CursorStream α}
    (hleaf : ∀ box payload, leafCheck box payload = true → BoxPredicate P box)
    {fuel topologyCursor payloadCursor : ℕ} {box : GapBox} {result : ℕ × ℕ}
    (hrun : replayAffineTree leafCheck topology payloads fuel
      topologyCursor payloadCursor box = some result) :
    BoxPredicate P box := by
  induction fuel generalizing topologyCursor payloadCursor box result with
  | zero => simp [replayAffineTree] at hrun
  | succ fuel ih =>
      cases htoken : topology.get? topologyCursor with
      | none => simp [replayAffineTree, htoken] at hrun
      | some token =>
          cases token with
          | terminal =>
              cases hpayload : payloads.get? payloadCursor with
              | none => simp [replayAffineTree, htoken, hpayload] at hrun
              | some payload =>
                  by_cases hc : leafCheck box payload = true
                  · exact hleaf box payload hc
                  · simp [replayAffineTree, htoken, hpayload, hc] at hrun
          | split axis =>
              cases hleft : replayAffineTree leafCheck topology payloads fuel
                  (topologyCursor + 1) payloadCursor (box.lowerHalf axis) with
              | none => simp [replayAffineTree, htoken, hleft] at hrun
              | some cursors =>
                  have hright : replayAffineTree leafCheck topology payloads fuel
                      cursors.1 cursors.2 (box.upperHalf axis) = some result := by
                    simpa [replayAffineTree, htoken, hleft] using hrun
                  have leftSound : BoxPredicate P (box.lowerHalf axis) := ih hleft
                  have rightSound : BoxPredicate P (box.upperHalf axis) := ih hright
                  exact boxPredicate_of_midpoint_children leftSound rightSound

/-- Exact stream exhaustion turns replay soundness into whole-tree soundness. -/
theorem checkAffineTree_sound {α : Type*} {P : (Fin 5 → ℝ) → Prop}
    {leafCheck : GapBox → α → Bool}
    {topology : CursorStream AffineTreeToken} {payloads : CursorStream α}
    {fuel : ℕ} {root : GapBox}
    (hleaf : ∀ box payload, leafCheck box payload = true → BoxPredicate P box)
    (hc : checkAffineTree leafCheck topology payloads fuel root = true) :
    BoxPredicate P root := by
  simp only [checkAffineTree, decide_eq_true_eq] at hc
  exact replayAffineTree_sound hleaf hc

/-- Accepted serialization exposes the exact terminal topology and payload cursors. -/
theorem checkAffineTree_exact_exhaustion {α : Type*}
    {leafCheck : GapBox → α → Bool}
    {topology : CursorStream AffineTreeToken} {payloads : CursorStream α}
    {fuel : ℕ} {root : GapBox}
    (hc : checkAffineTree leafCheck topology payloads fuel root = true) :
    replayAffineTree leafCheck topology payloads fuel 0 0 root =
      some (topology.length, payloads.length) := by
  simpa [checkAffineTree] using hc


/-- Terminal-kind payload. The topology stream only records terminal versus split. -/
inductive AffineLeafPayload (α : Type*) where
  | tail
  | quadratic (payload : α)
  deriving DecidableEq, Repr

/-- Combine the cheap span tail with an arbitrary certified quadratic leaf checker. -/
def affineLeafCheck {α : Type*} (A B : ℚ)
    (quadraticCheck : GapBox → α → Bool) (box : GapBox) :
    AffineLeafPayload α → Bool
  | .tail => affineTailCheck A B box
  | .quadratic payload => quadraticCheck box payload

/-- The exact affine energy target associated to rational constants. -/
def affineEnergyGoal (A B : ℚ) (g : Fin 5 → ℝ) : Prop :=
  ((A : ℚ) : ℝ) ≤ sextupleEnergy g + ((B : ℚ) : ℝ) * sextupleSpan g

/-- Sound quadratic leaves and affine tails give a sound combined terminal checker. -/
theorem affineLeafCheck_sound {α : Type*} {A B : ℚ}
    {quadraticCheck : GapBox → α → Bool}
    (hquadratic : ∀ box payload, quadraticCheck box payload = true →
      BoxPredicate (affineEnergyGoal A B) box) :
    ∀ box payload, affineLeafCheck A B quadraticCheck box payload = true →
      BoxPredicate (affineEnergyGoal A B) box := by
  intro box payload hc
  cases payload with
  | tail =>
      simp only [affineLeafCheck] at hc
      intro g hg
      exact affineTailCheck_sound hc hg
  | quadratic payload =>
      exact hquadratic box payload hc

/-- Generic soundness theorem for a serialized affine certificate tree. -/
theorem checkAffineCertificate_sound {α : Type*} {A B : ℚ}
    {quadraticCheck : GapBox → α → Bool}
    {topology : CursorStream AffineTreeToken}
    {payloads : CursorStream (AffineLeafPayload α)}
    {fuel : ℕ} {root : GapBox}
    (hquadratic : ∀ box payload, quadraticCheck box payload = true →
      BoxPredicate (affineEnergyGoal A B) box)
    (hc : checkAffineTree (affineLeafCheck A B quadraticCheck)
      topology payloads fuel root = true) :
    BoxPredicate (affineEnergyGoal A B) root := by
  exact checkAffineTree_sound (affineLeafCheck_sound hquadratic) hc

/-- Payload for a self-contained selected-lower-piece leaf. -/
structure LowerPieceLeaf where
  anchor : Fin 5 → ℚ
  pieces : Fin 15 → LowerPiece
  deriving DecidableEq, Repr

/-- Standalone quadratic terminal checker backed by `LowerPiece.check`. -/
def checkedLowerPieceLeafCheck (A B : ℚ) (box : GapBox)
    (leaf : LowerPieceLeaf) : Bool :=
  checkedLowerPieceTangentCheck A B box leaf.anchor leaf.pieces

/-- Standalone selected-piece terminal soundness. -/
theorem checkedLowerPieceLeafCheck_sound {A B : ℚ} :
    ∀ box leaf, checkedLowerPieceLeafCheck A B box leaf = true →
      BoxPredicate (affineEnergyGoal A B) box := by
  intro box leaf hc g hg
  exact checkedLowerPieceTangentCheck_sound hc hg

/-- A complete standalone selected-piece tree needs no theorem premise. -/
theorem checkedLowerPieceAffineTree_sound {A B : ℚ}
    {topology : CursorStream AffineTreeToken}
    {payloads : CursorStream (AffineLeafPayload LowerPieceLeaf)}
    {fuel : ℕ} {root : GapBox}
    (hc : checkAffineTree
      (affineLeafCheck A B (checkedLowerPieceLeafCheck A B))
      topology payloads fuel root = true) :
    BoxPredicate (affineEnergyGoal A B) root := by
  exact checkAffineCertificate_sound checkedLowerPieceLeafCheck_sound hc

/-- Concrete `A6/B6` conclusion of an accepted standalone tree. -/
theorem checkedLowerPieceAffineTree_A6_sound
    {topology : CursorStream AffineTreeToken}
    {payloads : CursorStream (AffineLeafPayload LowerPieceLeaf)}
    {fuel : ℕ} {root : GapBox}
    (hc : checkAffineTree
      (affineLeafCheck (1 / 80) (1094977 / 5000000000)
        (checkedLowerPieceLeafCheck (1 / 80) (1094977 / 5000000000)))
      topology payloads fuel root = true) :
    ∀ ⦃g⦄, root.Holds g → A6 ≤ sextupleEnergy g + B6 * sextupleSpan g := by
  intro g hg
  simpa [affineEnergyGoal, A6, B6] using
    (checkedLowerPieceAffineTree_sound hc hg)


/-- Compact exact box with one positive denominator shared by all ten endpoints. -/
structure SharedDenomGapBox where
  denominator : ℕ
  loNumerator : Fin 5 → ℤ
  hiNumerator : Fin 5 → ℤ
  deriving DecidableEq, Repr

namespace SharedDenomGapBox

/-- Decode the compact integer endpoints to exact rationals. -/
def toGapBox (box : SharedDenomGapBox) : GapBox where
  lo := fun i => (box.loNumerator i : ℚ) / (box.denominator : ℚ)
  hi := fun i => (box.hiNumerator i : ℚ) / (box.denominator : ℚ)

/-- Integer-only validation; it avoids repeated rational normalization. -/
def check (box : SharedDenomGapBox) : Bool :=
  decide (0 < box.denominator ∧ ∀ i, box.loNumerator i ≤ box.hiNumerator i)

/-- Integer endpoint validation implies the decoded rational box is ordered. -/
theorem check_sound {box : SharedDenomGapBox} (hc : box.check = true) :
    box.toGapBox.ordered = true := by
  simp only [check, decide_eq_true_eq] at hc
  rw [GapBox.ordered_iff]
  intro i
  simp only [toGapBox]
  have hden : (0 : ℚ) < (box.denominator : ℚ) := by exact_mod_cast hc.1
  apply (div_le_div_iff_of_pos_right hden).2
  exact_mod_cast hc.2 i

end SharedDenomGapBox

/-- Five small integer coordinates, interpreted relative to the current box. -/
structure RelativeAnchor where
  coordinate : Fin 5 → ℕ
  deriving DecidableEq, Repr

/-- Decode relative coordinates by exact rational interpolation in the current box. -/
def RelativeAnchor.decode (resolution : ℕ) (box : GapBox) (anchor : RelativeAnchor) :
    Fin 5 → ℚ := fun i =>
  box.lo i + (anchor.coordinate i : ℚ) / (resolution : ℚ) *
    (box.hi i - box.lo i)

/-- Integer-only bounds for a relative anchor. Dyadic resolution `16384` is the intended concrete encoding. -/
def RelativeAnchor.check (resolution : ℕ) (anchor : RelativeAnchor) : Bool :=
  decide (0 < resolution ∧ ∀ i, anchor.coordinate i ≤ resolution)

/-- A validated relative anchor decodes inside every ordered rational box. -/
theorem RelativeAnchor.decode_holdsRat {resolution : ℕ} {box : GapBox}
    {anchor : RelativeAnchor} (hbox : box.ordered = true)
    (ha : anchor.check resolution = true) :
    box.HoldsRat (anchor.decode resolution box) := by
  rw [GapBox.ordered_iff] at hbox
  simp only [RelativeAnchor.check, decide_eq_true_eq] at ha
  intro i
  have hres : (0 : ℚ) < (resolution : ℚ) := by exact_mod_cast ha.1
  have hcoord0 : (0 : ℚ) ≤ (anchor.coordinate i : ℚ) := by positivity
  have ht0 : (0 : ℚ) ≤ (anchor.coordinate i : ℚ) / (resolution : ℚ) :=
    div_nonneg hcoord0 hres.le
  have ht1 : (anchor.coordinate i : ℚ) / (resolution : ℚ) ≤ 1 := by
    rw [div_le_one hres]
    exact_mod_cast ha.2 i
  have hwidth : 0 ≤ box.hi i - box.lo i := sub_nonneg.mpr (hbox i)
  constructor
  · simp only [RelativeAnchor.decode]
    nlinarith [mul_nonneg ht0 hwidth]
  · simp only [RelativeAnchor.decode]
    nlinarith [mul_le_mul_of_nonneg_right ht1 hwidth]

/-- Tangent checker whose five anchor coordinates are stored as small integers. -/
def relativeRankTangentCheck {n : ℕ} (resolution : ℕ) (A B : ℚ)
    (box : GapBox) (anchor : RelativeAnchor) (terms : Fin n → RankOneModel) : Bool :=
  box.ordered && anchor.check resolution &&
    decide (∀ p, 0 ≤ (terms p).weight) &&
    decide (A ≤ rankTangentLower terms B box (anchor.decode resolution box))

/-- Soundness of the compact relative-anchor tangent checker. -/
theorem relativeRankTangentCheck_sound {n : ℕ} {resolution : ℕ} {A B : ℚ}
    {box : GapBox} {anchor : RelativeAnchor} {terms : Fin n → RankOneModel}
    (hc : relativeRankTangentCheck resolution A B box anchor terms = true)
    {g : Fin 5 → ℝ} (hg : box.Holds g) :
    ((A : ℚ) : ℝ) ≤ rankObjective terms B g := by
  simp only [relativeRankTangentCheck, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨_hbox, _hanchor⟩, hweight⟩, hA⟩ := hc
  have hAR : ((A : ℚ) : ℝ) ≤
      ((rankTangentLower terms B box (anchor.decode resolution box) : ℚ) : ℝ) := by
    exact_mod_cast hA
  exact hAR.trans (rankTangentLower_sound hweight hg)

/-- Compact relative-anchor leaf lifted through fifteen certified 1D models. -/
theorem relativeRankTangentCheck_energy_sound {resolution : ℕ} {A B : ℚ}
    {box : GapBox} {anchor : RelativeAnchor} {terms : Fin 15 → RankOneModel}
    (hc : relativeRankTangentCheck resolution A B box anchor terms = true)
    (hpair : ∀ ⦃g⦄, box.Holds g → ∀ p,
      (terms p).value g ≤ 2 * mtKernel (gapDistance g p) ^ 2) :
    ∀ ⦃g⦄, box.Holds g →
      ((A : ℚ) : ℝ) ≤ sextupleEnergy g + ((B : ℚ) : ℝ) * sextupleSpan g := by
  intro g hg
  exact (relativeRankTangentCheck_sound hc hg).trans
    (rankObjective_le_energy_of_pairwise (hpair hg))


/-- Canonical exact box `[0,limit]^5`. -/
def initialGapBox (limit : ℚ) : GapBox where
  lo := fun _ => 0
  hi := fun _ => limit

/-- Nonnegative gaps of total span at most `limit` lie in `[0,limit]^5`. -/
theorem initialGapBox_holds {limit : ℚ} {g : Fin 5 → ℝ}
    (hg : ∀ i, 0 ≤ g i) (hspan : sextupleSpan g ≤ ((limit : ℚ) : ℝ)) :
    (initialGapBox limit).Holds g := by
  intro i
  constructor
  · simpa [initialGapBox] using hg i
  · have hi : g i ≤ ∑ j, g j := by
      exact Finset.single_le_sum (fun j _ => hg j) (Finset.mem_univ i)
    simpa only [initialGapBox, sextupleSpan] using hi.trans hspan

/-- A sound tree on `[0,59]^5`, together with the exact tail, covers all
nonnegative five-gap configurations. -/
theorem affineTree_A6_global_of_root
    (hroot : BoxPredicate (fun g =>
      A6 ≤ sextupleEnergy g + B6 * sextupleSpan g) (initialGapBox 59))
    {g : Fin 5 → ℝ} (hg : ∀ i, 0 ≤ g i) :
    A6 ≤ sextupleEnergy g + B6 * sextupleSpan g := by
  by_cases hspan : 59 ≤ sextupleSpan g
  · exact sextuple_affine_of_span_ge_59 hspan
  · exact hroot (initialGapBox_holds hg (le_of_not_ge hspan))

/-- Global `A6/B6` soundness of a complete standalone tree on `[0,59]^5`. -/
theorem checkedLowerPieceAffineTree_A6_global_sound
    {topology : CursorStream AffineTreeToken}
    {payloads : CursorStream (AffineLeafPayload LowerPieceLeaf)}
    {fuel : ℕ}
    (hc : checkAffineTree
      (affineLeafCheck (1 / 80) (1094977 / 5000000000)
        (checkedLowerPieceLeafCheck (1 / 80) (1094977 / 5000000000)))
      topology payloads fuel (initialGapBox 59) = true)
    {g : Fin 5 → ℝ} (hg : ∀ i, 0 ≤ g i) :
    A6 ≤ sextupleEnergy g + B6 * sextupleSpan g := by
  apply affineTree_A6_global_of_root
  · exact checkedLowerPieceAffineTree_A6_sound hc
  · exact hg

end Zeta23.ThmD.Sextuple
