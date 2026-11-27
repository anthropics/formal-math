import Zeta23.ThmD.Sextuple.Macro.AffineAdapter

noncomputable section

namespace Zeta23.ThmD.Sextuple.MacroPrototype

open Zeta23.ThmD.Sextuple
open RatInterval

structure AffineOneModel where
  base : ℚ
  weight : ℚ
  slope : ℚ
  offset : ℚ
  deriving DecidableEq, Repr


def macroAffineOne : MacroPiece → AffineOneModel
  | .base p => ⟨p.a, p.c, 1, -p.q⟩
  | .well p => ⟨0, 2, wellSlope p, wellOffset p⟩

lemma macroAffineOne_value (p : MacroPiece) (x : ℝ) :
    (((macroAffineOne p).base : ℚ) : ℝ) + (((macroAffineOne p).weight : ℚ) : ℝ) *
      ((((macroAffineOne p).slope : ℚ) : ℝ) * x +
        (((macroAffineOne p).offset : ℚ) : ℝ)) ^ 2 = p.model x := by
  cases p with
  | base p =>
      simp only [macroAffineOne, MacroPiece.model, LowerPiece.model, Rat.cast_neg]
      ring
  | well p =>
      cases hs : p.side <;>
        simp [macroAffineOne, MacroPiece.model, WellCert.model, wellSlope, wellOffset, hs] <;> ring


def affineOneImage (m : AffineOneModel) (i : RatInterval) : RatInterval :=
  add (scale m.slope i) ⟨m.offset, m.offset⟩


def macroModelMin (p : MacroPiece) (i : RatInterval) : ℚ :=
  (macroAffineOne p).base + (macroAffineOne p).weight *
    LowerPiece.absLower (affineOneImage (macroAffineOne p) i) ^ 2

lemma macroModelMin_le {p : MacroPiece} {i : RatInterval} {x : ℝ}
    (hweight : 0 ≤ (macroAffineOne p).weight) (hx : Holds i x) :
    ((macroModelMin p i : ℚ) : ℝ) ≤ p.model x := by
  let m := macroAffineOne p
  have himage : Holds (affineOneImage m i)
      (((m.slope : ℚ) : ℝ) * x + ((m.offset : ℚ) : ℝ)) := by
    exact holds_add (holds_scale hx) (holds_point m.offset)
  have habs := LowerPiece.absLower_le_abs himage
  have habs0 : (0 : ℝ) ≤ (LowerPiece.absLower (affineOneImage m i) : ℚ) := by
    exact_mod_cast LowerPiece.absLower_nonneg (affineOneImage m i)
  have hsquare : ((LowerPiece.absLower (affineOneImage m i) : ℚ) : ℝ) ^ 2 ≤
      (((m.slope : ℚ) : ℝ) * x + ((m.offset : ℚ) : ℝ)) ^ 2 := by
    rw [← sq_abs (((m.slope : ℚ) : ℝ) * x + ((m.offset : ℚ) : ℝ))]
    exact pow_le_pow_left₀ habs0 habs 2
  have hw : (0 : ℝ) ≤ ((m.weight : ℚ) : ℝ) := by exact_mod_cast hweight
  rw [← macroAffineOne_value p x]
  simp only [macroModelMin, Rat.cast_add, Rat.cast_mul]
  have hfinal := add_le_add_left (mul_le_mul_of_nonneg_left hsquare hw)
    (((m.base : ℚ) : ℝ))
  simpa [m, add_comm] using hfinal


structure MacroScalarSegment (tableSize : ℕ) where
  box : RatInterval
  pieceIndex : Fin tableSize
  deriving DecidableEq, Repr

namespace MacroScalarSegment

def check {tableSize : ℕ} (table : Fin tableSize → MacroPiece)
    (a : ℚ) (s : MacroScalarSegment tableSize) : Bool :=
  decide (s.box.lo ≤ s.box.hi) &&
  decide ((table s.pieceIndex).box.lo ≤ s.box.lo) &&
  decide (s.box.hi ≤ (table s.pieceIndex).box.hi) &&
  decide (0 ≤ (macroAffineOne (table s.pieceIndex)).weight) &&
  decide (a ≤ macroModelMin (table s.pieceIndex) s.box)

lemma check_sound {tableSize : ℕ} {table : Fin tableSize → MacroPiece}
    {a : ℚ} {s : MacroScalarSegment tableSize} (hc : s.check table a = true)
    {x : ℝ} (hx : Holds s.box x) :
    (a : ℝ) ≤ (table s.pieceIndex).model x := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨_hord, _hlo⟩, _hhi⟩, hweight⟩, ha⟩ := hc
  have haR : (a : ℝ) ≤ (macroModelMin (table s.pieceIndex) s.box : ℚ) := by
    exact_mod_cast ha
  exact haR.trans (macroModelMin_le hweight hx)

end MacroScalarSegment


def scalarSegmentsCoverFrom {tableSize : ℕ} (cur last : ℚ) :
    List (MacroScalarSegment tableSize) → Bool
  | [] => decide (cur = last)
  | s :: ss => decide (s.box.lo = cur) && decide (s.box.lo ≤ s.box.hi) &&
      scalarSegmentsCoverFrom s.box.hi last ss

lemma scalarSegmentsCoverFrom_sound {tableSize : ℕ} {cur last : ℚ}
    {segments : List (MacroScalarSegment tableSize)} {x : ℝ}
    (hne : segments ≠ []) (hc : scalarSegmentsCoverFrom cur last segments = true)
    (hxlo : (cur : ℝ) ≤ x) (_hxhi : x ≤ (last : ℝ)) :
    ∃ s ∈ segments, Holds s.box x := by
  induction segments generalizing cur with
  | nil => exact (hne rfl).elim
  | cons s ss ih =>
      simp only [scalarSegmentsCoverFrom, Bool.and_eq_true, decide_eq_true_eq] at hc
      obtain ⟨⟨hfirst, _hord⟩, hrest⟩ := hc
      subst cur
      by_cases hx : x ≤ (s.box.hi : ℝ)
      · exact ⟨s, by simp, hxlo, hx⟩
      · cases ss with
        | nil =>
            simp only [scalarSegmentsCoverFrom, decide_eq_true_eq] at hrest
            have hlast : ((s.box.hi : ℚ) : ℝ) = (last : ℝ) := by exact_mod_cast hrest
            exact (hx (by rw [hlast]; assumption)).elim
        | cons next rest =>
            obtain ⟨found, hmem, hholds⟩ := ih (by simp) hrest (le_of_not_ge hx)
            exact ⟨found, by simp [hmem], hholds⟩


structure MacroScalarCert (tableSize : ℕ) where
  box : RatInterval
  a : ℚ
  segments : List (MacroScalarSegment tableSize)
  deriving DecidableEq, Repr

namespace MacroScalarCert

def check {tableSize : ℕ} (table : Fin tableSize → MacroPiece)
    (cert : MacroScalarCert tableSize) : Bool :=
  decide (cert.box.lo ≤ cert.box.hi) && decide (0 ≤ cert.a) &&
  decide (cert.segments ≠ []) &&
  scalarSegmentsCoverFrom cert.box.lo cert.box.hi cert.segments &&
  cert.segments.all (MacroScalarSegment.check table cert.a)

lemma check_sound {tableSize : ℕ} {table : Fin tableSize → MacroPiece}
    (htable : ∀ i, (table i).check = true) {cert : MacroScalarCert tableSize}
    (hc : cert.check table = true) {x : ℝ} (hx : Holds cert.box x) :
    (cert.a : ℝ) ≤ 2 * mtKernel x ^ 2 := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hc
  obtain ⟨⟨⟨⟨_hord, _ha⟩, hne⟩, hcover⟩, hall⟩ := hc
  obtain ⟨s, hmem, hs⟩ := scalarSegmentsCoverFrom_sound hne hcover hx.1 hx.2
  have hsc := hall s hmem
  simp only [MacroScalarSegment.check, Bool.and_eq_true, decide_eq_true_eq] at hsc
  obtain ⟨⟨⟨⟨_hsord, hslo⟩, hshi⟩, _hweight⟩, _hmin⟩ := hsc
  have hsloR : (((table s.pieceIndex).box.lo : ℚ) : ℝ) ≤ (s.box.lo : ℝ) := by
    exact_mod_cast hslo
  have hshiR : (s.box.hi : ℝ) ≤ (((table s.pieceIndex).box.hi : ℚ) : ℝ) := by
    exact_mod_cast hshi
  have hpiece : Holds (table s.pieceIndex).box x :=
    ⟨hsloR.trans hs.1, hs.2.trans hshiR⟩
  exact (MacroScalarSegment.check_sound (hall s hmem) hs).trans
    (MacroPiece.check_sound (htable s.pieceIndex) hpiece)

end MacroScalarCert

/-- One term is a table model, a globally checked scalar certificate, or zero. -/
inductive MacroTermRef (tableSize scalarCount : ℕ) where
  | piece (index : Fin tableSize)
  | scalar (index : Fin scalarCount)
  | zero
  deriving DecidableEq, Repr

structure MacroScalarLeaf (tableSize scalarCount : ℕ) where
  anchor : RelativeAnchor
  term : Fin 15 → MacroTermRef tableSize scalarCount
  deriving DecidableEq, Repr


def scalarRankModel (a : ℚ) : RankOneModel where
  base := a
  weight := 0
  offset := 0
  coeff := fun _ => 0


def macroScalarTerm {tableSize scalarCount : ℕ}
    (table : Fin tableSize → MacroPiece)
    (scalars : Fin scalarCount → MacroScalarCert tableSize)
    (leaf : MacroScalarLeaf tableSize scalarCount) (p : Fin 15) : RankOneModel :=
  match leaf.term p with
  | .piece i => macroPieceRankModel (fun _ => table i) p
  | .scalar i => scalarRankModel (scalars i).a
  | .zero => zeroRankModel


def macroScalarTermsFit {tableSize scalarCount : ℕ} (cutoff : ℚ)
    (table : Fin tableSize → MacroPiece)
    (scalars : Fin scalarCount → MacroScalarCert tableSize)
    (box : GapBox) (leaf : MacroScalarLeaf tableSize scalarCount) : Bool := by
  classical
  exact decide (∀ p,
    match leaf.term p with
    | .piece i => (table i).box.lo ≤ (clippedDistanceInterval cutoff box p).lo ∧
        (clippedDistanceInterval cutoff box p).hi ≤ (table i).box.hi
    | .scalar i => (scalars i).box.lo ≤ (clippedDistanceInterval cutoff box p).lo ∧
        (clippedDistanceInterval cutoff box p).hi ≤ (scalars i).box.hi
    | .zero => True)


def macroScalarDyadic14LeafCheck {tableSize scalarCount : ℕ}
    (table : Fin tableSize → MacroPiece)
    (scalars : Fin scalarCount → MacroScalarCert tableSize)
    (box : GapBox) (leaf : MacroScalarLeaf tableSize scalarCount) : Bool :=
  decide (∀ i, 0 ≤ box.lo i) &&
  macroScalarTermsFit macroCutoff table scalars box leaf &&
  relativeRankTangentCheck 16384 (1 / 80) (1094977 / 5000000000)
    box leaf.anchor (macroScalarTerm table scalars leaf)

/- The concrete soundness proof mirrors `macroOptionalDyadic14LeafCheck_sound`.
It is kept separate so the audited 56-piece envelope remains immutable. -/
theorem macroScalarDyadic14LeafCheck_sound {tableSize scalarCount : ℕ}
    {table : Fin tableSize → MacroPiece}
    {scalars : Fin scalarCount → MacroScalarCert tableSize}
    (htable : ∀ i, (table i).check = true)
    (hscalars : ∀ i, (scalars i).check table = true) :
    ∀ box leaf, macroScalarDyadic14LeafCheck table scalars box leaf = true →
      BoxPredicate (affineEnergyGoal (1 / 80) (1094977 / 5000000000)) box := by
  intro box leaf hc g hg
  simp only [macroScalarDyadic14LeafCheck, macroScalarTermsFit,
    Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨hbox0, hfit⟩, htangent⟩ := hc
  have hg0 : ∀ i, 0 ≤ g i := fun i => by
    have hlo : (0 : ℝ) ≤ ((box.lo i : ℚ) : ℝ) := by exact_mod_cast hbox0 i
    exact hlo.trans (hg i).1
  by_cases htail : A6 ≤ B6 * sextupleSpan g
  · have henergy := sextupleEnergy_nonneg g
    simp only [affineEnergyGoal]
    norm_num [A6, B6] at *
    linarith
  · have hspan : sextupleSpan g < ((macroCutoff : ℚ) : ℝ) := by
      norm_num [A6, B6, macroCutoff] at htail ⊢
      nlinarith
    have hpair : ∀ p, (macroScalarTerm table scalars leaf p).value g ≤
        2 * mtKernel (gapDistance g p) ^ 2 := by
      intro p
      have hd := distanceInterval_holds hg p
      have hdistSpan : gapDistance g p ≤ sextupleSpan g := by
        simp only [gapDistance, sextupleSpan]
        exact Finset.sum_le_sum_of_subset_of_nonneg (by simp [gapSupport])
          (fun j _ _ => hg0 j)
      have hcut : gapDistance g p ≤ ((macroCutoff : ℚ) : ℝ) :=
        hdistSpan.trans hspan.le
      have hclipped : Holds (clippedDistanceInterval macroCutoff box p)
          (gapDistance g p) := by
        constructor
        · exact hd.1
        · simp only [clippedDistanceInterval, Rat.cast_min]
          exact le_min hd.2 hcut
      cases href : leaf.term p with
      | zero =>
          simp [macroScalarTerm, href, zeroRankModel, RankOneModel.value,
            RankOneModel.dot]
          positivity
      | piece i =>
          have hi := hfit p
          simp [href] at hi
          have hloR : (((table i).box.lo : ℚ) : ℝ) ≤
              (((clippedDistanceInterval macroCutoff box p).lo : ℚ) : ℝ) := by
            exact_mod_cast hi.1
          have hhiR : (((clippedDistanceInterval macroCutoff box p).hi : ℚ) : ℝ) ≤
              (((table i).box.hi : ℚ) : ℝ) := by exact_mod_cast hi.2
          have hholds : Holds (table i).box (gapDistance g p) :=
            ⟨hloR.trans hclipped.1, hclipped.2.trans hhiR⟩
          simp [macroScalarTerm, href, macroPieceRankModel_value]
          exact MacroPiece.check_sound (htable i) hholds
      | scalar i =>
          have hi := hfit p
          simp [href] at hi
          have hloR : (((scalars i).box.lo : ℚ) : ℝ) ≤
              (((clippedDistanceInterval macroCutoff box p).lo : ℚ) : ℝ) := by
            exact_mod_cast hi.1
          have hhiR : (((clippedDistanceInterval macroCutoff box p).hi : ℚ) : ℝ) ≤
              (((scalars i).box.hi : ℚ) : ℝ) := by exact_mod_cast hi.2
          have hsbox : Holds (scalars i).box (gapDistance g p) :=
            ⟨hloR.trans hclipped.1, hclipped.2.trans hhiR⟩
          have hsound := MacroScalarCert.check_sound htable (hscalars i) hsbox
          simpa [macroScalarTerm, href, scalarRankModel, RankOneModel.value,
            RankOneModel.dot] using hsound
    have ht := relativeRankTangentCheck_sound htangent hg
    have he := rankObjective_le_energy_of_pairwise
      (B := (1094977 / 5000000000 : ℚ)) hpair
    simpa [affineEnergyGoal, A6, B6] using ht.trans he

end Zeta23.ThmD.Sextuple.MacroPrototype
