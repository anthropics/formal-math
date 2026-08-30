import Zeta23.ThmD.Sextuple.Macro.Analytic
import Zeta23.ThmD.Sextuple.AffineTree

noncomputable section

namespace Zeta23.ThmD.Sextuple.MacroPrototype

open Zeta23.ThmD.Sextuple
open RatInterval
open scoped BigOperators

def zeroLowerPiece : LowerPiece where
  box := ⟨0, 59⟩
  q := 0
  a := 0
  c := 0
  kind := .zero

lemma scaledConsecutive_dot (s : ℚ) (p : Fin 15) (g : Fin 5 → ℝ) :
    (∑ i, (((s * consecutiveCoeff p i : ℚ) : ℝ)) * g i) =
      ((s : ℚ) : ℝ) * gapDistance g p := by
  have hdot := lowerPieceRankModel_dot (fun _ => zeroLowerPiece) p g
  simp only [RankOneModel.dot, lowerPieceRankModel] at hdot
  rw [← hdot, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Rat.cast_mul]
  ring

def wellSlope (p : WellCert) : ℚ :=
  match p.side with
  | .left => -p.m
  | .right => p.m


def wellOffset (p : WellCert) : ℚ :=
  match p.side with
  | .left => p.v + p.m * p.q
  | .right => p.v - p.m * p.q


def wellRankModel (piece : WellCert) (p : Fin 15) : RankOneModel where
  base := 0
  weight := 2
  offset := wellOffset piece
  coeff := fun i => wellSlope piece * consecutiveCoeff p i


def macroPieceRankModel (pieces : Fin 15 → MacroPiece) (p : Fin 15) : RankOneModel :=
  match pieces p with
  | .base piece => lowerPieceRankModel (fun _ => piece) p
  | .well piece => wellRankModel piece p

lemma wellRankModel_dot (piece : WellCert) (p : Fin 15) (g : Fin 5 → ℝ) :
    (wellRankModel piece p).dot g =
      ((wellSlope piece : ℚ) : ℝ) * gapDistance g p := by
  simpa [RankOneModel.dot, wellRankModel] using scaledConsecutive_dot (wellSlope piece) p g

@[simp] theorem macroPieceRankModel_value (pieces : Fin 15 → MacroPiece)
    (p : Fin 15) (g : Fin 5 → ℝ) :
    (macroPieceRankModel pieces p).value g = (pieces p).model (gapDistance g p) := by
  cases hp : pieces p with
  | base piece =>
      simp [macroPieceRankModel, hp, MacroPiece.model]
  | well piece =>
      rw [macroPieceRankModel, hp, RankOneModel.value, wellRankModel_dot]
      cases hs : piece.side <;>
        simp [MacroPiece.model, WellCert.model, wellRankModel, wellSlope, wellOffset, hs] <;> ring

/-- Every selected macro piece contains its consecutive-distance interval. -/
def macroPiecesFit (box : GapBox) (pieces : Fin 15 → MacroPiece) : Bool :=
  decide (∀ p, (pieces p).box.lo ≤ (distanceInterval box p).lo ∧
    (distanceInterval box p).hi ≤ (pieces p).box.hi)

lemma distanceInterval_holds_selectedMacro {box : GapBox} {g : Fin 5 → ℝ}
    (hg : box.Holds g) {pieces : Fin 15 → MacroPiece}
    (hfit : ∀ p, (pieces p).box.lo ≤ (distanceInterval box p).lo ∧
      (distanceInterval box p).hi ≤ (pieces p).box.hi) (p : Fin 15) :
    Holds (pieces p).box (gapDistance g p) := by
  have hd := distanceInterval_holds hg p
  constructor
  · have hlo : (((pieces p).box.lo : ℚ) : ℝ) ≤
        (((distanceInterval box p).lo : ℚ) : ℝ) := by exact_mod_cast (hfit p).1
    exact hlo.trans hd.1
  · have hhi : (((distanceInterval box p).hi : ℚ) : ℝ) ≤
        (((pieces p).box.hi : ℚ) : ℝ) := by exact_mod_cast (hfit p).2
    exact hd.2.trans hhi

/-- Exact pairwise lift from checked signed macro models to sextuple kernel energy. -/
theorem macroPieceRankObjective_le_energy {B : ℚ} {box : GapBox}
    {pieces : Fin 15 → MacroPiece} (hcert : ∀ p, (pieces p).check = true)
    (hfit : ∀ p, (pieces p).box.lo ≤ (distanceInterval box p).lo ∧
      (distanceInterval box p).hi ≤ (pieces p).box.hi)
    {g : Fin 5 → ℝ} (hg : box.Holds g) :
    rankObjective (macroPieceRankModel pieces) B g ≤
      sextupleEnergy g + ((B : ℚ) : ℝ) * sextupleSpan g := by
  apply rankObjective_le_energy_of_pairwise
  intro p
  rw [macroPieceRankModel_value]
  exact MacroPiece.check_sound (hcert p)
    (distanceInterval_holds_selectedMacro hg hfit p)

/-- Compact relative-anchor tangent check over selected macro pieces. -/
def macroRelativeTangentCheck (resolution : ℕ) (A B : ℚ)
    (box : GapBox) (anchor : RelativeAnchor) (pieces : Fin 15 → MacroPiece) : Bool :=
  macroPiecesFit box pieces &&
    relativeRankTangentCheck resolution A B box anchor (macroPieceRankModel pieces)

/-- The checker consumes exact fit and dyadic-anchor obligations; global table checks are explicit. -/
theorem macroRelativeTangentCheck_sound {resolution : ℕ} {A B : ℚ}
    {box : GapBox} {anchor : RelativeAnchor} {pieces : Fin 15 → MacroPiece}
    (hcert : ∀ p, (pieces p).check = true)
    (hc : macroRelativeTangentCheck resolution A B box anchor pieces = true) :
    BoxPredicate (affineEnergyGoal A B) box := by
  simp only [macroRelativeTangentCheck, macroPiecesFit, Bool.and_eq_true,
    decide_eq_true_eq] at hc
  intro g hg
  exact (relativeRankTangentCheck_sound hc.2 hg).trans
    (macroPieceRankObjective_le_energy hcert hc.1 hg)

/-- Compact terminal payload: one dyadic anchor plus fifteen checked table indices. -/
structure MacroIndexedLeaf (tableSize : ℕ) where
  anchor : RelativeAnchor
  pieceIndex : Fin 15 → Fin tableSize
  deriving DecidableEq, Repr


def selectedMacroPieces {tableSize : ℕ} (table : Fin tableSize → MacroPiece)
    (leaf : MacroIndexedLeaf tableSize) : Fin 15 → MacroPiece :=
  fun p => table (leaf.pieceIndex p)


def macroIndexedLeafCheck {tableSize : ℕ} (resolution : ℕ) (A B : ℚ)
    (table : Fin tableSize → MacroPiece) (box : GapBox)
    (leaf : MacroIndexedLeaf tableSize) : Bool :=
  macroRelativeTangentCheck resolution A B box leaf.anchor
    (selectedMacroPieces table leaf)


theorem macroIndexedLeafCheck_sound {tableSize resolution : ℕ} {A B : ℚ}
    {table : Fin tableSize → MacroPiece}
    (htable : ∀ i, (table i).check = true) :
    ∀ box leaf, macroIndexedLeafCheck resolution A B table box leaf = true →
      BoxPredicate (affineEnergyGoal A B) box := by
  intro box leaf hc
  apply macroRelativeTangentCheck_sound (hc := hc)
  intro p
  exact htable (leaf.pieceIndex p)

/-- Intended concrete quadratic leaf: exact relative denominator `16384 = 2^14`. -/
def macroDyadic14LeafCheck {tableSize : ℕ} (A B : ℚ)
    (table : Fin tableSize → MacroPiece) (box : GapBox)
    (leaf : MacroIndexedLeaf tableSize) : Bool :=
  macroIndexedLeafCheck 16384 A B table box leaf


theorem macroDyadic14LeafCheck_sound {tableSize : ℕ} {A B : ℚ}
    {table : Fin tableSize → MacroPiece}
    (htable : ∀ i, (table i).check = true) :
    ∀ box leaf, macroDyadic14LeafCheck A B table box leaf = true →
      BoxPredicate (affineEnergyGoal A B) box := by
  exact macroIndexedLeafCheck_sound htable


/-- Exact threshold where the affine span term alone reaches `1/80`. -/
def macroCutoff : ℚ := 62500000 / 1094977

/-- Global zero fallback for a distance interval that crosses a macro-piece seam. -/
def zeroRankModel : RankOneModel where
  base := 0
  weight := 0
  offset := 0
  coeff := fun _ => 0

/-- A quadratic payload stores either one table index or the globally sound zero fallback. -/
structure MacroOptionalLeaf (tableSize : ℕ) where
  anchor : RelativeAnchor
  pieceIndex : Fin 15 → Option (Fin tableSize)
  deriving DecidableEq, Repr


def optionalMacroTerm {tableSize : ℕ} (table : Fin tableSize → MacroPiece)
    (leaf : MacroOptionalLeaf tableSize) (p : Fin 15) : RankOneModel :=
  match leaf.pieceIndex p with
  | none => zeroRankModel
  | some i => macroPieceRankModel (fun _ => table i) p


def clippedDistanceInterval (cutoff : ℚ) (box : GapBox) (p : Fin 15) : RatInterval where
  lo := (distanceInterval box p).lo
  hi := min (distanceInterval box p).hi cutoff

/-- Stored table indices must cover their clipped distance intervals; `none` needs no fit proof. -/
def optionalMacroPiecesFit {tableSize : ℕ} (cutoff : ℚ)
    (table : Fin tableSize → MacroPiece) (box : GapBox)
    (leaf : MacroOptionalLeaf tableSize) : Bool :=
  decide (∀ p i, leaf.pieceIndex p = some i →
    (table i).box.lo ≤ (clippedDistanceInterval cutoff box p).lo ∧
    (clippedDistanceInterval cutoff box p).hi ≤ (table i).box.hi)

/-- Concrete compact quadratic checker used by the serialized tree. -/
def macroOptionalDyadic14LeafCheck {tableSize : ℕ}
    (table : Fin tableSize → MacroPiece) (box : GapBox)
    (leaf : MacroOptionalLeaf tableSize) : Bool :=
  decide (∀ i, 0 ≤ box.lo i) &&
  optionalMacroPiecesFit macroCutoff table box leaf &&
  relativeRankTangentCheck 16384 (1 / 80) (1094977 / 5000000000)
    box leaf.anchor (optionalMacroTerm table leaf)

lemma optionalTerm_value_none {tableSize : ℕ} {table : Fin tableSize → MacroPiece}
    {leaf : MacroOptionalLeaf tableSize} {p : Fin 15} {g : Fin 5 → ℝ}
    (hindex : leaf.pieceIndex p = none) :
    (optionalMacroTerm table leaf p).value g = 0 := by
  simp [optionalMacroTerm, hindex, zeroRankModel, RankOneModel.value, RankOneModel.dot]

lemma optionalTerm_value_some {tableSize : ℕ} {table : Fin tableSize → MacroPiece}
    {leaf : MacroOptionalLeaf tableSize} {p : Fin 15} {i : Fin tableSize}
    {g : Fin 5 → ℝ} (hindex : leaf.pieceIndex p = some i) :
    (optionalMacroTerm table leaf p).value g = (table i).model (gapDistance g p) := by
  simp [optionalMacroTerm, hindex, macroPieceRankModel_value]

lemma clippedDistance_holds_selected {tableSize : ℕ} {table : Fin tableSize → MacroPiece}
    {leaf : MacroOptionalLeaf tableSize} {box : GapBox} {g : Fin 5 → ℝ}
    (hg : box.Holds g) (hg0 : ∀ i, 0 ≤ g i)
    (hspan : sextupleSpan g < (macroCutoff : ℚ))
    {p : Fin 15} {i : Fin tableSize} (hindex : leaf.pieceIndex p = some i)
    (hfit : ∀ p i, leaf.pieceIndex p = some i →
      (table i).box.lo ≤ (clippedDistanceInterval macroCutoff box p).lo ∧
      (clippedDistanceInterval macroCutoff box p).hi ≤ (table i).box.hi) :
    Holds (table i).box (gapDistance g p) := by
  have hd := distanceInterval_holds hg p
  have hdistSpan : gapDistance g p ≤ sextupleSpan g := by
    simp only [gapDistance, sextupleSpan]
    exact Finset.sum_le_sum_of_subset_of_nonneg (by simp [gapSupport])
      (fun j _ _ => hg0 j)
  constructor
  · have hlo : (((table i).box.lo : ℚ) : ℝ) ≤
        (((clippedDistanceInterval macroCutoff box p).lo : ℚ) : ℝ) := by
      exact_mod_cast (hfit p i hindex).1
    exact hlo.trans hd.1
  · have hcut : gapDistance g p ≤ ((macroCutoff : ℚ) : ℝ) :=
      hdistSpan.trans hspan.le
    have hmin : gapDistance g p ≤
        (((clippedDistanceInterval macroCutoff box p).hi : ℚ) : ℝ) := by
      simp only [clippedDistanceInterval, Rat.cast_min]
      exact le_min hd.2 hcut
    have hhi : (((clippedDistanceInterval macroCutoff box p).hi : ℚ) : ℝ) ≤
        (((table i).box.hi : ℚ) : ℝ) := by exact_mod_cast (hfit p i hindex).2
    exact hmin.trans hhi

/-- Soundness of the concrete optional-index leaf, including its affine-gap case. -/
theorem macroOptionalDyadic14LeafCheck_sound {tableSize : ℕ}
    {table : Fin tableSize → MacroPiece} (htable : ∀ i, (table i).check = true) :
    ∀ box leaf, macroOptionalDyadic14LeafCheck table box leaf = true →
      BoxPredicate (affineEnergyGoal (1 / 80) (1094977 / 5000000000)) box := by
  intro box leaf hc g hg
  simp only [macroOptionalDyadic14LeafCheck, optionalMacroPiecesFit,
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
    have hpair : ∀ p, (optionalMacroTerm table leaf p).value g ≤
        2 * mtKernel (gapDistance g p) ^ 2 := by
      intro p
      cases hindex : leaf.pieceIndex p with
      | none =>
          rw [optionalTerm_value_none hindex]
          positivity
      | some i =>
          rw [optionalTerm_value_some hindex]
          exact MacroPiece.check_sound (htable i)
            (clippedDistance_holds_selected hg hg0 hspan hindex hfit)
    have ht := relativeRankTangentCheck_sound htangent hg
    have he := rankObjective_le_energy_of_pairwise (B := (1094977 / 5000000000 : ℚ)) hpair
    simpa [affineEnergyGoal, A6, B6] using ht.trans he


end Zeta23.ThmD.Sextuple.MacroPrototype
