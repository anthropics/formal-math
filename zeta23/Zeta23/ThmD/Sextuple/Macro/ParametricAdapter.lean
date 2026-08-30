import Zeta23.ThmD.Sextuple.Macro.LeafCheck

noncomputable section

namespace Zeta23.ThmD.Sextuple.MacroPrototype

open Zeta23.ThmD.Sextuple
open RatInterval

/-- Parameterized scalar leaf check. The cutoff is separately visible and tied to `A/B`
in the soundness theorem. -/
def macroScalarLeafCheckAt {tableSize scalarCount : ℕ}
    (resolution : ℕ) (cutoff A B : ℚ)
    (table : Fin tableSize → MacroPiece)
    (scalars : Fin scalarCount → MacroScalarCert tableSize)
    (box : GapBox) (leaf : MacroScalarLeaf tableSize scalarCount) : Bool :=
  decide (∀ i, 0 ≤ box.lo i) &&
  leafTermsFit cutoff table scalars box leaf &&
  relativeRankTangentCheck resolution A B box leaf.anchor
    (macroScalarTerm table scalars leaf)


theorem macroScalarLeafCheckAt_sound {tableSize scalarCount : ℕ}
    {resolution : ℕ} {cutoff A B : ℚ}
    {table : Fin tableSize → MacroPiece}
    {scalars : Fin scalarCount → MacroScalarCert tableSize}
    (hB : 0 < B) (hcutoff : cutoff = A / B)
    (htable : ∀ i, (table i).check = true)
    (hscalars : ∀ i, (scalars i).check table = true) :
    ∀ box leaf, macroScalarLeafCheckAt resolution cutoff A B table scalars box leaf = true →
      BoxPredicate (affineEnergyGoal A B) box := by
  intro box leaf hc g hg
  simp only [macroScalarLeafCheckAt, leafTermsFit, Bool.and_eq_true,
    decide_eq_true_eq] at hc
  obtain ⟨⟨hbox0, hfit⟩, htangent⟩ := hc
  have hg0 : ∀ i, 0 ≤ g i := fun i => by
    have hlo : (0 : ℝ) ≤ ((box.lo i : ℚ) : ℝ) := by exact_mod_cast hbox0 i
    exact hlo.trans (hg i).1
  by_cases htail : ((A : ℚ) : ℝ) ≤ ((B : ℚ) : ℝ) * sextupleSpan g
  · have henergy := sextupleEnergy_nonneg g
    simp only [affineEnergyGoal]
    linarith
  · have hBR : (0 : ℝ) < ((B : ℚ) : ℝ) := by exact_mod_cast hB
    have hcutR : ((cutoff : ℚ) : ℝ) = ((A : ℚ) : ℝ) / ((B : ℚ) : ℝ) := by
      rw [hcutoff]
      push_cast
      rfl
    have hspan : sextupleSpan g < ((cutoff : ℚ) : ℝ) := by
      rw [hcutR, lt_div_iff₀ hBR]
      have hlt := lt_of_not_ge htail
      nlinarith
    have hpair : ∀ p, (macroScalarTerm table scalars leaf p).value g ≤
        2 * mtKernel (gapDistance g p) ^ 2 := by
      intro p
      have hd := distanceInterval_holds hg p
      have hdistSpan : gapDistance g p ≤ sextupleSpan g := by
        simp only [gapDistance, sextupleSpan]
        exact Finset.sum_le_sum_of_subset_of_nonneg (by simp [gapSupport])
          (fun j _ _ => hg0 j)
      have hcut : gapDistance g p ≤ ((cutoff : ℚ) : ℝ) :=
        hdistSpan.trans hspan.le
      have hclipped : Holds (clippedDistanceInterval cutoff box p)
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
          have hi' := hfit p
          rw [href] at hi'
          simp only [termRefFits, Bool.and_eq_true, decide_eq_true_eq] at hi' 
          have hloR : (((table i).box.lo : ℚ) : ℝ) ≤
              (((clippedDistanceInterval cutoff box p).lo : ℚ) : ℝ) := by exact_mod_cast hi'.1
          have hhiR : (((clippedDistanceInterval cutoff box p).hi : ℚ) : ℝ) ≤
              (((table i).box.hi : ℚ) : ℝ) := by exact_mod_cast hi'.2
          have hholds : Holds (table i).box (gapDistance g p) :=
            ⟨hloR.trans hclipped.1, hclipped.2.trans hhiR⟩
          simp [macroScalarTerm, href, macroPieceRankModel_value]
          exact MacroPiece.check_sound (htable i) hholds
      | scalar i =>
          have hi' := hfit p
          rw [href] at hi'
          simp only [termRefFits, Bool.and_eq_true, decide_eq_true_eq] at hi' 
          have hloR : (((scalars i).box.lo : ℚ) : ℝ) ≤
              (((clippedDistanceInterval cutoff box p).lo : ℚ) : ℝ) := by exact_mod_cast hi'.1
          have hhiR : (((clippedDistanceInterval cutoff box p).hi : ℚ) : ℝ) ≤
              (((scalars i).box.hi : ℚ) : ℝ) := by exact_mod_cast hi'.2
          have hsbox : Holds (scalars i).box (gapDistance g p) :=
            ⟨hloR.trans hclipped.1, hclipped.2.trans hhiR⟩
          have hsound := MacroScalarCert.check_sound htable (hscalars i) hsbox
          simpa [macroScalarTerm, href, scalarRankModel, RankOneModel.value,
            RankOneModel.dot] using hsound
    have ht := relativeRankTangentCheck_sound htangent hg
    have he := rankObjective_le_energy_of_pairwise (B := B) hpair
    exact ht.trans he

/-- Explicit, kernel-reducible parameterized leaf check. -/
def fastLeafCheckAt {tableSize scalarCount : ℕ}
    (resolution : ℕ) (cutoff A B : ℚ)
    (table : Fin tableSize → MacroPiece)
    (scalars : Fin scalarCount → MacroScalarCert tableSize)
    (box : GapBox) (leaf : MacroScalarLeaf tableSize scalarCount) : Bool :=
  decide (∀ i, 0 ≤ box.lo i) &&
  leafTermsFit cutoff table scalars box leaf &&
  relativeRankTangentCheck resolution A B box leaf.anchor
    (macroScalarTerm table scalars leaf)


theorem macroScalarLeafCheckAt_of_fastLeafCheckAt {tableSize scalarCount : ℕ}
    {resolution : ℕ} {cutoff A B : ℚ}
    {table : Fin tableSize → MacroPiece}
    {scalars : Fin scalarCount → MacroScalarCert tableSize}
    {box : GapBox} {leaf : MacroScalarLeaf tableSize scalarCount}
    (hc : fastLeafCheckAt resolution cutoff A B table scalars box leaf = true) :
    macroScalarLeafCheckAt resolution cutoff A B table scalars box leaf = true := by
  simpa [fastLeafCheckAt, macroScalarLeafCheckAt] using hc


theorem fastLeafCheckAt_sound {tableSize scalarCount : ℕ}
    {resolution : ℕ} {cutoff A B : ℚ}
    {table : Fin tableSize → MacroPiece}
    {scalars : Fin scalarCount → MacroScalarCert tableSize}
    (hB : 0 < B) (hcutoff : cutoff = A / B)
    (htable : ∀ i, (table i).check = true)
    (hscalars : ∀ i, (scalars i).check table = true) :
    ∀ box leaf, fastLeafCheckAt resolution cutoff A B table scalars box leaf = true →
      BoxPredicate (affineEnergyGoal A B) box := by
  intro box leaf hc
  exact macroScalarLeafCheckAt_sound hB hcutoff htable hscalars box leaf
    (macroScalarLeafCheckAt_of_fastLeafCheckAt hc)

/-- A parameterized root box and affine tail cover every nonnegative gap vector. -/
theorem affineTree_global_at {A B limit : ℚ}
    (hB : 0 ≤ B) (htail : A ≤ B * limit)
    (hroot : BoxPredicate (affineEnergyGoal A B) (initialGapBox limit))
    (g : Fin 5 → ℝ) (hg : ∀ i, 0 ≤ g i) :
    affineEnergyGoal A B g := by
  by_cases hspan : ((limit : ℚ) : ℝ) ≤ sextupleSpan g
  · have henergy := sextupleEnergy_nonneg g
    have hBR : (0 : ℝ) ≤ ((B : ℚ) : ℝ) := by exact_mod_cast hB
    have hmul : (((B * limit : ℚ) : ℚ) : ℝ) ≤
        ((B : ℚ) : ℝ) * sextupleSpan g := by
      push_cast
      exact mul_le_mul_of_nonneg_left hspan hBR
    have hAR : ((A : ℚ) : ℝ) ≤ (((B * limit : ℚ) : ℚ) : ℝ) := by
      exact_mod_cast htail
    simp only [affineEnergyGoal]
    linarith
  · exact hroot (initialGapBox_holds hg (le_of_not_ge hspan))


#print axioms fastLeafCheckAt_sound
#print axioms affineTree_global_at

end Zeta23.ThmD.Sextuple.MacroPrototype
