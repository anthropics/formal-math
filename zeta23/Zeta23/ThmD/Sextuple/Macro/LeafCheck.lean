import Zeta23.ThmD.Sextuple.Macro.ScalarAdapter

/-!
# Kernel-reducible quadratic leaf check

`macroScalarTermsFit` in the prototype adapter is defined through `classical`, so
its `Decidable` instance cannot be evaluated by the kernel.  This module supplies an
explicit Boolean fit check and proves that it implies the prototype check, so the
existing soundness theorem `macroScalarDyadic14LeafCheck_sound` is reused verbatim.
-/

noncomputable section

namespace Zeta23.ThmD.Sextuple.MacroPrototype

open Zeta23.ThmD.Sextuple
open RatInterval

/-- Explicit Boolean fit of one selected term on one clipped distance interval. -/
def termRefFits {tableSize scalarCount : ℕ} (cutoff : ℚ)
    (table : Fin tableSize → MacroPiece)
    (scalars : Fin scalarCount → MacroScalarCert tableSize)
    (box : GapBox) (p : Fin 15) : MacroTermRef tableSize scalarCount → Bool
  | .piece i =>
      decide ((table i).box.lo ≤ (clippedDistanceInterval cutoff box p).lo) &&
        decide ((clippedDistanceInterval cutoff box p).hi ≤ (table i).box.hi)
  | .scalar i =>
      decide ((scalars i).box.lo ≤ (clippedDistanceInterval cutoff box p).lo) &&
        decide ((clippedDistanceInterval cutoff box p).hi ≤ (scalars i).box.hi)
  | .zero => true

/-- All fifteen selected terms fit. -/
def leafTermsFit {tableSize scalarCount : ℕ} (cutoff : ℚ)
    (table : Fin tableSize → MacroPiece)
    (scalars : Fin scalarCount → MacroScalarCert tableSize)
    (box : GapBox) (leaf : MacroScalarLeaf tableSize scalarCount) : Bool :=
  decide (∀ p, termRefFits cutoff table scalars box p (leaf.term p) = true)

/-- Kernel-reducible concrete quadratic leaf check. -/
def fastLeafCheck {tableSize scalarCount : ℕ}
    (table : Fin tableSize → MacroPiece)
    (scalars : Fin scalarCount → MacroScalarCert tableSize)
    (box : GapBox) (leaf : MacroScalarLeaf tableSize scalarCount) : Bool :=
  decide (∀ i, 0 ≤ box.lo i) &&
  leafTermsFit macroCutoff table scalars box leaf &&
  relativeRankTangentCheck 16384 (1 / 80) (1094977 / 5000000000)
    box leaf.anchor (macroScalarTerm table scalars leaf)

/-- `decide` is `true` for any instance, including one chosen classically. -/
theorem decideEqTrueOf {p : Prop} {inst : Decidable p} (h : p) : @decide p inst = true := by
  cases inst with
  | isTrue _ => rfl
  | isFalse hn => exact absurd h hn

/-- The explicit fit check implies the prototype (classical) fit check. -/
lemma macroScalarTermsFit_of_leafTermsFit {tableSize scalarCount : ℕ} {cutoff : ℚ}
    {table : Fin tableSize → MacroPiece}
    {scalars : Fin scalarCount → MacroScalarCert tableSize}
    {box : GapBox} {leaf : MacroScalarLeaf tableSize scalarCount}
    (h : leafTermsFit cutoff table scalars box leaf = true) :
    macroScalarTermsFit cutoff table scalars box leaf = true := by
  simp only [leafTermsFit, decide_eq_true_eq] at h
  unfold macroScalarTermsFit
  refine decideEqTrueOf ?_
  intro p
  have hp := h p
  split
  · rename_i i heq
    rw [heq] at hp
    simp only [termRefFits, Bool.and_eq_true, decide_eq_true_eq] at hp
    exact hp
  · rename_i i heq
    rw [heq] at hp
    simp only [termRefFits, Bool.and_eq_true, decide_eq_true_eq] at hp
    exact hp
  · trivial

/-- The fast check implies the prototype check. -/
theorem macroScalarDyadic14LeafCheck_of_fastLeafCheck {tableSize scalarCount : ℕ}
    {table : Fin tableSize → MacroPiece}
    {scalars : Fin scalarCount → MacroScalarCert tableSize}
    {box : GapBox} {leaf : MacroScalarLeaf tableSize scalarCount}
    (hc : fastLeafCheck table scalars box leaf = true) :
    macroScalarDyadic14LeafCheck table scalars box leaf = true := by
  simp only [fastLeafCheck, Bool.and_eq_true] at hc
  obtain ⟨⟨h0, hfit⟩, ht⟩ := hc
  simp only [macroScalarDyadic14LeafCheck, Bool.and_eq_true]
  exact ⟨⟨h0, macroScalarTermsFit_of_leafTermsFit hfit⟩, ht⟩

/-- Soundness of the kernel-reducible leaf check. -/
theorem fastLeafCheck_sound {tableSize scalarCount : ℕ}
    {table : Fin tableSize → MacroPiece}
    {scalars : Fin scalarCount → MacroScalarCert tableSize}
    (htable : ∀ i, (table i).check = true)
    (hscalars : ∀ i, (scalars i).check table = true) :
    ∀ box leaf, fastLeafCheck table scalars box leaf = true →
      BoxPredicate (affineEnergyGoal (1 / 80) (1094977 / 5000000000)) box :=
  fun box leaf hc =>
    macroScalarDyadic14LeafCheck_sound htable hscalars box leaf
      (macroScalarDyadic14LeafCheck_of_fastLeafCheck hc)

end Zeta23.ThmD.Sextuple.MacroPrototype
