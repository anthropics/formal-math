import Zeta23.ThmD.Sextuple.A1285.TreeAssembly

/-!
# The concrete five-dimensional affine certificate at `A = 257 / 20000`

`improvedRootReplay` plus the exact stream lengths and the audited generic soundness layer give
`A1285.Certificate.sextuple_affine : 257 / 20000 ≤ sextupleEnergy g + B6 * sextupleSpan g`.
-/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

noncomputable section

namespace Zeta23.ThmD.Sextuple.MacroPrototype.A1285

open Zeta23.ThmD.Sextuple

theorem improvedTreeCheck :
    checkAffineTree improvedConcreteLeafCheck improvedTopologyStream
      improvedPayloadStream 74 improvedRootBox = true := by
  unfold checkAffineTree
  rw [improvedRootReplay]
  rfl

theorem improvedRootBox_predicate :
    BoxPredicate (affineEnergyGoal improvedA improvedB) improvedRootBox :=
  checkAffineTree_sound improvedConcreteLeafCheck_sound improvedTreeCheck

end Zeta23.ThmD.Sextuple.MacroPrototype.A1285

namespace Zeta23.ThmD.Sextuple.A1285.Certificate

open Zeta23.ThmD.Sextuple
open Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple.MacroPrototype.A1285

/-- **The concrete sextuple affine certificate at `A = 257 / 20000`, `B = B₆`.** -/
theorem sextuple_affine (g : Fin 5 → ℝ) (hg : ∀ i, 0 ≤ g i) :
    (257 / 20000 : ℝ) ≤ sextupleEnergy g + B6 * sextupleSpan g := by
  have hroot := improvedRootBox_predicate
  have hglobal := affineTree_global_at
    (A := (257 / 20000 : ℚ)) (B := (1094977 / 5000000000 : ℚ))
    (limit := (59 : ℚ)) (by norm_num) (by norm_num) hroot g hg
  simpa [affineEnergyGoal, B6] using hglobal

end Zeta23.ThmD.Sextuple.A1285.Certificate

end
