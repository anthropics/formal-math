import Zeta23.ThmD.Sextuple.A1290.TreeAssembly

/-!
# The concrete five-dimensional affine certificate at `A = 129 / 10000`

`improvedRootReplay` plus the exact stream lengths and the audited generic soundness layer give
`A1290.Certificate.sextuple_affine : 129 / 10000 ≤ sextupleEnergy g + B6 * sextupleSpan g`.
-/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

noncomputable section

namespace Zeta23.ThmD.Sextuple.MacroPrototype.A1290

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

end Zeta23.ThmD.Sextuple.MacroPrototype.A1290

namespace Zeta23.ThmD.Sextuple.A1290.Certificate

open Zeta23.ThmD.Sextuple
open Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple.MacroPrototype.A1290

/-- **The concrete sextuple affine certificate at `A = 129 / 10000`, `B = B₆`.** -/
theorem sextuple_affine (g : Fin 5 → ℝ) (hg : ∀ i, 0 ≤ g i) :
    (129 / 10000 : ℝ) ≤ sextupleEnergy g + B6 * sextupleSpan g := by
  have hroot := improvedRootBox_predicate
  have hglobal := affineTree_global_at
    (A := (129 / 10000 : ℚ)) (B := (1094977 / 5000000000 : ℚ))
    (limit := (59 : ℚ)) (by norm_num) (by norm_num) hroot g hg
  simpa [affineEnergyGoal, B6] using hglobal

end Zeta23.ThmD.Sextuple.A1290.Certificate

end
