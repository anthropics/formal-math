import Zeta23.ThmD.Sextuple.A1275.TreeAssembly

/-!
# The concrete five-dimensional affine certificate at `A = 51/4000`

The kernel-replayed root theorem `improvedRootReplay` (8,953 bounded subtree chunks
assembled through the generic split lemma) is combined with the exact stream lengths and
the audited generic soundness layer (`checkAffineTree_sound`, `affineTree_global_at`) to
give `A1275.Certificate.sextuple_affine`:
`51/4000 ≤ sextupleEnergy g + B6 * sextupleSpan g` for all nonnegative gap vectors.
-/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

noncomputable section

namespace Zeta23.ThmD.Sextuple.MacroPrototype

open Zeta23.ThmD.Sextuple

/-- The complete tree check: the root replay consumes exactly both streams. -/
theorem improvedTreeCheck :
    checkAffineTree improvedConcreteLeafCheck improvedTopologyStream
      improvedPayloadStream 90 improvedRootBox = true := by
  unfold checkAffineTree
  rw [improvedRootReplay]
  rfl

/-- Every nonnegative five-gap configuration in `[0,59]^5` satisfies the affine bound. -/
theorem improvedRootBox_predicate :
    BoxPredicate (affineEnergyGoal improvedA improvedB) improvedRootBox :=
  checkAffineTree_sound improvedConcreteLeafCheck_sound improvedTreeCheck

end Zeta23.ThmD.Sextuple.MacroPrototype

namespace Zeta23.ThmD.Sextuple.A1275.Certificate

open Zeta23.ThmD.Sextuple
open Zeta23.ThmD.Sextuple.MacroPrototype

/-- **The concrete sextuple affine certificate at `A = 51/4000`, `B = B₆`.** -/
theorem sextuple_affine (g : Fin 5 → ℝ) (hg : ∀ i, 0 ≤ g i) :
    (51 / 4000 : ℝ) ≤ sextupleEnergy g + B6 * sextupleSpan g := by
  have hroot := improvedRootBox_predicate
  have hglobal := affineTree_global_at
    (A := (51 / 4000 : ℚ)) (B := (1094977 / 5000000000 : ℚ))
    (limit := (59 : ℚ)) (by norm_num) (by norm_num) hroot g hg
  simpa [affineEnergyGoal, B6] using hglobal

end Zeta23.ThmD.Sextuple.A1275.Certificate

end
