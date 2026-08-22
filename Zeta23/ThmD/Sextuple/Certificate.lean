import Zeta23.ThmD.Sextuple.Macro.TreeAssembly
import Zeta23.ThmD.Sextuple.Macro.Layout

/-!
# The concrete five-dimensional affine certificate

Physical layout canonicality, exact stream exhaustion, and the root replay combine
with the audited generic soundness layer to give `sextuple_affine`.
-/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

noncomputable section

namespace Zeta23.ThmD.Sextuple.MacroPrototype

open Zeta23.ThmD.Sextuple

/-- Exact word count, sixty-bit words, zero final padding (linear Boolean check). -/
theorem topologyLayout : topologyLayoutBool tokenCount topologyWords = true := by
  decide +kernel

/-- The audited canonical topology layout predicate holds. -/
theorem topologyLayoutValid : PackedTopologyLayoutValid tokenCount topologyWords :=
  topologyLayoutBool_sound topologyLayout

/-- The audited Boolean layout guard accepts the topology words. -/
theorem topologyLayoutCheck : packedTopologyLayoutCheck tokenCount topologyWords = true :=
  (packedTopologyLayoutCheck_iff _ _).2 topologyLayoutValid

/-- The guarded audited stream constructor yields exactly the topology stream used here. -/
theorem topologyStream_checked :
    checkedPackedTopologyStream tokenCount topologyWords = some topologyStream := by
  simp [checkedPackedTopologyStream, topologyLayoutCheck, topologyStream]

/-- Exact block count, block width, zero final padding (linear Boolean check). -/
theorem leafLayout : leafLayoutBool leafCount leafBlocks = true := by
  decide +kernel

/-- The canonical leaf-block layout predicate holds. -/
theorem leafLayoutValid : PackedLeafLayoutValid leafCount leafBlocks :=
  leafLayoutBool_sound leafLayout

theorem topologyStream_length : topologyStream.length = tokenCount := rfl

theorem payloadStream_length : payloadStream.length = leafCount := rfl

/-- The complete tree check: the root replay consumes exactly both streams. -/
theorem treeCheck :
    checkAffineTree concreteLeafCheck topologyStream payloadStream 61 rootBox = true := by
  unfold checkAffineTree
  rw [rootReplay, topologyStream_length, payloadStream_length]
  decide

/-- Every nonnegative five-gap configuration in `[0,59]^5` satisfies the affine bound. -/
theorem rootBox_predicate :
    BoxPredicate (affineEnergyGoal (1 / 80) (1094977 / 5000000000)) rootBox :=
  checkAffineTree_sound concreteLeafCheck_sound treeCheck

end Zeta23.ThmD.Sextuple.MacroPrototype

namespace Zeta23.ThmD.Sextuple.Certificate

open Zeta23.ThmD.Sextuple

/-- **The concrete sextuple affine certificate.** -/
theorem sextuple_affine (g : Fin 5 → ℝ) (hg : ∀ i, 0 ≤ g i) :
    A6 ≤ sextupleEnergy g + B6 * sextupleSpan g := by
  apply affineTree_A6_global_of_root _ hg
  intro x hx
  have h := MacroPrototype.rootBox_predicate hx
  simp only [affineEnergyGoal] at h
  simp only [A6, B6]
  push_cast at h
  exact h

end Zeta23.ThmD.Sextuple.Certificate

end
