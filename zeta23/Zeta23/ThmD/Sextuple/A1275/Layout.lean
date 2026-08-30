import Zeta23.ThmD.Sextuple.A1275.TreeWords
import Zeta23.ThmD.Sextuple.Macro.Layout

/-!
# Physical layout of the `A = 51/4000` certificate words

The words are stored two levels deep (`TreeWords.lean`).  The audited flat layout
predicates (`PackedTopologyLayoutValid`, `PackedLeafLayoutValid`: exact word counts,
60-bit / 321·256-bit words, zero final padding) are proved here for the concatenated flat
arrays, through the linear Boolean checks of `Macro/Layout.lean`.
-/

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace Zeta23.ThmD.Sextuple.MacroPrototype

/-- The canonical flat topology words: the concatenation of `improvedTopologyBlocks`. -/
def improvedTopologyWords : Array ℕ :=
  ⟨(improvedTopologyBlocks.toList.map Array.toList).flatten⟩

/-- The canonical flat leaf-block words: the concatenation of `improvedLeafBlockGroups`. -/
def improvedLeafBlocks : Array ℕ :=
  ⟨(improvedLeafBlockGroups.toList.map Array.toList).flatten⟩

lemma improvedTopologyLayoutBool_check :
    topologyLayoutBool improvedTokenCount improvedTopologyWords = true := by
  decide +kernel

lemma improvedLeafLayoutBool_check :
    leafLayoutBool improvedLeafCount improvedLeafBlocks = true := by
  decide +kernel

theorem improvedTopologyLayoutValid :
    PackedTopologyLayoutValid improvedTokenCount improvedTopologyWords :=
  topologyLayoutBool_sound improvedTopologyLayoutBool_check

theorem improvedLeafLayoutValid :
    PackedLeafLayoutValid improvedLeafCount improvedLeafBlocks :=
  leafLayoutBool_sound improvedLeafLayoutBool_check

#print axioms improvedTopologyLayoutValid
#print axioms improvedLeafLayoutValid

end Zeta23.ThmD.Sextuple.MacroPrototype
