import Zeta23.ThmD.Sextuple.A1275.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 384860, payload cursor 192429, depth 4, 1 tokens. -/
theorem improvedChunk8928 :
    replayAffineTree improvedConcreteLeafCheck improvedTopologyStream improvedPayloadStream
      86 384860 192429 (improvedPathBox improvedRootBox [(true, ⟨0, by decide⟩), (false, ⟨3, by decide⟩), (true, ⟨1, by decide⟩), (false, ⟨2, by decide⟩)]) =
      some (384861, 192430) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
