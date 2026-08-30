import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 88921, payload cursor 44454, depth 16, 27 tokens. -/
theorem chunk2742 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 45 88921 44454 (pathBox rootBox [(false, 2), (true, 4), (true, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (88948, 44468) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
