import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 68600, payload cursor 34293, depth 24, 11 tokens. -/
theorem chunk2069 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 37 68600 34293 (pathBox rootBox [(true, 0), (true, 3), (true, 1), (true, 2), (true, 4), (true, 0), (true, 3), (true, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (true, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (68611, 34299) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
