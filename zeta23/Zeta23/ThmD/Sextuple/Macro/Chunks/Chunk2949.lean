import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 98517, payload cursor 49258, depth 3, 1 tokens. -/
theorem chunk2949 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 58 98517 49258 (pathBox rootBox [(true, 3), (true, 1), (false, 2)]) =
      some (98518, 49259) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
