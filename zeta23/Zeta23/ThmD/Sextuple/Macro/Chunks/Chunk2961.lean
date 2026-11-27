import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 99220, payload cursor 49607, depth 8, 87 tokens. -/
theorem chunk2961 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 53 99220 49607 (pathBox rootBox [(true, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (true, 2)]) =
      some (99307, 49651) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
