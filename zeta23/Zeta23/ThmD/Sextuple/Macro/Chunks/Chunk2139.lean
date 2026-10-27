import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 70274, payload cursor 35130, depth 16, 23 tokens. -/
theorem chunk2139 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 45 70274 35130 (pathBox rootBox [(false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (true, 2), (false, 4), (true, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (70297, 35142) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
