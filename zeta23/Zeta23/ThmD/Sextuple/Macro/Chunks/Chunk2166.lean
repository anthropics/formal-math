import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 70965, payload cursor 35476, depth 19, 31 tokens. -/
theorem chunk2166 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 42 70965 35476 (pathBox rootBox [(false, 0), (true, 3), (true, 1), (true, 2), (false, 4), (false, 0), (true, 3), (false, 1), (true, 2), (false, 4), (true, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (70996, 35492) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
