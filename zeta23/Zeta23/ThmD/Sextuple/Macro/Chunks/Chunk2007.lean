import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 66546, payload cursor 33267, depth 15, 75 tokens. -/
theorem chunk2007 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 46 66546 33267 (pathBox rootBox [(true, 4), (false, 0), (false, 3), (true, 1), (false, 2), (true, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (66621, 33305) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
