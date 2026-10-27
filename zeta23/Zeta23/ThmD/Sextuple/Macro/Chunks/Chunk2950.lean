import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 98532, payload cursor 49259, depth 15, 77 tokens. -/
theorem chunk2950 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 46 98532 49259 (pathBox rootBox [(false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (true, 2)]) =
      some (98609, 49298) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
