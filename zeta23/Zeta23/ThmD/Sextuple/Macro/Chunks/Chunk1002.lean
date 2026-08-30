import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 34385, payload cursor 17185, depth 18, 1 tokens. -/
theorem chunk1002 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 43 34385 17185 (pathBox rootBox [(false, 3), (true, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (34386, 17186) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
