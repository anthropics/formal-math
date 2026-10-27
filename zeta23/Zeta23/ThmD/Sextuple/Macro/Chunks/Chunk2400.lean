import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 78183, payload cursor 39084, depth 20, 1 tokens. -/
theorem chunk2400 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 41 78183 39084 (pathBox rootBox [(false, 4), (true, 0), (true, 3), (true, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (true, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (78184, 39085) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
