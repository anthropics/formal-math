import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 84307, payload cursor 42147, depth 15, 73 tokens. -/
theorem chunk2590 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 46 84307 42147 (pathBox rootBox [(false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (true, 0), (false, 3), (true, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (84380, 42184) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
