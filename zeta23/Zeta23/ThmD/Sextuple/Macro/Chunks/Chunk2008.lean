import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 66622, payload cursor 33305, depth 15, 87 tokens. -/
theorem chunk2008 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 46 66622 33305 (pathBox rootBox [(false, 4), (true, 0), (false, 3), (true, 1), (false, 2), (true, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (66709, 33349) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
