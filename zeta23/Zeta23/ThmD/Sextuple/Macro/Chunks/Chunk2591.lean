import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 84380, payload cursor 42184, depth 15, 27 tokens. -/
theorem chunk2591 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 46 84380 42184 (pathBox rootBox [(true, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (true, 0), (false, 3), (true, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (84407, 42198) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
