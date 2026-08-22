import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 98494, payload cursor 49243, depth 11, 17 tokens. -/
theorem chunk2942 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 50 98494 49243 (pathBox rootBox [(true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (true, 2), (false, 4), (false, 0), (false, 3), (true, 1), (false, 2)]) =
      some (98511, 49252) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
