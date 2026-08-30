import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 70061, payload cursor 35025, depth 15, 25 tokens. -/
theorem chunk2131 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 46 70061 35025 (pathBox rootBox [(true, 4), (true, 0), (false, 3), (true, 1), (false, 2), (false, 4), (true, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (70086, 35038) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
