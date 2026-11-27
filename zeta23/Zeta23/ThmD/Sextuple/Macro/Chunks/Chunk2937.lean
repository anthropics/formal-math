import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 98092, payload cursor 49042, depth 10, 73 tokens. -/
theorem chunk2937 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 51 98092 49042 (pathBox rootBox [(true, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (true, 1), (false, 2)]) =
      some (98165, 49079) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
