import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 95888, payload cursor 47941, depth 8, 65 tokens. -/
theorem chunk2901 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 53 95888 47941 (pathBox rootBox [(true, 3), (false, 1), (false, 2), (true, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (95953, 47974) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
