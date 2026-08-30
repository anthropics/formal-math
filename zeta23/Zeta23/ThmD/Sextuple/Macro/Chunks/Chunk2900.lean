import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 95827, payload cursor 47910, depth 9, 61 tokens. -/
theorem chunk2900 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 52 95827 47910 (pathBox rootBox [(true, 0), (false, 3), (false, 1), (false, 2), (true, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (95888, 47941) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
