import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 99009, payload cursor 49500, depth 12, 53 tokens. -/
theorem chunk2958 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 49 99009 49500 (pathBox rootBox [(true, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (true, 2)]) =
      some (99062, 49527) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
