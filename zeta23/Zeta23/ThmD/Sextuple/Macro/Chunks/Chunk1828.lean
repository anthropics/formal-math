import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 60842, payload cursor 30415, depth 16, 9 tokens. -/
theorem chunk1828 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 45 60842 30415 (pathBox rootBox [(false, 2), (true, 4), (true, 0), (false, 3), (true, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (60851, 30420) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
