import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 85766, payload cursor 42873, depth 36, 19 tokens. -/
theorem chunk2626 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 25 85766 42873 (pathBox rootBox [(false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (true, 2), (true, 4), (true, 0), (true, 3), (true, 1), (true, 2), (true, 4), (true, 0), (true, 3), (true, 1), (true, 2), (true, 4), (true, 0), (true, 3), (true, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (85785, 42883) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
