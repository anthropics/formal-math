import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 41603, payload cursor 20793, depth 31, 49 tokens. -/
theorem chunk1258 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 30 41603 20793 (pathBox rootBox [(false, 2), (true, 4), (true, 0), (true, 3), (false, 1), (true, 2), (true, 4), (false, 0), (true, 3), (true, 1), (false, 2), (true, 4), (true, 0), (true, 3), (true, 1), (true, 2), (false, 4), (true, 0), (false, 3), (false, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (41652, 20818) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
