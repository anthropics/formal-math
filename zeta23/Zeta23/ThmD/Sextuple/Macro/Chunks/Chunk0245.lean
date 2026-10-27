import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 8039, payload cursor 4011, depth 28, 1 tokens. -/
theorem chunk0245 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 33 8039 4011 (pathBox rootBox [(false, 3), (false, 1), (true, 2), (false, 4), (true, 0), (false, 3), (true, 1), (true, 2), (true, 4), (true, 0), (true, 3), (true, 1), (true, 2), (true, 4), (false, 0), (true, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (8040, 4012) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
