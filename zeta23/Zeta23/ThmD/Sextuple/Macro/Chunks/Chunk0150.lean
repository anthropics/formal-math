import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 5386, payload cursor 2684, depth 29, 67 tokens. -/
theorem chunk0150 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 32 5386 2684 (pathBox rootBox [(false, 0), (true, 3), (false, 1), (false, 2), (true, 4), (true, 0), (false, 3), (true, 1), (true, 2), (true, 4), (true, 0), (true, 3), (true, 1), (true, 2), (false, 4), (false, 0), (true, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (5453, 2718) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
