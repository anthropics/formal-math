import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 5378, payload cursor 2681, depth 24, 1 tokens. -/
theorem chunk0147 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 37 5378 2681 (pathBox rootBox [(false, 0), (false, 3), (true, 1), (true, 2), (true, 4), (true, 0), (true, 3), (true, 1), (true, 2), (false, 4), (false, 0), (true, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (5379, 2682) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
