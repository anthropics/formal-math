import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 67377, payload cursor 33682, depth 16, 9 tokens. -/
theorem chunk2033 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 45 67377 33682 (pathBox rootBox [(false, 2), (false, 4), (true, 0), (false, 3), (false, 1), (true, 2), (true, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (67386, 33687) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
