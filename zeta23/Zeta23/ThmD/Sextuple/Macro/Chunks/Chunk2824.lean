import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 91519, payload cursor 45752, depth 21, 31 tokens. -/
theorem chunk2824 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 40 91519 45752 (pathBox rootBox [(false, 2), (true, 4), (true, 0), (true, 3), (true, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (91550, 45768) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
