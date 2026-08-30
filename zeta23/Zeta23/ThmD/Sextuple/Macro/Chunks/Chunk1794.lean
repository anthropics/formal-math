import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 59732, payload cursor 29860, depth 21, 85 tokens. -/
theorem chunk1794 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 40 59732 29860 (pathBox rootBox [(true, 2), (true, 4), (true, 0), (true, 3), (true, 1), (true, 2), (true, 4), (false, 0), (false, 3), (true, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (59817, 29903) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
