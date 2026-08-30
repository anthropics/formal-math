import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 74160, payload cursor 37073, depth 17, 21 tokens. -/
theorem chunk2282 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 44 74160 37073 (pathBox rootBox [(false, 1), (true, 2), (false, 4), (false, 0), (false, 3), (true, 1), (false, 2), (false, 4), (false, 0), (true, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (74181, 37084) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
