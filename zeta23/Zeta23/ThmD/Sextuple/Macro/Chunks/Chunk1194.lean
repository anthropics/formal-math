import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 39598, payload cursor 19791, depth 32, 1 tokens. -/
theorem chunk1194 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 29 39598 19791 (pathBox rootBox [(true, 1), (true, 2), (true, 4), (true, 0), (false, 3), (true, 1), (true, 2), (false, 4), (true, 0), (true, 3), (true, 1), (false, 2), (true, 4), (true, 0), (true, 3), (true, 1), (true, 2), (true, 4), (false, 0), (false, 3), (false, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (39599, 19792) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
