import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 64546, payload cursor 32267, depth 19, 3 tokens. -/
theorem chunk1925 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 42 64546 32267 (pathBox rootBox [(false, 0), (true, 3), (true, 1), (true, 2), (false, 4), (true, 0), (true, 3), (true, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (64549, 32269) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
