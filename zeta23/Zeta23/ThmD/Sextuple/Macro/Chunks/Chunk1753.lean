import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 58389, payload cursor 29188, depth 17, 17 tokens. -/
theorem chunk1753 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 44 58389 29188 (pathBox rootBox [(false, 1), (true, 2), (true, 4), (false, 0), (false, 3), (true, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (58406, 29197) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
