import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 42243, payload cursor 21112, depth 37, 39 tokens. -/
theorem chunk1276 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 24 42243 21112 (pathBox rootBox [(true, 1), (false, 2), (false, 4), (true, 0), (true, 3), (false, 1), (true, 2), (true, 4), (true, 0), (false, 3), (true, 1), (true, 2), (true, 4), (false, 0), (true, 3), (true, 1), (false, 2), (true, 4), (true, 0), (true, 3), (true, 1), (true, 2), (false, 4), (true, 0), (false, 3), (false, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (42282, 21132) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
