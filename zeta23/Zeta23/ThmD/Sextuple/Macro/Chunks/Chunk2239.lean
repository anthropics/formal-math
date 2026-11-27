import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 73126, payload cursor 36556, depth 25, 67 tokens. -/
theorem chunk2239 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 36 73126 36556 (pathBox rootBox [(true, 4), (true, 0), (false, 3), (true, 1), (true, 2), (true, 4), (true, 0), (true, 3), (true, 1), (true, 2), (true, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (true, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (73193, 36590) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
