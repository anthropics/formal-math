import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 94637, payload cursor 47313, depth 14, 65 tokens. -/
theorem chunk2882 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 47 94637 47313 (pathBox rootBox [(true, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (true, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (94702, 47346) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
