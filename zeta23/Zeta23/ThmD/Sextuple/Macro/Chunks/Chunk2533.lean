import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 82023, payload cursor 41006, depth 15, 23 tokens. -/
theorem chunk2533 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 46 82023 41006 (pathBox rootBox [(true, 4), (true, 0), (false, 3), (true, 1), (false, 2), (false, 4), (false, 0), (false, 3), (true, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (82046, 41018) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
