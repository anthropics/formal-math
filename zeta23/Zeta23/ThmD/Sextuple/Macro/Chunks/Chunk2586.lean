import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 84002, payload cursor 41996, depth 13, 57 tokens. -/
theorem chunk2586 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 48 84002 41996 (pathBox rootBox [(true, 3), (false, 1), (false, 2), (true, 4), (false, 0), (false, 3), (true, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (84059, 42025) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
