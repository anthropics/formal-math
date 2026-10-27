import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 94219, payload cursor 47105, depth 13, 43 tokens. -/
theorem chunk2875 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 48 94219 47105 (pathBox rootBox [(true, 3), (false, 1), (true, 2), (false, 4), (false, 0), (true, 3), (false, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (94262, 47127) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
