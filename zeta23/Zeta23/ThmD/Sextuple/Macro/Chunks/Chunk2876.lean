import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 94262, payload cursor 47127, depth 12, 51 tokens. -/
theorem chunk2876 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 49 94262 47127 (pathBox rootBox [(true, 1), (true, 2), (false, 4), (false, 0), (true, 3), (false, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (94313, 47153) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
