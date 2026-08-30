import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 78911, payload cursor 39447, depth 30, 61 tokens. -/
theorem chunk2421 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 31 78911 39447 (pathBox rootBox [(true, 4), (false, 0), (true, 3), (false, 1), (true, 2), (true, 4), (true, 0), (true, 3), (false, 1), (true, 2), (true, 4), (true, 0), (true, 3), (true, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (true, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (78972, 39478) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
