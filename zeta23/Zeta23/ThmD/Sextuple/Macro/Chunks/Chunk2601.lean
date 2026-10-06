import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 84952, payload cursor 42470, depth 15, 31 tokens. -/
theorem chunk2601 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 46 84952 42470 (pathBox rootBox [(true, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (true, 3), (true, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (84983, 42486) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
