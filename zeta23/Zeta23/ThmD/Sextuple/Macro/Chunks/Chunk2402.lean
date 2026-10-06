import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 78188, payload cursor 39086, depth 23, 1 tokens. -/
theorem chunk2402 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 38 78188 39086 (pathBox rootBox [(false, 3), (false, 1), (true, 2), (true, 4), (true, 0), (true, 3), (true, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (true, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (78189, 39087) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
