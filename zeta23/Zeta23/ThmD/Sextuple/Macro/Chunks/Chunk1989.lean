import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 66192, payload cursor 33089, depth 16, 1 tokens. -/
theorem chunk1989 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 45 66192 33089 (pathBox rootBox [(false, 2), (false, 4), (false, 0), (false, 3), (true, 1), (false, 2), (true, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (66193, 33090) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
