import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 70099, payload cursor 35043, depth 18, 5 tokens. -/
theorem chunk2134 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 43 70099 35043 (pathBox rootBox [(false, 3), (true, 1), (true, 2), (false, 4), (false, 0), (true, 3), (true, 1), (false, 2), (false, 4), (true, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (70104, 35046) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
