import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 79882, payload cursor 39933, depth 25, 1 tokens. -/
theorem chunk2470 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 36 79882 39933 (pathBox rootBox [(false, 4), (false, 0), (true, 3), (false, 1), (true, 2), (true, 4), (true, 0), (true, 3), (true, 1), (true, 2), (false, 4), (true, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (true, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (79883, 39934) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
