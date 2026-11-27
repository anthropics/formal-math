import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 88503, payload cursor 44243, depth 29, 1 tokens. -/
theorem chunk2728 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 32 88503 44243 (pathBox rootBox [(false, 0), (true, 3), (true, 1), (false, 2), (true, 4), (false, 0), (true, 3), (true, 1), (false, 2), (true, 4), (true, 0), (true, 3), (true, 1), (true, 2), (false, 4), (true, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (88504, 44244) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
