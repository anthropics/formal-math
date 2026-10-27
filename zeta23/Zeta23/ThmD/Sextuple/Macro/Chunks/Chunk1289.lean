import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 42573, payload cursor 21277, depth 35, 1 tokens. -/
theorem chunk1289 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 26 42573 21277 (pathBox rootBox [(false, 4), (true, 0), (false, 3), (false, 1), (true, 2), (false, 4), (true, 0), (true, 3), (true, 1), (true, 2), (true, 4), (false, 0), (true, 3), (true, 1), (false, 2), (true, 4), (true, 0), (true, 3), (true, 1), (true, 2), (false, 4), (true, 0), (false, 3), (false, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (42574, 21278) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
