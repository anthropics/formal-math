import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 76721, payload cursor 38354, depth 16, 11 tokens. -/
theorem chunk2364 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 45 76721 38354 (pathBox rootBox [(false, 2), (false, 4), (false, 0), (false, 3), (true, 1), (true, 2), (false, 4), (false, 0), (true, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (76732, 38360) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
