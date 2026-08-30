import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 64532, payload cursor 32260, depth 17, 7 tokens. -/
theorem chunk1923 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 44 64532 32260 (pathBox rootBox [(false, 1), (true, 2), (false, 4), (true, 0), (true, 3), (true, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (64539, 32264) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
