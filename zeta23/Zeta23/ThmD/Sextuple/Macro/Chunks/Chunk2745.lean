import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 89028, payload cursor 44507, depth 17, 99 tokens. -/
theorem chunk2745 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 44 89028 44507 (pathBox rootBox [(true, 1), (false, 2), (false, 4), (false, 0), (true, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (89127, 44557) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
