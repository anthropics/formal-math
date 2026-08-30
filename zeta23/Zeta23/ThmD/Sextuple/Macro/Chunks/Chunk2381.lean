import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 77657, payload cursor 38824, depth 12, 89 tokens. -/
theorem chunk2381 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 49 77657 38824 (pathBox rootBox [(true, 1), (false, 2), (false, 4), (true, 0), (true, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (77746, 38869) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
