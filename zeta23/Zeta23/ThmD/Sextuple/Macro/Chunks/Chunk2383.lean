import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 77844, payload cursor 38918, depth 12, 35 tokens. -/
theorem chunk2383 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 49 77844 38918 (pathBox rootBox [(true, 1), (true, 2), (false, 4), (true, 0), (true, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (77879, 38936) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
