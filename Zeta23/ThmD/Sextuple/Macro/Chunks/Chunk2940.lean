import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 98325, payload cursor 49160, depth 7, 81 tokens. -/
theorem chunk2940 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 54 98325 49160 (pathBox rootBox [(true, 1), (false, 2), (false, 4), (false, 0), (false, 3), (true, 1), (false, 2)]) =
      some (98406, 49201) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
