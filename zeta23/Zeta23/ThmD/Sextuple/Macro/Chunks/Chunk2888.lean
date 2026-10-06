import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 95034, payload cursor 47512, depth 14, 33 tokens. -/
theorem chunk2888 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 47 95034 47512 (pathBox rootBox [(true, 0), (false, 3), (false, 1), (true, 2), (false, 4), (false, 0), (false, 3), (true, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (95067, 47529) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
