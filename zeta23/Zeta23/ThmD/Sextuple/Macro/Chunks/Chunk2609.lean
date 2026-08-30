import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 85403, payload cursor 42698, depth 10, 67 tokens. -/
theorem chunk2609 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 51 85403 42698 (pathBox rootBox [(true, 4), (false, 0), (true, 3), (true, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (85470, 42732) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
