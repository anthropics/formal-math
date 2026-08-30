import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 88948, payload cursor 44468, depth 16, 75 tokens. -/
theorem chunk2743 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 45 88948 44468 (pathBox rootBox [(true, 2), (true, 4), (true, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (89023, 44506) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
