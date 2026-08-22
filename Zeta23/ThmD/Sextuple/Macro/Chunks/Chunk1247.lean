import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 41390, payload cursor 20688, depth 17, 1 tokens. -/
theorem chunk1247 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 44 41390 20688 (pathBox rootBox [(false, 1), (true, 2), (false, 4), (true, 0), (false, 3), (false, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (41391, 20689) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
