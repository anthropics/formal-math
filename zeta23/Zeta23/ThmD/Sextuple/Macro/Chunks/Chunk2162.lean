import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 70915, payload cursor 35452, depth 15, 29 tokens. -/
theorem chunk2162 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 46 70915 35452 (pathBox rootBox [(true, 4), (true, 0), (false, 3), (false, 1), (true, 2), (false, 4), (true, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (70944, 35467) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
