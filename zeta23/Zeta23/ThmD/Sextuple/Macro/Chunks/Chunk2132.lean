import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 70089, payload cursor 35038, depth 16, 1 tokens. -/
theorem chunk2132 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 45 70089 35038 (pathBox rootBox [(false, 2), (false, 4), (false, 0), (true, 3), (true, 1), (false, 2), (false, 4), (true, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (70090, 35039) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
