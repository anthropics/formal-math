import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 92419, payload cursor 46204, depth 15, 35 tokens. -/
theorem chunk2846 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 46 92419 46204 (pathBox rootBox [(true, 4), (false, 0), (false, 3), (true, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (92454, 46222) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
