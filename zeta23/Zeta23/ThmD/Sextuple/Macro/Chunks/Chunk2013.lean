import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 66845, payload cursor 33417, depth 15, 29 tokens. -/
theorem chunk2013 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 46 66845 33417 (pathBox rootBox [(true, 4), (false, 0), (true, 3), (true, 1), (false, 2), (true, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (66874, 33432) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
