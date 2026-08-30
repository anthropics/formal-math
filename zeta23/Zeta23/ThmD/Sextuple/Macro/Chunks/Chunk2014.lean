import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 66874, payload cursor 33432, depth 14, 27 tokens. -/
theorem chunk2014 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 47 66874 33432 (pathBox rootBox [(true, 0), (true, 3), (true, 1), (false, 2), (true, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (66901, 33446) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
