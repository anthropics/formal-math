import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 65780, payload cursor 32883, depth 18, 11 tokens. -/
theorem chunk1975 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 43 65780 32883 (pathBox rootBox [(false, 3), (true, 1), (true, 2), (false, 4), (false, 0), (true, 3), (false, 1), (false, 2), (true, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (65791, 32889) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
