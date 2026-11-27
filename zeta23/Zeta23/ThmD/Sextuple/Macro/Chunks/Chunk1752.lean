import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 58367, payload cursor 29177, depth 16, 21 tokens. -/
theorem chunk1752 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 45 58367 29177 (pathBox rootBox [(false, 2), (true, 4), (false, 0), (false, 3), (true, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (58388, 29188) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
