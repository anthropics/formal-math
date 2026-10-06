import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 65778, payload cursor 32882, depth 17, 1 tokens. -/
theorem chunk1974 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 44 65778 32882 (pathBox rootBox [(false, 1), (true, 2), (false, 4), (false, 0), (true, 3), (false, 1), (false, 2), (true, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (65779, 32883) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
