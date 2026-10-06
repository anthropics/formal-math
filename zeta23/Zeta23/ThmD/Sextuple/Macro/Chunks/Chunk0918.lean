import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 31955, payload cursor 15971, depth 17, 15 tokens. -/
theorem chunk0918 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 44 31955 15971 (pathBox rootBox [(false, 1), (true, 2), (true, 4), (false, 0), (true, 3), (true, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (31970, 15979) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
