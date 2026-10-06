import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 60995, payload cursor 30491, depth 16, 27 tokens. -/
theorem chunk1835 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 45 60995 30491 (pathBox rootBox [(false, 2), (false, 4), (false, 0), (true, 3), (true, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (61022, 30505) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
