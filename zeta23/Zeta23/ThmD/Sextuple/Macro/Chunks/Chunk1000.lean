import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 34349, payload cursor 17167, depth 16, 33 tokens. -/
theorem chunk1000 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 45 34349 17167 (pathBox rootBox [(false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (34382, 17184) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
