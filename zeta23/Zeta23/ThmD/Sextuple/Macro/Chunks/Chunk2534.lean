import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 82049, payload cursor 41018, depth 16, 1 tokens. -/
theorem chunk2534 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 45 82049 41018 (pathBox rootBox [(false, 2), (false, 4), (false, 0), (true, 3), (true, 1), (false, 2), (false, 4), (false, 0), (false, 3), (true, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (82050, 41019) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
