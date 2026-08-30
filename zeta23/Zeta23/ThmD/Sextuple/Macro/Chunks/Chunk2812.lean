import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 91307, payload cursor 45647, depth 17, 7 tokens. -/
theorem chunk2812 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 44 91307 45647 (pathBox rootBox [(false, 1), (true, 2), (false, 4), (false, 0), (true, 3), (true, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (91314, 45651) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
