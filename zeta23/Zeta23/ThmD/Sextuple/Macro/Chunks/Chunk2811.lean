import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 91253, payload cursor 45620, depth 16, 53 tokens. -/
theorem chunk2811 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 45 91253 45620 (pathBox rootBox [(false, 2), (false, 4), (false, 0), (true, 3), (true, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (91306, 45647) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
