import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 88384, payload cursor 44185, depth 19, 9 tokens. -/
theorem chunk2721 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 42 88384 44185 (pathBox rootBox [(false, 0), (true, 3), (true, 1), (true, 2), (false, 4), (true, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (88393, 44190) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
