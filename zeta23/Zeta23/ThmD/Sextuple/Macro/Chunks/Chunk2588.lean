import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 84159, payload cursor 42075, depth 12, 99 tokens. -/
theorem chunk2588 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 49 84159 42075 (pathBox rootBox [(false, 1), (true, 2), (true, 4), (false, 0), (false, 3), (true, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (84258, 42125) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
