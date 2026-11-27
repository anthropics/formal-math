import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 73282, payload cursor 36634, depth 19, 7 tokens. -/
theorem chunk2244 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 42 73282 36634 (pathBox rootBox [(false, 0), (true, 3), (true, 1), (true, 2), (false, 4), (true, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (true, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (73289, 36638) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
