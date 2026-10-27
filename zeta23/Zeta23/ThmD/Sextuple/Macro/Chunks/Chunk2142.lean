import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 70302, payload cursor 35144, depth 19, 67 tokens. -/
theorem chunk2142 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 42 70302 35144 (pathBox rootBox [(false, 0), (true, 3), (true, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (true, 2), (false, 4), (true, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (70369, 35178) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
