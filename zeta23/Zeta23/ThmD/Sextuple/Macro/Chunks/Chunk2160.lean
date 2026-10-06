import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 70722, payload cursor 35355, depth 16, 95 tokens. -/
theorem chunk2160 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 45 70722 35355 (pathBox rootBox [(true, 2), (true, 4), (false, 0), (false, 3), (false, 1), (true, 2), (false, 4), (true, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (70817, 35403) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
