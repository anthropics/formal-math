import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 93592, payload cursor 46792, depth 12, 47 tokens. -/
theorem chunk2866 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 49 93592 46792 (pathBox rootBox [(true, 1), (true, 2), (false, 4), (true, 0), (false, 3), (false, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (93639, 46816) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
