import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 97608, payload cursor 48803, depth 4, 1 tokens. -/
theorem chunk2928 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 57 97608 48803 (pathBox rootBox [(true, 0), (true, 3), (false, 1), (false, 2)]) =
      some (97609, 48804) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
