import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 71738, payload cursor 35865, depth 12, 33 tokens. -/
theorem chunk2182 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 49 71738 35865 (pathBox rootBox [(true, 1), (true, 2), (true, 4), (true, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (71771, 35882) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
