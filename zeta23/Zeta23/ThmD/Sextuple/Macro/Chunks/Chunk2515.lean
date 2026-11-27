import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 81451, payload cursor 40719, depth 17, 31 tokens. -/
theorem chunk2515 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 44 81451 40719 (pathBox rootBox [(false, 1), (true, 2), (false, 4), (true, 0), (true, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (true, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (81482, 40735) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
