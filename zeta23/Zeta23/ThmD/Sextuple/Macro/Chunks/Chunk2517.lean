import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 81561, payload cursor 40775, depth 15, 21 tokens. -/
theorem chunk2517 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 46 81561 40775 (pathBox rootBox [(true, 4), (true, 0), (true, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (true, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (81582, 40786) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
