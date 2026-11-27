import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 66928, payload cursor 33457, depth 17, 1 tokens. -/
theorem chunk2016 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 44 66928 33457 (pathBox rootBox [(false, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (true, 2), (true, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (66929, 33458) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
