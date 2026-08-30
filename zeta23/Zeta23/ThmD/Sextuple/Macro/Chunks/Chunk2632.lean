import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 85889, payload cursor 42937, depth 17, 1 tokens. -/
theorem chunk2632 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 44 85889 42937 (pathBox rootBox [(false, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (85890, 42938) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
