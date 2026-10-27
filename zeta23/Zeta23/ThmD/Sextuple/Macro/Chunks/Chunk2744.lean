import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 89027, payload cursor 44506, depth 17, 1 tokens. -/
theorem chunk2744 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 44 89027 44506 (pathBox rootBox [(false, 1), (false, 2), (false, 4), (false, 0), (true, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (89028, 44507) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
