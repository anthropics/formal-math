import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 45228, payload cursor 22607, depth 19, 1 tokens. -/
theorem chunk1372 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 42 45228 22607 (pathBox rootBox [(false, 0), (true, 3), (true, 1), (true, 2), (false, 4), (false, 0), (true, 3), (false, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (45229, 22608) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
