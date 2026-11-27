import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 70957, payload cursor 35472, depth 17, 1 tokens. -/
theorem chunk2164 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 44 70957 35472 (pathBox rootBox [(false, 1), (true, 2), (false, 4), (false, 0), (true, 3), (false, 1), (true, 2), (false, 4), (true, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (70958, 35473) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
