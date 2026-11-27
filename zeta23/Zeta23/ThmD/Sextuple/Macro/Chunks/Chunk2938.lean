import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 98165, payload cursor 49079, depth 9, 77 tokens. -/
theorem chunk2938 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 52 98165 49079 (pathBox rootBox [(true, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (true, 1), (false, 2)]) =
      some (98242, 49118) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
