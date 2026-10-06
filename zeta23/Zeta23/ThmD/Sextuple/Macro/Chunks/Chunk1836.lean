import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 61023, payload cursor 30505, depth 17, 21 tokens. -/
theorem chunk1836 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 44 61023 30505 (pathBox rootBox [(false, 1), (true, 2), (false, 4), (false, 0), (true, 3), (true, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (61044, 30516) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
