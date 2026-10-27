import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 81595, payload cursor 40790, depth 21, 1 tokens. -/
theorem chunk2522 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 40 81595 40790 (pathBox rootBox [(false, 2), (true, 4), (true, 0), (true, 3), (false, 1), (true, 2), (false, 4), (false, 0), (false, 3), (true, 1), (false, 2), (false, 4), (false, 0), (false, 3), (true, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (81596, 40791) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
