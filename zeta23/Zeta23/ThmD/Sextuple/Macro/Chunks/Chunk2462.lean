import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 79787, payload cursor 39887, depth 22, 5 tokens. -/
theorem chunk2462 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 39 79787 39887 (pathBox rootBox [(true, 1), (true, 2), (true, 4), (true, 0), (true, 3), (true, 1), (true, 2), (true, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (true, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (79792, 39890) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
