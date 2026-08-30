import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 87807, payload cursor 43896, depth 24, 1 tokens. -/
theorem chunk2703 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 37 87807 43896 (pathBox rootBox [(false, 0), (true, 3), (true, 1), (false, 2), (true, 4), (true, 0), (true, 3), (true, 1), (true, 2), (true, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (87808, 43897) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
