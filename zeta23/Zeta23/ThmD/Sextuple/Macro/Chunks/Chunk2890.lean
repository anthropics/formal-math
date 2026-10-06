import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 95112, payload cursor 47552, depth 12, 61 tokens. -/
theorem chunk2890 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 49 95112 47552 (pathBox rootBox [(true, 1), (true, 2), (false, 4), (false, 0), (false, 3), (true, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (95173, 47583) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
