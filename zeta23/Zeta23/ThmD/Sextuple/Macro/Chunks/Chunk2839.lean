import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 92063, payload cursor 46026, depth 15, 27 tokens. -/
theorem chunk2839 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 46 92063 46026 (pathBox rootBox [(true, 4), (true, 0), (false, 3), (false, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (92090, 46040) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
