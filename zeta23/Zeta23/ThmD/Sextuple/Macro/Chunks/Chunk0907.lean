import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 31641, payload cursor 15813, depth 31, 5 tokens. -/
theorem chunk0907 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 30 31641 15813 (pathBox rootBox [(true, 2), (true, 4), (true, 0), (true, 3), (true, 1), (true, 2), (true, 4), (true, 0), (false, 3), (false, 1), (true, 2), (true, 4), (true, 0), (true, 3), (true, 1), (true, 2), (false, 4), (false, 0), (true, 3), (true, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (31646, 15816) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
