import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 68850, payload cursor 34418, depth 16, 1 tokens. -/
theorem chunk2082 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 45 68850 34418 (pathBox rootBox [(false, 2), (false, 4), (true, 0), (false, 3), (false, 1), (false, 2), (false, 4), (true, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (68851, 34419) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
