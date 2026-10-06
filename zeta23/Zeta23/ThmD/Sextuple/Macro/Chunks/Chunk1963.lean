import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 65504, payload cursor 32745, depth 19, 11 tokens. -/
theorem chunk1963 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 42 65504 32745 (pathBox rootBox [(false, 0), (true, 3), (true, 1), (true, 2), (false, 4), (true, 0), (false, 3), (false, 1), (false, 2), (true, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (65515, 32751) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
