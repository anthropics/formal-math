import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 95658, payload cursor 47824, depth 12, 77 tokens. -/
theorem chunk2897 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 49 95658 47824 (pathBox rootBox [(false, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (true, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (95735, 47863) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
