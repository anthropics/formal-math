import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 70105, payload cursor 35046, depth 19, 35 tokens. -/
theorem chunk2135 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 42 70105 35046 (pathBox rootBox [(false, 0), (true, 3), (true, 1), (true, 2), (false, 4), (false, 0), (true, 3), (true, 1), (false, 2), (false, 4), (true, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (70140, 35064) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
