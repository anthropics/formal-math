import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 75712, payload cursor 37849, depth 20, 1 tokens. -/
theorem chunk2333 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 41 75712 37849 (pathBox rootBox [(false, 4), (true, 0), (true, 3), (true, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (true, 2), (false, 4), (false, 0), (true, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (75713, 37850) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
