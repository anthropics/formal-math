import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 85552, payload cursor 42768, depth 18, 1 tokens. -/
theorem chunk2612 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 43 85552 42768 (pathBox rootBox [(false, 3), (true, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (85553, 42769) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
