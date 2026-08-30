import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 64766, payload cursor 32375, depth 21, 1 tokens. -/
theorem chunk1935 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 40 64766 32375 (pathBox rootBox [(false, 2), (false, 4), (true, 0), (true, 3), (true, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (true, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (64767, 32376) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
