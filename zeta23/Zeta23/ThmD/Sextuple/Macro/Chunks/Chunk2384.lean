import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 77879, payload cursor 38936, depth 10, 61 tokens. -/
theorem chunk2384 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 51 77879 38936 (pathBox rootBox [(true, 4), (true, 0), (true, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (77940, 38967) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
