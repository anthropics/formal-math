import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 85895, payload cursor 42940, depth 20, 1 tokens. -/
theorem chunk2635 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 41 85895 42940 (pathBox rootBox [(false, 4), (true, 0), (true, 3), (true, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (85896, 42941) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
