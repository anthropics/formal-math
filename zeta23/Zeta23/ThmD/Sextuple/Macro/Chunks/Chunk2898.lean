import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 95735, payload cursor 47863, depth 12, 33 tokens. -/
theorem chunk2898 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 49 95735 47863 (pathBox rootBox [(true, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (true, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (95768, 47880) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
