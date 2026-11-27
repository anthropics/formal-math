import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 52468, payload cursor 26227, depth 17, 37 tokens. -/
theorem chunk1585 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 44 52468 26227 (pathBox rootBox [(false, 1), (true, 2), (false, 4), (false, 0), (false, 3), (true, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (52505, 26246) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
