import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 60529, payload cursor 30257, depth 28, 17 tokens. -/
theorem chunk1820 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 33 60529 30257 (pathBox rootBox [(false, 3), (true, 1), (true, 2), (true, 4), (true, 0), (true, 3), (false, 1), (false, 2), (true, 4), (true, 0), (true, 3), (true, 1), (true, 2), (false, 4), (true, 0), (false, 3), (true, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (60546, 30266) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
