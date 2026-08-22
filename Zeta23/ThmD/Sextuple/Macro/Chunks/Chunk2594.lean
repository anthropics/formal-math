import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 84526, payload cursor 42258, depth 13, 73 tokens. -/
theorem chunk2594 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 48 84526 42258 (pathBox rootBox [(false, 3), (true, 1), (false, 2), (false, 4), (true, 0), (false, 3), (true, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (84599, 42295) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
