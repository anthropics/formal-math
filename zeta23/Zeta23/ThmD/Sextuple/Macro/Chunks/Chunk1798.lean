import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 59867, payload cursor 29927, depth 19, 21 tokens. -/
theorem chunk1798 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 42 59867 29927 (pathBox rootBox [(false, 0), (true, 3), (true, 1), (true, 2), (false, 4), (true, 0), (false, 3), (true, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (59888, 29938) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
