import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 83333, payload cursor 41660, depth 17, 47 tokens. -/
theorem chunk2572 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 44 83333 41660 (pathBox rootBox [(false, 1), (true, 2), (false, 4), (false, 0), (true, 3), (false, 1), (true, 2), (false, 4), (false, 0), (false, 3), (true, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (83380, 41684) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
