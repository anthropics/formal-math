import Zeta23.ThmD.Sextuple.A1275.Layout
import Zeta23.ThmD.Sextuple.A1275.Assembly.Part089

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- The complete improved replay consumes both logical streams exactly. -/
theorem improvedRootReplay :
    replayAffineTree improvedConcreteLeafCheck improvedTopologyStream improvedPayloadStream
      90 0 0 improvedRootBox = some (385967, 192984) := by
  have h := improvedNode8951
  simpa only [improvedPathBox] using h

#print axioms improvedRootReplay

end Zeta23.ThmD.Sextuple.MacroPrototype
