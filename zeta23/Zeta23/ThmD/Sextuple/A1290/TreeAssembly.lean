import Zeta23.ThmD.Sextuple.A1290.Layout
import Zeta23.ThmD.Sextuple.A1290.Assembly.Part569

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype.A1290
open Zeta23.ThmD.Sextuple

/-- The complete replay consumes both logical streams exactly. -/
theorem improvedRootReplay :
    replayAffineTree improvedConcreteLeafCheck improvedTopologyStream improvedPayloadStream
      74 0 0 improvedRootBox = some (3550925, 1775463) := by
  have h := improvedNode56922
  simpa only [improvedPathBox] using h

#print axioms improvedRootReplay

end Zeta23.ThmD.Sextuple.MacroPrototype.A1290
