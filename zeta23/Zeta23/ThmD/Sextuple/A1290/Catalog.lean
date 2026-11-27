import Zeta23.ThmD.Sextuple.A1275.Catalog
import Zeta23.ThmD.Sextuple.A1290.RefinementData2

/-!
# The 666-model catalog: stable 56 + refinement v1 (216) + refinement v2 (394)

`improvedCatalog2 i` is the stable piece `i` for `i < 56`, the v1 refinement cell `i − 56` for
`56 ≤ i < 272` (both through `A1275.Catalog.improvedCatalog`), and the v2 piece `i − 272` otherwise.
-/

namespace Zeta23.ThmD.Sextuple.MacroPrototype.A1290

open Zeta23.ThmD.Sextuple
open Zeta23.ThmD.Sextuple.MacroPrototype

def improvedCatalog2 (i : Fin 666) : MacroPiece :=
  if h : i.val < 272 then improvedCatalog ⟨i.val, h⟩
  else refinement2Table ⟨i.val - 272, by omega⟩

theorem improvedCatalog2_check (i : Fin 666) : (improvedCatalog2 i).check = true := by
  unfold improvedCatalog2
  split
  · exact improvedCatalog_check _
  · exact refinement2Table_check _

#print axioms improvedCatalog2_check

end Zeta23.ThmD.Sextuple.MacroPrototype.A1290
