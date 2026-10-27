import Zeta23.ThmD.Sextuple.Macro.EnvelopeData

namespace Zeta23.ThmD.Sextuple.MacroPrototype

open Zeta23.ThmD.Sextuple
open RatInterval

/-- The immutable stable 56-piece envelope as a bounded table. -/
def stableMacroTable (i : Fin 56) : MacroPiece :=
  match i.val with
  | 0 => macroPiece0
  | 1 => macroPiece1
  | 2 => macroPiece2
  | 3 => macroPiece3
  | 4 => macroPiece4
  | 5 => macroPiece5
  | 6 => macroPiece6
  | 7 => macroPiece7
  | 8 => macroPiece8
  | 9 => macroPiece9
  | 10 => macroPiece10
  | 11 => macroPiece11
  | 12 => macroPiece12
  | 13 => macroPiece13
  | 14 => macroPiece14
  | 15 => macroPiece15
  | 16 => macroPiece16
  | 17 => macroPiece17
  | 18 => macroPiece18
  | 19 => macroPiece19
  | 20 => macroPiece20
  | 21 => macroPiece21
  | 22 => macroPiece22
  | 23 => macroPiece23
  | 24 => macroPiece24
  | 25 => macroPiece25
  | 26 => macroPiece26
  | 27 => macroPiece27
  | 28 => macroPiece28
  | 29 => macroPiece29
  | 30 => macroPiece30
  | 31 => macroPiece31
  | 32 => macroPiece32
  | 33 => macroPiece33
  | 34 => macroPiece34
  | 35 => macroPiece35
  | 36 => macroPiece36
  | 37 => macroPiece37
  | 38 => macroPiece38
  | 39 => macroPiece39
  | 40 => macroPiece40
  | 41 => macroPiece41
  | 42 => macroPiece42
  | 43 => macroPiece43
  | 44 => macroPiece44
  | 45 => macroPiece45
  | 46 => macroPiece46
  | 47 => macroPiece47
  | 48 => macroPiece48
  | 49 => macroPiece49
  | 50 => macroPiece50
  | 51 => macroPiece51
  | 52 => macroPiece52
  | 53 => macroPiece53
  | 54 => macroPiece54
  | _ => macroPiece55

set_option maxHeartbeats 0 in
theorem stableMacroTable_check (i : Fin 56) : (stableMacroTable i).check = true := by
  fin_cases i
  · exact macroPiece0_check
  · exact macroPiece1_check
  · exact macroPiece2_check
  · exact macroPiece3_check
  · exact macroPiece4_check
  · exact macroPiece5_check
  · exact macroPiece6_check
  · exact macroPiece7_check
  · exact macroPiece8_check
  · exact macroPiece9_check
  · exact macroPiece10_check
  · exact macroPiece11_check
  · exact macroPiece12_check
  · exact macroPiece13_check
  · exact macroPiece14_check
  · exact macroPiece15_check
  · exact macroPiece16_check
  · exact macroPiece17_check
  · exact macroPiece18_check
  · exact macroPiece19_check
  · exact macroPiece20_check
  · exact macroPiece21_check
  · exact macroPiece22_check
  · exact macroPiece23_check
  · exact macroPiece24_check
  · exact macroPiece25_check
  · exact macroPiece26_check
  · exact macroPiece27_check
  · exact macroPiece28_check
  · exact macroPiece29_check
  · exact macroPiece30_check
  · exact macroPiece31_check
  · exact macroPiece32_check
  · exact macroPiece33_check
  · exact macroPiece34_check
  · exact macroPiece35_check
  · exact macroPiece36_check
  · exact macroPiece37_check
  · exact macroPiece38_check
  · exact macroPiece39_check
  · exact macroPiece40_check
  · exact macroPiece41_check
  · exact macroPiece42_check
  · exact macroPiece43_check
  · exact macroPiece44_check
  · exact macroPiece45_check
  · exact macroPiece46_check
  · exact macroPiece47_check
  · exact macroPiece48_check
  · exact macroPiece49_check
  · exact macroPiece50_check
  · exact macroPiece51_check
  · exact macroPiece52_check
  · exact macroPiece53_check
  · exact macroPiece54_check
  · exact macroPiece55_check

#print axioms stableMacroTable_check

end Zeta23.ThmD.Sextuple.MacroPrototype
