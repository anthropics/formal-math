import Zeta23.ThmD.Sextuple.Macro.EnvelopeData
import Zeta23.ThmD.Sextuple.Macro.ScalarAdapter

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

def scalarCert0 : MacroScalarCert 56 := {
  box := ⟨0, (59/16)⟩
  a := (14630385677/1000000000000)
  segments := [
    { box := ⟨0, 2⟩, pieceIndex := 0 },
    { box := ⟨2, (59/16)⟩, pieceIndex := 1 }
  ]
}

def scalarCert1 : MacroScalarCert 56 := {
  box := ⟨(177/32), (413/64)⟩
  a := (240331540082023567461363898729/200000000000000000000000000000000)
  segments := [
    { box := ⟨(177/32), (235723/40000)⟩, pieceIndex := 1 },
    { box := ⟨(235723/40000), (250723/40000)⟩, pieceIndex := 2 },
    { box := ⟨(250723/40000), (413/64)⟩, pieceIndex := 3 }
  ]
}

def scalarCert2 : MacroScalarCert 56 := {
  box := ⟨(531/32), (2419/128)⟩
  a := (46487548851628354344042770920761/2000000000000000000000000000000000000)
  segments := [
    { box := ⟨(531/32), (9113373/500000)⟩, pieceIndex := 13 },
    { box := ⟨(9113373/500000), (9300873/500000)⟩, pieceIndex := 14 },
    { box := ⟨(9300873/500000), (2419/128)⟩, pieceIndex := 15 }
  ]
}

def scalarCert3 : MacroScalarCert 56 := {
  box := ⟨(177/16), (1593/128)⟩
  a := (65397592496506782025616240039841/80000000000000000000000000000000000)
  segments := [
    { box := ⟨(177/16), (1200529/100000)⟩, pieceIndex := 7 },
    { box := ⟨(1200529/100000), (1238029/100000)⟩, pieceIndex := 8 },
    { box := ⟨(1238029/100000), (1593/128)⟩, pieceIndex := 9 }
  ]
}

def scalarCert4 : MacroScalarCert 56 := {
  box := ⟨(177/32), (767/128)⟩
  a := (14630385677/1000000000000)
  segments := [
    { box := ⟨(177/32), (235723/40000)⟩, pieceIndex := 1 },
    { box := ⟨(235723/40000), (767/128)⟩, pieceIndex := 2 }
  ]
}

def scalarCert5 : MacroScalarCert 56 := {
  box := ⟨(767/128), (413/64)⟩
  a := (240331540082023567461363898729/200000000000000000000000000000000)
  segments := [
    { box := ⟨(767/128), (250723/40000)⟩, pieceIndex := 2 },
    { box := ⟨(250723/40000), (413/64)⟩, pieceIndex := 3 }
  ]
}

def scalarCert6 : MacroScalarCert 56 := {
  box := ⟨(2183/128), (2419/128)⟩
  a := (46487548851628354344042770920761/2000000000000000000000000000000000000)
  segments := [
    { box := ⟨(2183/128), (9113373/500000)⟩, pieceIndex := 13 },
    { box := ⟨(9113373/500000), (9300873/500000)⟩, pieceIndex := 14 },
    { box := ⟨(9300873/500000), (2419/128)⟩, pieceIndex := 15 }
  ]
}

def scalarCert7 : MacroScalarCert 56 := {
  box := ⟨(1475/128), (1593/128)⟩
  a := (65397592496506782025616240039841/80000000000000000000000000000000000)
  segments := [
    { box := ⟨(1475/128), (1200529/100000)⟩, pieceIndex := 7 },
    { box := ⟨(1200529/100000), (1238029/100000)⟩, pieceIndex := 8 },
    { box := ⟨(1238029/100000), (1593/128)⟩, pieceIndex := 9 }
  ]
}

def scalarCert8 : MacroScalarCert 56 := {
  box := ⟨(1121/64), (2419/128)⟩
  a := (46487548851628354344042770920761/2000000000000000000000000000000000000)
  segments := [
    { box := ⟨(1121/64), (9113373/500000)⟩, pieceIndex := 13 },
    { box := ⟨(9113373/500000), (9300873/500000)⟩, pieceIndex := 14 },
    { box := ⟨(9300873/500000), (2419/128)⟩, pieceIndex := 15 }
  ]
}

def scalarCert9 : MacroScalarCert 56 := {
  box := ⟨(767/64), (3245/256)⟩
  a := (17210569648841618553013464187489/320000000000000000000000000000000000)
  segments := [
    { box := ⟨(767/64), (1200529/100000)⟩, pieceIndex := 7 },
    { box := ⟨(1200529/100000), (1238029/100000)⟩, pieceIndex := 8 },
    { box := ⟨(1238029/100000), (3245/256)⟩, pieceIndex := 9 }
  ]
}

def scalarCert10 : MacroScalarCert 56 := {
  box := ⟨(1593/256), (413/64)⟩
  a := (240331540082023567461363898729/200000000000000000000000000000000)
  segments := [
    { box := ⟨(1593/256), (250723/40000)⟩, pieceIndex := 2 },
    { box := ⟨(250723/40000), (413/64)⟩, pieceIndex := 3 }
  ]
}

def scalarCert11 : MacroScalarCert 56 := {
  box := ⟨(3127/256), (3245/256)⟩
  a := (17210569648841618553013464187489/320000000000000000000000000000000000)
  segments := [
    { box := ⟨(3127/256), (1238029/100000)⟩, pieceIndex := 8 },
    { box := ⟨(1238029/100000), (3245/256)⟩, pieceIndex := 9 }
  ]
}

def scalarCert12 : MacroScalarCert 56 := {
  box := ⟨(1593/256), (3245/512)⟩
  a := (158816615479971569880581165995249/51200000000000000000000000000000000)
  segments := [
    { box := ⟨(1593/256), (250723/40000)⟩, pieceIndex := 2 },
    { box := ⟨(250723/40000), (3245/512)⟩, pieceIndex := 3 }
  ]
}

def scalarCert13 : MacroScalarCert 56 := {
  box := ⟨(12921/512), (6667/256)⟩
  a := (9576976453294042395280846609/80000000000000000000000000000000000)
  segments := [
    { box := ⟨(12921/512), (2560347/100000)⟩, pieceIndex := 23 },
    { box := ⟨(2560347/100000), (2597847/100000)⟩, pieceIndex := 24 },
    { box := ⟨(2597847/100000), (6667/256)⟩, pieceIndex := 25 }
  ]
}

def scalarCert14 : MacroScalarCert 56 := {
  box := ⟨(9735/512), (5015/256)⟩
  a := (5885158970114111451770320882689/1280000000000000000000000000000000000)
  segments := [
    { box := ⟨(9735/512), (19351747/1000000)⟩, pieceIndex := 17 },
    { box := ⟨(19351747/1000000), (5015/256)⟩, pieceIndex := 18 }
  ]
}

def scalarCert15 : MacroScalarCert 56 := {
  box := ⟨(12921/512), (13275/512)⟩
  a := (9576976453294042395280846609/80000000000000000000000000000000000)
  segments := [
    { box := ⟨(12921/512), (2560347/100000)⟩, pieceIndex := 23 },
    { box := ⟨(2560347/100000), (13275/512)⟩, pieceIndex := 24 }
  ]
}

def scalarCert16 : MacroScalarCert 56 := {
  box := ⟨(8083/256), (8319/256)⟩
  a := (167322041776912901830875682929/20000000000000000000000000000000000)
  segments := [
    { box := ⟨(8083/256), (6373527/200000)⟩, pieceIndex := 29 },
    { box := ⟨(6373527/200000), (6448527/200000)⟩, pieceIndex := 30 },
    { box := ⟨(6448527/200000), (8319/256)⟩, pieceIndex := 31 }
  ]
}

def scalarCert17 : MacroScalarCert 56 := {
  box := ⟨(3245/128), (6667/256)⟩
  a := (146846847802364886838234197249/5000000000000000000000000000000000)
  segments := [
    { box := ⟨(3245/128), (2560347/100000)⟩, pieceIndex := 23 },
    { box := ⟨(2560347/100000), (2597847/100000)⟩, pieceIndex := 24 },
    { box := ⟨(2597847/100000), (6667/256)⟩, pieceIndex := 25 }
  ]
}

def scalarCert18 : MacroScalarCert 56 := {
  box := ⟨(8083/256), (16579/512)⟩
  a := (167322041776912901830875682929/20000000000000000000000000000000000)
  segments := [
    { box := ⟨(8083/256), (6373527/200000)⟩, pieceIndex := 29 },
    { box := ⟨(6373527/200000), (6448527/200000)⟩, pieceIndex := 30 },
    { box := ⟨(6448527/200000), (16579/512)⟩, pieceIndex := 31 }
  ]
}

def scalarCert19 : MacroScalarCert 56 := {
  box := ⟨(3245/128), (13275/512)⟩
  a := (146846847802364886838234197249/5000000000000000000000000000000000)
  segments := [
    { box := ⟨(3245/128), (2560347/100000)⟩, pieceIndex := 23 },
    { box := ⟨(2560347/100000), (13275/512)⟩, pieceIndex := 24 }
  ]
}

def scalarCert20 : MacroScalarCert 56 := {
  box := ⟨(9735/512), (9971/512)⟩
  a := (5885158970114111451770320882689/1280000000000000000000000000000000000)
  segments := [
    { box := ⟨(9735/512), (19351747/1000000)⟩, pieceIndex := 17 },
    { box := ⟨(19351747/1000000), (9971/512)⟩, pieceIndex := 18 }
  ]
}

def scalarCert21 : MacroScalarCert 56 := {
  box := ⟨(12921/512), (413/16)⟩
  a := (9576976453294042395280846609/80000000000000000000000000000000000)
  segments := [
    { box := ⟨(12921/512), (2560347/100000)⟩, pieceIndex := 23 },
    { box := ⟨(2560347/100000), (413/16)⟩, pieceIndex := 24 }
  ]
}

def scalarCert22 : MacroScalarCert 56 := {
  box := ⟨(16225/512), (8319/256)⟩
  a := (3895225326904878308147162909841/80000000000000000000000000000000000)
  segments := [
    { box := ⟨(16225/512), (6373527/200000)⟩, pieceIndex := 29 },
    { box := ⟨(6373527/200000), (6448527/200000)⟩, pieceIndex := 30 },
    { box := ⟨(6448527/200000), (8319/256)⟩, pieceIndex := 31 }
  ]
}

def scalarCert23 : MacroScalarCert 56 := {
  box := ⟨(9735/512), (1239/64)⟩
  a := (5885158970114111451770320882689/1280000000000000000000000000000000000)
  segments := [
    { box := ⟨(9735/512), (19351747/1000000)⟩, pieceIndex := 17 },
    { box := ⟨(19351747/1000000), (1239/64)⟩, pieceIndex := 18 }
  ]
}

def scalarCert24 : MacroScalarCert 56 := {
  box := ⟨(13039/512), (6667/256)⟩
  a := (8807754158064216214287607996609/80000000000000000000000000000000000)
  segments := [
    { box := ⟨(13039/512), (2560347/100000)⟩, pieceIndex := 23 },
    { box := ⟨(2560347/100000), (2597847/100000)⟩, pieceIndex := 24 },
    { box := ⟨(2597847/100000), (6667/256)⟩, pieceIndex := 25 }
  ]
}

def scalarCert25 : MacroScalarCert 56 := {
  box := ⟨(4897/256), (5015/256)⟩
  a := (24983035225416475609781457263641/320000000000000000000000000000000000)
  segments := [
    { box := ⟨(4897/256), (19351747/1000000)⟩, pieceIndex := 17 },
    { box := ⟨(19351747/1000000), (5015/256)⟩, pieceIndex := 18 }
  ]
}

def scalarCert26 : MacroScalarCert 56 := {
  box := ⟨(6549/512), (3363/256)⟩
  a := (74120289942676230668914274104729/8000000000000000000000000000000000000)
  segments := [
    { box := ⟨(6549/512), (13130291/1000000)⟩, pieceIndex := 11 },
    { box := ⟨(13130291/1000000), (3363/256)⟩, pieceIndex := 12 }
  ]
}

def scalarCert27 : MacroScalarCert 56 := {
  box := ⟨(12921/512), (13157/512)⟩
  a := (9576976453294042395280846609/80000000000000000000000000000000000)
  segments := [
    { box := ⟨(12921/512), (2560347/100000)⟩, pieceIndex := 23 },
    { box := ⟨(2560347/100000), (13157/512)⟩, pieceIndex := 24 }
  ]
}

def scalarCert28 : MacroScalarCert 56 := {
  box := ⟨(16225/512), (16579/512)⟩
  a := (3895225326904878308147162909841/80000000000000000000000000000000000)
  segments := [
    { box := ⟨(16225/512), (6373527/200000)⟩, pieceIndex := 29 },
    { box := ⟨(6373527/200000), (6448527/200000)⟩, pieceIndex := 30 },
    { box := ⟨(6448527/200000), (16579/512)⟩, pieceIndex := 31 }
  ]
}

def scalarCert29 : MacroScalarCert 56 := {
  box := ⟨(3245/128), (413/16)⟩
  a := (146846847802364886838234197249/5000000000000000000000000000000000)
  segments := [
    { box := ⟨(3245/128), (2560347/100000)⟩, pieceIndex := 23 },
    { box := ⟨(2560347/100000), (413/16)⟩, pieceIndex := 24 }
  ]
}

def scalarCert30 : MacroScalarCert 56 := {
  box := ⟨(4071/128), (8319/256)⟩
  a := (611979482867143614802669851201/5000000000000000000000000000000000)
  segments := [
    { box := ⟨(4071/128), (6373527/200000)⟩, pieceIndex := 29 },
    { box := ⟨(6373527/200000), (6448527/200000)⟩, pieceIndex := 30 },
    { box := ⟨(6448527/200000), (8319/256)⟩, pieceIndex := 31 }
  ]
}

def scalarCert31 : MacroScalarCert 56 := {
  box := ⟨(4071/128), (16579/512)⟩
  a := (611979482867143614802669851201/5000000000000000000000000000000000)
  segments := [
    { box := ⟨(4071/128), (6373527/200000)⟩, pieceIndex := 29 },
    { box := ⟨(6373527/200000), (6448527/200000)⟩, pieceIndex := 30 },
    { box := ⟨(6448527/200000), (16579/512)⟩, pieceIndex := 31 }
  ]
}

def scalarCert32 : MacroScalarCert 56 := {
  box := ⟨(13039/512), (13275/512)⟩
  a := (8807754158064216214287607996609/80000000000000000000000000000000000)
  segments := [
    { box := ⟨(13039/512), (2560347/100000)⟩, pieceIndex := 23 },
    { box := ⟨(2560347/100000), (13275/512)⟩, pieceIndex := 24 }
  ]
}

def scalarCert33 : MacroScalarCert 56 := {
  box := ⟨(4897/256), (9971/512)⟩
  a := (24983035225416475609781457263641/320000000000000000000000000000000000)
  segments := [
    { box := ⟨(4897/256), (19351747/1000000)⟩, pieceIndex := 17 },
    { box := ⟨(19351747/1000000), (9971/512)⟩, pieceIndex := 18 }
  ]
}

def scalarCert34 : MacroScalarCert 56 := {
  box := ⟨(16343/512), (8319/256)⟩
  a := (19145944597030269950435668435441/80000000000000000000000000000000000)
  segments := [
    { box := ⟨(16343/512), (6448527/200000)⟩, pieceIndex := 30 },
    { box := ⟨(6448527/200000), (8319/256)⟩, pieceIndex := 31 }
  ]
}

def scalarCert35 : MacroScalarCert 56 := {
  box := ⟨(6549/256), (6667/256)⟩
  a := (4846047689033107029255715842121/20000000000000000000000000000000000)
  segments := [
    { box := ⟨(6549/256), (2560347/100000)⟩, pieceIndex := 23 },
    { box := ⟨(2560347/100000), (2597847/100000)⟩, pieceIndex := 24 },
    { box := ⟨(2597847/100000), (6667/256)⟩, pieceIndex := 25 }
  ]
}

def scalarCert36 : MacroScalarCert 56 := {
  box := ⟨(9853/512), (5015/256)⟩
  a := (308609266148826216472188856757689/1280000000000000000000000000000000000)
  segments := [
    { box := ⟨(9853/512), (19351747/1000000)⟩, pieceIndex := 17 },
    { box := ⟨(19351747/1000000), (5015/256)⟩, pieceIndex := 18 }
  ]
}

def scalarCert37 : MacroScalarCert 56 := {
  box := ⟨(413/32), (3363/256)⟩
  a := (20678976077282851379745931419361/125000000000000000000000000000000000)
  segments := [
    { box := ⟨(413/32), (13130291/1000000)⟩, pieceIndex := 11 },
    { box := ⟨(13130291/1000000), (3363/256)⟩, pieceIndex := 12 }
  ]
}

def scalarCert38 : MacroScalarCert 56 := {
  box := ⟨(8083/256), (4189/128)⟩
  a := (167322041776912901830875682929/20000000000000000000000000000000000)
  segments := [
    { box := ⟨(8083/256), (6373527/200000)⟩, pieceIndex := 29 },
    { box := ⟨(6373527/200000), (6448527/200000)⟩, pieceIndex := 30 },
    { box := ⟨(6448527/200000), (4189/128)⟩, pieceIndex := 31 }
  ]
}

def scalarCert39 : MacroScalarCert 56 := {
  box := ⟨(3245/128), (3363/128)⟩
  a := (146846847802364886838234197249/5000000000000000000000000000000000)
  segments := [
    { box := ⟨(3245/128), (2560347/100000)⟩, pieceIndex := 23 },
    { box := ⟨(2560347/100000), (2597847/100000)⟩, pieceIndex := 24 },
    { box := ⟨(2597847/100000), (3363/128)⟩, pieceIndex := 25 }
  ]
}

def scalarCert40 : MacroScalarCert 56 := {
  box := ⟨(4897/256), (2537/128)⟩
  a := (24983035225416475609781457263641/320000000000000000000000000000000000)
  segments := [
    { box := ⟨(4897/256), (19351747/1000000)⟩, pieceIndex := 17 },
    { box := ⟨(19351747/1000000), (19726747/1000000)⟩, pieceIndex := 18 },
    { box := ⟨(19726747/1000000), (2537/128)⟩, pieceIndex := 19 }
  ]
}

def scalarCert41 : MacroScalarCert 56 := {
  box := ⟨(413/32), (1711/128)⟩
  a := (20678976077282851379745931419361/125000000000000000000000000000000000)
  segments := [
    { box := ⟨(413/32), (13130291/1000000)⟩, pieceIndex := 11 },
    { box := ⟨(13130291/1000000), (1711/128)⟩, pieceIndex := 12 }
  ]
}

def scalarCert42 : MacroScalarCert 56 := {
  box := ⟨(8083/256), (16697/512)⟩
  a := (167322041776912901830875682929/20000000000000000000000000000000000)
  segments := [
    { box := ⟨(8083/256), (6373527/200000)⟩, pieceIndex := 29 },
    { box := ⟨(6373527/200000), (6448527/200000)⟩, pieceIndex := 30 },
    { box := ⟨(6448527/200000), (16697/512)⟩, pieceIndex := 31 }
  ]
}

def scalarCert43 : MacroScalarCert 56 := {
  box := ⟨(3245/128), (13393/512)⟩
  a := (146846847802364886838234197249/5000000000000000000000000000000000)
  segments := [
    { box := ⟨(3245/128), (2560347/100000)⟩, pieceIndex := 23 },
    { box := ⟨(2560347/100000), (2597847/100000)⟩, pieceIndex := 24 },
    { box := ⟨(2597847/100000), (13393/512)⟩, pieceIndex := 25 }
  ]
}

def scalarCert44 : MacroScalarCert 56 := {
  box := ⟨(4897/256), (10089/512)⟩
  a := (24983035225416475609781457263641/320000000000000000000000000000000000)
  segments := [
    { box := ⟨(4897/256), (19351747/1000000)⟩, pieceIndex := 17 },
    { box := ⟨(19351747/1000000), (10089/512)⟩, pieceIndex := 18 }
  ]
}

def scalarCert45 : MacroScalarCert 56 := {
  box := ⟨(16225/512), (4189/128)⟩
  a := (3895225326904878308147162909841/80000000000000000000000000000000000)
  segments := [
    { box := ⟨(16225/512), (6373527/200000)⟩, pieceIndex := 29 },
    { box := ⟨(6373527/200000), (6448527/200000)⟩, pieceIndex := 30 },
    { box := ⟨(6448527/200000), (4189/128)⟩, pieceIndex := 31 }
  ]
}

def scalarCert46 : MacroScalarCert 56 := {
  box := ⟨(13039/512), (3363/128)⟩
  a := (8807754158064216214287607996609/80000000000000000000000000000000000)
  segments := [
    { box := ⟨(13039/512), (2560347/100000)⟩, pieceIndex := 23 },
    { box := ⟨(2560347/100000), (2597847/100000)⟩, pieceIndex := 24 },
    { box := ⟨(2597847/100000), (3363/128)⟩, pieceIndex := 25 }
  ]
}

def scalarCert47 : MacroScalarCert 56 := {
  box := ⟨(9853/512), (2537/128)⟩
  a := (308609266148826216472188856757689/1280000000000000000000000000000000000)
  segments := [
    { box := ⟨(9853/512), (19351747/1000000)⟩, pieceIndex := 17 },
    { box := ⟨(19351747/1000000), (19726747/1000000)⟩, pieceIndex := 18 },
    { box := ⟨(19726747/1000000), (2537/128)⟩, pieceIndex := 19 }
  ]
}

def scalarCert48 : MacroScalarCert 56 := {
  box := ⟨(16225/512), (16697/512)⟩
  a := (3895225326904878308147162909841/80000000000000000000000000000000000)
  segments := [
    { box := ⟨(16225/512), (6373527/200000)⟩, pieceIndex := 29 },
    { box := ⟨(6373527/200000), (6448527/200000)⟩, pieceIndex := 30 },
    { box := ⟨(6448527/200000), (16697/512)⟩, pieceIndex := 31 }
  ]
}

def scalarCert49 : MacroScalarCert 56 := {
  box := ⟨(13039/512), (13393/512)⟩
  a := (8807754158064216214287607996609/80000000000000000000000000000000000)
  segments := [
    { box := ⟨(13039/512), (2560347/100000)⟩, pieceIndex := 23 },
    { box := ⟨(2560347/100000), (2597847/100000)⟩, pieceIndex := 24 },
    { box := ⟨(2597847/100000), (13393/512)⟩, pieceIndex := 25 }
  ]
}

def scalarCert50 : MacroScalarCert 56 := {
  box := ⟨(4071/128), (4189/128)⟩
  a := (611979482867143614802669851201/5000000000000000000000000000000000)
  segments := [
    { box := ⟨(4071/128), (6373527/200000)⟩, pieceIndex := 29 },
    { box := ⟨(6373527/200000), (6448527/200000)⟩, pieceIndex := 30 },
    { box := ⟨(6448527/200000), (4189/128)⟩, pieceIndex := 31 }
  ]
}

def scalarCert51 : MacroScalarCert 56 := {
  box := ⟨(6549/256), (3363/128)⟩
  a := (4846047689033107029255715842121/20000000000000000000000000000000000)
  segments := [
    { box := ⟨(6549/256), (2560347/100000)⟩, pieceIndex := 23 },
    { box := ⟨(2560347/100000), (2597847/100000)⟩, pieceIndex := 24 },
    { box := ⟨(2597847/100000), (3363/128)⟩, pieceIndex := 25 }
  ]
}

def scalarCert52 : MacroScalarCert 56 := {
  box := ⟨(413/32), (885/64)⟩
  a := (20678976077282851379745931419361/125000000000000000000000000000000000)
  segments := [
    { box := ⟨(413/32), (13130291/1000000)⟩, pieceIndex := 11 },
    { box := ⟨(13130291/1000000), (13505291/1000000)⟩, pieceIndex := 12 },
    { box := ⟨(13505291/1000000), (885/64)⟩, pieceIndex := 13 }
  ]
}

def scalarCert53 : MacroScalarCert 56 := {
  box := ⟨(885/128), (59/8)⟩
  a := (228930241058556007916075349120001/125000000000000000000000000000000000)
  segments := [
    { box := ⟨(885/128), (1754519/250000)⟩, pieceIndex := 5 },
    { box := ⟨(1754519/250000), (59/8)⟩, pieceIndex := 6 }
  ]
}

def scalarCert54 : MacroScalarCert 56 := {
  box := ⟨(413/32), (6785/512)⟩
  a := (20678976077282851379745931419361/125000000000000000000000000000000000)
  segments := [
    { box := ⟨(413/32), (13130291/1000000)⟩, pieceIndex := 11 },
    { box := ⟨(13130291/1000000), (6785/512)⟩, pieceIndex := 12 }
  ]
}

def scalarCert55 : MacroScalarCert 56 := {
  box := ⟨(9853/512), (10089/512)⟩
  a := (308609266148826216472188856757689/1280000000000000000000000000000000000)
  segments := [
    { box := ⟨(9853/512), (19351747/1000000)⟩, pieceIndex := 17 },
    { box := ⟨(19351747/1000000), (10089/512)⟩, pieceIndex := 18 }
  ]
}

def scalarCert56 : MacroScalarCert 56 := {
  box := ⟨(6667/512), (1711/128)⟩
  a := (4115134404786270922924483404604729/8000000000000000000000000000000000000)
  segments := [
    { box := ⟨(6667/512), (13130291/1000000)⟩, pieceIndex := 11 },
    { box := ⟨(13130291/1000000), (1711/128)⟩, pieceIndex := 12 }
  ]
}

def scalarCert57 : MacroScalarCert 56 := {
  box := ⟨(1239/64), (2537/128)⟩
  a := (676206949938427113180992093521/1250000000000000000000000000000000)
  segments := [
    { box := ⟨(1239/64), (19726747/1000000)⟩, pieceIndex := 18 },
    { box := ⟨(19726747/1000000), (2537/128)⟩, pieceIndex := 19 }
  ]
}

def scalarCert58 : MacroScalarCert 56 := {
  box := ⟨(8083/256), (531/16)⟩
  a := (167322041776912901830875682929/20000000000000000000000000000000000)
  segments := [
    { box := ⟨(8083/256), (6373527/200000)⟩, pieceIndex := 29 },
    { box := ⟨(6373527/200000), (6448527/200000)⟩, pieceIndex := 30 },
    { box := ⟨(6448527/200000), (531/16)⟩, pieceIndex := 31 }
  ]
}

def scalarCert59 : MacroScalarCert 56 := {
  box := ⟨(8083/256), (8437/256)⟩
  a := (167322041776912901830875682929/20000000000000000000000000000000000)
  segments := [
    { box := ⟨(8083/256), (6373527/200000)⟩, pieceIndex := 29 },
    { box := ⟨(6373527/200000), (6448527/200000)⟩, pieceIndex := 30 },
    { box := ⟨(6448527/200000), (8437/256)⟩, pieceIndex := 31 }
  ]
}

def scalarCert60 : MacroScalarCert 56 := {
  box := ⟨(4071/128), (16697/512)⟩
  a := (611979482867143614802669851201/5000000000000000000000000000000000)
  segments := [
    { box := ⟨(4071/128), (6373527/200000)⟩, pieceIndex := 29 },
    { box := ⟨(6373527/200000), (6448527/200000)⟩, pieceIndex := 30 },
    { box := ⟨(6448527/200000), (16697/512)⟩, pieceIndex := 31 }
  ]
}

def scalarCert61 : MacroScalarCert 56 := {
  box := ⟨(16343/512), (4189/128)⟩
  a := (19145944597030269950435668435441/80000000000000000000000000000000000)
  segments := [
    { box := ⟨(16343/512), (6448527/200000)⟩, pieceIndex := 30 },
    { box := ⟨(6448527/200000), (4189/128)⟩, pieceIndex := 31 }
  ]
}

def scalarCert62 : MacroScalarCert 56 := {
  box := ⟨(16343/512), (16697/512)⟩
  a := (19145944597030269950435668435441/80000000000000000000000000000000000)
  segments := [
    { box := ⟨(16343/512), (6448527/200000)⟩, pieceIndex := 30 },
    { box := ⟨(6448527/200000), (16697/512)⟩, pieceIndex := 31 }
  ]
}

def scalarCert63 : MacroScalarCert 56 := {
  box := ⟨(8201/256), (16697/512)⟩
  a := (7402913802521846133201894614329/20000000000000000000000000000000000)
  segments := [
    { box := ⟨(8201/256), (6448527/200000)⟩, pieceIndex := 30 },
    { box := ⟨(6448527/200000), (16697/512)⟩, pieceIndex := 31 }
  ]
}

def scalarCert64 : MacroScalarCert 56 := {
  box := ⟨(8201/256), (4189/128)⟩
  a := (7402913802521846133201894614329/20000000000000000000000000000000000)
  segments := [
    { box := ⟨(8201/256), (6448527/200000)⟩, pieceIndex := 30 },
    { box := ⟨(6448527/200000), (4189/128)⟩, pieceIndex := 31 }
  ]
}

def scalarCert65 : MacroScalarCert 56 := {
  box := ⟨(16461/512), (4189/128)⟩
  a := (104124691/250000000000)
  segments := [
    { box := ⟨(16461/512), (6448527/200000)⟩, pieceIndex := 30 },
    { box := ⟨(6448527/200000), (4189/128)⟩, pieceIndex := 31 }
  ]
}

def scalarCert66 : MacroScalarCert 56 := {
  box := ⟨(9853/512), (20001/1024)⟩
  a := (308609266148826216472188856757689/1280000000000000000000000000000000000)
  segments := [
    { box := ⟨(9853/512), (19351747/1000000)⟩, pieceIndex := 17 },
    { box := ⟨(19351747/1000000), (20001/1024)⟩, pieceIndex := 18 }
  ]
}

def scalarCert67 : MacroScalarCert 56 := {
  box := ⟨(6549/256), (26609/1024)⟩
  a := (4846047689033107029255715842121/20000000000000000000000000000000000)
  segments := [
    { box := ⟨(6549/256), (2560347/100000)⟩, pieceIndex := 23 },
    { box := ⟨(2560347/100000), (2597847/100000)⟩, pieceIndex := 24 },
    { box := ⟨(2597847/100000), (26609/1024)⟩, pieceIndex := 25 }
  ]
}

def scalarCert68 : MacroScalarCert 56 := {
  box := ⟨(16461/512), (33453/1024)⟩
  a := (104124691/250000000000)
  segments := [
    { box := ⟨(16461/512), (6448527/200000)⟩, pieceIndex := 30 },
    { box := ⟨(6448527/200000), (33453/1024)⟩, pieceIndex := 31 }
  ]
}

def scalarCert69 : MacroScalarCert 56 := {
  box := ⟨(19765/1024), (5015/256)⟩
  a := (1823736530063038278523442761733881/5120000000000000000000000000000000000)
  segments := [
    { box := ⟨(19765/1024), (19351747/1000000)⟩, pieceIndex := 17 },
    { box := ⟨(19351747/1000000), (5015/256)⟩, pieceIndex := 18 }
  ]
}

def scalarCert70 : MacroScalarCert 56 := {
  box := ⟨(26255/1024), (6667/256)⟩
  a := (4444557066199270754582755713921/12800000000000000000000000000000000)
  segments := [
    { box := ⟨(26255/1024), (2597847/100000)⟩, pieceIndex := 24 },
    { box := ⟨(2597847/100000), (6667/256)⟩, pieceIndex := 25 }
  ]
}

def scalarCert71 : MacroScalarCert 56 := {
  box := ⟨(32981/1024), (4189/128)⟩
  a := (104124691/250000000000)
  segments := [
    { box := ⟨(32981/1024), (6448527/200000)⟩, pieceIndex := 30 },
    { box := ⟨(6448527/200000), (4189/128)⟩, pieceIndex := 31 }
  ]
}

def scalarCert72 : MacroScalarCert 56 := {
  box := ⟨(19529/1024), (1239/64)⟩
  a := (154319528085755766258938540108881/5120000000000000000000000000000000000)
  segments := [
    { box := ⟨(19529/1024), (19351747/1000000)⟩, pieceIndex := 17 },
    { box := ⟨(19351747/1000000), (1239/64)⟩, pieceIndex := 18 }
  ]
}

def scalarCert73 : MacroScalarCert 56 := {
  box := ⟨(4071/128), (8437/256)⟩
  a := (611979482867143614802669851201/5000000000000000000000000000000000)
  segments := [
    { box := ⟨(4071/128), (6373527/200000)⟩, pieceIndex := 29 },
    { box := ⟨(6373527/200000), (6448527/200000)⟩, pieceIndex := 30 },
    { box := ⟨(6448527/200000), (8437/256)⟩, pieceIndex := 31 }
  ]
}

def scalarCert74 : MacroScalarCert 56 := {
  box := ⟨(4071/128), (16815/512)⟩
  a := (611979482867143614802669851201/5000000000000000000000000000000000)
  segments := [
    { box := ⟨(4071/128), (6373527/200000)⟩, pieceIndex := 29 },
    { box := ⟨(6373527/200000), (6448527/200000)⟩, pieceIndex := 30 },
    { box := ⟨(6448527/200000), (16815/512)⟩, pieceIndex := 31 }
  ]
}

def scalarCert75 : MacroScalarCert 56 := {
  box := ⟨(16343/512), (8437/256)⟩
  a := (19145944597030269950435668435441/80000000000000000000000000000000000)
  segments := [
    { box := ⟨(16343/512), (6448527/200000)⟩, pieceIndex := 30 },
    { box := ⟨(6448527/200000), (8437/256)⟩, pieceIndex := 31 }
  ]
}

def scalarCert76 : MacroScalarCert 56 := {
  box := ⟨(16343/512), (16815/512)⟩
  a := (19145944597030269950435668435441/80000000000000000000000000000000000)
  segments := [
    { box := ⟨(16343/512), (6448527/200000)⟩, pieceIndex := 30 },
    { box := ⟨(6448527/200000), (16815/512)⟩, pieceIndex := 31 }
  ]
}

def scalarCert77 : MacroScalarCert 56 := {
  box := ⟨(8201/256), (8437/256)⟩
  a := (7402913802521846133201894614329/20000000000000000000000000000000000)
  segments := [
    { box := ⟨(8201/256), (6448527/200000)⟩, pieceIndex := 30 },
    { box := ⟨(6448527/200000), (8437/256)⟩, pieceIndex := 31 }
  ]
}

def scalarCert78 : MacroScalarCert 56 := {
  box := ⟨(8201/256), (16815/512)⟩
  a := (7402913802521846133201894614329/20000000000000000000000000000000000)
  segments := [
    { box := ⟨(8201/256), (6448527/200000)⟩, pieceIndex := 30 },
    { box := ⟨(6448527/200000), (16815/512)⟩, pieceIndex := 31 }
  ]
}

def scalarCert79 : MacroScalarCert 56 := {
  box := ⟨(6549/256), (13393/512)⟩
  a := (4846047689033107029255715842121/20000000000000000000000000000000000)
  segments := [
    { box := ⟨(6549/256), (2560347/100000)⟩, pieceIndex := 23 },
    { box := ⟨(2560347/100000), (2597847/100000)⟩, pieceIndex := 24 },
    { box := ⟨(2597847/100000), (13393/512)⟩, pieceIndex := 25 }
  ]
}

def scalarCert80 : MacroScalarCert 56 := {
  box := ⟨(16461/512), (8437/256)⟩
  a := (104124691/250000000000)
  segments := [
    { box := ⟨(16461/512), (6448527/200000)⟩, pieceIndex := 30 },
    { box := ⟨(6448527/200000), (8437/256)⟩, pieceIndex := 31 }
  ]
}

def scalarCert81 : MacroScalarCert 56 := {
  box := ⟨(13157/512), (3363/128)⟩
  a := (1405713487152099986076881071449/3200000000000000000000000000000000)
  segments := [
    { box := ⟨(13157/512), (2597847/100000)⟩, pieceIndex := 24 },
    { box := ⟨(2597847/100000), (3363/128)⟩, pieceIndex := 25 }
  ]
}

def scalarCert82 : MacroScalarCert 56 := {
  box := ⟨(4071/128), (531/16)⟩
  a := (611979482867143614802669851201/5000000000000000000000000000000000)
  segments := [
    { box := ⟨(4071/128), (6373527/200000)⟩, pieceIndex := 29 },
    { box := ⟨(6373527/200000), (6448527/200000)⟩, pieceIndex := 30 },
    { box := ⟨(6448527/200000), (531/16)⟩, pieceIndex := 31 }
  ]
}

def scalarCert83 : MacroScalarCert 56 := {
  box := ⟨(8201/256), (531/16)⟩
  a := (7402913802521846133201894614329/20000000000000000000000000000000000)
  segments := [
    { box := ⟨(8201/256), (6448527/200000)⟩, pieceIndex := 30 },
    { box := ⟨(6448527/200000), (531/16)⟩, pieceIndex := 31 }
  ]
}

def scalarCert84 : MacroScalarCert 56 := {
  box := ⟨(8201/256), (16933/512)⟩
  a := (7402913802521846133201894614329/20000000000000000000000000000000000)
  segments := [
    { box := ⟨(8201/256), (6448527/200000)⟩, pieceIndex := 30 },
    { box := ⟨(6448527/200000), (16933/512)⟩, pieceIndex := 31 }
  ]
}

def scalarCert85 : MacroScalarCert 56 := {
  box := ⟨(16461/512), (531/16)⟩
  a := (104124691/250000000000)
  segments := [
    { box := ⟨(16461/512), (6448527/200000)⟩, pieceIndex := 30 },
    { box := ⟨(6448527/200000), (531/16)⟩, pieceIndex := 31 }
  ]
}

def scalarCert86 : MacroScalarCert 56 := {
  box := ⟨(16461/512), (16933/512)⟩
  a := (104124691/250000000000)
  segments := [
    { box := ⟨(16461/512), (6448527/200000)⟩, pieceIndex := 30 },
    { box := ⟨(6448527/200000), (16933/512)⟩, pieceIndex := 31 }
  ]
}

def scalarCert87 : MacroScalarCert 56 := {
  box := ⟨(8083/256), (4307/128)⟩
  a := (167322041776912901830875682929/20000000000000000000000000000000000)
  segments := [
    { box := ⟨(8083/256), (6373527/200000)⟩, pieceIndex := 29 },
    { box := ⟨(6373527/200000), (6448527/200000)⟩, pieceIndex := 30 },
    { box := ⟨(6448527/200000), (4307/128)⟩, pieceIndex := 31 }
  ]
}

def scalarCert88 : MacroScalarCert 56 := {
  box := ⟨(4897/256), (649/32)⟩
  a := (24983035225416475609781457263641/320000000000000000000000000000000000)
  segments := [
    { box := ⟨(4897/256), (19351747/1000000)⟩, pieceIndex := 17 },
    { box := ⟨(19351747/1000000), (19726747/1000000)⟩, pieceIndex := 18 },
    { box := ⟨(19726747/1000000), (649/32)⟩, pieceIndex := 19 }
  ]
}

def scalarCert89 : MacroScalarCert 56 := {
  box := ⟨(4071/128), (2183/64)⟩
  a := (611979482867143614802669851201/5000000000000000000000000000000000)
  segments := [
    { box := ⟨(4071/128), (6373527/200000)⟩, pieceIndex := 29 },
    { box := ⟨(6373527/200000), (6448527/200000)⟩, pieceIndex := 30 },
    { box := ⟨(6448527/200000), (2183/64)⟩, pieceIndex := 31 }
  ]
}

def scalarCert90 : MacroScalarCert 56 := {
  box := ⟨(413/32), (59/4)⟩
  a := (20678976077282851379745931419361/125000000000000000000000000000000000)
  segments := [
    { box := ⟨(413/32), (13130291/1000000)⟩, pieceIndex := 11 },
    { box := ⟨(13130291/1000000), (13505291/1000000)⟩, pieceIndex := 12 },
    { box := ⟨(13505291/1000000), (59/4)⟩, pieceIndex := 13 }
  ]
}

def scalarCert91 : MacroScalarCert 56 := {
  box := ⟨(413/32), (1829/128)⟩
  a := (20678976077282851379745931419361/125000000000000000000000000000000000)
  segments := [
    { box := ⟨(413/32), (13130291/1000000)⟩, pieceIndex := 11 },
    { box := ⟨(13130291/1000000), (13505291/1000000)⟩, pieceIndex := 12 },
    { box := ⟨(13505291/1000000), (1829/128)⟩, pieceIndex := 13 }
  ]
}

def scalarCert92 : MacroScalarCert 56 := {
  box := ⟨(3245/128), (1711/64)⟩
  a := (146846847802364886838234197249/5000000000000000000000000000000000)
  segments := [
    { box := ⟨(3245/128), (2560347/100000)⟩, pieceIndex := 23 },
    { box := ⟨(2560347/100000), (2597847/100000)⟩, pieceIndex := 24 },
    { box := ⟨(2597847/100000), (1711/64)⟩, pieceIndex := 25 }
  ]
}

def scalarCert93 : MacroScalarCert 56 := {
  box := ⟨(3245/128), (6785/256)⟩
  a := (146846847802364886838234197249/5000000000000000000000000000000000)
  segments := [
    { box := ⟨(3245/128), (2560347/100000)⟩, pieceIndex := 23 },
    { box := ⟨(2560347/100000), (2597847/100000)⟩, pieceIndex := 24 },
    { box := ⟨(2597847/100000), (6785/256)⟩, pieceIndex := 25 }
  ]
}

def scalarCert94 : MacroScalarCert 56 := {
  box := ⟨(4897/256), (5133/256)⟩
  a := (24983035225416475609781457263641/320000000000000000000000000000000000)
  segments := [
    { box := ⟨(4897/256), (19351747/1000000)⟩, pieceIndex := 17 },
    { box := ⟨(19351747/1000000), (19726747/1000000)⟩, pieceIndex := 18 },
    { box := ⟨(19726747/1000000), (5133/256)⟩, pieceIndex := 19 }
  ]
}

def scalarCert95 : MacroScalarCert 56 := {
  box := ⟨(413/32), (3481/256)⟩
  a := (20678976077282851379745931419361/125000000000000000000000000000000000)
  segments := [
    { box := ⟨(413/32), (13130291/1000000)⟩, pieceIndex := 11 },
    { box := ⟨(13130291/1000000), (13505291/1000000)⟩, pieceIndex := 12 },
    { box := ⟨(13505291/1000000), (3481/256)⟩, pieceIndex := 13 }
  ]
}

def scalarCert96 : MacroScalarCert 56 := {
  box := ⟨(13157/512), (13393/512)⟩
  a := (1405713487152099986076881071449/3200000000000000000000000000000000)
  segments := [
    { box := ⟨(13157/512), (2597847/100000)⟩, pieceIndex := 24 },
    { box := ⟨(2597847/100000), (13393/512)⟩, pieceIndex := 25 }
  ]
}

def scalarCert97 : MacroScalarCert 56 := {
  box := ⟨(6667/512), (6785/512)⟩
  a := (4115134404786270922924483404604729/8000000000000000000000000000000000000)
  segments := [
    { box := ⟨(6667/512), (13130291/1000000)⟩, pieceIndex := 11 },
    { box := ⟨(13130291/1000000), (6785/512)⟩, pieceIndex := 12 }
  ]
}

def scalarCert98 : MacroScalarCert 56 := {
  box := ⟨(6549/256), (6785/256)⟩
  a := (4846047689033107029255715842121/20000000000000000000000000000000000)
  segments := [
    { box := ⟨(6549/256), (2560347/100000)⟩, pieceIndex := 23 },
    { box := ⟨(2560347/100000), (2597847/100000)⟩, pieceIndex := 24 },
    { box := ⟨(2597847/100000), (6785/256)⟩, pieceIndex := 25 }
  ]
}

def scalarCert99 : MacroScalarCert 56 := {
  box := ⟨(1239/64), (5133/256)⟩
  a := (676206949938427113180992093521/1250000000000000000000000000000000)
  segments := [
    { box := ⟨(1239/64), (19726747/1000000)⟩, pieceIndex := 18 },
    { box := ⟨(19726747/1000000), (5133/256)⟩, pieceIndex := 19 }
  ]
}

def scalarCert100 : MacroScalarCert 56 := {
  box := ⟨(3363/256), (3481/256)⟩
  a := (9644871623714213790537153110875761/8000000000000000000000000000000000000)
  segments := [
    { box := ⟨(3363/256), (13505291/1000000)⟩, pieceIndex := 12 },
    { box := ⟨(13505291/1000000), (3481/256)⟩, pieceIndex := 13 }
  ]
}

def scalarCert101 : MacroScalarCert 56 := {
  box := ⟨(6549/256), (1711/64)⟩
  a := (4846047689033107029255715842121/20000000000000000000000000000000000)
  segments := [
    { box := ⟨(6549/256), (2560347/100000)⟩, pieceIndex := 23 },
    { box := ⟨(2560347/100000), (2597847/100000)⟩, pieceIndex := 24 },
    { box := ⟨(2597847/100000), (1711/64)⟩, pieceIndex := 25 }
  ]
}

def scalarCert102 : MacroScalarCert 56 := {
  box := ⟨(1239/64), (649/32)⟩
  a := (676206949938427113180992093521/1250000000000000000000000000000000)
  segments := [
    { box := ⟨(1239/64), (19726747/1000000)⟩, pieceIndex := 18 },
    { box := ⟨(19726747/1000000), (649/32)⟩, pieceIndex := 19 }
  ]
}

def scalarCert103 : MacroScalarCert 56 := {
  box := ⟨(3363/256), (885/64)⟩
  a := (9644871623714213790537153110875761/8000000000000000000000000000000000000)
  segments := [
    { box := ⟨(3363/256), (13505291/1000000)⟩, pieceIndex := 12 },
    { box := ⟨(13505291/1000000), (885/64)⟩, pieceIndex := 13 }
  ]
}

def scalarCert104 : MacroScalarCert 56 := {
  box := ⟨(3245/128), (3481/128)⟩
  a := (146846847802364886838234197249/5000000000000000000000000000000000)
  segments := [
    { box := ⟨(3245/128), (2560347/100000)⟩, pieceIndex := 23 },
    { box := ⟨(2560347/100000), (2597847/100000)⟩, pieceIndex := 24 },
    { box := ⟨(2597847/100000), (3481/128)⟩, pieceIndex := 25 }
  ]
}

def scalarCert105 : MacroScalarCert 56 := {
  box := ⟨(1239/64), (2655/128)⟩
  a := (676206949938427113180992093521/1250000000000000000000000000000000)
  segments := [
    { box := ⟨(1239/64), (19726747/1000000)⟩, pieceIndex := 18 },
    { box := ⟨(19726747/1000000), (2655/128)⟩, pieceIndex := 19 }
  ]
}

def scalarCert106 : MacroScalarCert 56 := {
  box := ⟨(1711/128), (1829/128)⟩
  a := (1610977803/1000000000000)
  segments := [
    { box := ⟨(1711/128), (13505291/1000000)⟩, pieceIndex := 12 },
    { box := ⟨(13505291/1000000), (1829/128)⟩, pieceIndex := 13 }
  ]
}

def scalarCert107 : MacroScalarCert 56 := {
  box := ⟨(3245/128), (885/32)⟩
  a := (146846847802364886838234197249/5000000000000000000000000000000000)
  segments := [
    { box := ⟨(3245/128), (2560347/100000)⟩, pieceIndex := 23 },
    { box := ⟨(2560347/100000), (2597847/100000)⟩, pieceIndex := 24 },
    { box := ⟨(2597847/100000), (885/32)⟩, pieceIndex := 25 }
  ]
}

def scalarCert108 : MacroScalarCert 56 := {
  box := ⟨(1239/64), (1357/64)⟩
  a := (676206949938427113180992093521/1250000000000000000000000000000000)
  segments := [
    { box := ⟨(1239/64), (19726747/1000000)⟩, pieceIndex := 18 },
    { box := ⟨(19726747/1000000), (1357/64)⟩, pieceIndex := 19 }
  ]
}

def scalarCert109 : MacroScalarCert 56 := {
  box := ⟨(1711/128), (59/4)⟩
  a := (1610977803/1000000000000)
  segments := [
    { box := ⟨(1711/128), (13505291/1000000)⟩, pieceIndex := 12 },
    { box := ⟨(13505291/1000000), (59/4)⟩, pieceIndex := 13 }
  ]
}

def scalarCert110 : MacroScalarCert 56 := {
  box := ⟨(413/16), (3363/128)⟩
  a := (148698801/250000000000)
  segments := [
    { box := ⟨(413/16), (2597847/100000)⟩, pieceIndex := 24 },
    { box := ⟨(2597847/100000), (3363/128)⟩, pieceIndex := 25 }
  ]
}

def scalarCert111 : MacroScalarCert 56 := {
  box := ⟨(6549/256), (13511/512)⟩
  a := (4846047689033107029255715842121/20000000000000000000000000000000000)
  segments := [
    { box := ⟨(6549/256), (2560347/100000)⟩, pieceIndex := 23 },
    { box := ⟨(2560347/100000), (2597847/100000)⟩, pieceIndex := 24 },
    { box := ⟨(2597847/100000), (13511/512)⟩, pieceIndex := 25 }
  ]
}

def scalarCert112 : MacroScalarCert 56 := {
  box := ⟨(13157/512), (6785/256)⟩
  a := (1405713487152099986076881071449/3200000000000000000000000000000000)
  segments := [
    { box := ⟨(13157/512), (2597847/100000)⟩, pieceIndex := 24 },
    { box := ⟨(2597847/100000), (6785/256)⟩, pieceIndex := 25 }
  ]
}

def scalarCert113 : MacroScalarCert 56 := {
  box := ⟨(13157/512), (13511/512)⟩
  a := (1405713487152099986076881071449/3200000000000000000000000000000000)
  segments := [
    { box := ⟨(13157/512), (2597847/100000)⟩, pieceIndex := 24 },
    { box := ⟨(2597847/100000), (13511/512)⟩, pieceIndex := 25 }
  ]
}

def scalarCert114 : MacroScalarCert 56 := {
  box := ⟨(413/16), (6785/256)⟩
  a := (148698801/250000000000)
  segments := [
    { box := ⟨(413/16), (2597847/100000)⟩, pieceIndex := 24 },
    { box := ⟨(2597847/100000), (6785/256)⟩, pieceIndex := 25 }
  ]
}

def scalarCert115 : MacroScalarCert 56 := {
  box := ⟨(413/16), (1711/64)⟩
  a := (148698801/250000000000)
  segments := [
    { box := ⟨(413/16), (2597847/100000)⟩, pieceIndex := 24 },
    { box := ⟨(2597847/100000), (1711/64)⟩, pieceIndex := 25 }
  ]
}

def scalarCert116 : MacroScalarCert 56 := {
  box := ⟨(413/16), (13629/512)⟩
  a := (148698801/250000000000)
  segments := [
    { box := ⟨(413/16), (2597847/100000)⟩, pieceIndex := 24 },
    { box := ⟨(2597847/100000), (13629/512)⟩, pieceIndex := 25 }
  ]
}

def scalarCert117 : MacroScalarCert 56 := {
  box := ⟨(13275/512), (1711/64)⟩
  a := (148698801/250000000000)
  segments := [
    { box := ⟨(13275/512), (2597847/100000)⟩, pieceIndex := 24 },
    { box := ⟨(2597847/100000), (1711/64)⟩, pieceIndex := 25 }
  ]
}

def scalarCert118 : MacroScalarCert 56 := {
  box := ⟨(3245/128), (6903/256)⟩
  a := (146846847802364886838234197249/5000000000000000000000000000000000)
  segments := [
    { box := ⟨(3245/128), (2560347/100000)⟩, pieceIndex := 23 },
    { box := ⟨(2560347/100000), (2597847/100000)⟩, pieceIndex := 24 },
    { box := ⟨(2597847/100000), (6903/256)⟩, pieceIndex := 25 }
  ]
}

def scalarCert119 : MacroScalarCert 56 := {
  box := ⟨(6549/256), (3481/128)⟩
  a := (4846047689033107029255715842121/20000000000000000000000000000000000)
  segments := [
    { box := ⟨(6549/256), (2560347/100000)⟩, pieceIndex := 23 },
    { box := ⟨(2560347/100000), (2597847/100000)⟩, pieceIndex := 24 },
    { box := ⟨(2597847/100000), (3481/128)⟩, pieceIndex := 25 }
  ]
}

def scalarCert120 : MacroScalarCert 56 := {
  box := ⟨(413/16), (885/32)⟩
  a := (148698801/250000000000)
  segments := [
    { box := ⟨(413/16), (2597847/100000)⟩, pieceIndex := 24 },
    { box := ⟨(2597847/100000), (885/32)⟩, pieceIndex := 25 }
  ]
}

def scalarCert121 : MacroScalarCert 56 := {
  box := ⟨(8083/256), (8555/256)⟩
  a := (167322041776912901830875682929/20000000000000000000000000000000000)
  segments := [
    { box := ⟨(8083/256), (6373527/200000)⟩, pieceIndex := 29 },
    { box := ⟨(6373527/200000), (6448527/200000)⟩, pieceIndex := 30 },
    { box := ⟨(6448527/200000), (8555/256)⟩, pieceIndex := 31 }
  ]
}

def scalarCert122 : MacroScalarCert 56 := {
  box := ⟨(4071/128), (4307/128)⟩
  a := (611979482867143614802669851201/5000000000000000000000000000000000)
  segments := [
    { box := ⟨(4071/128), (6373527/200000)⟩, pieceIndex := 29 },
    { box := ⟨(6373527/200000), (6448527/200000)⟩, pieceIndex := 30 },
    { box := ⟨(6448527/200000), (4307/128)⟩, pieceIndex := 31 }
  ]
}

def scalarCert123 : MacroScalarCert 56 := {
  box := ⟨(4071/128), (8555/256)⟩
  a := (611979482867143614802669851201/5000000000000000000000000000000000)
  segments := [
    { box := ⟨(4071/128), (6373527/200000)⟩, pieceIndex := 29 },
    { box := ⟨(6373527/200000), (6448527/200000)⟩, pieceIndex := 30 },
    { box := ⟨(6448527/200000), (8555/256)⟩, pieceIndex := 31 }
  ]
}

def scalarCert124 : MacroScalarCert 56 := {
  box := ⟨(16461/512), (16815/512)⟩
  a := (104124691/250000000000)
  segments := [
    { box := ⟨(16461/512), (6448527/200000)⟩, pieceIndex := 30 },
    { box := ⟨(6448527/200000), (16815/512)⟩, pieceIndex := 31 }
  ]
}

def scalarCert125 : MacroScalarCert 56 := {
  box := ⟨(13157/512), (26727/1024)⟩
  a := (1405713487152099986076881071449/3200000000000000000000000000000000)
  segments := [
    { box := ⟨(13157/512), (2597847/100000)⟩, pieceIndex := 24 },
    { box := ⟨(2597847/100000), (26727/1024)⟩, pieceIndex := 25 }
  ]
}

def scalarCert126 : MacroScalarCert 56 := {
  box := ⟨(4897/256), (19883/1024)⟩
  a := (24983035225416475609781457263641/320000000000000000000000000000000000)
  segments := [
    { box := ⟨(4897/256), (19351747/1000000)⟩, pieceIndex := 17 },
    { box := ⟨(19351747/1000000), (19883/1024)⟩, pieceIndex := 18 }
  ]
}

def scalarCert127 : MacroScalarCert 56 := {
  box := ⟨(26373/1024), (13393/512)⟩
  a := (6939535078070123213019812388921/12800000000000000000000000000000000)
  segments := [
    { box := ⟨(26373/1024), (2597847/100000)⟩, pieceIndex := 24 },
    { box := ⟨(2597847/100000), (13393/512)⟩, pieceIndex := 25 }
  ]
}

def scalarCert128 : MacroScalarCert 56 := {
  box := ⟨(19647/1024), (9971/512)⟩
  a := (759767742443179976299775611858881/5120000000000000000000000000000000000)
  segments := [
    { box := ⟨(19647/1024), (19351747/1000000)⟩, pieceIndex := 17 },
    { box := ⟨(19351747/1000000), (9971/512)⟩, pieceIndex := 18 }
  ]
}

def scalarCert129 : MacroScalarCert 56 := {
  box := ⟨(1239/64), (10207/512)⟩
  a := (676206949938427113180992093521/1250000000000000000000000000000000)
  segments := [
    { box := ⟨(1239/64), (19726747/1000000)⟩, pieceIndex := 18 },
    { box := ⟨(19726747/1000000), (10207/512)⟩, pieceIndex := 19 }
  ]
}

def scalarCert130 : MacroScalarCert 56 := {
  box := ⟨(9971/512), (5133/256)⟩
  a := (1100717327808522518900723987406129/1280000000000000000000000000000000000)
  segments := [
    { box := ⟨(9971/512), (19726747/1000000)⟩, pieceIndex := 18 },
    { box := ⟨(19726747/1000000), (5133/256)⟩, pieceIndex := 19 }
  ]
}

def scalarCert131 : MacroScalarCert 56 := {
  box := ⟨(8201/256), (8555/256)⟩
  a := (7402913802521846133201894614329/20000000000000000000000000000000000)
  segments := [
    { box := ⟨(8201/256), (6448527/200000)⟩, pieceIndex := 30 },
    { box := ⟨(6448527/200000), (8555/256)⟩, pieceIndex := 31 }
  ]
}

def scalarCert132 : MacroScalarCert 56 := {
  box := ⟨(413/16), (13511/512)⟩
  a := (148698801/250000000000)
  segments := [
    { box := ⟨(413/16), (2597847/100000)⟩, pieceIndex := 24 },
    { box := ⟨(2597847/100000), (13511/512)⟩, pieceIndex := 25 }
  ]
}

def scalarCert133 : MacroScalarCert 56 := {
  box := ⟨(13275/512), (6785/256)⟩
  a := (148698801/250000000000)
  segments := [
    { box := ⟨(13275/512), (2597847/100000)⟩, pieceIndex := 24 },
    { box := ⟨(2597847/100000), (6785/256)⟩, pieceIndex := 25 }
  ]
}

def scalarCert134 : MacroScalarCert 56 := {
  box := ⟨(8201/256), (4307/128)⟩
  a := (7402913802521846133201894614329/20000000000000000000000000000000000)
  segments := [
    { box := ⟨(8201/256), (6448527/200000)⟩, pieceIndex := 30 },
    { box := ⟨(6448527/200000), (4307/128)⟩, pieceIndex := 31 }
  ]
}

def scalarCert135 : MacroScalarCert 56 := {
  box := ⟨(5015/256), (649/32)⟩
  a := (459565243/500000000000)
  segments := [
    { box := ⟨(5015/256), (19726747/1000000)⟩, pieceIndex := 18 },
    { box := ⟨(19726747/1000000), (649/32)⟩, pieceIndex := 19 }
  ]
}

def scalarCert136 : MacroScalarCert 56 := {
  box := ⟨(1711/128), (885/64)⟩
  a := (1610977803/1000000000000)
  segments := [
    { box := ⟨(1711/128), (13505291/1000000)⟩, pieceIndex := 12 },
    { box := ⟨(13505291/1000000), (885/64)⟩, pieceIndex := 13 }
  ]
}

def scalarCert137 : MacroScalarCert 56 := {
  box := ⟨(4071/128), (4425/128)⟩
  a := (611979482867143614802669851201/5000000000000000000000000000000000)
  segments := [
    { box := ⟨(4071/128), (6373527/200000)⟩, pieceIndex := 29 },
    { box := ⟨(6373527/200000), (6448527/200000)⟩, pieceIndex := 30 },
    { box := ⟨(6448527/200000), (4425/128)⟩, pieceIndex := 31 }
  ]
}

def scalarCert138 : MacroScalarCert 56 := {
  box := ⟨(4071/128), (8673/256)⟩
  a := (611979482867143614802669851201/5000000000000000000000000000000000)
  segments := [
    { box := ⟨(4071/128), (6373527/200000)⟩, pieceIndex := 29 },
    { box := ⟨(6373527/200000), (6448527/200000)⟩, pieceIndex := 30 },
    { box := ⟨(6448527/200000), (8673/256)⟩, pieceIndex := 31 }
  ]
}

def scalarCert139 : MacroScalarCert 56 := {
  box := ⟨(8201/256), (2183/64)⟩
  a := (7402913802521846133201894614329/20000000000000000000000000000000000)
  segments := [
    { box := ⟨(8201/256), (6448527/200000)⟩, pieceIndex := 30 },
    { box := ⟨(6448527/200000), (2183/64)⟩, pieceIndex := 31 }
  ]
}

def scalarCert140 : MacroScalarCert 56 := {
  box := ⟨(6549/256), (6903/256)⟩
  a := (4846047689033107029255715842121/20000000000000000000000000000000000)
  segments := [
    { box := ⟨(6549/256), (2560347/100000)⟩, pieceIndex := 23 },
    { box := ⟨(2560347/100000), (2597847/100000)⟩, pieceIndex := 24 },
    { box := ⟨(2597847/100000), (6903/256)⟩, pieceIndex := 25 }
  ]
}

def scalarCert141 : MacroScalarCert 56 := {
  box := ⟨(8201/256), (8673/256)⟩
  a := (7402913802521846133201894614329/20000000000000000000000000000000000)
  segments := [
    { box := ⟨(8201/256), (6448527/200000)⟩, pieceIndex := 30 },
    { box := ⟨(6448527/200000), (8673/256)⟩, pieceIndex := 31 }
  ]
}

def scalarCert142 : MacroScalarCert 56 := {
  box := ⟨(413/16), (3481/128)⟩
  a := (148698801/250000000000)
  segments := [
    { box := ⟨(413/16), (2597847/100000)⟩, pieceIndex := 24 },
    { box := ⟨(2597847/100000), (3481/128)⟩, pieceIndex := 25 }
  ]
}

def scalarCert143 : MacroScalarCert 56 := {
  box := ⟨(4071/128), (1121/32)⟩
  a := (611979482867143614802669851201/5000000000000000000000000000000000)
  segments := [
    { box := ⟨(4071/128), (6373527/200000)⟩, pieceIndex := 29 },
    { box := ⟨(6373527/200000), (6448527/200000)⟩, pieceIndex := 30 },
    { box := ⟨(6448527/200000), (1121/32)⟩, pieceIndex := 31 }
  ]
}

def scalarCert144 : MacroScalarCert 56 := {
  box := ⟨(9971/512), (2537/128)⟩
  a := (1100717327808522518900723987406129/1280000000000000000000000000000000000)
  segments := [
    { box := ⟨(9971/512), (19726747/1000000)⟩, pieceIndex := 18 },
    { box := ⟨(19726747/1000000), (2537/128)⟩, pieceIndex := 19 }
  ]
}

def scalarCert145 : MacroScalarCert 56 := {
  box := ⟨(413/16), (6903/256)⟩
  a := (148698801/250000000000)
  segments := [
    { box := ⟨(413/16), (2597847/100000)⟩, pieceIndex := 24 },
    { box := ⟨(2597847/100000), (6903/256)⟩, pieceIndex := 25 }
  ]
}

def scalarCert146 : MacroScalarCert 56 := {
  box := ⟨(3245/128), (1829/64)⟩
  a := (146846847802364886838234197249/5000000000000000000000000000000000)
  segments := [
    { box := ⟨(3245/128), (2560347/100000)⟩, pieceIndex := 23 },
    { box := ⟨(2560347/100000), (2597847/100000)⟩, pieceIndex := 24 },
    { box := ⟨(2597847/100000), (1829/64)⟩, pieceIndex := 25 }
  ]
}

def scalarCert147 : MacroScalarCert 56 := {
  box := ⟨(3245/128), (3599/128)⟩
  a := (146846847802364886838234197249/5000000000000000000000000000000000)
  segments := [
    { box := ⟨(3245/128), (2560347/100000)⟩, pieceIndex := 23 },
    { box := ⟨(2560347/100000), (2597847/100000)⟩, pieceIndex := 24 },
    { box := ⟨(2597847/100000), (3599/128)⟩, pieceIndex := 25 }
  ]
}

def scalarCert148 : MacroScalarCert 56 := {
  box := ⟨(413/16), (3599/128)⟩
  a := (148698801/250000000000)
  segments := [
    { box := ⟨(413/16), (2597847/100000)⟩, pieceIndex := 24 },
    { box := ⟨(2597847/100000), (3599/128)⟩, pieceIndex := 25 }
  ]
}

def scalarCert149 : MacroScalarCert 56 := {
  box := ⟨(413/16), (1829/64)⟩
  a := (148698801/250000000000)
  segments := [
    { box := ⟨(413/16), (2597847/100000)⟩, pieceIndex := 24 },
    { box := ⟨(2597847/100000), (1829/64)⟩, pieceIndex := 25 }
  ]
}

def scalarCert150 : MacroScalarCert 56 := {
  box := ⟨(4071/128), (2301/64)⟩
  a := (611979482867143614802669851201/5000000000000000000000000000000000)
  segments := [
    { box := ⟨(4071/128), (6373527/200000)⟩, pieceIndex := 29 },
    { box := ⟨(6373527/200000), (6448527/200000)⟩, pieceIndex := 30 },
    { box := ⟨(6448527/200000), (2301/64)⟩, pieceIndex := 31 }
  ]
}

def scalarCert151 : MacroScalarCert 56 := {
  box := ⟨(4071/128), (4543/128)⟩
  a := (611979482867143614802669851201/5000000000000000000000000000000000)
  segments := [
    { box := ⟨(4071/128), (6373527/200000)⟩, pieceIndex := 29 },
    { box := ⟨(6373527/200000), (6448527/200000)⟩, pieceIndex := 30 },
    { box := ⟨(6448527/200000), (4543/128)⟩, pieceIndex := 31 }
  ]
}

def scalarCert152 : MacroScalarCert 56 := {
  box := ⟨(8201/256), (33335/1024)⟩
  a := (7402913802521846133201894614329/20000000000000000000000000000000000)
  segments := [
    { box := ⟨(8201/256), (6448527/200000)⟩, pieceIndex := 30 },
    { box := ⟨(6448527/200000), (33335/1024)⟩, pieceIndex := 31 }
  ]
}

def scalarCert153 : MacroScalarCert 56 := {
  box := ⟨(1593/256), (6431/1024)⟩
  a := (897778972081946888029153112244121/204800000000000000000000000000000000)
  segments := [
    { box := ⟨(1593/256), (250723/40000)⟩, pieceIndex := 2 },
    { box := ⟨(250723/40000), (6431/1024)⟩, pieceIndex := 3 }
  ]
}

def scalarCert154 : MacroScalarCert 56 := {
  box := ⟨(32863/1024), (16697/512)⟩
  a := (104124691/250000000000)
  segments := [
    { box := ⟨(32863/1024), (6448527/200000)⟩, pieceIndex := 30 },
    { box := ⟨(6448527/200000), (16697/512)⟩, pieceIndex := 31 }
  ]
}

def scalarCert155 : MacroScalarCert 56 := {
  box := ⟨(9971/512), (10207/512)⟩
  a := (1100717327808522518900723987406129/1280000000000000000000000000000000000)
  segments := [
    { box := ⟨(9971/512), (19726747/1000000)⟩, pieceIndex := 18 },
    { box := ⟨(19726747/1000000), (10207/512)⟩, pieceIndex := 19 }
  ]
}

def scalarCert156 : MacroScalarCert 56 := {
  box := ⟨(5015/256), (5133/256)⟩
  a := (459565243/500000000000)
  segments := [
    { box := ⟨(5015/256), (19726747/1000000)⟩, pieceIndex := 18 },
    { box := ⟨(19726747/1000000), (5133/256)⟩, pieceIndex := 19 }
  ]
}

def scalarCert157 : MacroScalarCert 56 := {
  box := ⟨(1239/64), (5251/256)⟩
  a := (676206949938427113180992093521/1250000000000000000000000000000000)
  segments := [
    { box := ⟨(1239/64), (19726747/1000000)⟩, pieceIndex := 18 },
    { box := ⟨(19726747/1000000), (5251/256)⟩, pieceIndex := 19 }
  ]
}

def scalarCert158 : MacroScalarCert 56 := {
  box := ⟨(5015/256), (2655/128)⟩
  a := (459565243/500000000000)
  segments := [
    { box := ⟨(5015/256), (19726747/1000000)⟩, pieceIndex := 18 },
    { box := ⟨(19726747/1000000), (2655/128)⟩, pieceIndex := 19 }
  ]
}

def scalarCert159 : MacroScalarCert 56 := {
  box := ⟨(5015/256), (5251/256)⟩
  a := (459565243/500000000000)
  segments := [
    { box := ⟨(5015/256), (19726747/1000000)⟩, pieceIndex := 18 },
    { box := ⟨(19726747/1000000), (5251/256)⟩, pieceIndex := 19 }
  ]
}

def scalarCert160 : MacroScalarCert 56 := {
  box := ⟨(1239/64), (177/8)⟩
  a := (676206949938427113180992093521/1250000000000000000000000000000000)
  segments := [
    { box := ⟨(1239/64), (19726747/1000000)⟩, pieceIndex := 18 },
    { box := ⟨(19726747/1000000), (177/8)⟩, pieceIndex := 19 }
  ]
}

def scalarCert161 : MacroScalarCert 56 := {
  box := ⟨(1239/64), (2773/128)⟩
  a := (676206949938427113180992093521/1250000000000000000000000000000000)
  segments := [
    { box := ⟨(1239/64), (19726747/1000000)⟩, pieceIndex := 18 },
    { box := ⟨(19726747/1000000), (2773/128)⟩, pieceIndex := 19 }
  ]
}

def scalarCert162 : MacroScalarCert 56 := {
  box := ⟨(13275/512), (13629/512)⟩
  a := (148698801/250000000000)
  segments := [
    { box := ⟨(13275/512), (2597847/100000)⟩, pieceIndex := 24 },
    { box := ⟨(2597847/100000), (13629/512)⟩, pieceIndex := 25 }
  ]
}

def scalarCert163 : MacroScalarCert 56 := {
  box := ⟨(5015/256), (10325/512)⟩
  a := (459565243/500000000000)
  segments := [
    { box := ⟨(5015/256), (19726747/1000000)⟩, pieceIndex := 18 },
    { box := ⟨(19726747/1000000), (10325/512)⟩, pieceIndex := 19 }
  ]
}

def scalarCert164 : MacroScalarCert 56 := {
  box := ⟨(10089/512), (649/32)⟩
  a := (459565243/500000000000)
  segments := [
    { box := ⟨(10089/512), (19726747/1000000)⟩, pieceIndex := 18 },
    { box := ⟨(19726747/1000000), (649/32)⟩, pieceIndex := 19 }
  ]
}

def scalarCert165 : MacroScalarCert 56 := {
  box := ⟨(6785/512), (3481/256)⟩
  a := (1610977803/1000000000000)
  segments := [
    { box := ⟨(6785/512), (13505291/1000000)⟩, pieceIndex := 12 },
    { box := ⟨(13505291/1000000), (3481/256)⟩, pieceIndex := 13 }
  ]
}

def scalarCert166 : MacroScalarCert 56 := {
  box := ⟨(10089/512), (10325/512)⟩
  a := (459565243/500000000000)
  segments := [
    { box := ⟨(10089/512), (19726747/1000000)⟩, pieceIndex := 18 },
    { box := ⟨(19726747/1000000), (10325/512)⟩, pieceIndex := 19 }
  ]
}

def scalarCert167 : MacroScalarCert 56 := {
  box := ⟨(413/16), (59/2)⟩
  a := (148698801/250000000000)
  segments := [
    { box := ⟨(413/16), (2597847/100000)⟩, pieceIndex := 24 },
    { box := ⟨(2597847/100000), (59/2)⟩, pieceIndex := 25 }
  ]
}

def scalarCert168 : MacroScalarCert 56 := {
  box := ⟨(413/16), (3717/128)⟩
  a := (148698801/250000000000)
  segments := [
    { box := ⟨(413/16), (2597847/100000)⟩, pieceIndex := 24 },
    { box := ⟨(2597847/100000), (3717/128)⟩, pieceIndex := 25 }
  ]
}

def scalarCert169 : MacroScalarCert 56 := {
  box := ⟨(413/16), (7021/256)⟩
  a := (148698801/250000000000)
  segments := [
    { box := ⟨(413/16), (2597847/100000)⟩, pieceIndex := 24 },
    { box := ⟨(2597847/100000), (7021/256)⟩, pieceIndex := 25 }
  ]
}

def scalarCert170 : MacroScalarCert 56 := {
  box := ⟨(5015/256), (10207/512)⟩
  a := (459565243/500000000000)
  segments := [
    { box := ⟨(5015/256), (19726747/1000000)⟩, pieceIndex := 18 },
    { box := ⟨(19726747/1000000), (10207/512)⟩, pieceIndex := 19 }
  ]
}

def scalarCert171 : MacroScalarCert 56 := {
  box := ⟨(59/8), (177/16)⟩
  a := (3595147923/1000000000000)
  segments := [
    { box := ⟨(59/8), (1848269/250000)⟩, pieceIndex := 6 },
    { box := ⟨(1848269/250000), (177/16)⟩, pieceIndex := 7 }
  ]
}

def scalarCert172 : MacroScalarCert 56 := {
  box := ⟨(413/32), (295/16)⟩
  a := (20678976077282851379745931419361/125000000000000000000000000000000000)
  segments := [
    { box := ⟨(413/32), (13130291/1000000)⟩, pieceIndex := 11 },
    { box := ⟨(13130291/1000000), (13505291/1000000)⟩, pieceIndex := 12 },
    { box := ⟨(13505291/1000000), (9113373/500000)⟩, pieceIndex := 13 },
    { box := ⟨(9113373/500000), (295/16)⟩, pieceIndex := 14 }
  ]
}

def scalarCert173 : MacroScalarCert 56 := {
  box := ⟨(413/32), (531/32)⟩
  a := (20678976077282851379745931419361/125000000000000000000000000000000000)
  segments := [
    { box := ⟨(413/32), (13130291/1000000)⟩, pieceIndex := 11 },
    { box := ⟨(13130291/1000000), (13505291/1000000)⟩, pieceIndex := 12 },
    { box := ⟨(13505291/1000000), (531/32)⟩, pieceIndex := 13 }
  ]
}

def scalarCert174 : MacroScalarCert 56 := {
  box := ⟨(59/8), (295/32)⟩
  a := (3595147923/1000000000000)
  segments := [
    { box := ⟨(59/8), (1848269/250000)⟩, pieceIndex := 6 },
    { box := ⟨(1848269/250000), (295/32)⟩, pieceIndex := 7 }
  ]
}

def scalarCert175 : MacroScalarCert 56 := {
  box := ⟨(413/32), (1003/64)⟩
  a := (20678976077282851379745931419361/125000000000000000000000000000000000)
  segments := [
    { box := ⟨(413/32), (13130291/1000000)⟩, pieceIndex := 11 },
    { box := ⟨(13130291/1000000), (13505291/1000000)⟩, pieceIndex := 12 },
    { box := ⟨(13505291/1000000), (1003/64)⟩, pieceIndex := 13 }
  ]
}

def scalarCert176 : MacroScalarCert 56 := {
  box := ⟨(413/16), (1947/64)⟩
  a := (148698801/250000000000)
  segments := [
    { box := ⟨(413/16), (2597847/100000)⟩, pieceIndex := 24 },
    { box := ⟨(2597847/100000), (1947/64)⟩, pieceIndex := 25 }
  ]
}

def scalarCert177 : MacroScalarCert 56 := {
  box := ⟨(1239/64), (1475/64)⟩
  a := (676206949938427113180992093521/1250000000000000000000000000000000)
  segments := [
    { box := ⟨(1239/64), (19726747/1000000)⟩, pieceIndex := 18 },
    { box := ⟨(19726747/1000000), (1475/64)⟩, pieceIndex := 19 }
  ]
}

def scalarCert178 : MacroScalarCert 56 := {
  box := ⟨(1239/64), (767/32)⟩
  a := (676206949938427113180992093521/1250000000000000000000000000000000)
  segments := [
    { box := ⟨(1239/64), (19726747/1000000)⟩, pieceIndex := 18 },
    { box := ⟨(19726747/1000000), (767/32)⟩, pieceIndex := 19 }
  ]
}

def scalarCert179 : MacroScalarCert 56 := {
  box := ⟨(413/16), (1003/32)⟩
  a := (37896421104977184428389275321/1250000000000000000000000000000000)
  segments := [
    { box := ⟨(413/16), (2597847/100000)⟩, pieceIndex := 24 },
    { box := ⟨(2597847/100000), (15371317/500000)⟩, pieceIndex := 25 },
    { box := ⟨(15371317/500000), (15558817/500000)⟩, pieceIndex := 26 },
    { box := ⟨(15558817/500000), (1003/32)⟩, pieceIndex := 27 }
  ]
}

def scalarCert180 : MacroScalarCert 56 := {
  box := ⟨(1711/64), (1003/32)⟩
  a := (37896421104977184428389275321/1250000000000000000000000000000000)
  segments := [
    { box := ⟨(1711/64), (15371317/500000)⟩, pieceIndex := 25 },
    { box := ⟨(15371317/500000), (15558817/500000)⟩, pieceIndex := 26 },
    { box := ⟨(15558817/500000), (1003/32)⟩, pieceIndex := 27 }
  ]
}

def scalarCert181 : MacroScalarCert 56 := {
  box := ⟨(59/4), (295/16)⟩
  a := (361710019498569118941886428649/312500000000000000000000000000000)
  segments := [
    { box := ⟨(59/4), (9113373/500000)⟩, pieceIndex := 13 },
    { box := ⟨(9113373/500000), (295/16)⟩, pieceIndex := 14 }
  ]
}

def scalarCert182 : MacroScalarCert 56 := {
  box := ⟨(649/32), (1593/64)⟩
  a := (1859160367141373243742933961/7629394531250000000000000000000)
  segments := [
    { box := ⟨(649/32), (24478469/1000000)⟩, pieceIndex := 19 },
    { box := ⟨(24478469/1000000), (24853469/1000000)⟩, pieceIndex := 20 },
    { box := ⟨(24853469/1000000), (1593/64)⟩, pieceIndex := 21 }
  ]
}

def scalarCert183 : MacroScalarCert 56 := {
  box := ⟨(1357/64), (1593/64)⟩
  a := (1859160367141373243742933961/7629394531250000000000000000000)
  segments := [
    { box := ⟨(1357/64), (24478469/1000000)⟩, pieceIndex := 19 },
    { box := ⟨(24478469/1000000), (24853469/1000000)⟩, pieceIndex := 20 },
    { box := ⟨(24853469/1000000), (1593/64)⟩, pieceIndex := 21 }
  ]
}

def scalarCert184 : MacroScalarCert 56 := {
  box := ⟨(1003/64), (295/16)⟩
  a := (361710019498569118941886428649/312500000000000000000000000000000)
  segments := [
    { box := ⟨(1003/64), (9113373/500000)⟩, pieceIndex := 13 },
    { box := ⟨(9113373/500000), (295/16)⟩, pieceIndex := 14 }
  ]
}

def scalarCert185 : MacroScalarCert 56 := {
  box := ⟨(885/32), (1003/32)⟩
  a := (37896421104977184428389275321/1250000000000000000000000000000000)
  segments := [
    { box := ⟨(885/32), (15371317/500000)⟩, pieceIndex := 25 },
    { box := ⟨(15371317/500000), (15558817/500000)⟩, pieceIndex := 26 },
    { box := ⟨(15558817/500000), (1003/32)⟩, pieceIndex := 27 }
  ]
}

def scalarCert186 : MacroScalarCert 56 := {
  box := ⟨(177/8), (1593/64)⟩
  a := (1859160367141373243742933961/7629394531250000000000000000000)
  segments := [
    { box := ⟨(177/8), (24478469/1000000)⟩, pieceIndex := 19 },
    { box := ⟨(24478469/1000000), (24853469/1000000)⟩, pieceIndex := 20 },
    { box := ⟨(24853469/1000000), (1593/64)⟩, pieceIndex := 21 }
  ]
}

def scalarCert187 : MacroScalarCert 56 := {
  box := ⟨(531/32), (295/16)⟩
  a := (361710019498569118941886428649/312500000000000000000000000000000)
  segments := [
    { box := ⟨(531/32), (9113373/500000)⟩, pieceIndex := 13 },
    { box := ⟨(9113373/500000), (295/16)⟩, pieceIndex := 14 }
  ]
}

def scalarCert188 : MacroScalarCert 56 := {
  box := ⟨(2301/128), (2419/128)⟩
  a := (46487548851628354344042770920761/2000000000000000000000000000000000000)
  segments := [
    { box := ⟨(2301/128), (9113373/500000)⟩, pieceIndex := 13 },
    { box := ⟨(9113373/500000), (9300873/500000)⟩, pieceIndex := 14 },
    { box := ⟨(9300873/500000), (2419/128)⟩, pieceIndex := 15 }
  ]
}

def scalarCert189 : MacroScalarCert 56 := {
  box := ⟨(767/64), (1593/128)⟩
  a := (65397592496506782025616240039841/80000000000000000000000000000000000)
  segments := [
    { box := ⟨(767/64), (1200529/100000)⟩, pieceIndex := 7 },
    { box := ⟨(1200529/100000), (1238029/100000)⟩, pieceIndex := 8 },
    { box := ⟨(1238029/100000), (1593/128)⟩, pieceIndex := 9 }
  ]
}

def scalarCert190 : MacroScalarCert 56 := {
  box := ⟨(767/32), (6431/256)⟩
  a := (769227545671561646446829644881/31250000000000000000000000000000000)
  segments := [
    { box := ⟨(767/32), (24478469/1000000)⟩, pieceIndex := 19 },
    { box := ⟨(24478469/1000000), (24853469/1000000)⟩, pieceIndex := 20 },
    { box := ⟨(24853469/1000000), (6431/256)⟩, pieceIndex := 21 }
  ]
}

def scalarCert191 : MacroScalarCert 56 := {
  box := ⟨(2419/64), (1239/32)⟩
  a := (125628559827345406318287851649/125000000000000000000000000000000000)
  segments := [
    { box := ⟨(2419/64), (38138093/1000000)⟩, pieceIndex := 35 },
    { box := ⟨(38138093/1000000), (38513093/1000000)⟩, pieceIndex := 36 },
    { box := ⟨(38513093/1000000), (1239/32)⟩, pieceIndex := 37 }
  ]
}

def scalarCert192 : MacroScalarCert 56 := {
  box := ⟨(2419/64), (19765/512)⟩
  a := (125628559827345406318287851649/125000000000000000000000000000000000)
  segments := [
    { box := ⟨(2419/64), (38138093/1000000)⟩, pieceIndex := 35 },
    { box := ⟨(38138093/1000000), (38513093/1000000)⟩, pieceIndex := 36 },
    { box := ⟨(38513093/1000000), (19765/512)⟩, pieceIndex := 37 }
  ]
}

def scalarCert193 : MacroScalarCert 56 := {
  box := ⟨(19411/512), (1239/32)⟩
  a := (625761533908596174465411009662769/32000000000000000000000000000000000000)
  segments := [
    { box := ⟨(19411/512), (38138093/1000000)⟩, pieceIndex := 35 },
    { box := ⟨(38138093/1000000), (38513093/1000000)⟩, pieceIndex := 36 },
    { box := ⟨(38513093/1000000), (1239/32)⟩, pieceIndex := 37 }
  ]
}

def scalarCert194 : MacroScalarCert 56 := {
  box := ⟨(19411/512), (19765/512)⟩
  a := (625761533908596174465411009662769/32000000000000000000000000000000000000)
  segments := [
    { box := ⟨(19411/512), (38138093/1000000)⟩, pieceIndex := 35 },
    { box := ⟨(38138093/1000000), (38513093/1000000)⟩, pieceIndex := 36 },
    { box := ⟨(38513093/1000000), (19765/512)⟩, pieceIndex := 37 }
  ]
}

def scalarCert195 : MacroScalarCert 56 := {
  box := ⟨(9735/256), (1239/32)⟩
  a := (491938936455960966047921141896161/8000000000000000000000000000000000000)
  segments := [
    { box := ⟨(9735/256), (38138093/1000000)⟩, pieceIndex := 35 },
    { box := ⟨(38138093/1000000), (38513093/1000000)⟩, pieceIndex := 36 },
    { box := ⟨(38513093/1000000), (1239/32)⟩, pieceIndex := 37 }
  ]
}

def scalarCert196 : MacroScalarCert 56 := {
  box := ⟨(2419/64), (9971/256)⟩
  a := (125628559827345406318287851649/125000000000000000000000000000000000)
  segments := [
    { box := ⟨(2419/64), (38138093/1000000)⟩, pieceIndex := 35 },
    { box := ⟨(38138093/1000000), (38513093/1000000)⟩, pieceIndex := 36 },
    { box := ⟨(38513093/1000000), (9971/256)⟩, pieceIndex := 37 }
  ]
}

def scalarCert197 : MacroScalarCert 56 := {
  box := ⟨(2419/64), (19883/512)⟩
  a := (125628559827345406318287851649/125000000000000000000000000000000000)
  segments := [
    { box := ⟨(2419/64), (38138093/1000000)⟩, pieceIndex := 35 },
    { box := ⟨(38138093/1000000), (38513093/1000000)⟩, pieceIndex := 36 },
    { box := ⟨(38513093/1000000), (19883/512)⟩, pieceIndex := 37 }
  ]
}

def scalarCert198 : MacroScalarCert 56 := {
  box := ⟨(19411/512), (9971/256)⟩
  a := (625761533908596174465411009662769/32000000000000000000000000000000000000)
  segments := [
    { box := ⟨(19411/512), (38138093/1000000)⟩, pieceIndex := 35 },
    { box := ⟨(38138093/1000000), (38513093/1000000)⟩, pieceIndex := 36 },
    { box := ⟨(38513093/1000000), (9971/256)⟩, pieceIndex := 37 }
  ]
}

def scalarCert199 : MacroScalarCert 56 := {
  box := ⟨(19411/512), (19883/512)⟩
  a := (625761533908596174465411009662769/32000000000000000000000000000000000000)
  segments := [
    { box := ⟨(19411/512), (38138093/1000000)⟩, pieceIndex := 35 },
    { box := ⟨(38138093/1000000), (38513093/1000000)⟩, pieceIndex := 36 },
    { box := ⟨(38513093/1000000), (19883/512)⟩, pieceIndex := 37 }
  ]
}

def scalarCert200 : MacroScalarCert 56 := {
  box := ⟨(9735/256), (9971/256)⟩
  a := (491938936455960966047921141896161/8000000000000000000000000000000000000)
  segments := [
    { box := ⟨(9735/256), (38138093/1000000)⟩, pieceIndex := 35 },
    { box := ⟨(38138093/1000000), (38513093/1000000)⟩, pieceIndex := 36 },
    { box := ⟨(38513093/1000000), (9971/256)⟩, pieceIndex := 37 }
  ]
}

def scalarCert201 : MacroScalarCert 56 := {
  box := ⟨(8083/256), (2065/64)⟩
  a := (167322041776912901830875682929/20000000000000000000000000000000000)
  segments := [
    { box := ⟨(8083/256), (6373527/200000)⟩, pieceIndex := 29 },
    { box := ⟨(6373527/200000), (6448527/200000)⟩, pieceIndex := 30 },
    { box := ⟨(6448527/200000), (2065/64)⟩, pieceIndex := 31 }
  ]
}

def scalarCert202 : MacroScalarCert 56 := {
  box := ⟨(9735/256), (19883/512)⟩
  a := (491938936455960966047921141896161/8000000000000000000000000000000000000)
  segments := [
    { box := ⟨(9735/256), (38138093/1000000)⟩, pieceIndex := 35 },
    { box := ⟨(38138093/1000000), (38513093/1000000)⟩, pieceIndex := 36 },
    { box := ⟨(38513093/1000000), (19883/512)⟩, pieceIndex := 37 }
  ]
}

def scalarCert203 : MacroScalarCert 56 := {
  box := ⟨(8083/256), (16461/512)⟩
  a := (167322041776912901830875682929/20000000000000000000000000000000000)
  segments := [
    { box := ⟨(8083/256), (6373527/200000)⟩, pieceIndex := 29 },
    { box := ⟨(6373527/200000), (16461/512)⟩, pieceIndex := 30 }
  ]
}

def scalarCert204 : MacroScalarCert 56 := {
  box := ⟨(19529/512), (9971/256)⟩
  a := (172336030037728650247271147738569/1280000000000000000000000000000000000)
  segments := [
    { box := ⟨(19529/512), (38513093/1000000)⟩, pieceIndex := 36 },
    { box := ⟨(38513093/1000000), (9971/256)⟩, pieceIndex := 37 }
  ]
}

def scalarCert205 : MacroScalarCert 56 := {
  box := ⟨(16225/512), (2065/64)⟩
  a := (3895225326904878308147162909841/80000000000000000000000000000000000)
  segments := [
    { box := ⟨(16225/512), (6373527/200000)⟩, pieceIndex := 29 },
    { box := ⟨(6373527/200000), (6448527/200000)⟩, pieceIndex := 30 },
    { box := ⟨(6448527/200000), (2065/64)⟩, pieceIndex := 31 }
  ]
}

def scalarCert206 : MacroScalarCert 56 := {
  box := ⟨(19529/512), (19883/512)⟩
  a := (172336030037728650247271147738569/1280000000000000000000000000000000000)
  segments := [
    { box := ⟨(19529/512), (38513093/1000000)⟩, pieceIndex := 36 },
    { box := ⟨(38513093/1000000), (19883/512)⟩, pieceIndex := 37 }
  ]
}

def scalarCert207 : MacroScalarCert 56 := {
  box := ⟨(4897/128), (9971/256)⟩
  a := (17456552780050285252554156310809/80000000000000000000000000000000000)
  segments := [
    { box := ⟨(4897/128), (38513093/1000000)⟩, pieceIndex := 36 },
    { box := ⟨(38513093/1000000), (9971/256)⟩, pieceIndex := 37 }
  ]
}

def scalarCert208 : MacroScalarCert 56 := {
  box := ⟨(2419/64), (5015/128)⟩
  a := (125628559827345406318287851649/125000000000000000000000000000000000)
  segments := [
    { box := ⟨(2419/64), (38138093/1000000)⟩, pieceIndex := 35 },
    { box := ⟨(38138093/1000000), (38513093/1000000)⟩, pieceIndex := 36 },
    { box := ⟨(38513093/1000000), (5015/128)⟩, pieceIndex := 37 }
  ]
}

def scalarCert209 : MacroScalarCert 56 := {
  box := ⟨(9735/256), (5015/128)⟩
  a := (491938936455960966047921141896161/8000000000000000000000000000000000000)
  segments := [
    { box := ⟨(9735/256), (38138093/1000000)⟩, pieceIndex := 35 },
    { box := ⟨(38138093/1000000), (38513093/1000000)⟩, pieceIndex := 36 },
    { box := ⟨(38513093/1000000), (5015/128)⟩, pieceIndex := 37 }
  ]
}

def scalarCert210 : MacroScalarCert 56 := {
  box := ⟨(9735/256), (20001/512)⟩
  a := (491938936455960966047921141896161/8000000000000000000000000000000000000)
  segments := [
    { box := ⟨(9735/256), (38138093/1000000)⟩, pieceIndex := 35 },
    { box := ⟨(38138093/1000000), (38513093/1000000)⟩, pieceIndex := 36 },
    { box := ⟨(38513093/1000000), (20001/512)⟩, pieceIndex := 37 }
  ]
}

def scalarCert211 : MacroScalarCert 56 := {
  box := ⟨(19529/512), (5015/128)⟩
  a := (172336030037728650247271147738569/1280000000000000000000000000000000000)
  segments := [
    { box := ⟨(19529/512), (38513093/1000000)⟩, pieceIndex := 36 },
    { box := ⟨(38513093/1000000), (5015/128)⟩, pieceIndex := 37 }
  ]
}

def scalarCert212 : MacroScalarCert 56 := {
  box := ⟨(295/16), (2419/128)⟩
  a := (46487548851628354344042770920761/2000000000000000000000000000000000000)
  segments := [
    { box := ⟨(295/16), (9300873/500000)⟩, pieceIndex := 14 },
    { box := ⟨(9300873/500000), (2419/128)⟩, pieceIndex := 15 }
  ]
}

def scalarCert213 : MacroScalarCert 56 := {
  box := ⟨(767/64), (3127/256)⟩
  a := (219261670598035323657524238642169/80000000000000000000000000000000000)
  segments := [
    { box := ⟨(767/64), (1200529/100000)⟩, pieceIndex := 7 },
    { box := ⟨(1200529/100000), (3127/256)⟩, pieceIndex := 8 }
  ]
}

def scalarCert214 : MacroScalarCert 56 := {
  box := ⟨(3127/256), (1593/128)⟩
  a := (65397592496506782025616240039841/80000000000000000000000000000000000)
  segments := [
    { box := ⟨(3127/256), (1238029/100000)⟩, pieceIndex := 8 },
    { box := ⟨(1238029/100000), (1593/128)⟩, pieceIndex := 9 }
  ]
}

def scalarCert215 : MacroScalarCert 56 := {
  box := ⟨(2419/64), (2537/64)⟩
  a := (125628559827345406318287851649/125000000000000000000000000000000000)
  segments := [
    { box := ⟨(2419/64), (38138093/1000000)⟩, pieceIndex := 35 },
    { box := ⟨(38138093/1000000), (38513093/1000000)⟩, pieceIndex := 36 },
    { box := ⟨(38513093/1000000), (2537/64)⟩, pieceIndex := 37 }
  ]
}

def scalarCert216 : MacroScalarCert 56 := {
  box := ⟨(2419/64), (10089/256)⟩
  a := (125628559827345406318287851649/125000000000000000000000000000000000)
  segments := [
    { box := ⟨(2419/64), (38138093/1000000)⟩, pieceIndex := 35 },
    { box := ⟨(38138093/1000000), (38513093/1000000)⟩, pieceIndex := 36 },
    { box := ⟨(38513093/1000000), (10089/256)⟩, pieceIndex := 37 }
  ]
}

def scalarCert217 : MacroScalarCert 56 := {
  box := ⟨(19529/512), (20001/512)⟩
  a := (172336030037728650247271147738569/1280000000000000000000000000000000000)
  segments := [
    { box := ⟨(19529/512), (38513093/1000000)⟩, pieceIndex := 36 },
    { box := ⟨(38513093/1000000), (20001/512)⟩, pieceIndex := 37 }
  ]
}

def scalarCert218 : MacroScalarCert 56 := {
  box := ⟨(4897/128), (5015/128)⟩
  a := (17456552780050285252554156310809/80000000000000000000000000000000000)
  segments := [
    { box := ⟨(4897/128), (38513093/1000000)⟩, pieceIndex := 36 },
    { box := ⟨(38513093/1000000), (5015/128)⟩, pieceIndex := 37 }
  ]
}

def scalarCert219 : MacroScalarCert 56 := {
  box := ⟨(4897/128), (20001/512)⟩
  a := (17456552780050285252554156310809/80000000000000000000000000000000000)
  segments := [
    { box := ⟨(4897/128), (38513093/1000000)⟩, pieceIndex := 36 },
    { box := ⟨(38513093/1000000), (20001/512)⟩, pieceIndex := 37 }
  ]
}

def scalarCert220 : MacroScalarCert 56 := {
  box := ⟨(19647/512), (20001/512)⟩
  a := (76986939/250000000000)
  segments := [
    { box := ⟨(19647/512), (38513093/1000000)⟩, pieceIndex := 36 },
    { box := ⟨(38513093/1000000), (20001/512)⟩, pieceIndex := 37 }
  ]
}

def scalarCert221 : MacroScalarCert 56 := {
  box := ⟨(19647/512), (5015/128)⟩
  a := (76986939/250000000000)
  segments := [
    { box := ⟨(19647/512), (38513093/1000000)⟩, pieceIndex := 36 },
    { box := ⟨(38513093/1000000), (5015/128)⟩, pieceIndex := 37 }
  ]
}

def scalarCert222 : MacroScalarCert 56 := {
  box := ⟨(9735/256), (10089/256)⟩
  a := (491938936455960966047921141896161/8000000000000000000000000000000000000)
  segments := [
    { box := ⟨(9735/256), (38138093/1000000)⟩, pieceIndex := 35 },
    { box := ⟨(38138093/1000000), (38513093/1000000)⟩, pieceIndex := 36 },
    { box := ⟨(38513093/1000000), (10089/256)⟩, pieceIndex := 37 }
  ]
}

def scalarCert223 : MacroScalarCert 56 := {
  box := ⟨(4897/128), (10089/256)⟩
  a := (17456552780050285252554156310809/80000000000000000000000000000000000)
  segments := [
    { box := ⟨(4897/128), (38513093/1000000)⟩, pieceIndex := 36 },
    { box := ⟨(38513093/1000000), (10089/256)⟩, pieceIndex := 37 }
  ]
}

def scalarCert224 : MacroScalarCert 56 := {
  box := ⟨(4897/128), (20119/512)⟩
  a := (17456552780050285252554156310809/80000000000000000000000000000000000)
  segments := [
    { box := ⟨(4897/128), (38513093/1000000)⟩, pieceIndex := 36 },
    { box := ⟨(38513093/1000000), (20119/512)⟩, pieceIndex := 37 }
  ]
}

def scalarCert225 : MacroScalarCert 56 := {
  box := ⟨(19647/512), (10089/256)⟩
  a := (76986939/250000000000)
  segments := [
    { box := ⟨(19647/512), (38513093/1000000)⟩, pieceIndex := 36 },
    { box := ⟨(38513093/1000000), (10089/256)⟩, pieceIndex := 37 }
  ]
}

def scalarCert226 : MacroScalarCert 56 := {
  box := ⟨(19647/512), (20119/512)⟩
  a := (76986939/250000000000)
  segments := [
    { box := ⟨(19647/512), (38513093/1000000)⟩, pieceIndex := 36 },
    { box := ⟨(38513093/1000000), (20119/512)⟩, pieceIndex := 37 }
  ]
}

def scalarCert227 : MacroScalarCert 56 := {
  box := ⟨(9853/256), (10089/256)⟩
  a := (76986939/250000000000)
  segments := [
    { box := ⟨(9853/256), (38513093/1000000)⟩, pieceIndex := 36 },
    { box := ⟨(38513093/1000000), (10089/256)⟩, pieceIndex := 37 }
  ]
}

def scalarCert228 : MacroScalarCert 56 := {
  box := ⟨(9735/256), (2537/64)⟩
  a := (491938936455960966047921141896161/8000000000000000000000000000000000000)
  segments := [
    { box := ⟨(9735/256), (38138093/1000000)⟩, pieceIndex := 35 },
    { box := ⟨(38138093/1000000), (38513093/1000000)⟩, pieceIndex := 36 },
    { box := ⟨(38513093/1000000), (2537/64)⟩, pieceIndex := 37 }
  ]
}

def scalarCert229 : MacroScalarCert 56 := {
  box := ⟨(4897/128), (2537/64)⟩
  a := (17456552780050285252554156310809/80000000000000000000000000000000000)
  segments := [
    { box := ⟨(4897/128), (38513093/1000000)⟩, pieceIndex := 36 },
    { box := ⟨(38513093/1000000), (2537/64)⟩, pieceIndex := 37 }
  ]
}

def scalarCert230 : MacroScalarCert 56 := {
  box := ⟨(9853/256), (2537/64)⟩
  a := (76986939/250000000000)
  segments := [
    { box := ⟨(9853/256), (38513093/1000000)⟩, pieceIndex := 36 },
    { box := ⟨(38513093/1000000), (2537/64)⟩, pieceIndex := 37 }
  ]
}

def scalarCert231 : MacroScalarCert 56 := {
  box := ⟨(6195/256), (6431/256)⟩
  a := (769227545671561646446829644881/31250000000000000000000000000000000)
  segments := [
    { box := ⟨(6195/256), (24478469/1000000)⟩, pieceIndex := 19 },
    { box := ⟨(24478469/1000000), (24853469/1000000)⟩, pieceIndex := 20 },
    { box := ⟨(24853469/1000000), (6431/256)⟩, pieceIndex := 21 }
  ]
}

def scalarCert232 : MacroScalarCert 56 := {
  box := ⟨(2301/128), (4779/256)⟩
  a := (2891119993742916046127024249511169/8000000000000000000000000000000000000)
  segments := [
    { box := ⟨(2301/128), (9113373/500000)⟩, pieceIndex := 13 },
    { box := ⟨(9113373/500000), (9300873/500000)⟩, pieceIndex := 14 },
    { box := ⟨(9300873/500000), (4779/256)⟩, pieceIndex := 15 }
  ]
}

def scalarCert233 : MacroScalarCert 56 := {
  box := ⟨(4661/256), (2419/128)⟩
  a := (46487548851628354344042770920761/2000000000000000000000000000000000000)
  segments := [
    { box := ⟨(4661/256), (9113373/500000)⟩, pieceIndex := 13 },
    { box := ⟨(9113373/500000), (9300873/500000)⟩, pieceIndex := 14 },
    { box := ⟨(9300873/500000), (2419/128)⟩, pieceIndex := 15 }
  ]
}

def scalarCert234 : MacroScalarCert 56 := {
  box := ⟨(3127/128), (6431/256)⟩
  a := (769227545671561646446829644881/31250000000000000000000000000000000)
  segments := [
    { box := ⟨(3127/128), (24478469/1000000)⟩, pieceIndex := 19 },
    { box := ⟨(24478469/1000000), (24853469/1000000)⟩, pieceIndex := 20 },
    { box := ⟨(24853469/1000000), (6431/256)⟩, pieceIndex := 21 }
  ]
}

def scalarCert235 : MacroScalarCert 56 := {
  box := ⟨(4661/256), (4779/256)⟩
  a := (2891119993742916046127024249511169/8000000000000000000000000000000000000)
  segments := [
    { box := ⟨(4661/256), (9113373/500000)⟩, pieceIndex := 13 },
    { box := ⟨(9113373/500000), (9300873/500000)⟩, pieceIndex := 14 },
    { box := ⟨(9300873/500000), (4779/256)⟩, pieceIndex := 15 }
  ]
}

def scalarCert236 : MacroScalarCert 56 := {
  box := ⟨(2419/64), (5133/128)⟩
  a := (125628559827345406318287851649/125000000000000000000000000000000000)
  segments := [
    { box := ⟨(2419/64), (38138093/1000000)⟩, pieceIndex := 35 },
    { box := ⟨(38138093/1000000), (38513093/1000000)⟩, pieceIndex := 36 },
    { box := ⟨(38513093/1000000), (5133/128)⟩, pieceIndex := 37 }
  ]
}

def scalarCert237 : MacroScalarCert 56 := {
  box := ⟨(2419/64), (10207/256)⟩
  a := (125628559827345406318287851649/125000000000000000000000000000000000)
  segments := [
    { box := ⟨(2419/64), (38138093/1000000)⟩, pieceIndex := 35 },
    { box := ⟨(38138093/1000000), (38513093/1000000)⟩, pieceIndex := 36 },
    { box := ⟨(38513093/1000000), (10207/256)⟩, pieceIndex := 37 }
  ]
}

def scalarCert238 : MacroScalarCert 56 := {
  box := ⟨(9735/256), (5133/128)⟩
  a := (491938936455960966047921141896161/8000000000000000000000000000000000000)
  segments := [
    { box := ⟨(9735/256), (38138093/1000000)⟩, pieceIndex := 35 },
    { box := ⟨(38138093/1000000), (38513093/1000000)⟩, pieceIndex := 36 },
    { box := ⟨(38513093/1000000), (5133/128)⟩, pieceIndex := 37 }
  ]
}

def scalarCert239 : MacroScalarCert 56 := {
  box := ⟨(9735/256), (10207/256)⟩
  a := (491938936455960966047921141896161/8000000000000000000000000000000000000)
  segments := [
    { box := ⟨(9735/256), (38138093/1000000)⟩, pieceIndex := 35 },
    { box := ⟨(38138093/1000000), (38513093/1000000)⟩, pieceIndex := 36 },
    { box := ⟨(38513093/1000000), (10207/256)⟩, pieceIndex := 37 }
  ]
}

def scalarCert240 : MacroScalarCert 56 := {
  box := ⟨(9853/256), (20119/512)⟩
  a := (76986939/250000000000)
  segments := [
    { box := ⟨(9853/256), (38513093/1000000)⟩, pieceIndex := 36 },
    { box := ⟨(38513093/1000000), (20119/512)⟩, pieceIndex := 37 }
  ]
}

def scalarCert241 : MacroScalarCert 56 := {
  box := ⟨(4897/128), (10207/256)⟩
  a := (17456552780050285252554156310809/80000000000000000000000000000000000)
  segments := [
    { box := ⟨(4897/128), (38513093/1000000)⟩, pieceIndex := 36 },
    { box := ⟨(38513093/1000000), (10207/256)⟩, pieceIndex := 37 }
  ]
}

def scalarCert242 : MacroScalarCert 56 := {
  box := ⟨(9853/256), (10207/256)⟩
  a := (76986939/250000000000)
  segments := [
    { box := ⟨(9853/256), (38513093/1000000)⟩, pieceIndex := 36 },
    { box := ⟨(38513093/1000000), (10207/256)⟩, pieceIndex := 37 }
  ]
}

def scalarCert243 : MacroScalarCert 56 := {
  box := ⟨(4897/128), (5133/128)⟩
  a := (17456552780050285252554156310809/80000000000000000000000000000000000)
  segments := [
    { box := ⟨(4897/128), (38513093/1000000)⟩, pieceIndex := 36 },
    { box := ⟨(38513093/1000000), (5133/128)⟩, pieceIndex := 37 }
  ]
}

def scalarCert244 : MacroScalarCert 56 := {
  box := ⟨(2419/64), (649/16)⟩
  a := (125628559827345406318287851649/125000000000000000000000000000000000)
  segments := [
    { box := ⟨(2419/64), (38138093/1000000)⟩, pieceIndex := 35 },
    { box := ⟨(38138093/1000000), (38513093/1000000)⟩, pieceIndex := 36 },
    { box := ⟨(38513093/1000000), (649/16)⟩, pieceIndex := 37 }
  ]
}

def scalarCert245 : MacroScalarCert 56 := {
  box := ⟨(2419/64), (5251/128)⟩
  a := (125628559827345406318287851649/125000000000000000000000000000000000)
  segments := [
    { box := ⟨(2419/64), (38138093/1000000)⟩, pieceIndex := 35 },
    { box := ⟨(38138093/1000000), (38513093/1000000)⟩, pieceIndex := 36 },
    { box := ⟨(38513093/1000000), (5251/128)⟩, pieceIndex := 37 }
  ]
}

def scalarCert246 : MacroScalarCert 56 := {
  box := ⟨(2419/64), (2655/64)⟩
  a := (125628559827345406318287851649/125000000000000000000000000000000000)
  segments := [
    { box := ⟨(2419/64), (38138093/1000000)⟩, pieceIndex := 35 },
    { box := ⟨(38138093/1000000), (38513093/1000000)⟩, pieceIndex := 36 },
    { box := ⟨(38513093/1000000), (2655/64)⟩, pieceIndex := 37 }
  ]
}

def scalarCert247 : MacroScalarCert 56 := {
  box := ⟨(9853/256), (20237/512)⟩
  a := (76986939/250000000000)
  segments := [
    { box := ⟨(9853/256), (38513093/1000000)⟩, pieceIndex := 36 },
    { box := ⟨(38513093/1000000), (20237/512)⟩, pieceIndex := 37 }
  ]
}

def scalarCert248 : MacroScalarCert 56 := {
  box := ⟨(295/16), (9617/512)⟩
  a := (4543500314017536620797999797247801/32000000000000000000000000000000000000)
  segments := [
    { box := ⟨(295/16), (9300873/500000)⟩, pieceIndex := 14 },
    { box := ⟨(9300873/500000), (9617/512)⟩, pieceIndex := 15 }
  ]
}

def scalarCert249 : MacroScalarCert 56 := {
  box := ⟨(9499/512), (2419/128)⟩
  a := (46487548851628354344042770920761/2000000000000000000000000000000000000)
  segments := [
    { box := ⟨(9499/512), (9300873/500000)⟩, pieceIndex := 14 },
    { box := ⟨(9300873/500000), (2419/128)⟩, pieceIndex := 15 }
  ]
}

def scalarCert250 : MacroScalarCert 56 := {
  box := ⟨(2419/64), (1357/32)⟩
  a := (125628559827345406318287851649/125000000000000000000000000000000000)
  segments := [
    { box := ⟨(2419/64), (38138093/1000000)⟩, pieceIndex := 35 },
    { box := ⟨(38138093/1000000), (38513093/1000000)⟩, pieceIndex := 36 },
    { box := ⟨(38513093/1000000), (1357/32)⟩, pieceIndex := 37 }
  ]
}

def scalarCert251 : MacroScalarCert 56 := {
  box := ⟨(2419/64), (5369/128)⟩
  a := (125628559827345406318287851649/125000000000000000000000000000000000)
  segments := [
    { box := ⟨(2419/64), (38138093/1000000)⟩, pieceIndex := 35 },
    { box := ⟨(38138093/1000000), (38513093/1000000)⟩, pieceIndex := 36 },
    { box := ⟨(38513093/1000000), (5369/128)⟩, pieceIndex := 37 }
  ]
}

def scalarCert252 : MacroScalarCert 56 := {
  box := ⟨(4897/128), (649/16)⟩
  a := (17456552780050285252554156310809/80000000000000000000000000000000000)
  segments := [
    { box := ⟨(4897/128), (38513093/1000000)⟩, pieceIndex := 36 },
    { box := ⟨(38513093/1000000), (649/16)⟩, pieceIndex := 37 }
  ]
}

def scalarCert253 : MacroScalarCert 56 := {
  box := ⟨(4897/128), (10325/256)⟩
  a := (17456552780050285252554156310809/80000000000000000000000000000000000)
  segments := [
    { box := ⟨(4897/128), (38513093/1000000)⟩, pieceIndex := 36 },
    { box := ⟨(38513093/1000000), (10325/256)⟩, pieceIndex := 37 }
  ]
}

def scalarCert254 : MacroScalarCert 56 := {
  box := ⟨(13275/512), (13511/512)⟩
  a := (148698801/250000000000)
  segments := [
    { box := ⟨(13275/512), (2597847/100000)⟩, pieceIndex := 24 },
    { box := ⟨(2597847/100000), (13511/512)⟩, pieceIndex := 25 }
  ]
}

def scalarCert255 : MacroScalarCert 56 := {
  box := ⟨(9853/256), (5015/128)⟩
  a := (76986939/250000000000)
  segments := [
    { box := ⟨(9853/256), (38513093/1000000)⟩, pieceIndex := 36 },
    { box := ⟨(38513093/1000000), (5015/128)⟩, pieceIndex := 37 }
  ]
}

def scalarCert256 : MacroScalarCert 56 := {
  box := ⟨(9853/256), (5133/128)⟩
  a := (76986939/250000000000)
  segments := [
    { box := ⟨(9853/256), (38513093/1000000)⟩, pieceIndex := 36 },
    { box := ⟨(38513093/1000000), (5133/128)⟩, pieceIndex := 37 }
  ]
}

def scalarCert257 : MacroScalarCert 56 := {
  box := ⟨(9853/256), (10325/256)⟩
  a := (76986939/250000000000)
  segments := [
    { box := ⟨(9853/256), (38513093/1000000)⟩, pieceIndex := 36 },
    { box := ⟨(38513093/1000000), (10325/256)⟩, pieceIndex := 37 }
  ]
}

def scalarCert258 : MacroScalarCert 56 := {
  box := ⟨(9853/256), (649/16)⟩
  a := (76986939/250000000000)
  segments := [
    { box := ⟨(9853/256), (38513093/1000000)⟩, pieceIndex := 36 },
    { box := ⟨(38513093/1000000), (649/16)⟩, pieceIndex := 37 }
  ]
}

def scalarCert259 : MacroScalarCert 56 := {
  box := ⟨(4897/128), (5251/128)⟩
  a := (17456552780050285252554156310809/80000000000000000000000000000000000)
  segments := [
    { box := ⟨(4897/128), (38513093/1000000)⟩, pieceIndex := 36 },
    { box := ⟨(38513093/1000000), (5251/128)⟩, pieceIndex := 37 }
  ]
}

def scalarCert260 : MacroScalarCert 56 := {
  box := ⟨(4897/128), (2655/64)⟩
  a := (17456552780050285252554156310809/80000000000000000000000000000000000)
  segments := [
    { box := ⟨(4897/128), (38513093/1000000)⟩, pieceIndex := 36 },
    { box := ⟨(38513093/1000000), (2655/64)⟩, pieceIndex := 37 }
  ]
}

def scalarCert261 : MacroScalarCert 56 := {
  box := ⟨(4897/128), (5369/128)⟩
  a := (17456552780050285252554156310809/80000000000000000000000000000000000)
  segments := [
    { box := ⟨(4897/128), (38513093/1000000)⟩, pieceIndex := 36 },
    { box := ⟨(38513093/1000000), (5369/128)⟩, pieceIndex := 37 }
  ]
}

def scalarCert262 : MacroScalarCert 56 := {
  box := ⟨(4897/128), (1357/32)⟩
  a := (17456552780050285252554156310809/80000000000000000000000000000000000)
  segments := [
    { box := ⟨(4897/128), (38513093/1000000)⟩, pieceIndex := 36 },
    { box := ⟨(38513093/1000000), (1357/32)⟩, pieceIndex := 37 }
  ]
}

def scalarCert263 : MacroScalarCert 56 := {
  box := ⟨(2419/64), (2773/64)⟩
  a := (125628559827345406318287851649/125000000000000000000000000000000000)
  segments := [
    { box := ⟨(2419/64), (38138093/1000000)⟩, pieceIndex := 35 },
    { box := ⟨(38138093/1000000), (38513093/1000000)⟩, pieceIndex := 36 },
    { box := ⟨(38513093/1000000), (43287167/1000000)⟩, pieceIndex := 37 },
    { box := ⟨(43287167/1000000), (2773/64)⟩, pieceIndex := 38 }
  ]
}

def scalarCert264 : MacroScalarCert 56 := {
  box := ⟨(1239/32), (2773/64)⟩
  a := (76986939/250000000000)
  segments := [
    { box := ⟨(1239/32), (43287167/1000000)⟩, pieceIndex := 37 },
    { box := ⟨(43287167/1000000), (2773/64)⟩, pieceIndex := 38 }
  ]
}

def scalarCert265 : MacroScalarCert 56 := {
  box := ⟨(8083/256), (8201/256)⟩
  a := (167322041776912901830875682929/20000000000000000000000000000000000)
  segments := [
    { box := ⟨(8083/256), (6373527/200000)⟩, pieceIndex := 29 },
    { box := ⟨(6373527/200000), (8201/256)⟩, pieceIndex := 30 }
  ]
}

def scalarCert266 : MacroScalarCert 56 := {
  box := ⟨(3245/128), (13157/512)⟩
  a := (146846847802364886838234197249/5000000000000000000000000000000000)
  segments := [
    { box := ⟨(3245/128), (2560347/100000)⟩, pieceIndex := 23 },
    { box := ⟨(2560347/100000), (13157/512)⟩, pieceIndex := 24 }
  ]
}

def scalarCert267 : MacroScalarCert 56 := {
  box := ⟨(16225/512), (16461/512)⟩
  a := (3895225326904878308147162909841/80000000000000000000000000000000000)
  segments := [
    { box := ⟨(16225/512), (6373527/200000)⟩, pieceIndex := 29 },
    { box := ⟨(6373527/200000), (16461/512)⟩, pieceIndex := 30 }
  ]
}

def scalarCert268 : MacroScalarCert 56 := {
  box := ⟨(4897/256), (1239/64)⟩
  a := (24983035225416475609781457263641/320000000000000000000000000000000000)
  segments := [
    { box := ⟨(4897/256), (19351747/1000000)⟩, pieceIndex := 17 },
    { box := ⟨(19351747/1000000), (1239/64)⟩, pieceIndex := 18 }
  ]
}

def scalarCert269 : MacroScalarCert 56 := {
  box := ⟨(13039/512), (413/16)⟩
  a := (8807754158064216214287607996609/80000000000000000000000000000000000)
  segments := [
    { box := ⟨(13039/512), (2560347/100000)⟩, pieceIndex := 23 },
    { box := ⟨(2560347/100000), (413/16)⟩, pieceIndex := 24 }
  ]
}

def scalarCert270 : MacroScalarCert 56 := {
  box := ⟨(4071/128), (2065/64)⟩
  a := (611979482867143614802669851201/5000000000000000000000000000000000)
  segments := [
    { box := ⟨(4071/128), (6373527/200000)⟩, pieceIndex := 29 },
    { box := ⟨(6373527/200000), (6448527/200000)⟩, pieceIndex := 30 },
    { box := ⟨(6448527/200000), (2065/64)⟩, pieceIndex := 31 }
  ]
}

def scalarCert271 : MacroScalarCert 56 := {
  box := ⟨(19529/512), (1239/32)⟩
  a := (172336030037728650247271147738569/1280000000000000000000000000000000000)
  segments := [
    { box := ⟨(19529/512), (38513093/1000000)⟩, pieceIndex := 36 },
    { box := ⟨(38513093/1000000), (1239/32)⟩, pieceIndex := 37 }
  ]
}

def scalarCert272 : MacroScalarCert 56 := {
  box := ⟨(4897/128), (19883/512)⟩
  a := (17456552780050285252554156310809/80000000000000000000000000000000000)
  segments := [
    { box := ⟨(4897/128), (38513093/1000000)⟩, pieceIndex := 36 },
    { box := ⟨(38513093/1000000), (19883/512)⟩, pieceIndex := 37 }
  ]
}

def scalarCert273 : MacroScalarCert 56 := {
  box := ⟨(19647/512), (9971/256)⟩
  a := (76986939/250000000000)
  segments := [
    { box := ⟨(19647/512), (38513093/1000000)⟩, pieceIndex := 36 },
    { box := ⟨(38513093/1000000), (9971/256)⟩, pieceIndex := 37 }
  ]
}

def scalarCert274 : MacroScalarCert 56 := {
  box := ⟨(9853/512), (9971/512)⟩
  a := (308609266148826216472188856757689/1280000000000000000000000000000000000)
  segments := [
    { box := ⟨(9853/512), (19351747/1000000)⟩, pieceIndex := 17 },
    { box := ⟨(19351747/1000000), (9971/512)⟩, pieceIndex := 18 }
  ]
}

def scalarCert275 : MacroScalarCert 56 := {
  box := ⟨(6549/256), (13275/512)⟩
  a := (4846047689033107029255715842121/20000000000000000000000000000000000)
  segments := [
    { box := ⟨(6549/256), (2560347/100000)⟩, pieceIndex := 23 },
    { box := ⟨(2560347/100000), (13275/512)⟩, pieceIndex := 24 }
  ]
}

def scalarCert276 : MacroScalarCert 56 := {
  box := ⟨(16343/512), (16579/512)⟩
  a := (19145944597030269950435668435441/80000000000000000000000000000000000)
  segments := [
    { box := ⟨(16343/512), (6448527/200000)⟩, pieceIndex := 30 },
    { box := ⟨(6448527/200000), (16579/512)⟩, pieceIndex := 31 }
  ]
}

def scalarCert277 : MacroScalarCert 56 := {
  box := ⟨(6313/512), (1593/128)⟩
  a := (65397592496506782025616240039841/80000000000000000000000000000000000)
  segments := [
    { box := ⟨(6313/512), (1238029/100000)⟩, pieceIndex := 8 },
    { box := ⟨(1238029/100000), (1593/128)⟩, pieceIndex := 9 }
  ]
}

def scalarCert278 : MacroScalarCert 56 := {
  box := ⟨(8201/256), (8319/256)⟩
  a := (7402913802521846133201894614329/20000000000000000000000000000000000)
  segments := [
    { box := ⟨(8201/256), (6448527/200000)⟩, pieceIndex := 30 },
    { box := ⟨(6448527/200000), (8319/256)⟩, pieceIndex := 31 }
  ]
}

def scalarCert279 : MacroScalarCert 56 := {
  box := ⟨(22597/512), (11505/256)⟩
  a := (12404326906898653543170837152761/2000000000000000000000000000000000000)
  segments := [
    { box := ⟨(22597/512), (5551521/125000)⟩, pieceIndex := 41 },
    { box := ⟨(5551521/125000), (1399599/31250)⟩, pieceIndex := 42 },
    { box := ⟨(1399599/31250), (11505/256)⟩, pieceIndex := 43 }
  ]
}

def scalarCert280 : MacroScalarCert 56 := {
  box := ⟨(22597/512), (2891/64)⟩
  a := (12404326906898653543170837152761/2000000000000000000000000000000000000)
  segments := [
    { box := ⟨(22597/512), (5551521/125000)⟩, pieceIndex := 41 },
    { box := ⟨(5551521/125000), (1399599/31250)⟩, pieceIndex := 42 },
    { box := ⟨(1399599/31250), (2891/64)⟩, pieceIndex := 43 }
  ]
}

def scalarCert281 : MacroScalarCert 56 := {
  box := ⟨(22597/512), (23069/512)⟩
  a := (12404326906898653543170837152761/2000000000000000000000000000000000000)
  segments := [
    { box := ⟨(22597/512), (5551521/125000)⟩, pieceIndex := 41 },
    { box := ⟨(5551521/125000), (1399599/31250)⟩, pieceIndex := 42 },
    { box := ⟨(1399599/31250), (23069/512)⟩, pieceIndex := 43 }
  ]
}

def scalarCert282 : MacroScalarCert 56 := {
  box := ⟨(177/4), (2891/64)⟩
  a := (3600341844467488615851330529/122070312500000000000000000000000)
  segments := [
    { box := ⟨(177/4), (5551521/125000)⟩, pieceIndex := 41 },
    { box := ⟨(5551521/125000), (1399599/31250)⟩, pieceIndex := 42 },
    { box := ⟨(1399599/31250), (2891/64)⟩, pieceIndex := 43 }
  ]
}

def scalarCert283 : MacroScalarCert 56 := {
  box := ⟨(177/4), (11623/256)⟩
  a := (3600341844467488615851330529/122070312500000000000000000000000)
  segments := [
    { box := ⟨(177/4), (5551521/125000)⟩, pieceIndex := 41 },
    { box := ⟨(5551521/125000), (1399599/31250)⟩, pieceIndex := 42 },
    { box := ⟨(1399599/31250), (11623/256)⟩, pieceIndex := 43 }
  ]
}

def scalarCert284 : MacroScalarCert 56 := {
  box := ⟨(177/4), (23187/512)⟩
  a := (3600341844467488615851330529/122070312500000000000000000000000)
  segments := [
    { box := ⟨(177/4), (5551521/125000)⟩, pieceIndex := 41 },
    { box := ⟨(5551521/125000), (1399599/31250)⟩, pieceIndex := 42 },
    { box := ⟨(1399599/31250), (23187/512)⟩, pieceIndex := 43 }
  ]
}

def scalarCert285 : MacroScalarCert 56 := {
  box := ⟨(22715/512), (11623/256)⟩
  a := (140156038325279709457315581152761/2000000000000000000000000000000000000)
  segments := [
    { box := ⟨(22715/512), (5551521/125000)⟩, pieceIndex := 41 },
    { box := ⟨(5551521/125000), (1399599/31250)⟩, pieceIndex := 42 },
    { box := ⟨(1399599/31250), (11623/256)⟩, pieceIndex := 43 }
  ]
}

def scalarCert286 : MacroScalarCert 56 := {
  box := ⟨(177/4), (5841/128)⟩
  a := (3600341844467488615851330529/122070312500000000000000000000000)
  segments := [
    { box := ⟨(177/4), (5551521/125000)⟩, pieceIndex := 41 },
    { box := ⟨(5551521/125000), (1399599/31250)⟩, pieceIndex := 42 },
    { box := ⟨(1399599/31250), (5841/128)⟩, pieceIndex := 43 }
  ]
}

def scalarCert287 : MacroScalarCert 56 := {
  box := ⟨(177/4), (23069/512)⟩
  a := (3600341844467488615851330529/122070312500000000000000000000000)
  segments := [
    { box := ⟨(177/4), (5551521/125000)⟩, pieceIndex := 41 },
    { box := ⟨(5551521/125000), (1399599/31250)⟩, pieceIndex := 42 },
    { box := ⟨(1399599/31250), (23069/512)⟩, pieceIndex := 43 }
  ]
}

def scalarCert288 : MacroScalarCert 56 := {
  box := ⟨(22715/512), (2891/64)⟩
  a := (140156038325279709457315581152761/2000000000000000000000000000000000000)
  segments := [
    { box := ⟨(22715/512), (5551521/125000)⟩, pieceIndex := 41 },
    { box := ⟨(5551521/125000), (1399599/31250)⟩, pieceIndex := 42 },
    { box := ⟨(1399599/31250), (2891/64)⟩, pieceIndex := 43 }
  ]
}

def scalarCert289 : MacroScalarCert 56 := {
  box := ⟨(22715/512), (23187/512)⟩
  a := (140156038325279709457315581152761/2000000000000000000000000000000000000)
  segments := [
    { box := ⟨(22715/512), (5551521/125000)⟩, pieceIndex := 41 },
    { box := ⟨(5551521/125000), (1399599/31250)⟩, pieceIndex := 42 },
    { box := ⟨(1399599/31250), (23187/512)⟩, pieceIndex := 43 }
  ]
}

def scalarCert290 : MacroScalarCert 56 := {
  box := ⟨(11387/256), (11623/256)⟩
  a := (65768103458522511747545895061489/500000000000000000000000000000000000)
  segments := [
    { box := ⟨(11387/256), (1399599/31250)⟩, pieceIndex := 42 },
    { box := ⟨(1399599/31250), (11623/256)⟩, pieceIndex := 43 }
  ]
}

def scalarCert291 : MacroScalarCert 56 := {
  box := ⟨(11387/256), (5841/128)⟩
  a := (65768103458522511747545895061489/500000000000000000000000000000000000)
  segments := [
    { box := ⟨(11387/256), (1399599/31250)⟩, pieceIndex := 42 },
    { box := ⟨(1399599/31250), (5841/128)⟩, pieceIndex := 43 }
  ]
}

def scalarCert292 : MacroScalarCert 56 := {
  box := ⟨(11387/256), (23305/512)⟩
  a := (65768103458522511747545895061489/500000000000000000000000000000000000)
  segments := [
    { box := ⟨(11387/256), (1399599/31250)⟩, pieceIndex := 42 },
    { box := ⟨(1399599/31250), (23305/512)⟩, pieceIndex := 43 }
  ]
}

def scalarCert293 : MacroScalarCert 56 := {
  box := ⟨(22833/512), (5841/128)⟩
  a := (403384292552130139662239000449081/2000000000000000000000000000000000000)
  segments := [
    { box := ⟨(22833/512), (1399599/31250)⟩, pieceIndex := 42 },
    { box := ⟨(1399599/31250), (5841/128)⟩, pieceIndex := 43 }
  ]
}

def scalarCert294 : MacroScalarCert 56 := {
  box := ⟨(22833/512), (23305/512)⟩
  a := (403384292552130139662239000449081/2000000000000000000000000000000000000)
  segments := [
    { box := ⟨(22833/512), (1399599/31250)⟩, pieceIndex := 42 },
    { box := ⟨(1399599/31250), (23305/512)⟩, pieceIndex := 43 }
  ]
}

def scalarCert295 : MacroScalarCert 56 := {
  box := ⟨(5723/128), (5841/128)⟩
  a := (236947891/1000000000000)
  segments := [
    { box := ⟨(5723/128), (1399599/31250)⟩, pieceIndex := 42 },
    { box := ⟨(1399599/31250), (5841/128)⟩, pieceIndex := 43 }
  ]
}

def scalarCert296 : MacroScalarCert 56 := {
  box := ⟨(177/4), (11741/256)⟩
  a := (3600341844467488615851330529/122070312500000000000000000000000)
  segments := [
    { box := ⟨(177/4), (5551521/125000)⟩, pieceIndex := 41 },
    { box := ⟨(5551521/125000), (1399599/31250)⟩, pieceIndex := 42 },
    { box := ⟨(1399599/31250), (11741/256)⟩, pieceIndex := 43 }
  ]
}

def scalarCert297 : MacroScalarCert 56 := {
  box := ⟨(11387/256), (11741/256)⟩
  a := (65768103458522511747545895061489/500000000000000000000000000000000000)
  segments := [
    { box := ⟨(11387/256), (1399599/31250)⟩, pieceIndex := 42 },
    { box := ⟨(1399599/31250), (11741/256)⟩, pieceIndex := 43 }
  ]
}

def scalarCert298 : MacroScalarCert 56 := {
  box := ⟨(177/4), (1475/32)⟩
  a := (3600341844467488615851330529/122070312500000000000000000000000)
  segments := [
    { box := ⟨(177/4), (5551521/125000)⟩, pieceIndex := 41 },
    { box := ⟨(5551521/125000), (1399599/31250)⟩, pieceIndex := 42 },
    { box := ⟨(1399599/31250), (1475/32)⟩, pieceIndex := 43 }
  ]
}

def scalarCert299 : MacroScalarCert 56 := {
  box := ⟨(11387/256), (1475/32)⟩
  a := (65768103458522511747545895061489/500000000000000000000000000000000000)
  segments := [
    { box := ⟨(11387/256), (1399599/31250)⟩, pieceIndex := 42 },
    { box := ⟨(1399599/31250), (1475/32)⟩, pieceIndex := 43 }
  ]
}

def scalarCert300 : MacroScalarCert 56 := {
  box := ⟨(11387/256), (23187/512)⟩
  a := (65768103458522511747545895061489/500000000000000000000000000000000000)
  segments := [
    { box := ⟨(11387/256), (1399599/31250)⟩, pieceIndex := 42 },
    { box := ⟨(1399599/31250), (23187/512)⟩, pieceIndex := 43 }
  ]
}

def scalarCert301 : MacroScalarCert 56 := {
  box := ⟨(22833/512), (11623/256)⟩
  a := (403384292552130139662239000449081/2000000000000000000000000000000000000)
  segments := [
    { box := ⟨(22833/512), (1399599/31250)⟩, pieceIndex := 42 },
    { box := ⟨(1399599/31250), (11623/256)⟩, pieceIndex := 43 }
  ]
}

def scalarCert302 : MacroScalarCert 56 := {
  box := ⟨(177/4), (5959/128)⟩
  a := (3600341844467488615851330529/122070312500000000000000000000000)
  segments := [
    { box := ⟨(177/4), (5551521/125000)⟩, pieceIndex := 41 },
    { box := ⟨(5551521/125000), (1399599/31250)⟩, pieceIndex := 42 },
    { box := ⟨(1399599/31250), (5959/128)⟩, pieceIndex := 43 }
  ]
}

def scalarCert303 : MacroScalarCert 56 := {
  box := ⟨(177/4), (11859/256)⟩
  a := (3600341844467488615851330529/122070312500000000000000000000000)
  segments := [
    { box := ⟨(177/4), (5551521/125000)⟩, pieceIndex := 41 },
    { box := ⟨(5551521/125000), (1399599/31250)⟩, pieceIndex := 42 },
    { box := ⟨(1399599/31250), (11859/256)⟩, pieceIndex := 43 }
  ]
}

def scalarCert304 : MacroScalarCert 56 := {
  box := ⟨(5723/128), (11741/256)⟩
  a := (236947891/1000000000000)
  segments := [
    { box := ⟨(5723/128), (1399599/31250)⟩, pieceIndex := 42 },
    { box := ⟨(1399599/31250), (11741/256)⟩, pieceIndex := 43 }
  ]
}

def scalarCert305 : MacroScalarCert 56 := {
  box := ⟨(5723/128), (23423/512)⟩
  a := (236947891/1000000000000)
  segments := [
    { box := ⟨(5723/128), (1399599/31250)⟩, pieceIndex := 42 },
    { box := ⟨(1399599/31250), (23423/512)⟩, pieceIndex := 43 }
  ]
}

def scalarCert306 : MacroScalarCert 56 := {
  box := ⟨(11387/256), (11859/256)⟩
  a := (65768103458522511747545895061489/500000000000000000000000000000000000)
  segments := [
    { box := ⟨(11387/256), (1399599/31250)⟩, pieceIndex := 42 },
    { box := ⟨(1399599/31250), (11859/256)⟩, pieceIndex := 43 }
  ]
}

def scalarCert307 : MacroScalarCert 56 := {
  box := ⟨(11387/256), (5959/128)⟩
  a := (65768103458522511747545895061489/500000000000000000000000000000000000)
  segments := [
    { box := ⟨(11387/256), (1399599/31250)⟩, pieceIndex := 42 },
    { box := ⟨(1399599/31250), (5959/128)⟩, pieceIndex := 43 }
  ]
}

def scalarCert308 : MacroScalarCert 56 := {
  box := ⟨(177/4), (3009/64)⟩
  a := (3600341844467488615851330529/122070312500000000000000000000000)
  segments := [
    { box := ⟨(177/4), (5551521/125000)⟩, pieceIndex := 41 },
    { box := ⟨(5551521/125000), (1399599/31250)⟩, pieceIndex := 42 },
    { box := ⟨(1399599/31250), (3009/64)⟩, pieceIndex := 43 }
  ]
}

def scalarCert309 : MacroScalarCert 56 := {
  box := ⟨(5723/128), (1475/32)⟩
  a := (236947891/1000000000000)
  segments := [
    { box := ⟨(5723/128), (1399599/31250)⟩, pieceIndex := 42 },
    { box := ⟨(1399599/31250), (1475/32)⟩, pieceIndex := 43 }
  ]
}

def scalarCert310 : MacroScalarCert 56 := {
  box := ⟨(5723/128), (11859/256)⟩
  a := (236947891/1000000000000)
  segments := [
    { box := ⟨(5723/128), (1399599/31250)⟩, pieceIndex := 42 },
    { box := ⟨(1399599/31250), (11859/256)⟩, pieceIndex := 43 }
  ]
}

def scalarCert311 : MacroScalarCert 56 := {
  box := ⟨(5723/128), (5959/128)⟩
  a := (236947891/1000000000000)
  segments := [
    { box := ⟨(5723/128), (1399599/31250)⟩, pieceIndex := 42 },
    { box := ⟨(1399599/31250), (5959/128)⟩, pieceIndex := 43 }
  ]
}

def scalarCert312 : MacroScalarCert 56 := {
  box := ⟨(5723/128), (3009/64)⟩
  a := (236947891/1000000000000)
  segments := [
    { box := ⟨(5723/128), (1399599/31250)⟩, pieceIndex := 42 },
    { box := ⟨(1399599/31250), (3009/64)⟩, pieceIndex := 43 }
  ]
}

def scalarCert313 : MacroScalarCert 56 := {
  box := ⟨(177/4), (6077/128)⟩
  a := (3600341844467488615851330529/122070312500000000000000000000000)
  segments := [
    { box := ⟨(177/4), (5551521/125000)⟩, pieceIndex := 41 },
    { box := ⟨(5551521/125000), (1399599/31250)⟩, pieceIndex := 42 },
    { box := ⟨(1399599/31250), (6077/128)⟩, pieceIndex := 43 }
  ]
}

def scalarCert314 : MacroScalarCert 56 := {
  box := ⟨(177/4), (767/16)⟩
  a := (3600341844467488615851330529/122070312500000000000000000000000)
  segments := [
    { box := ⟨(177/4), (5551521/125000)⟩, pieceIndex := 41 },
    { box := ⟨(5551521/125000), (1399599/31250)⟩, pieceIndex := 42 },
    { box := ⟨(1399599/31250), (767/16)⟩, pieceIndex := 43 }
  ]
}

def scalarCert315 : MacroScalarCert 56 := {
  box := ⟨(177/4), (3127/64)⟩
  a := (3600341844467488615851330529/122070312500000000000000000000000)
  segments := [
    { box := ⟨(177/4), (5551521/125000)⟩, pieceIndex := 41 },
    { box := ⟨(5551521/125000), (1399599/31250)⟩, pieceIndex := 42 },
    { box := ⟨(1399599/31250), (3127/64)⟩, pieceIndex := 43 }
  ]
}

def scalarCert316 : MacroScalarCert 56 := {
  box := ⟨(177/4), (1593/32)⟩
  a := (3600341844467488615851330529/122070312500000000000000000000000)
  segments := [
    { box := ⟨(177/4), (5551521/125000)⟩, pieceIndex := 41 },
    { box := ⟨(5551521/125000), (1399599/31250)⟩, pieceIndex := 42 },
    { box := ⟨(1399599/31250), (4956351/100000)⟩, pieceIndex := 43 },
    { box := ⟨(4956351/100000), (1593/32)⟩, pieceIndex := 44 }
  ]
}

def scalarCert317 : MacroScalarCert 56 := {
  box := ⟨(177/4), (6195/128)⟩
  a := (3600341844467488615851330529/122070312500000000000000000000000)
  segments := [
    { box := ⟨(177/4), (5551521/125000)⟩, pieceIndex := 41 },
    { box := ⟨(5551521/125000), (1399599/31250)⟩, pieceIndex := 42 },
    { box := ⟨(1399599/31250), (6195/128)⟩, pieceIndex := 43 }
  ]
}

def scalarCert318 : MacroScalarCert 56 := {
  box := ⟨(5723/128), (6077/128)⟩
  a := (236947891/1000000000000)
  segments := [
    { box := ⟨(5723/128), (1399599/31250)⟩, pieceIndex := 42 },
    { box := ⟨(1399599/31250), (6077/128)⟩, pieceIndex := 43 }
  ]
}

def scalarCert319 : MacroScalarCert 56 := {
  box := ⟨(5723/128), (767/16)⟩
  a := (236947891/1000000000000)
  segments := [
    { box := ⟨(5723/128), (1399599/31250)⟩, pieceIndex := 42 },
    { box := ⟨(1399599/31250), (767/16)⟩, pieceIndex := 43 }
  ]
}

def scalarCert320 : MacroScalarCert 56 := {
  box := ⟨(5723/128), (6195/128)⟩
  a := (236947891/1000000000000)
  segments := [
    { box := ⟨(5723/128), (1399599/31250)⟩, pieceIndex := 42 },
    { box := ⟨(1399599/31250), (6195/128)⟩, pieceIndex := 43 }
  ]
}

def scalarCert321 : MacroScalarCert 56 := {
  box := ⟨(5723/128), (3127/64)⟩
  a := (236947891/1000000000000)
  segments := [
    { box := ⟨(5723/128), (1399599/31250)⟩, pieceIndex := 42 },
    { box := ⟨(1399599/31250), (3127/64)⟩, pieceIndex := 43 }
  ]
}

def scalarCert322 : MacroScalarCert 56 := {
  box := ⟨(2891/64), (1593/32)⟩
  a := (46836154938348103515241447449/312500000000000000000000000000000)
  segments := [
    { box := ⟨(2891/64), (4956351/100000)⟩, pieceIndex := 43 },
    { box := ⟨(4956351/100000), (1593/32)⟩, pieceIndex := 44 }
  ]
}

def scalarCert323 : MacroScalarCert 56 := {
  box := ⟨(59/8), (531/64)⟩
  a := (3595147923/1000000000000)
  segments := [
    { box := ⟨(59/8), (1848269/250000)⟩, pieceIndex := 6 },
    { box := ⟨(1848269/250000), (531/64)⟩, pieceIndex := 7 }
  ]
}

def scalarCert324 : MacroScalarCert 56 := {
  box := ⟨(59/2), (1003/32)⟩
  a := (37896421104977184428389275321/1250000000000000000000000000000000)
  segments := [
    { box := ⟨(59/2), (15371317/500000)⟩, pieceIndex := 25 },
    { box := ⟨(15371317/500000), (15558817/500000)⟩, pieceIndex := 26 },
    { box := ⟨(15558817/500000), (1003/32)⟩, pieceIndex := 27 }
  ]
}

def scalarCert325 : MacroScalarCert 56 := {
  box := ⟨(2419/64), (9853/256)⟩
  a := (125628559827345406318287851649/125000000000000000000000000000000000)
  segments := [
    { box := ⟨(2419/64), (38138093/1000000)⟩, pieceIndex := 35 },
    { box := ⟨(38138093/1000000), (9853/256)⟩, pieceIndex := 36 }
  ]
}

def scalarCert326 : MacroScalarCert 56 := {
  box := ⟨(19411/512), (9853/256)⟩
  a := (625761533908596174465411009662769/32000000000000000000000000000000000000)
  segments := [
    { box := ⟨(19411/512), (38138093/1000000)⟩, pieceIndex := 35 },
    { box := ⟨(38138093/1000000), (9853/256)⟩, pieceIndex := 36 }
  ]
}

def scalarCert327 : MacroScalarCert 56 := {
  box := ⟨(9735/256), (19765/512)⟩
  a := (491938936455960966047921141896161/8000000000000000000000000000000000000)
  segments := [
    { box := ⟨(9735/256), (38138093/1000000)⟩, pieceIndex := 35 },
    { box := ⟨(38138093/1000000), (38513093/1000000)⟩, pieceIndex := 36 },
    { box := ⟨(38513093/1000000), (19765/512)⟩, pieceIndex := 37 }
  ]
}

def scalarCert328 : MacroScalarCert 56 := {
  box := ⟨(3009/128), (1593/64)⟩
  a := (1859160367141373243742933961/7629394531250000000000000000000)
  segments := [
    { box := ⟨(3009/128), (24478469/1000000)⟩, pieceIndex := 19 },
    { box := ⟨(24478469/1000000), (24853469/1000000)⟩, pieceIndex := 20 },
    { box := ⟨(24853469/1000000), (1593/64)⟩, pieceIndex := 21 }
  ]
}

def scalarCert329 : MacroScalarCert 56 := {
  box := ⟨(1121/64), (295/16)⟩
  a := (361710019498569118941886428649/312500000000000000000000000000000)
  segments := [
    { box := ⟨(1121/64), (9113373/500000)⟩, pieceIndex := 13 },
    { box := ⟨(9113373/500000), (295/16)⟩, pieceIndex := 14 }
  ]
}

def scalarCert330 : MacroScalarCert 56 := {
  box := ⟨(9499/512), (9617/512)⟩
  a := (4543500314017536620797999797247801/32000000000000000000000000000000000000)
  segments := [
    { box := ⟨(9499/512), (9300873/500000)⟩, pieceIndex := 14 },
    { box := ⟨(9300873/500000), (9617/512)⟩, pieceIndex := 15 }
  ]
}

def scalarCert331 : MacroScalarCert 56 := {
  box := ⟨(8083/256), (32745/1024)⟩
  a := (167322041776912901830875682929/20000000000000000000000000000000000)
  segments := [
    { box := ⟨(8083/256), (6373527/200000)⟩, pieceIndex := 29 },
    { box := ⟨(6373527/200000), (32745/1024)⟩, pieceIndex := 30 }
  ]
}

def scalarCert332 : MacroScalarCert 56 := {
  box := ⟨(9735/256), (39471/1024)⟩
  a := (491938936455960966047921141896161/8000000000000000000000000000000000000)
  segments := [
    { box := ⟨(9735/256), (38138093/1000000)⟩, pieceIndex := 35 },
    { box := ⟨(38138093/1000000), (38513093/1000000)⟩, pieceIndex := 36 },
    { box := ⟨(38513093/1000000), (39471/1024)⟩, pieceIndex := 37 }
  ]
}

def scalarCert333 : MacroScalarCert 56 := {
  box := ⟨(32391/1024), (8201/256)⟩
  a := (7793772368438963417005384017489/320000000000000000000000000000000000)
  segments := [
    { box := ⟨(32391/1024), (6373527/200000)⟩, pieceIndex := 29 },
    { box := ⟨(6373527/200000), (8201/256)⟩, pieceIndex := 30 }
  ]
}

def scalarCert334 : MacroScalarCert 56 := {
  box := ⟨(38999/1024), (19765/512)⟩
  a := (11677601791109548745136801743604201/128000000000000000000000000000000000000)
  segments := [
    { box := ⟨(38999/1024), (38138093/1000000)⟩, pieceIndex := 35 },
    { box := ⟨(38138093/1000000), (38513093/1000000)⟩, pieceIndex := 36 },
    { box := ⟨(38513093/1000000), (19765/512)⟩, pieceIndex := 37 }
  ]
}

def scalarCert335 : MacroScalarCert 56 := {
  box := ⟨(32273/1024), (16343/512)⟩
  a := (231042207594442269454532367489/320000000000000000000000000000000000)
  segments := [
    { box := ⟨(32273/1024), (6373527/200000)⟩, pieceIndex := 29 },
    { box := ⟨(6373527/200000), (16343/512)⟩, pieceIndex := 30 }
  ]
}

def scalarCert336 : MacroScalarCert 56 := {
  box := ⟨(19765/1024), (20001/1024)⟩
  a := (1823736530063038278523442761733881/5120000000000000000000000000000000000)
  segments := [
    { box := ⟨(19765/1024), (19351747/1000000)⟩, pieceIndex := 17 },
    { box := ⟨(19351747/1000000), (20001/1024)⟩, pieceIndex := 18 }
  ]
}

def scalarCert337 : MacroScalarCert 56 := {
  box := ⟨(32391/1024), (32745/1024)⟩
  a := (7793772368438963417005384017489/320000000000000000000000000000000000)
  segments := [
    { box := ⟨(32391/1024), (6373527/200000)⟩, pieceIndex := 29 },
    { box := ⟨(6373527/200000), (32745/1024)⟩, pieceIndex := 30 }
  ]
}

def scalarCert338 : MacroScalarCert 56 := {
  box := ⟨(38999/1024), (39471/1024)⟩
  a := (11677601791109548745136801743604201/128000000000000000000000000000000000000)
  segments := [
    { box := ⟨(38999/1024), (38138093/1000000)⟩, pieceIndex := 35 },
    { box := ⟨(38138093/1000000), (38513093/1000000)⟩, pieceIndex := 36 },
    { box := ⟨(38513093/1000000), (39471/1024)⟩, pieceIndex := 37 }
  ]
}

def scalarCert339 : MacroScalarCert 56 := {
  box := ⟨(13275/1024), (3363/256)⟩
  a := (10106004869046375733963486802372041/32000000000000000000000000000000000000)
  segments := [
    { box := ⟨(13275/1024), (13130291/1000000)⟩, pieceIndex := 11 },
    { box := ⟨(13130291/1000000), (3363/256)⟩, pieceIndex := 12 }
  ]
}

def scalarCert340 : MacroScalarCert 56 := {
  box := ⟨(16225/512), (8201/256)⟩
  a := (3895225326904878308147162909841/80000000000000000000000000000000000)
  segments := [
    { box := ⟨(16225/512), (6373527/200000)⟩, pieceIndex := 29 },
    { box := ⟨(6373527/200000), (8201/256)⟩, pieceIndex := 30 }
  ]
}

def scalarCert341 : MacroScalarCert 56 := {
  box := ⟨(19529/512), (19765/512)⟩
  a := (172336030037728650247271147738569/1280000000000000000000000000000000000)
  segments := [
    { box := ⟨(19529/512), (38513093/1000000)⟩, pieceIndex := 36 },
    { box := ⟨(38513093/1000000), (19765/512)⟩, pieceIndex := 37 }
  ]
}

def scalarCert342 : MacroScalarCert 56 := {
  box := ⟨(8083/256), (16343/512)⟩
  a := (167322041776912901830875682929/20000000000000000000000000000000000)
  segments := [
    { box := ⟨(8083/256), (6373527/200000)⟩, pieceIndex := 29 },
    { box := ⟨(6373527/200000), (16343/512)⟩, pieceIndex := 30 }
  ]
}

def scalarCert343 : MacroScalarCert 56 := {
  box := ⟨(19529/512), (39589/1024)⟩
  a := (172336030037728650247271147738569/1280000000000000000000000000000000000)
  segments := [
    { box := ⟨(19529/512), (38513093/1000000)⟩, pieceIndex := 36 },
    { box := ⟨(38513093/1000000), (39589/1024)⟩, pieceIndex := 37 }
  ]
}

def scalarCert344 : MacroScalarCert 56 := {
  box := ⟨(39117/1024), (1239/32)⟩
  a := (890431430789413157949114897032401/5120000000000000000000000000000000000)
  segments := [
    { box := ⟨(39117/1024), (38513093/1000000)⟩, pieceIndex := 36 },
    { box := ⟨(38513093/1000000), (1239/32)⟩, pieceIndex := 37 }
  ]
}

def scalarCert345 : MacroScalarCert 56 := {
  box := ⟨(16225/512), (32863/1024)⟩
  a := (3895225326904878308147162909841/80000000000000000000000000000000000)
  segments := [
    { box := ⟨(16225/512), (6373527/200000)⟩, pieceIndex := 29 },
    { box := ⟨(6373527/200000), (32863/1024)⟩, pieceIndex := 30 }
  ]
}

def scalarCert346 : MacroScalarCert 56 := {
  box := ⟨(3245/128), (26255/1024)⟩
  a := (146846847802364886838234197249/5000000000000000000000000000000000)
  segments := [
    { box := ⟨(3245/128), (2560347/100000)⟩, pieceIndex := 23 },
    { box := ⟨(2560347/100000), (26255/1024)⟩, pieceIndex := 24 }
  ]
}

def scalarCert347 : MacroScalarCert 56 := {
  box := ⟨(32509/1024), (16461/512)⟩
  a := (26038539485972255876043813792489/320000000000000000000000000000000000)
  segments := [
    { box := ⟨(32509/1024), (6373527/200000)⟩, pieceIndex := 29 },
    { box := ⟨(6373527/200000), (16461/512)⟩, pieceIndex := 30 }
  ]
}

def scalarCert348 : MacroScalarCert 56 := {
  box := ⟨(26019/1024), (13157/512)⟩
  a := (20255491443383191868469013039561/320000000000000000000000000000000000)
  segments := [
    { box := ⟨(26019/1024), (2560347/100000)⟩, pieceIndex := 23 },
    { box := ⟨(2560347/100000), (13157/512)⟩, pieceIndex := 24 }
  ]
}

def scalarCert349 : MacroScalarCert 56 := {
  box := ⟨(19647/1024), (19883/1024)⟩
  a := (759767742443179976299775611858881/5120000000000000000000000000000000000)
  segments := [
    { box := ⟨(19647/1024), (19351747/1000000)⟩, pieceIndex := 17 },
    { box := ⟨(19351747/1000000), (19883/1024)⟩, pieceIndex := 18 }
  ]
}

def scalarCert350 : MacroScalarCert 56 := {
  box := ⟨(39117/1024), (39589/1024)⟩
  a := (890431430789413157949114897032401/5120000000000000000000000000000000000)
  segments := [
    { box := ⟨(39117/1024), (38513093/1000000)⟩, pieceIndex := 36 },
    { box := ⟨(38513093/1000000), (39589/1024)⟩, pieceIndex := 37 }
  ]
}

def scalarCert351 : MacroScalarCert 56 := {
  box := ⟨(32509/1024), (32863/1024)⟩
  a := (26038539485972255876043813792489/320000000000000000000000000000000000)
  segments := [
    { box := ⟨(32509/1024), (6373527/200000)⟩, pieceIndex := 29 },
    { box := ⟨(6373527/200000), (32863/1024)⟩, pieceIndex := 30 }
  ]
}

def scalarCert352 : MacroScalarCert 56 := {
  box := ⟨(4897/128), (1239/32)⟩
  a := (17456552780050285252554156310809/80000000000000000000000000000000000)
  segments := [
    { box := ⟨(4897/128), (38513093/1000000)⟩, pieceIndex := 36 },
    { box := ⟨(38513093/1000000), (1239/32)⟩, pieceIndex := 37 }
  ]
}

def scalarCert353 : MacroScalarCert 56 := {
  box := ⟨(4071/128), (16461/512)⟩
  a := (611979482867143614802669851201/5000000000000000000000000000000000)
  segments := [
    { box := ⟨(4071/128), (6373527/200000)⟩, pieceIndex := 29 },
    { box := ⟨(6373527/200000), (16461/512)⟩, pieceIndex := 30 }
  ]
}

def scalarCert354 : MacroScalarCert 56 := {
  box := ⟨(4897/128), (39707/1024)⟩
  a := (17456552780050285252554156310809/80000000000000000000000000000000000)
  segments := [
    { box := ⟨(4897/128), (38513093/1000000)⟩, pieceIndex := 36 },
    { box := ⟨(38513093/1000000), (39707/1024)⟩, pieceIndex := 37 }
  ]
}

def scalarCert355 : MacroScalarCert 56 := {
  box := ⟨(39235/1024), (19883/512)⟩
  a := (1369707961552329895632137911532401/5120000000000000000000000000000000000)
  segments := [
    { box := ⟨(39235/1024), (38513093/1000000)⟩, pieceIndex := 36 },
    { box := ⟨(38513093/1000000), (19883/512)⟩, pieceIndex := 37 }
  ]
}

def scalarCert356 : MacroScalarCert 56 := {
  box := ⟨(39235/1024), (39707/1024)⟩
  a := (1369707961552329895632137911532401/5120000000000000000000000000000000000)
  segments := [
    { box := ⟨(39235/1024), (38513093/1000000)⟩, pieceIndex := 36 },
    { box := ⟨(38513093/1000000), (39707/1024)⟩, pieceIndex := 37 }
  ]
}

def scalarCert357 : MacroScalarCert 56 := {
  box := ⟨(19647/512), (19883/512)⟩
  a := (76986939/250000000000)
  segments := [
    { box := ⟨(19647/512), (38513093/1000000)⟩, pieceIndex := 36 },
    { box := ⟨(38513093/1000000), (19883/512)⟩, pieceIndex := 37 }
  ]
}

def scalarCert358 : MacroScalarCert 56 := {
  box := ⟨(4071/128), (32981/1024)⟩
  a := (611979482867143614802669851201/5000000000000000000000000000000000)
  segments := [
    { box := ⟨(4071/128), (6373527/200000)⟩, pieceIndex := 29 },
    { box := ⟨(6373527/200000), (32981/1024)⟩, pieceIndex := 30 }
  ]
}

def scalarCert359 : MacroScalarCert 56 := {
  box := ⟨(32627/1024), (2065/64)⟩
  a := (54965343560194319646569821692489/320000000000000000000000000000000000)
  segments := [
    { box := ⟨(32627/1024), (6373527/200000)⟩, pieceIndex := 29 },
    { box := ⟨(6373527/200000), (6448527/200000)⟩, pieceIndex := 30 },
    { box := ⟨(6448527/200000), (2065/64)⟩, pieceIndex := 31 }
  ]
}

def scalarCert360 : MacroScalarCert 56 := {
  box := ⟨(19647/512), (39825/1024)⟩
  a := (76986939/250000000000)
  segments := [
    { box := ⟨(19647/512), (38513093/1000000)⟩, pieceIndex := 36 },
    { box := ⟨(38513093/1000000), (39825/1024)⟩, pieceIndex := 37 }
  ]
}

def scalarCert361 : MacroScalarCert 56 := {
  box := ⟨(13039/512), (26373/1024)⟩
  a := (8807754158064216214287607996609/80000000000000000000000000000000000)
  segments := [
    { box := ⟨(13039/512), (2560347/100000)⟩, pieceIndex := 23 },
    { box := ⟨(2560347/100000), (26373/1024)⟩, pieceIndex := 24 }
  ]
}

def scalarCert362 : MacroScalarCert 56 := {
  box := ⟨(39353/1024), (9971/256)⟩
  a := (76986939/250000000000)
  segments := [
    { box := ⟨(39353/1024), (38513093/1000000)⟩, pieceIndex := 36 },
    { box := ⟨(38513093/1000000), (9971/256)⟩, pieceIndex := 37 }
  ]
}

def scalarCert363 : MacroScalarCert 56 := {
  box := ⟨(26137/1024), (413/16)⟩
  a := (54324773825972371723691245464561/320000000000000000000000000000000000)
  segments := [
    { box := ⟨(26137/1024), (2560347/100000)⟩, pieceIndex := 23 },
    { box := ⟨(2560347/100000), (413/16)⟩, pieceIndex := 24 }
  ]
}

def scalarCert364 : MacroScalarCert 56 := {
  box := ⟨(9853/256), (20001/512)⟩
  a := (76986939/250000000000)
  segments := [
    { box := ⟨(9853/256), (38513093/1000000)⟩, pieceIndex := 36 },
    { box := ⟨(38513093/1000000), (20001/512)⟩, pieceIndex := 37 }
  ]
}

def scalarCert365 : MacroScalarCert 56 := {
  box := ⟨(16343/512), (33099/1024)⟩
  a := (19145944597030269950435668435441/80000000000000000000000000000000000)
  segments := [
    { box := ⟨(16343/512), (6448527/200000)⟩, pieceIndex := 30 },
    { box := ⟨(6448527/200000), (33099/1024)⟩, pieceIndex := 31 }
  ]
}

def scalarCert366 : MacroScalarCert 56 := {
  box := ⟨(32745/1024), (16579/512)⟩
  a := (96378734194223377991070077769889/320000000000000000000000000000000000)
  segments := [
    { box := ⟨(32745/1024), (6448527/200000)⟩, pieceIndex := 30 },
    { box := ⟨(6448527/200000), (16579/512)⟩, pieceIndex := 31 }
  ]
}

def scalarCert367 : MacroScalarCert 56 := {
  box := ⟨(13157/512), (6667/256)⟩
  a := (1405713487152099986076881071449/3200000000000000000000000000000000)
  segments := [
    { box := ⟨(13157/512), (2597847/100000)⟩, pieceIndex := 24 },
    { box := ⟨(2597847/100000), (6667/256)⟩, pieceIndex := 25 }
  ]
}

def scalarCert368 : MacroScalarCert 56 := {
  box := ⟨(32627/1024), (32981/1024)⟩
  a := (54965343560194319646569821692489/320000000000000000000000000000000000)
  segments := [
    { box := ⟨(32627/1024), (6373527/200000)⟩, pieceIndex := 29 },
    { box := ⟨(6373527/200000), (32981/1024)⟩, pieceIndex := 30 }
  ]
}

def scalarCert369 : MacroScalarCert 56 := {
  box := ⟨(16343/512), (2065/64)⟩
  a := (19145944597030269950435668435441/80000000000000000000000000000000000)
  segments := [
    { box := ⟨(16343/512), (6448527/200000)⟩, pieceIndex := 30 },
    { box := ⟨(6448527/200000), (2065/64)⟩, pieceIndex := 31 }
  ]
}

def scalarCert370 : MacroScalarCert 56 := {
  box := ⟨(26019/1024), (26255/1024)⟩
  a := (20255491443383191868469013039561/320000000000000000000000000000000000)
  segments := [
    { box := ⟨(26019/1024), (2560347/100000)⟩, pieceIndex := 23 },
    { box := ⟨(2560347/100000), (26255/1024)⟩, pieceIndex := 24 }
  ]
}

def scalarCert371 : MacroScalarCert 56 := {
  box := ⟨(13039/512), (13157/512)⟩
  a := (8807754158064216214287607996609/80000000000000000000000000000000000)
  segments := [
    { box := ⟨(13039/512), (2560347/100000)⟩, pieceIndex := 23 },
    { box := ⟨(2560347/100000), (13157/512)⟩, pieceIndex := 24 }
  ]
}

def scalarCert372 : MacroScalarCert 56 := {
  box := ⟨(39353/1024), (39825/1024)⟩
  a := (76986939/250000000000)
  segments := [
    { box := ⟨(39353/1024), (38513093/1000000)⟩, pieceIndex := 36 },
    { box := ⟨(38513093/1000000), (39825/1024)⟩, pieceIndex := 37 }
  ]
}

def scalarCert373 : MacroScalarCert 56 := {
  box := ⟨(32745/1024), (33099/1024)⟩
  a := (96378734194223377991070077769889/320000000000000000000000000000000000)
  segments := [
    { box := ⟨(32745/1024), (6448527/200000)⟩, pieceIndex := 30 },
    { box := ⟨(6448527/200000), (33099/1024)⟩, pieceIndex := 31 }
  ]
}

def scalarCert374 : MacroScalarCert 56 := {
  box := ⟨(9853/256), (9971/256)⟩
  a := (76986939/250000000000)
  segments := [
    { box := ⟨(9853/256), (38513093/1000000)⟩, pieceIndex := 36 },
    { box := ⟨(38513093/1000000), (9971/256)⟩, pieceIndex := 37 }
  ]
}

def scalarCert375 : MacroScalarCert 56 := {
  box := ⟨(8201/256), (16579/512)⟩
  a := (7402913802521846133201894614329/20000000000000000000000000000000000)
  segments := [
    { box := ⟨(8201/256), (6448527/200000)⟩, pieceIndex := 30 },
    { box := ⟨(6448527/200000), (16579/512)⟩, pieceIndex := 31 }
  ]
}

def scalarCert376 : MacroScalarCert 56 := {
  box := ⟨(9853/256), (39943/1024)⟩
  a := (76986939/250000000000)
  segments := [
    { box := ⟨(9853/256), (38513093/1000000)⟩, pieceIndex := 36 },
    { box := ⟨(38513093/1000000), (39943/1024)⟩, pieceIndex := 37 }
  ]
}

def scalarCert377 : MacroScalarCert 56 := {
  box := ⟨(8201/256), (33217/1024)⟩
  a := (7402913802521846133201894614329/20000000000000000000000000000000000)
  segments := [
    { box := ⟨(8201/256), (6448527/200000)⟩, pieceIndex := 30 },
    { box := ⟨(6448527/200000), (33217/1024)⟩, pieceIndex := 31 }
  ]
}

def scalarCert378 : MacroScalarCert 56 := {
  box := ⟨(6549/256), (26491/1024)⟩
  a := (4846047689033107029255715842121/20000000000000000000000000000000000)
  segments := [
    { box := ⟨(6549/256), (2560347/100000)⟩, pieceIndex := 23 },
    { box := ⟨(2560347/100000), (26491/1024)⟩, pieceIndex := 24 }
  ]
}

def scalarCert379 : MacroScalarCert 56 := {
  box := ⟨(32863/1024), (8319/256)⟩
  a := (104124691/250000000000)
  segments := [
    { box := ⟨(32863/1024), (6448527/200000)⟩, pieceIndex := 30 },
    { box := ⟨(6448527/200000), (8319/256)⟩, pieceIndex := 31 }
  ]
}

def scalarCert380 : MacroScalarCert 56 := {
  box := ⟨(16461/512), (16697/512)⟩
  a := (104124691/250000000000)
  segments := [
    { box := ⟨(16461/512), (6448527/200000)⟩, pieceIndex := 30 },
    { box := ⟨(6448527/200000), (16697/512)⟩, pieceIndex := 31 }
  ]
}

def scalarCert381 : MacroScalarCert 56 := {
  box := ⟨(9971/512), (20237/1024)⟩
  a := (1100717327808522518900723987406129/1280000000000000000000000000000000000)
  segments := [
    { box := ⟨(9971/512), (19726747/1000000)⟩, pieceIndex := 18 },
    { box := ⟨(19726747/1000000), (20237/1024)⟩, pieceIndex := 19 }
  ]
}

def scalarCert382 : MacroScalarCert 56 := {
  box := ⟨(20001/1024), (2537/128)⟩
  a := (459565243/500000000000)
  segments := [
    { box := ⟨(20001/1024), (19726747/1000000)⟩, pieceIndex := 18 },
    { box := ⟨(19726747/1000000), (2537/128)⟩, pieceIndex := 19 }
  ]
}

def scalarCert383 : MacroScalarCert 56 := {
  box := ⟨(6667/512), (3363/256)⟩
  a := (4115134404786270922924483404604729/8000000000000000000000000000000000000)
  segments := [
    { box := ⟨(6667/512), (13130291/1000000)⟩, pieceIndex := 11 },
    { box := ⟨(13130291/1000000), (3363/256)⟩, pieceIndex := 12 }
  ]
}

def scalarCert384 : MacroScalarCert 56 := {
  box := ⟨(413/16), (13393/512)⟩
  a := (148698801/250000000000)
  segments := [
    { box := ⟨(413/16), (2597847/100000)⟩, pieceIndex := 24 },
    { box := ⟨(2597847/100000), (13393/512)⟩, pieceIndex := 25 }
  ]
}

def scalarCert385 : MacroScalarCert 56 := {
  box := ⟨(295/16), (4779/256)⟩
  a := (2891119993742916046127024249511169/8000000000000000000000000000000000000)
  segments := [
    { box := ⟨(295/16), (9300873/500000)⟩, pieceIndex := 14 },
    { box := ⟨(9300873/500000), (4779/256)⟩, pieceIndex := 15 }
  ]
}

def scalarCert386 : MacroScalarCert 56 := {
  box := ⟨(767/64), (6195/512)⟩
  a := (3595147923/1000000000000)
  segments := [
    { box := ⟨(767/64), (1200529/100000)⟩, pieceIndex := 7 },
    { box := ⟨(1200529/100000), (6195/512)⟩, pieceIndex := 8 }
  ]
}

def scalarCert387 : MacroScalarCert 56 := {
  box := ⟨(6667/512), (13511/1024)⟩
  a := (4115134404786270922924483404604729/8000000000000000000000000000000000000)
  segments := [
    { box := ⟨(6667/512), (13130291/1000000)⟩, pieceIndex := 11 },
    { box := ⟨(13130291/1000000), (13511/1024)⟩, pieceIndex := 12 }
  ]
}

def scalarCert388 : MacroScalarCert 56 := {
  box := ⟨(20001/1024), (20237/1024)⟩
  a := (459565243/500000000000)
  segments := [
    { box := ⟨(20001/1024), (19726747/1000000)⟩, pieceIndex := 18 },
    { box := ⟨(19726747/1000000), (20237/1024)⟩, pieceIndex := 19 }
  ]
}

def scalarCert389 : MacroScalarCert 56 := {
  box := ⟨(13393/1024), (6785/512)⟩
  a := (24357416126080533826418298891497041/32000000000000000000000000000000000000)
  segments := [
    { box := ⟨(13393/1024), (13130291/1000000)⟩, pieceIndex := 11 },
    { box := ⟨(13130291/1000000), (6785/512)⟩, pieceIndex := 12 }
  ]
}

def scalarCert390 : MacroScalarCert 56 := {
  box := ⟨(5015/256), (2537/128)⟩
  a := (459565243/500000000000)
  segments := [
    { box := ⟨(5015/256), (19726747/1000000)⟩, pieceIndex := 18 },
    { box := ⟨(19726747/1000000), (2537/128)⟩, pieceIndex := 19 }
  ]
}

def scalarCert391 : MacroScalarCert 56 := {
  box := ⟨(13393/1024), (13511/1024)⟩
  a := (24357416126080533826418298891497041/32000000000000000000000000000000000000)
  segments := [
    { box := ⟨(13393/1024), (13130291/1000000)⟩, pieceIndex := 11 },
    { box := ⟨(13130291/1000000), (13511/1024)⟩, pieceIndex := 12 }
  ]
}

def scalarCert392 : MacroScalarCert 56 := {
  box := ⟨(5015/256), (20355/1024)⟩
  a := (459565243/500000000000)
  segments := [
    { box := ⟨(5015/256), (19726747/1000000)⟩, pieceIndex := 18 },
    { box := ⟨(19726747/1000000), (20355/1024)⟩, pieceIndex := 19 }
  ]
}

def scalarCert393 : MacroScalarCert 56 := {
  box := ⟨(20119/1024), (20355/1024)⟩
  a := (459565243/500000000000)
  segments := [
    { box := ⟨(20119/1024), (19726747/1000000)⟩, pieceIndex := 18 },
    { box := ⟨(19726747/1000000), (20355/1024)⟩, pieceIndex := 19 }
  ]
}

def scalarCert394 : MacroScalarCert 56 := {
  box := ⟨(20119/1024), (10207/512)⟩
  a := (459565243/500000000000)
  segments := [
    { box := ⟨(20119/1024), (19726747/1000000)⟩, pieceIndex := 18 },
    { box := ⟨(19726747/1000000), (10207/512)⟩, pieceIndex := 19 }
  ]
}

def scalarCert395 : MacroScalarCert 56 := {
  box := ⟨(32863/1024), (33217/1024)⟩
  a := (104124691/250000000000)
  segments := [
    { box := ⟨(32863/1024), (6448527/200000)⟩, pieceIndex := 30 },
    { box := ⟨(6448527/200000), (33217/1024)⟩, pieceIndex := 31 }
  ]
}

def scalarCert396 : MacroScalarCert 56 := {
  box := ⟨(26137/1024), (26373/1024)⟩
  a := (54324773825972371723691245464561/320000000000000000000000000000000000)
  segments := [
    { box := ⟨(26137/1024), (2560347/100000)⟩, pieceIndex := 23 },
    { box := ⟨(2560347/100000), (26373/1024)⟩, pieceIndex := 24 }
  ]
}

def scalarCert397 : MacroScalarCert 56 := {
  box := ⟨(16461/512), (33335/1024)⟩
  a := (104124691/250000000000)
  segments := [
    { box := ⟨(16461/512), (6448527/200000)⟩, pieceIndex := 30 },
    { box := ⟨(6448527/200000), (33335/1024)⟩, pieceIndex := 31 }
  ]
}

def scalarCert398 : MacroScalarCert 56 := {
  box := ⟨(13157/512), (26609/1024)⟩
  a := (1405713487152099986076881071449/3200000000000000000000000000000000)
  segments := [
    { box := ⟨(13157/512), (2597847/100000)⟩, pieceIndex := 24 },
    { box := ⟨(2597847/100000), (26609/1024)⟩, pieceIndex := 25 }
  ]
}

def scalarCert399 : MacroScalarCert 56 := {
  box := ⟨(32981/1024), (16697/512)⟩
  a := (104124691/250000000000)
  segments := [
    { box := ⟨(32981/1024), (6448527/200000)⟩, pieceIndex := 30 },
    { box := ⟨(6448527/200000), (16697/512)⟩, pieceIndex := 31 }
  ]
}

def scalarCert400 : MacroScalarCert 56 := {
  box := ⟨(19647/1024), (1239/64)⟩
  a := (759767742443179976299775611858881/5120000000000000000000000000000000000)
  segments := [
    { box := ⟨(19647/1024), (19351747/1000000)⟩, pieceIndex := 17 },
    { box := ⟨(19351747/1000000), (1239/64)⟩, pieceIndex := 18 }
  ]
}

def scalarCert401 : MacroScalarCert 56 := {
  box := ⟨(26373/1024), (6667/256)⟩
  a := (6939535078070123213019812388921/12800000000000000000000000000000000)
  segments := [
    { box := ⟨(26373/1024), (2597847/100000)⟩, pieceIndex := 24 },
    { box := ⟨(2597847/100000), (6667/256)⟩, pieceIndex := 25 }
  ]
}

def scalarCert402 : MacroScalarCert 56 := {
  box := ⟨(1829/64), (1003/32)⟩
  a := (37896421104977184428389275321/1250000000000000000000000000000000)
  segments := [
    { box := ⟨(1829/64), (15371317/500000)⟩, pieceIndex := 25 },
    { box := ⟨(15371317/500000), (15558817/500000)⟩, pieceIndex := 26 },
    { box := ⟨(15558817/500000), (1003/32)⟩, pieceIndex := 27 }
  ]
}

def scalarCert403 : MacroScalarCert 56 := {
  box := ⟨(1475/64), (1593/64)⟩
  a := (1859160367141373243742933961/7629394531250000000000000000000)
  segments := [
    { box := ⟨(1475/64), (24478469/1000000)⟩, pieceIndex := 19 },
    { box := ⟨(24478469/1000000), (24853469/1000000)⟩, pieceIndex := 20 },
    { box := ⟨(24853469/1000000), (1593/64)⟩, pieceIndex := 21 }
  ]
}

def scalarCert404 : MacroScalarCert 56 := {
  box := ⟨(2419/64), (19647/512)⟩
  a := (125628559827345406318287851649/125000000000000000000000000000000000)
  segments := [
    { box := ⟨(2419/64), (38138093/1000000)⟩, pieceIndex := 35 },
    { box := ⟨(38138093/1000000), (19647/512)⟩, pieceIndex := 36 }
  ]
}

def scalarCert405 : MacroScalarCert 56 := {
  box := ⟨(3835/128), (1003/32)⟩
  a := (37896421104977184428389275321/1250000000000000000000000000000000)
  segments := [
    { box := ⟨(3835/128), (15371317/500000)⟩, pieceIndex := 25 },
    { box := ⟨(15371317/500000), (15558817/500000)⟩, pieceIndex := 26 },
    { box := ⟨(15558817/500000), (1003/32)⟩, pieceIndex := 27 }
  ]
}

def scalarCert406 : MacroScalarCert 56 := {
  box := ⟨(767/32), (1593/64)⟩
  a := (1859160367141373243742933961/7629394531250000000000000000000)
  segments := [
    { box := ⟨(767/32), (24478469/1000000)⟩, pieceIndex := 19 },
    { box := ⟨(24478469/1000000), (24853469/1000000)⟩, pieceIndex := 20 },
    { box := ⟨(24853469/1000000), (1593/64)⟩, pieceIndex := 21 }
  ]
}

def scalarCert407 : MacroScalarCert 56 := {
  box := ⟨(6313/256), (6431/256)⟩
  a := (769227545671561646446829644881/31250000000000000000000000000000000)
  segments := [
    { box := ⟨(6313/256), (24853469/1000000)⟩, pieceIndex := 20 },
    { box := ⟨(24853469/1000000), (6431/256)⟩, pieceIndex := 21 }
  ]
}

def scalarCert408 : MacroScalarCert 56 := {
  box := ⟨(3953/128), (16107/512)⟩
  a := (1982313064455441554709887444329/1280000000000000000000000000000000000)
  segments := [
    { box := ⟨(3953/128), (15558817/500000)⟩, pieceIndex := 26 },
    { box := ⟨(15558817/500000), (16107/512)⟩, pieceIndex := 27 }
  ]
}

def scalarCert409 : MacroScalarCert 56 := {
  box := ⟨(7847/256), (1003/32)⟩
  a := (37896421104977184428389275321/1250000000000000000000000000000000)
  segments := [
    { box := ⟨(7847/256), (15371317/500000)⟩, pieceIndex := 25 },
    { box := ⟨(15371317/500000), (15558817/500000)⟩, pieceIndex := 26 },
    { box := ⟨(15558817/500000), (1003/32)⟩, pieceIndex := 27 }
  ]
}

def scalarCert410 : MacroScalarCert 56 := {
  box := ⟨(3127/128), (1593/64)⟩
  a := (1859160367141373243742933961/7629394531250000000000000000000)
  segments := [
    { box := ⟨(3127/128), (24478469/1000000)⟩, pieceIndex := 19 },
    { box := ⟨(24478469/1000000), (24853469/1000000)⟩, pieceIndex := 20 },
    { box := ⟨(24853469/1000000), (1593/64)⟩, pieceIndex := 21 }
  ]
}

def scalarCert411 : MacroScalarCert 56 := {
  box := ⟨(177/4), (11505/256)⟩
  a := (3600341844467488615851330529/122070312500000000000000000000000)
  segments := [
    { box := ⟨(177/4), (5551521/125000)⟩, pieceIndex := 41 },
    { box := ⟨(5551521/125000), (1399599/31250)⟩, pieceIndex := 42 },
    { box := ⟨(1399599/31250), (11505/256)⟩, pieceIndex := 43 }
  ]
}

def scalarCert412 : MacroScalarCert 56 := {
  box := ⟨(22715/512), (23069/512)⟩
  a := (140156038325279709457315581152761/2000000000000000000000000000000000000)
  segments := [
    { box := ⟨(22715/512), (5551521/125000)⟩, pieceIndex := 41 },
    { box := ⟨(5551521/125000), (1399599/31250)⟩, pieceIndex := 42 },
    { box := ⟨(1399599/31250), (23069/512)⟩, pieceIndex := 43 }
  ]
}

def scalarCert413 : MacroScalarCert 56 := {
  box := ⟨(11387/256), (2891/64)⟩
  a := (65768103458522511747545895061489/500000000000000000000000000000000000)
  segments := [
    { box := ⟨(11387/256), (1399599/31250)⟩, pieceIndex := 42 },
    { box := ⟨(1399599/31250), (2891/64)⟩, pieceIndex := 43 }
  ]
}

def scalarCert414 : MacroScalarCert 56 := {
  box := ⟨(6313/256), (12803/512)⟩
  a := (13224910662800597294854280157649/125000000000000000000000000000000000)
  segments := [
    { box := ⟨(6313/256), (24853469/1000000)⟩, pieceIndex := 20 },
    { box := ⟨(24853469/1000000), (12803/512)⟩, pieceIndex := 21 }
  ]
}

def scalarCert415 : MacroScalarCert 56 := {
  box := ⟨(12685/512), (6431/256)⟩
  a := (769227545671561646446829644881/31250000000000000000000000000000000)
  segments := [
    { box := ⟨(12685/512), (24853469/1000000)⟩, pieceIndex := 20 },
    { box := ⟨(24853469/1000000), (6431/256)⟩, pieceIndex := 21 }
  ]
}

def scalarCert416 : MacroScalarCert 56 := {
  box := ⟨(22597/512), (22951/512)⟩
  a := (12404326906898653543170837152761/2000000000000000000000000000000000000)
  segments := [
    { box := ⟨(22597/512), (5551521/125000)⟩, pieceIndex := 41 },
    { box := ⟨(5551521/125000), (1399599/31250)⟩, pieceIndex := 42 },
    { box := ⟨(1399599/31250), (22951/512)⟩, pieceIndex := 43 }
  ]
}

def scalarCert417 : MacroScalarCert 56 := {
  box := ⟨(1947/64), (1003/32)⟩
  a := (37896421104977184428389275321/1250000000000000000000000000000000)
  segments := [
    { box := ⟨(1947/64), (15371317/500000)⟩, pieceIndex := 25 },
    { box := ⟨(15371317/500000), (15558817/500000)⟩, pieceIndex := 26 },
    { box := ⟨(15558817/500000), (1003/32)⟩, pieceIndex := 27 }
  ]
}

def scalarCert418 : MacroScalarCert 56 := {
  box := ⟨(767/32), (6313/256)⟩
  a := (1408273486016716753984882108683841/2000000000000000000000000000000000000)
  segments := [
    { box := ⟨(767/32), (24478469/1000000)⟩, pieceIndex := 19 },
    { box := ⟨(24478469/1000000), (6313/256)⟩, pieceIndex := 20 }
  ]
}

def scalarCert419 : MacroScalarCert 56 := {
  box := ⟨(6195/256), (1593/64)⟩
  a := (1859160367141373243742933961/7629394531250000000000000000000)
  segments := [
    { box := ⟨(6195/256), (24478469/1000000)⟩, pieceIndex := 19 },
    { box := ⟨(24478469/1000000), (24853469/1000000)⟩, pieceIndex := 20 },
    { box := ⟨(24853469/1000000), (1593/64)⟩, pieceIndex := 21 }
  ]
}

def scalarCert420 : MacroScalarCert 56 := {
  box := ⟨(6195/256), (6313/256)⟩
  a := (1408273486016716753984882108683841/2000000000000000000000000000000000000)
  segments := [
    { box := ⟨(6195/256), (24478469/1000000)⟩, pieceIndex := 19 },
    { box := ⟨(24478469/1000000), (6313/256)⟩, pieceIndex := 20 }
  ]
}

def scalarCert421 : MacroScalarCert 56 := {
  box := ⟨(22715/512), (11505/256)⟩
  a := (140156038325279709457315581152761/2000000000000000000000000000000000000)
  segments := [
    { box := ⟨(22715/512), (5551521/125000)⟩, pieceIndex := 41 },
    { box := ⟨(5551521/125000), (1399599/31250)⟩, pieceIndex := 42 },
    { box := ⟨(1399599/31250), (11505/256)⟩, pieceIndex := 43 }
  ]
}

def scalarCert422 : MacroScalarCert 56 := {
  box := ⟨(2419/64), (4897/128)⟩
  a := (125628559827345406318287851649/125000000000000000000000000000000000)
  segments := [
    { box := ⟨(2419/64), (38138093/1000000)⟩, pieceIndex := 35 },
    { box := ⟨(38138093/1000000), (4897/128)⟩, pieceIndex := 36 }
  ]
}

def scalarCert423 : MacroScalarCert 56 := {
  box := ⟨(11387/256), (23069/512)⟩
  a := (65768103458522511747545895061489/500000000000000000000000000000000000)
  segments := [
    { box := ⟨(11387/256), (1399599/31250)⟩, pieceIndex := 42 },
    { box := ⟨(1399599/31250), (23069/512)⟩, pieceIndex := 43 }
  ]
}

def scalarCert424 : MacroScalarCert 56 := {
  box := ⟨(19411/512), (19647/512)⟩
  a := (625761533908596174465411009662769/32000000000000000000000000000000000000)
  segments := [
    { box := ⟨(19411/512), (38138093/1000000)⟩, pieceIndex := 35 },
    { box := ⟨(38138093/1000000), (19647/512)⟩, pieceIndex := 36 }
  ]
}

def scalarCert425 : MacroScalarCert 56 := {
  box := ⟨(22833/512), (23187/512)⟩
  a := (403384292552130139662239000449081/2000000000000000000000000000000000000)
  segments := [
    { box := ⟨(22833/512), (1399599/31250)⟩, pieceIndex := 42 },
    { box := ⟨(1399599/31250), (23187/512)⟩, pieceIndex := 43 }
  ]
}

def scalarCert426 : MacroScalarCert 56 := {
  box := ⟨(5723/128), (11623/256)⟩
  a := (236947891/1000000000000)
  segments := [
    { box := ⟨(5723/128), (1399599/31250)⟩, pieceIndex := 42 },
    { box := ⟨(1399599/31250), (11623/256)⟩, pieceIndex := 43 }
  ]
}

def scalarCert427 : MacroScalarCert 56 := {
  box := ⟨(5723/128), (23305/512)⟩
  a := (236947891/1000000000000)
  segments := [
    { box := ⟨(5723/128), (1399599/31250)⟩, pieceIndex := 42 },
    { box := ⟨(1399599/31250), (23305/512)⟩, pieceIndex := 43 }
  ]
}

def scalarCert428 : MacroScalarCert 56 := {
  box := ⟨(5723/128), (11977/256)⟩
  a := (236947891/1000000000000)
  segments := [
    { box := ⟨(5723/128), (1399599/31250)⟩, pieceIndex := 42 },
    { box := ⟨(1399599/31250), (11977/256)⟩, pieceIndex := 43 }
  ]
}

def scalarCert429 : MacroScalarCert 56 := {
  box := ⟨(177/4), (22951/512)⟩
  a := (3600341844467488615851330529/122070312500000000000000000000000)
  segments := [
    { box := ⟨(177/4), (5551521/125000)⟩, pieceIndex := 41 },
    { box := ⟨(5551521/125000), (1399599/31250)⟩, pieceIndex := 42 },
    { box := ⟨(1399599/31250), (22951/512)⟩, pieceIndex := 43 }
  ]
}

def scalarCert430 : MacroScalarCert 56 := {
  box := ⟨(22597/512), (5723/128)⟩
  a := (12404326906898653543170837152761/2000000000000000000000000000000000000)
  segments := [
    { box := ⟨(22597/512), (5551521/125000)⟩, pieceIndex := 41 },
    { box := ⟨(5551521/125000), (5723/128)⟩, pieceIndex := 42 }
  ]
}

def scalarCert431 : MacroScalarCert 56 := {
  box := ⟨(2419/64), (39117/1024)⟩
  a := (125628559827345406318287851649/125000000000000000000000000000000000)
  segments := [
    { box := ⟨(2419/64), (38138093/1000000)⟩, pieceIndex := 35 },
    { box := ⟨(38138093/1000000), (39117/1024)⟩, pieceIndex := 36 }
  ]
}

def scalarCert432 : MacroScalarCert 56 := {
  box := ⟨(22715/512), (45961/1024)⟩
  a := (140156038325279709457315581152761/2000000000000000000000000000000000000)
  segments := [
    { box := ⟨(22715/512), (5551521/125000)⟩, pieceIndex := 41 },
    { box := ⟨(5551521/125000), (1399599/31250)⟩, pieceIndex := 42 },
    { box := ⟨(1399599/31250), (45961/1024)⟩, pieceIndex := 43 }
  ]
}

def scalarCert433 : MacroScalarCert 56 := {
  box := ⟨(38763/1024), (4897/128)⟩
  a := (941648095787567227326613280229201/128000000000000000000000000000000000000)
  segments := [
    { box := ⟨(38763/1024), (38138093/1000000)⟩, pieceIndex := 35 },
    { box := ⟨(38138093/1000000), (4897/128)⟩, pieceIndex := 36 }
  ]
}

def scalarCert434 : MacroScalarCert 56 := {
  box := ⟨(45489/1024), (11505/256)⟩
  a := (816478761924151067555100775499449/8000000000000000000000000000000000000)
  segments := [
    { box := ⟨(45489/1024), (1399599/31250)⟩, pieceIndex := 42 },
    { box := ⟨(1399599/31250), (11505/256)⟩, pieceIndex := 43 }
  ]
}

def scalarCert435 : MacroScalarCert 56 := {
  box := ⟨(19411/512), (39235/1024)⟩
  a := (625761533908596174465411009662769/32000000000000000000000000000000000000)
  segments := [
    { box := ⟨(19411/512), (38138093/1000000)⟩, pieceIndex := 35 },
    { box := ⟨(38138093/1000000), (39235/1024)⟩, pieceIndex := 36 }
  ]
}

def scalarCert436 : MacroScalarCert 56 := {
  box := ⟨(38881/1024), (19647/512)⟩
  a := (4812837764803654107675019035354201/128000000000000000000000000000000000000)
  segments := [
    { box := ⟨(38881/1024), (38138093/1000000)⟩, pieceIndex := 35 },
    { box := ⟨(38138093/1000000), (19647/512)⟩, pieceIndex := 36 }
  ]
}

def scalarCert437 : MacroScalarCert 56 := {
  box := ⟨(11387/256), (46079/1024)⟩
  a := (65768103458522511747545895061489/500000000000000000000000000000000000)
  segments := [
    { box := ⟨(11387/256), (1399599/31250)⟩, pieceIndex := 42 },
    { box := ⟨(1399599/31250), (46079/1024)⟩, pieceIndex := 43 }
  ]
}

def scalarCert438 : MacroScalarCert 56 := {
  box := ⟨(45607/1024), (23069/512)⟩
  a := (1317975791431150018325352729749449/8000000000000000000000000000000000000)
  segments := [
    { box := ⟨(45607/1024), (1399599/31250)⟩, pieceIndex := 42 },
    { box := ⟨(1399599/31250), (23069/512)⟩, pieceIndex := 43 }
  ]
}

def scalarCert439 : MacroScalarCert 56 := {
  box := ⟨(9735/256), (9853/256)⟩
  a := (491938936455960966047921141896161/8000000000000000000000000000000000000)
  segments := [
    { box := ⟨(9735/256), (38138093/1000000)⟩, pieceIndex := 35 },
    { box := ⟨(38138093/1000000), (9853/256)⟩, pieceIndex := 36 }
  ]
}

def scalarCert440 : MacroScalarCert 56 := {
  box := ⟨(9735/256), (39353/1024)⟩
  a := (491938936455960966047921141896161/8000000000000000000000000000000000000)
  segments := [
    { box := ⟨(9735/256), (38138093/1000000)⟩, pieceIndex := 35 },
    { box := ⟨(38138093/1000000), (39353/1024)⟩, pieceIndex := 36 }
  ]
}

def scalarCert441 : MacroScalarCert 56 := {
  box := ⟨(38999/1024), (9853/256)⟩
  a := (11677601791109548745136801743604201/128000000000000000000000000000000000000)
  segments := [
    { box := ⟨(38999/1024), (38138093/1000000)⟩, pieceIndex := 35 },
    { box := ⟨(38138093/1000000), (9853/256)⟩, pieceIndex := 36 }
  ]
}

def scalarCert442 : MacroScalarCert 56 := {
  box := ⟨(22833/512), (2891/64)⟩
  a := (403384292552130139662239000449081/2000000000000000000000000000000000000)
  segments := [
    { box := ⟨(22833/512), (1399599/31250)⟩, pieceIndex := 42 },
    { box := ⟨(1399599/31250), (2891/64)⟩, pieceIndex := 43 }
  ]
}

def scalarCert443 : MacroScalarCert 56 := {
  box := ⟨(22833/512), (46197/1024)⟩
  a := (403384292552130139662239000449081/2000000000000000000000000000000000000)
  segments := [
    { box := ⟨(22833/512), (1399599/31250)⟩, pieceIndex := 42 },
    { box := ⟨(1399599/31250), (46197/1024)⟩, pieceIndex := 43 }
  ]
}

def scalarCert444 : MacroScalarCert 56 := {
  box := ⟨(45725/1024), (2891/64)⟩
  a := (236947891/1000000000000)
  segments := [
    { box := ⟨(45725/1024), (1399599/31250)⟩, pieceIndex := 42 },
    { box := ⟨(1399599/31250), (2891/64)⟩, pieceIndex := 43 }
  ]
}

def scalarCert445 : MacroScalarCert 56 := {
  box := ⟨(5723/128), (23187/512)⟩
  a := (236947891/1000000000000)
  segments := [
    { box := ⟨(5723/128), (1399599/31250)⟩, pieceIndex := 42 },
    { box := ⟨(1399599/31250), (23187/512)⟩, pieceIndex := 43 }
  ]
}

def scalarCert446 : MacroScalarCert 56 := {
  box := ⟨(177/4), (45843/1024)⟩
  a := (3600341844467488615851330529/122070312500000000000000000000000)
  segments := [
    { box := ⟨(177/4), (5551521/125000)⟩, pieceIndex := 41 },
    { box := ⟨(5551521/125000), (45843/1024)⟩, pieceIndex := 42 }
  ]
}

def scalarCert447 : MacroScalarCert 56 := {
  box := ⟨(45371/1024), (22951/512)⟩
  a := (380995896373736237860712551314169/8000000000000000000000000000000000000)
  segments := [
    { box := ⟨(45371/1024), (5551521/125000)⟩, pieceIndex := 41 },
    { box := ⟨(5551521/125000), (1399599/31250)⟩, pieceIndex := 42 },
    { box := ⟨(1399599/31250), (22951/512)⟩, pieceIndex := 43 }
  ]
}

def scalarCert448 : MacroScalarCert 56 := {
  box := ⟨(45135/1024), (22833/512)⟩
  a := (8326505390882798349213653439169/8000000000000000000000000000000000000)
  segments := [
    { box := ⟨(45135/1024), (5551521/125000)⟩, pieceIndex := 41 },
    { box := ⟨(5551521/125000), (22833/512)⟩, pieceIndex := 42 }
  ]
}

def scalarCert449 : MacroScalarCert 56 := {
  box := ⟨(22597/512), (45725/1024)⟩
  a := (12404326906898653543170837152761/2000000000000000000000000000000000000)
  segments := [
    { box := ⟨(22597/512), (5551521/125000)⟩, pieceIndex := 41 },
    { box := ⟨(5551521/125000), (45725/1024)⟩, pieceIndex := 42 }
  ]
}

def scalarCert450 : MacroScalarCert 56 := {
  box := ⟨(45253/1024), (5723/128)⟩
  a := (125492473536974126032423063314169/8000000000000000000000000000000000000)
  segments := [
    { box := ⟨(45253/1024), (5551521/125000)⟩, pieceIndex := 41 },
    { box := ⟨(5551521/125000), (5723/128)⟩, pieceIndex := 42 }
  ]
}

def scalarCert451 : MacroScalarCert 56 := {
  box := ⟨(22597/512), (22833/512)⟩
  a := (12404326906898653543170837152761/2000000000000000000000000000000000000)
  segments := [
    { box := ⟨(22597/512), (5551521/125000)⟩, pieceIndex := 41 },
    { box := ⟨(5551521/125000), (22833/512)⟩, pieceIndex := 42 }
  ]
}

def scalarCert452 : MacroScalarCert 56 := {
  box := ⟨(45253/1024), (45725/1024)⟩
  a := (125492473536974126032423063314169/8000000000000000000000000000000000000)
  segments := [
    { box := ⟨(45253/1024), (5551521/125000)⟩, pieceIndex := 41 },
    { box := ⟨(5551521/125000), (45725/1024)⟩, pieceIndex := 42 }
  ]
}

def scalarCert453 : MacroScalarCert 56 := {
  box := ⟨(2419/64), (19529/512)⟩
  a := (125628559827345406318287851649/125000000000000000000000000000000000)
  segments := [
    { box := ⟨(2419/64), (38138093/1000000)⟩, pieceIndex := 35 },
    { box := ⟨(38138093/1000000), (19529/512)⟩, pieceIndex := 36 }
  ]
}

def scalarCert454 : MacroScalarCert 56 := {
  box := ⟨(177/4), (5723/128)⟩
  a := (3600341844467488615851330529/122070312500000000000000000000000)
  segments := [
    { box := ⟨(177/4), (5551521/125000)⟩, pieceIndex := 41 },
    { box := ⟨(5551521/125000), (5723/128)⟩, pieceIndex := 42 }
  ]
}

def scalarCert455 : MacroScalarCert 56 := {
  box := ⟨(177/4), (45725/1024)⟩
  a := (3600341844467488615851330529/122070312500000000000000000000000)
  segments := [
    { box := ⟨(177/4), (5551521/125000)⟩, pieceIndex := 41 },
    { box := ⟨(5551521/125000), (45725/1024)⟩, pieceIndex := 42 }
  ]
}

def scalarCert456 : MacroScalarCert 56 := {
  box := ⟨(4071/128), (32863/1024)⟩
  a := (611979482867143614802669851201/5000000000000000000000000000000000)
  segments := [
    { box := ⟨(4071/128), (6373527/200000)⟩, pieceIndex := 29 },
    { box := ⟨(6373527/200000), (32863/1024)⟩, pieceIndex := 30 }
  ]
}

def scalarCert457 : MacroScalarCert 56 := {
  box := ⟨(6313/512), (12685/1024)⟩
  a := (5885991482681207829900684848390449/5120000000000000000000000000000000000)
  segments := [
    { box := ⟨(6313/512), (1238029/100000)⟩, pieceIndex := 8 },
    { box := ⟨(1238029/100000), (12685/1024)⟩, pieceIndex := 9 }
  ]
}

def scalarCert458 : MacroScalarCert 56 := {
  box := ⟨(38763/1024), (19529/512)⟩
  a := (941648095787567227326613280229201/128000000000000000000000000000000000000)
  segments := [
    { box := ⟨(38763/1024), (38138093/1000000)⟩, pieceIndex := 35 },
    { box := ⟨(38138093/1000000), (19529/512)⟩, pieceIndex := 36 }
  ]
}

def scalarCert459 : MacroScalarCert 56 := {
  box := ⟨(45371/1024), (5723/128)⟩
  a := (380995896373736237860712551314169/8000000000000000000000000000000000000)
  segments := [
    { box := ⟨(45371/1024), (5551521/125000)⟩, pieceIndex := 41 },
    { box := ⟨(5551521/125000), (5723/128)⟩, pieceIndex := 42 }
  ]
}

def scalarCert460 : MacroScalarCert 56 := {
  box := ⟨(32627/1024), (16461/512)⟩
  a := (54965343560194319646569821692489/320000000000000000000000000000000000)
  segments := [
    { box := ⟨(32627/1024), (6373527/200000)⟩, pieceIndex := 29 },
    { box := ⟨(6373527/200000), (16461/512)⟩, pieceIndex := 30 }
  ]
}

def scalarCert461 : MacroScalarCert 56 := {
  box := ⟨(45371/1024), (45843/1024)⟩
  a := (380995896373736237860712551314169/8000000000000000000000000000000000000)
  segments := [
    { box := ⟨(45371/1024), (5551521/125000)⟩, pieceIndex := 41 },
    { box := ⟨(5551521/125000), (45843/1024)⟩, pieceIndex := 42 }
  ]
}

def scalarCert462 : MacroScalarCert 56 := {
  box := ⟨(22715/512), (22951/512)⟩
  a := (140156038325279709457315581152761/2000000000000000000000000000000000000)
  segments := [
    { box := ⟨(22715/512), (5551521/125000)⟩, pieceIndex := 41 },
    { box := ⟨(5551521/125000), (1399599/31250)⟩, pieceIndex := 42 },
    { box := ⟨(1399599/31250), (22951/512)⟩, pieceIndex := 43 }
  ]
}

def scalarCert463 : MacroScalarCert 56 := {
  box := ⟨(22715/512), (45843/1024)⟩
  a := (140156038325279709457315581152761/2000000000000000000000000000000000000)
  segments := [
    { box := ⟨(22715/512), (5551521/125000)⟩, pieceIndex := 41 },
    { box := ⟨(5551521/125000), (45843/1024)⟩, pieceIndex := 42 }
  ]
}

def scalarCert464 : MacroScalarCert 56 := {
  box := ⟨(45489/1024), (22951/512)⟩
  a := (816478761924151067555100775499449/8000000000000000000000000000000000000)
  segments := [
    { box := ⟨(45489/1024), (1399599/31250)⟩, pieceIndex := 42 },
    { box := ⟨(1399599/31250), (22951/512)⟩, pieceIndex := 43 }
  ]
}

def scalarCert465 : MacroScalarCert 56 := {
  box := ⟨(32745/1024), (2065/64)⟩
  a := (96378734194223377991070077769889/320000000000000000000000000000000000)
  segments := [
    { box := ⟨(32745/1024), (6448527/200000)⟩, pieceIndex := 30 },
    { box := ⟨(6448527/200000), (2065/64)⟩, pieceIndex := 31 }
  ]
}

def scalarCert466 : MacroScalarCert 56 := {
  box := ⟨(38763/1024), (39117/1024)⟩
  a := (941648095787567227326613280229201/128000000000000000000000000000000000000)
  segments := [
    { box := ⟨(38763/1024), (38138093/1000000)⟩, pieceIndex := 35 },
    { box := ⟨(38138093/1000000), (39117/1024)⟩, pieceIndex := 36 }
  ]
}

def scalarCert467 : MacroScalarCert 56 := {
  box := ⟨(6549/256), (413/16)⟩
  a := (4846047689033107029255715842121/20000000000000000000000000000000000)
  segments := [
    { box := ⟨(6549/256), (2560347/100000)⟩, pieceIndex := 23 },
    { box := ⟨(2560347/100000), (413/16)⟩, pieceIndex := 24 }
  ]
}

def scalarCert468 : MacroScalarCert 56 := {
  box := ⟨(19411/512), (4897/128)⟩
  a := (625761533908596174465411009662769/32000000000000000000000000000000000000)
  segments := [
    { box := ⟨(19411/512), (38138093/1000000)⟩, pieceIndex := 35 },
    { box := ⟨(38138093/1000000), (4897/128)⟩, pieceIndex := 36 }
  ]
}

def scalarCert469 : MacroScalarCert 56 := {
  box := ⟨(45489/1024), (45961/1024)⟩
  a := (816478761924151067555100775499449/8000000000000000000000000000000000000)
  segments := [
    { box := ⟨(45489/1024), (1399599/31250)⟩, pieceIndex := 42 },
    { box := ⟨(1399599/31250), (45961/1024)⟩, pieceIndex := 43 }
  ]
}

def scalarCert470 : MacroScalarCert 56 := {
  box := ⟨(11387/256), (11505/256)⟩
  a := (65768103458522511747545895061489/500000000000000000000000000000000000)
  segments := [
    { box := ⟨(11387/256), (1399599/31250)⟩, pieceIndex := 42 },
    { box := ⟨(1399599/31250), (11505/256)⟩, pieceIndex := 43 }
  ]
}

def scalarCert471 : MacroScalarCert 56 := {
  box := ⟨(38881/1024), (39235/1024)⟩
  a := (4812837764803654107675019035354201/128000000000000000000000000000000000000)
  segments := [
    { box := ⟨(38881/1024), (38138093/1000000)⟩, pieceIndex := 35 },
    { box := ⟨(38138093/1000000), (39235/1024)⟩, pieceIndex := 36 }
  ]
}

def scalarCert472 : MacroScalarCert 56 := {
  box := ⟨(45607/1024), (46079/1024)⟩
  a := (1317975791431150018325352729749449/8000000000000000000000000000000000000)
  segments := [
    { box := ⟨(45607/1024), (1399599/31250)⟩, pieceIndex := 42 },
    { box := ⟨(1399599/31250), (46079/1024)⟩, pieceIndex := 43 }
  ]
}

def scalarCert473 : MacroScalarCert 56 := {
  box := ⟨(9735/256), (19647/512)⟩
  a := (491938936455960966047921141896161/8000000000000000000000000000000000000)
  segments := [
    { box := ⟨(9735/256), (38138093/1000000)⟩, pieceIndex := 35 },
    { box := ⟨(38138093/1000000), (19647/512)⟩, pieceIndex := 36 }
  ]
}

def scalarCert474 : MacroScalarCert 56 := {
  box := ⟨(26373/1024), (26609/1024)⟩
  a := (6939535078070123213019812388921/12800000000000000000000000000000000)
  segments := [
    { box := ⟨(26373/1024), (2597847/100000)⟩, pieceIndex := 24 },
    { box := ⟨(2597847/100000), (26609/1024)⟩, pieceIndex := 25 }
  ]
}

def scalarCert475 : MacroScalarCert 56 := {
  box := ⟨(38999/1024), (39353/1024)⟩
  a := (11677601791109548745136801743604201/128000000000000000000000000000000000000)
  segments := [
    { box := ⟨(38999/1024), (38138093/1000000)⟩, pieceIndex := 35 },
    { box := ⟨(38138093/1000000), (39353/1024)⟩, pieceIndex := 36 }
  ]
}

def scalarCert476 : MacroScalarCert 56 := {
  box := ⟨(22833/512), (23069/512)⟩
  a := (403384292552130139662239000449081/2000000000000000000000000000000000000)
  segments := [
    { box := ⟨(22833/512), (1399599/31250)⟩, pieceIndex := 42 },
    { box := ⟨(1399599/31250), (23069/512)⟩, pieceIndex := 43 }
  ]
}

def scalarCert477 : MacroScalarCert 56 := {
  box := ⟨(45725/1024), (46197/1024)⟩
  a := (236947891/1000000000000)
  segments := [
    { box := ⟨(45725/1024), (1399599/31250)⟩, pieceIndex := 42 },
    { box := ⟨(1399599/31250), (46197/1024)⟩, pieceIndex := 43 }
  ]
}

def scalarCert478 : MacroScalarCert 56 := {
  box := ⟨(19411/512), (39117/1024)⟩
  a := (625761533908596174465411009662769/32000000000000000000000000000000000000)
  segments := [
    { box := ⟨(19411/512), (38138093/1000000)⟩, pieceIndex := 35 },
    { box := ⟨(38138093/1000000), (39117/1024)⟩, pieceIndex := 36 }
  ]
}

def scalarCert479 : MacroScalarCert 56 := {
  box := ⟨(13039/512), (26255/1024)⟩
  a := (8807754158064216214287607996609/80000000000000000000000000000000000)
  segments := [
    { box := ⟨(13039/512), (2560347/100000)⟩, pieceIndex := 23 },
    { box := ⟨(2560347/100000), (26255/1024)⟩, pieceIndex := 24 }
  ]
}

def scalarCert480 : MacroScalarCert 56 := {
  box := ⟨(38881/1024), (4897/128)⟩
  a := (4812837764803654107675019035354201/128000000000000000000000000000000000000)
  segments := [
    { box := ⟨(38881/1024), (38138093/1000000)⟩, pieceIndex := 35 },
    { box := ⟨(38138093/1000000), (4897/128)⟩, pieceIndex := 36 }
  ]
}

def scalarCert481 : MacroScalarCert 56 := {
  box := ⟨(26137/1024), (13157/512)⟩
  a := (54324773825972371723691245464561/320000000000000000000000000000000000)
  segments := [
    { box := ⟨(26137/1024), (2560347/100000)⟩, pieceIndex := 23 },
    { box := ⟨(2560347/100000), (13157/512)⟩, pieceIndex := 24 }
  ]
}

def scalarCert482 : MacroScalarCert 56 := {
  box := ⟨(38881/1024), (39117/1024)⟩
  a := (4812837764803654107675019035354201/128000000000000000000000000000000000000)
  segments := [
    { box := ⟨(38881/1024), (38138093/1000000)⟩, pieceIndex := 35 },
    { box := ⟨(38138093/1000000), (39117/1024)⟩, pieceIndex := 36 }
  ]
}

def scalarCert483 : MacroScalarCert 56 := {
  box := ⟨(9735/256), (4897/128)⟩
  a := (491938936455960966047921141896161/8000000000000000000000000000000000000)
  segments := [
    { box := ⟨(9735/256), (38138093/1000000)⟩, pieceIndex := 35 },
    { box := ⟨(38138093/1000000), (4897/128)⟩, pieceIndex := 36 }
  ]
}

def scalarCert484 : MacroScalarCert 56 := {
  box := ⟨(11387/256), (22951/512)⟩
  a := (65768103458522511747545895061489/500000000000000000000000000000000000)
  segments := [
    { box := ⟨(11387/256), (1399599/31250)⟩, pieceIndex := 42 },
    { box := ⟨(1399599/31250), (22951/512)⟩, pieceIndex := 43 }
  ]
}

def scalarCert485 : MacroScalarCert 56 := {
  box := ⟨(11387/256), (45961/1024)⟩
  a := (65768103458522511747545895061489/500000000000000000000000000000000000)
  segments := [
    { box := ⟨(11387/256), (1399599/31250)⟩, pieceIndex := 42 },
    { box := ⟨(1399599/31250), (45961/1024)⟩, pieceIndex := 43 }
  ]
}

def scalarCert486 : MacroScalarCert 56 := {
  box := ⟨(8201/256), (33099/1024)⟩
  a := (7402913802521846133201894614329/20000000000000000000000000000000000)
  segments := [
    { box := ⟨(8201/256), (6448527/200000)⟩, pieceIndex := 30 },
    { box := ⟨(6448527/200000), (33099/1024)⟩, pieceIndex := 31 }
  ]
}

def scalarCert487 : MacroScalarCert 56 := {
  box := ⟨(19411/512), (19529/512)⟩
  a := (625761533908596174465411009662769/32000000000000000000000000000000000000)
  segments := [
    { box := ⟨(19411/512), (38138093/1000000)⟩, pieceIndex := 35 },
    { box := ⟨(38138093/1000000), (19529/512)⟩, pieceIndex := 36 }
  ]
}

def scalarCert488 : MacroScalarCert 56 := {
  box := ⟨(45607/1024), (45961/1024)⟩
  a := (1317975791431150018325352729749449/8000000000000000000000000000000000000)
  segments := [
    { box := ⟨(45607/1024), (1399599/31250)⟩, pieceIndex := 42 },
    { box := ⟨(1399599/31250), (45961/1024)⟩, pieceIndex := 43 }
  ]
}

def scalarCert489 : MacroScalarCert 56 := {
  box := ⟨(45607/1024), (11505/256)⟩
  a := (1317975791431150018325352729749449/8000000000000000000000000000000000000)
  segments := [
    { box := ⟨(45607/1024), (1399599/31250)⟩, pieceIndex := 42 },
    { box := ⟨(1399599/31250), (11505/256)⟩, pieceIndex := 43 }
  ]
}

def scalarCert490 : MacroScalarCert 56 := {
  box := ⟨(32863/1024), (16579/512)⟩
  a := (104124691/250000000000)
  segments := [
    { box := ⟨(32863/1024), (6448527/200000)⟩, pieceIndex := 30 },
    { box := ⟨(6448527/200000), (16579/512)⟩, pieceIndex := 31 }
  ]
}

def scalarCert491 : MacroScalarCert 56 := {
  box := ⟨(9735/256), (39235/1024)⟩
  a := (491938936455960966047921141896161/8000000000000000000000000000000000000)
  segments := [
    { box := ⟨(9735/256), (38138093/1000000)⟩, pieceIndex := 35 },
    { box := ⟨(38138093/1000000), (39235/1024)⟩, pieceIndex := 36 }
  ]
}

def scalarCert492 : MacroScalarCert 56 := {
  box := ⟨(38999/1024), (19647/512)⟩
  a := (11677601791109548745136801743604201/128000000000000000000000000000000000000)
  segments := [
    { box := ⟨(38999/1024), (38138093/1000000)⟩, pieceIndex := 35 },
    { box := ⟨(38138093/1000000), (19647/512)⟩, pieceIndex := 36 }
  ]
}

def scalarCert493 : MacroScalarCert 56 := {
  box := ⟨(5723/128), (46315/1024)⟩
  a := (236947891/1000000000000)
  segments := [
    { box := ⟨(5723/128), (1399599/31250)⟩, pieceIndex := 42 },
    { box := ⟨(1399599/31250), (46315/1024)⟩, pieceIndex := 43 }
  ]
}

def scalarCert494 : MacroScalarCert 56 := {
  box := ⟨(45843/1024), (23187/512)⟩
  a := (236947891/1000000000000)
  segments := [
    { box := ⟨(45843/1024), (1399599/31250)⟩, pieceIndex := 42 },
    { box := ⟨(1399599/31250), (23187/512)⟩, pieceIndex := 43 }
  ]
}

def scalarCert495 : MacroScalarCert 56 := {
  box := ⟨(19529/512), (39471/1024)⟩
  a := (172336030037728650247271147738569/1280000000000000000000000000000000000)
  segments := [
    { box := ⟨(19529/512), (38513093/1000000)⟩, pieceIndex := 36 },
    { box := ⟨(38513093/1000000), (39471/1024)⟩, pieceIndex := 37 }
  ]
}

def scalarCert496 : MacroScalarCert 56 := {
  box := ⟨(39117/1024), (19765/512)⟩
  a := (890431430789413157949114897032401/5120000000000000000000000000000000000)
  segments := [
    { box := ⟨(39117/1024), (38513093/1000000)⟩, pieceIndex := 36 },
    { box := ⟨(38513093/1000000), (19765/512)⟩, pieceIndex := 37 }
  ]
}

def scalarCert497 : MacroScalarCert 56 := {
  box := ⟨(4897/128), (39589/1024)⟩
  a := (17456552780050285252554156310809/80000000000000000000000000000000000)
  segments := [
    { box := ⟨(4897/128), (38513093/1000000)⟩, pieceIndex := 36 },
    { box := ⟨(38513093/1000000), (39589/1024)⟩, pieceIndex := 37 }
  ]
}

def scalarCert498 : MacroScalarCert 56 := {
  box := ⟨(39235/1024), (1239/32)⟩
  a := (1369707961552329895632137911532401/5120000000000000000000000000000000000)
  segments := [
    { box := ⟨(39235/1024), (38513093/1000000)⟩, pieceIndex := 36 },
    { box := ⟨(38513093/1000000), (1239/32)⟩, pieceIndex := 37 }
  ]
}

def scalarCert499 : MacroScalarCert 56 := {
  box := ⟨(25783/512), (13157/256)⟩
  a := (77268664145143861057015595361/80000000000000000000000000000000000)
  segments := [
    { box := ⟨(25783/512), (50688511/1000000)⟩, pieceIndex := 47 },
    { box := ⟨(50688511/1000000), (51063511/1000000)⟩, pieceIndex := 48 },
    { box := ⟨(51063511/1000000), (13157/256)⟩, pieceIndex := 49 }
  ]
}

def scalarCert500 : MacroScalarCert 56 := {
  box := ⟨(25783/512), (26255/512)⟩
  a := (77268664145143861057015595361/80000000000000000000000000000000000)
  segments := [
    { box := ⟨(25783/512), (50688511/1000000)⟩, pieceIndex := 47 },
    { box := ⟨(50688511/1000000), (51063511/1000000)⟩, pieceIndex := 48 },
    { box := ⟨(51063511/1000000), (26255/512)⟩, pieceIndex := 49 }
  ]
}

def scalarCert501 : MacroScalarCert 56 := {
  box := ⟨(12921/256), (13157/256)⟩
  a := (253733660265444510657503816809/20000000000000000000000000000000000)
  segments := [
    { box := ⟨(12921/256), (50688511/1000000)⟩, pieceIndex := 47 },
    { box := ⟨(50688511/1000000), (51063511/1000000)⟩, pieceIndex := 48 },
    { box := ⟨(51063511/1000000), (13157/256)⟩, pieceIndex := 49 }
  ]
}

def scalarCert502 : MacroScalarCert 56 := {
  box := ⟨(12921/256), (413/8)⟩
  a := (253733660265444510657503816809/20000000000000000000000000000000000)
  segments := [
    { box := ⟨(12921/256), (50688511/1000000)⟩, pieceIndex := 47 },
    { box := ⟨(50688511/1000000), (51063511/1000000)⟩, pieceIndex := 48 },
    { box := ⟨(51063511/1000000), (413/8)⟩, pieceIndex := 49 }
  ]
}

def scalarCert503 : MacroScalarCert 56 := {
  box := ⟨(12921/256), (26373/512)⟩
  a := (253733660265444510657503816809/20000000000000000000000000000000000)
  segments := [
    { box := ⟨(12921/256), (50688511/1000000)⟩, pieceIndex := 47 },
    { box := ⟨(50688511/1000000), (51063511/1000000)⟩, pieceIndex := 48 },
    { box := ⟨(51063511/1000000), (26373/512)⟩, pieceIndex := 49 }
  ]
}

def scalarCert504 : MacroScalarCert 56 := {
  box := ⟨(25901/512), (413/8)⟩
  a := (3016845497858850148660534470361/80000000000000000000000000000000000)
  segments := [
    { box := ⟨(25901/512), (50688511/1000000)⟩, pieceIndex := 47 },
    { box := ⟨(50688511/1000000), (51063511/1000000)⟩, pieceIndex := 48 },
    { box := ⟨(51063511/1000000), (413/8)⟩, pieceIndex := 49 }
  ]
}

def scalarCert505 : MacroScalarCert 56 := {
  box := ⟨(12921/256), (13275/256)⟩
  a := (253733660265444510657503816809/20000000000000000000000000000000000)
  segments := [
    { box := ⟨(12921/256), (50688511/1000000)⟩, pieceIndex := 47 },
    { box := ⟨(50688511/1000000), (51063511/1000000)⟩, pieceIndex := 48 },
    { box := ⟨(51063511/1000000), (13275/256)⟩, pieceIndex := 49 }
  ]
}

def scalarCert506 : MacroScalarCert 56 := {
  box := ⟨(3245/64), (13275/256)⟩
  a := (9965930645410815779513042967721/125000000000000000000000000000000000)
  segments := [
    { box := ⟨(3245/64), (51063511/1000000)⟩, pieceIndex := 48 },
    { box := ⟨(51063511/1000000), (13275/256)⟩, pieceIndex := 49 }
  ]
}

def scalarCert507 : MacroScalarCert 56 := {
  box := ⟨(25783/512), (13039/256)⟩
  a := (77268664145143861057015595361/80000000000000000000000000000000000)
  segments := [
    { box := ⟨(25783/512), (50688511/1000000)⟩, pieceIndex := 47 },
    { box := ⟨(50688511/1000000), (13039/256)⟩, pieceIndex := 48 }
  ]
}

def scalarCert508 : MacroScalarCert 56 := {
  box := ⟨(25783/512), (52097/1024)⟩
  a := (77268664145143861057015595361/80000000000000000000000000000000000)
  segments := [
    { box := ⟨(25783/512), (50688511/1000000)⟩, pieceIndex := 47 },
    { box := ⟨(50688511/1000000), (52097/1024)⟩, pieceIndex := 48 }
  ]
}

def scalarCert509 : MacroScalarCert 56 := {
  box := ⟨(51625/1024), (13039/256)⟩
  a := (1652284170473624845145301959569/320000000000000000000000000000000000)
  segments := [
    { box := ⟨(51625/1024), (50688511/1000000)⟩, pieceIndex := 47 },
    { box := ⟨(50688511/1000000), (13039/256)⟩, pieceIndex := 48 }
  ]
}

def scalarCert510 : MacroScalarCert 56 := {
  box := ⟨(25783/512), (26137/512)⟩
  a := (77268664145143861057015595361/80000000000000000000000000000000000)
  segments := [
    { box := ⟨(25783/512), (50688511/1000000)⟩, pieceIndex := 47 },
    { box := ⟨(50688511/1000000), (26137/512)⟩, pieceIndex := 48 }
  ]
}

def scalarCert511 : MacroScalarCert 56 := {
  box := ⟨(25783/512), (6549/128)⟩
  a := (77268664145143861057015595361/80000000000000000000000000000000000)
  segments := [
    { box := ⟨(25783/512), (50688511/1000000)⟩, pieceIndex := 47 },
    { box := ⟨(50688511/1000000), (51063511/1000000)⟩, pieceIndex := 48 },
    { box := ⟨(51063511/1000000), (6549/128)⟩, pieceIndex := 49 }
  ]
}

def scalarCert512 : MacroScalarCert 56 := {
  box := ⟨(12921/256), (6549/128)⟩
  a := (253733660265444510657503816809/20000000000000000000000000000000000)
  segments := [
    { box := ⟨(12921/256), (50688511/1000000)⟩, pieceIndex := 47 },
    { box := ⟨(50688511/1000000), (51063511/1000000)⟩, pieceIndex := 48 },
    { box := ⟨(51063511/1000000), (6549/128)⟩, pieceIndex := 49 }
  ]
}

def scalarCert513 : MacroScalarCert 56 := {
  box := ⟨(12921/256), (26255/512)⟩
  a := (253733660265444510657503816809/20000000000000000000000000000000000)
  segments := [
    { box := ⟨(12921/256), (50688511/1000000)⟩, pieceIndex := 47 },
    { box := ⟨(50688511/1000000), (51063511/1000000)⟩, pieceIndex := 48 },
    { box := ⟨(51063511/1000000), (26255/512)⟩, pieceIndex := 49 }
  ]
}

def scalarCert514 : MacroScalarCert 56 := {
  box := ⟨(12921/256), (26137/512)⟩
  a := (253733660265444510657503816809/20000000000000000000000000000000000)
  segments := [
    { box := ⟨(12921/256), (50688511/1000000)⟩, pieceIndex := 47 },
    { box := ⟨(50688511/1000000), (26137/512)⟩, pieceIndex := 48 }
  ]
}

def scalarCert515 : MacroScalarCert 56 := {
  box := ⟨(12921/256), (52215/1024)⟩
  a := (253733660265444510657503816809/20000000000000000000000000000000000)
  segments := [
    { box := ⟨(12921/256), (50688511/1000000)⟩, pieceIndex := 47 },
    { box := ⟨(50688511/1000000), (52215/1024)⟩, pieceIndex := 48 }
  ]
}

def scalarCert516 : MacroScalarCert 56 := {
  box := ⟨(51743/1024), (26137/512)⟩
  a := (7531437837901037420352339709569/320000000000000000000000000000000000)
  segments := [
    { box := ⟨(51743/1024), (50688511/1000000)⟩, pieceIndex := 47 },
    { box := ⟨(50688511/1000000), (26137/512)⟩, pieceIndex := 48 }
  ]
}

def scalarCert517 : MacroScalarCert 56 := {
  box := ⟨(32391/1024), (16343/512)⟩
  a := (7793772368438963417005384017489/320000000000000000000000000000000000)
  segments := [
    { box := ⟨(32391/1024), (6373527/200000)⟩, pieceIndex := 29 },
    { box := ⟨(6373527/200000), (16343/512)⟩, pieceIndex := 30 }
  ]
}

def scalarCert518 : MacroScalarCert 56 := {
  box := ⟨(25901/512), (6549/128)⟩
  a := (3016845497858850148660534470361/80000000000000000000000000000000000)
  segments := [
    { box := ⟨(25901/512), (50688511/1000000)⟩, pieceIndex := 47 },
    { box := ⟨(50688511/1000000), (51063511/1000000)⟩, pieceIndex := 48 },
    { box := ⟨(51063511/1000000), (6549/128)⟩, pieceIndex := 49 }
  ]
}

def scalarCert519 : MacroScalarCert 56 := {
  box := ⟨(25901/512), (26255/512)⟩
  a := (3016845497858850148660534470361/80000000000000000000000000000000000)
  segments := [
    { box := ⟨(25901/512), (50688511/1000000)⟩, pieceIndex := 47 },
    { box := ⟨(50688511/1000000), (51063511/1000000)⟩, pieceIndex := 48 },
    { box := ⟨(51063511/1000000), (26255/512)⟩, pieceIndex := 49 }
  ]
}

def scalarCert520 : MacroScalarCert 56 := {
  box := ⟨(25901/512), (13157/256)⟩
  a := (3016845497858850148660534470361/80000000000000000000000000000000000)
  segments := [
    { box := ⟨(25901/512), (50688511/1000000)⟩, pieceIndex := 47 },
    { box := ⟨(50688511/1000000), (51063511/1000000)⟩, pieceIndex := 48 },
    { box := ⟨(51063511/1000000), (13157/256)⟩, pieceIndex := 49 }
  ]
}

def scalarCert521 : MacroScalarCert 56 := {
  box := ⟨(3245/64), (13157/256)⟩
  a := (9965930645410815779513042967721/125000000000000000000000000000000000)
  segments := [
    { box := ⟨(3245/64), (51063511/1000000)⟩, pieceIndex := 48 },
    { box := ⟨(51063511/1000000), (13157/256)⟩, pieceIndex := 49 }
  ]
}

def scalarCert522 : MacroScalarCert 56 := {
  box := ⟨(25901/512), (26373/512)⟩
  a := (3016845497858850148660534470361/80000000000000000000000000000000000)
  segments := [
    { box := ⟨(25901/512), (50688511/1000000)⟩, pieceIndex := 47 },
    { box := ⟨(50688511/1000000), (51063511/1000000)⟩, pieceIndex := 48 },
    { box := ⟨(51063511/1000000), (26373/512)⟩, pieceIndex := 49 }
  ]
}

def scalarCert523 : MacroScalarCert 56 := {
  box := ⟨(3245/64), (26373/512)⟩
  a := (9965930645410815779513042967721/125000000000000000000000000000000000)
  segments := [
    { box := ⟨(3245/64), (51063511/1000000)⟩, pieceIndex := 48 },
    { box := ⟨(51063511/1000000), (26373/512)⟩, pieceIndex := 49 }
  ]
}

def scalarCert524 : MacroScalarCert 56 := {
  box := ⟨(3245/64), (413/8)⟩
  a := (9965930645410815779513042967721/125000000000000000000000000000000000)
  segments := [
    { box := ⟨(3245/64), (51063511/1000000)⟩, pieceIndex := 48 },
    { box := ⟨(51063511/1000000), (413/8)⟩, pieceIndex := 49 }
  ]
}

def scalarCert525 : MacroScalarCert 56 := {
  box := ⟨(3245/64), (26491/512)⟩
  a := (9965930645410815779513042967721/125000000000000000000000000000000000)
  segments := [
    { box := ⟨(3245/64), (51063511/1000000)⟩, pieceIndex := 48 },
    { box := ⟨(51063511/1000000), (26491/512)⟩, pieceIndex := 49 }
  ]
}

def scalarCert526 : MacroScalarCert 56 := {
  box := ⟨(26019/512), (413/8)⟩
  a := (4108970484551816539322694210502201/32000000000000000000000000000000000000)
  segments := [
    { box := ⟨(26019/512), (51063511/1000000)⟩, pieceIndex := 48 },
    { box := ⟨(51063511/1000000), (413/8)⟩, pieceIndex := 49 }
  ]
}

def scalarCert527 : MacroScalarCert 56 := {
  box := ⟨(26019/512), (26491/512)⟩
  a := (4108970484551816539322694210502201/32000000000000000000000000000000000000)
  segments := [
    { box := ⟨(26019/512), (51063511/1000000)⟩, pieceIndex := 48 },
    { box := ⟨(51063511/1000000), (26491/512)⟩, pieceIndex := 49 }
  ]
}

def scalarCert528 : MacroScalarCert 56 := {
  box := ⟨(26019/512), (13275/256)⟩
  a := (4108970484551816539322694210502201/32000000000000000000000000000000000000)
  segments := [
    { box := ⟨(26019/512), (51063511/1000000)⟩, pieceIndex := 48 },
    { box := ⟨(51063511/1000000), (13275/256)⟩, pieceIndex := 49 }
  ]
}

def scalarCert529 : MacroScalarCert 56 := {
  box := ⟨(12921/256), (6667/128)⟩
  a := (253733660265444510657503816809/20000000000000000000000000000000000)
  segments := [
    { box := ⟨(12921/256), (50688511/1000000)⟩, pieceIndex := 47 },
    { box := ⟨(50688511/1000000), (51063511/1000000)⟩, pieceIndex := 48 },
    { box := ⟨(51063511/1000000), (6667/128)⟩, pieceIndex := 49 }
  ]
}

def scalarCert530 : MacroScalarCert 56 := {
  box := ⟨(3245/64), (6667/128)⟩
  a := (9965930645410815779513042967721/125000000000000000000000000000000000)
  segments := [
    { box := ⟨(3245/64), (51063511/1000000)⟩, pieceIndex := 48 },
    { box := ⟨(51063511/1000000), (6667/128)⟩, pieceIndex := 49 }
  ]
}

def scalarCert531 : MacroScalarCert 56 := {
  box := ⟨(13039/256), (6667/128)⟩
  a := (587393/3125000000)
  segments := [
    { box := ⟨(13039/256), (51063511/1000000)⟩, pieceIndex := 48 },
    { box := ⟨(51063511/1000000), (6667/128)⟩, pieceIndex := 49 }
  ]
}

def scalarCert532 : MacroScalarCert 56 := {
  box := ⟨(12921/256), (13393/256)⟩
  a := (253733660265444510657503816809/20000000000000000000000000000000000)
  segments := [
    { box := ⟨(12921/256), (50688511/1000000)⟩, pieceIndex := 47 },
    { box := ⟨(50688511/1000000), (51063511/1000000)⟩, pieceIndex := 48 },
    { box := ⟨(51063511/1000000), (13393/256)⟩, pieceIndex := 49 }
  ]
}

def scalarCert533 : MacroScalarCert 56 := {
  box := ⟨(12921/256), (3363/64)⟩
  a := (253733660265444510657503816809/20000000000000000000000000000000000)
  segments := [
    { box := ⟨(12921/256), (50688511/1000000)⟩, pieceIndex := 47 },
    { box := ⟨(50688511/1000000), (51063511/1000000)⟩, pieceIndex := 48 },
    { box := ⟨(51063511/1000000), (3363/64)⟩, pieceIndex := 49 }
  ]
}

def scalarCert534 : MacroScalarCert 56 := {
  box := ⟨(3245/64), (6785/128)⟩
  a := (9965930645410815779513042967721/125000000000000000000000000000000000)
  segments := [
    { box := ⟨(3245/64), (51063511/1000000)⟩, pieceIndex := 48 },
    { box := ⟨(51063511/1000000), (6785/128)⟩, pieceIndex := 49 }
  ]
}

def scalarCert535 : MacroScalarCert 56 := {
  box := ⟨(3245/64), (1711/32)⟩
  a := (9965930645410815779513042967721/125000000000000000000000000000000000)
  segments := [
    { box := ⟨(3245/64), (51063511/1000000)⟩, pieceIndex := 48 },
    { box := ⟨(51063511/1000000), (1711/32)⟩, pieceIndex := 49 }
  ]
}

def scalarCert536 : MacroScalarCert 56 := {
  box := ⟨(3245/64), (13511/256)⟩
  a := (9965930645410815779513042967721/125000000000000000000000000000000000)
  segments := [
    { box := ⟨(3245/64), (51063511/1000000)⟩, pieceIndex := 48 },
    { box := ⟨(51063511/1000000), (13511/256)⟩, pieceIndex := 49 }
  ]
}

def scalarCert537 : MacroScalarCert 56 := {
  box := ⟨(3245/64), (3363/64)⟩
  a := (9965930645410815779513042967721/125000000000000000000000000000000000)
  segments := [
    { box := ⟨(3245/64), (51063511/1000000)⟩, pieceIndex := 48 },
    { box := ⟨(51063511/1000000), (3363/64)⟩, pieceIndex := 49 }
  ]
}

def scalarCert538 : MacroScalarCert 56 := {
  box := ⟨(3245/64), (13393/256)⟩
  a := (9965930645410815779513042967721/125000000000000000000000000000000000)
  segments := [
    { box := ⟨(3245/64), (51063511/1000000)⟩, pieceIndex := 48 },
    { box := ⟨(51063511/1000000), (13393/256)⟩, pieceIndex := 49 }
  ]
}

def scalarCert539 : MacroScalarCert 56 := {
  box := ⟨(13039/256), (13393/256)⟩
  a := (587393/3125000000)
  segments := [
    { box := ⟨(13039/256), (51063511/1000000)⟩, pieceIndex := 48 },
    { box := ⟨(51063511/1000000), (13393/256)⟩, pieceIndex := 49 }
  ]
}

def scalarCert540 : MacroScalarCert 56 := {
  box := ⟨(13039/256), (3363/64)⟩
  a := (587393/3125000000)
  segments := [
    { box := ⟨(13039/256), (51063511/1000000)⟩, pieceIndex := 48 },
    { box := ⟨(51063511/1000000), (3363/64)⟩, pieceIndex := 49 }
  ]
}

def scalarCert541 : MacroScalarCert 56 := {
  box := ⟨(13039/256), (13511/256)⟩
  a := (587393/3125000000)
  segments := [
    { box := ⟨(13039/256), (51063511/1000000)⟩, pieceIndex := 48 },
    { box := ⟨(51063511/1000000), (13511/256)⟩, pieceIndex := 49 }
  ]
}

def scalarCert542 : MacroScalarCert 56 := {
  box := ⟨(13039/256), (6785/128)⟩
  a := (587393/3125000000)
  segments := [
    { box := ⟨(13039/256), (51063511/1000000)⟩, pieceIndex := 48 },
    { box := ⟨(51063511/1000000), (6785/128)⟩, pieceIndex := 49 }
  ]
}

def scalarCert543 : MacroScalarCert 56 := {
  box := ⟨(3245/64), (885/16)⟩
  a := (9965930645410815779513042967721/125000000000000000000000000000000000)
  segments := [
    { box := ⟨(3245/64), (51063511/1000000)⟩, pieceIndex := 48 },
    { box := ⟨(51063511/1000000), (885/16)⟩, pieceIndex := 49 }
  ]
}

def scalarCert544 : MacroScalarCert 56 := {
  box := ⟨(3245/64), (3599/64)⟩
  a := (6679430045452291605179741688609/125000000000000000000000000000000000)
  segments := [
    { box := ⟨(3245/64), (51063511/1000000)⟩, pieceIndex := 48 },
    { box := ⟨(51063511/1000000), (55841369/1000000)⟩, pieceIndex := 49 },
    { box := ⟨(55841369/1000000), (56216369/1000000)⟩, pieceIndex := 50 },
    { box := ⟨(56216369/1000000), (3599/64)⟩, pieceIndex := 51 }
  ]
}

def scalarCert545 : MacroScalarCert 56 := {
  box := ⟨(3717/128), (1003/32)⟩
  a := (37896421104977184428389275321/1250000000000000000000000000000000)
  segments := [
    { box := ⟨(3717/128), (15371317/500000)⟩, pieceIndex := 25 },
    { box := ⟨(15371317/500000), (15558817/500000)⟩, pieceIndex := 26 },
    { box := ⟨(15558817/500000), (1003/32)⟩, pieceIndex := 27 }
  ]
}

def scalarCert546 : MacroScalarCert 56 := {
  box := ⟨(32509/1024), (8201/256)⟩
  a := (26038539485972255876043813792489/320000000000000000000000000000000000)
  segments := [
    { box := ⟨(32509/1024), (6373527/200000)⟩, pieceIndex := 29 },
    { box := ⟨(6373527/200000), (8201/256)⟩, pieceIndex := 30 }
  ]
}

def scalarCert547 : MacroScalarCert 56 := {
  box := ⟨(19647/512), (39707/1024)⟩
  a := (76986939/250000000000)
  segments := [
    { box := ⟨(19647/512), (38513093/1000000)⟩, pieceIndex := 36 },
    { box := ⟨(38513093/1000000), (39707/1024)⟩, pieceIndex := 37 }
  ]
}

def scalarCert548 : MacroScalarCert 56 := {
  box := ⟨(39353/1024), (19883/512)⟩
  a := (76986939/250000000000)
  segments := [
    { box := ⟨(39353/1024), (38513093/1000000)⟩, pieceIndex := 36 },
    { box := ⟨(38513093/1000000), (19883/512)⟩, pieceIndex := 37 }
  ]
}

def scalarCert549 : MacroScalarCert 56 := {
  box := ⟨(9853/256), (39825/1024)⟩
  a := (76986939/250000000000)
  segments := [
    { box := ⟨(9853/256), (38513093/1000000)⟩, pieceIndex := 36 },
    { box := ⟨(38513093/1000000), (39825/1024)⟩, pieceIndex := 37 }
  ]
}

def scalarCert550 : MacroScalarCert 56 := {
  box := ⟨(6549/256), (26373/1024)⟩
  a := (4846047689033107029255715842121/20000000000000000000000000000000000)
  segments := [
    { box := ⟨(6549/256), (2560347/100000)⟩, pieceIndex := 23 },
    { box := ⟨(2560347/100000), (26373/1024)⟩, pieceIndex := 24 }
  ]
}

def scalarCert551 : MacroScalarCert 56 := {
  box := ⟨(13275/512), (3363/128)⟩
  a := (148698801/250000000000)
  segments := [
    { box := ⟨(13275/512), (2597847/100000)⟩, pieceIndex := 24 },
    { box := ⟨(2597847/100000), (3363/128)⟩, pieceIndex := 25 }
  ]
}

def scalarCert552 : MacroScalarCert 56 := {
  box := ⟨(45253/1024), (22833/512)⟩
  a := (125492473536974126032423063314169/8000000000000000000000000000000000000)
  segments := [
    { box := ⟨(45253/1024), (5551521/125000)⟩, pieceIndex := 41 },
    { box := ⟨(5551521/125000), (22833/512)⟩, pieceIndex := 42 }
  ]
}

def scalarCert553 : MacroScalarCert 56 := {
  box := ⟨(8201/256), (2065/64)⟩
  a := (7402913802521846133201894614329/20000000000000000000000000000000000)
  segments := [
    { box := ⟨(8201/256), (6448527/200000)⟩, pieceIndex := 30 },
    { box := ⟨(6448527/200000), (2065/64)⟩, pieceIndex := 31 }
  ]
}

def scalarCert554 : MacroScalarCert 56 := {
  box := ⟨(32863/1024), (33099/1024)⟩
  a := (104124691/250000000000)
  segments := [
    { box := ⟨(32863/1024), (6448527/200000)⟩, pieceIndex := 30 },
    { box := ⟨(6448527/200000), (33099/1024)⟩, pieceIndex := 31 }
  ]
}

def scalarCert555 : MacroScalarCert 56 := {
  box := ⟨(22833/512), (46079/1024)⟩
  a := (403384292552130139662239000449081/2000000000000000000000000000000000000)
  segments := [
    { box := ⟨(22833/512), (1399599/31250)⟩, pieceIndex := 42 },
    { box := ⟨(1399599/31250), (46079/1024)⟩, pieceIndex := 43 }
  ]
}

def scalarCert556 : MacroScalarCert 56 := {
  box := ⟨(45725/1024), (23069/512)⟩
  a := (236947891/1000000000000)
  segments := [
    { box := ⟨(45725/1024), (1399599/31250)⟩, pieceIndex := 42 },
    { box := ⟨(1399599/31250), (23069/512)⟩, pieceIndex := 43 }
  ]
}

def scalarCert557 : MacroScalarCert 56 := {
  box := ⟨(15871/512), (16107/512)⟩
  a := (1982313064455441554709887444329/1280000000000000000000000000000000000)
  segments := [
    { box := ⟨(15871/512), (15558817/500000)⟩, pieceIndex := 26 },
    { box := ⟨(15558817/500000), (16107/512)⟩, pieceIndex := 27 }
  ]
}

def scalarCert558 : MacroScalarCert 56 := {
  box := ⟨(12685/512), (12803/512)⟩
  a := (13224910662800597294854280157649/125000000000000000000000000000000000)
  segments := [
    { box := ⟨(12685/512), (24853469/1000000)⟩, pieceIndex := 20 },
    { box := ⟨(24853469/1000000), (12803/512)⟩, pieceIndex := 21 }
  ]
}

def scalarCert559 : MacroScalarCert 56 := {
  box := ⟨(6313/256), (1593/64)⟩
  a := (1859160367141373243742933961/7629394531250000000000000000000)
  segments := [
    { box := ⟨(6313/256), (24853469/1000000)⟩, pieceIndex := 20 },
    { box := ⟨(24853469/1000000), (1593/64)⟩, pieceIndex := 21 }
  ]
}

def scalarCert560 : MacroScalarCert 56 := {
  box := ⟨(7965/256), (16107/512)⟩
  a := (1982313064455441554709887444329/1280000000000000000000000000000000000)
  segments := [
    { box := ⟨(7965/256), (15558817/500000)⟩, pieceIndex := 26 },
    { box := ⟨(15558817/500000), (16107/512)⟩, pieceIndex := 27 }
  ]
}

def scalarCert561 : MacroScalarCert 56 := {
  box := ⟨(3245/64), (26255/512)⟩
  a := (9965930645410815779513042967721/125000000000000000000000000000000000)
  segments := [
    { box := ⟨(3245/64), (51063511/1000000)⟩, pieceIndex := 48 },
    { box := ⟨(51063511/1000000), (26255/512)⟩, pieceIndex := 49 }
  ]
}

def scalarCert562 : MacroScalarCert 56 := {
  box := ⟨(3245/64), (6903/128)⟩
  a := (9965930645410815779513042967721/125000000000000000000000000000000000)
  segments := [
    { box := ⟨(3245/64), (51063511/1000000)⟩, pieceIndex := 48 },
    { box := ⟨(51063511/1000000), (6903/128)⟩, pieceIndex := 49 }
  ]
}

def scalarCert563 : MacroScalarCert 56 := {
  box := ⟨(3835/128), (7965/256)⟩
  a := (1624834442189069327106291141707521/8000000000000000000000000000000000000)
  segments := [
    { box := ⟨(3835/128), (15371317/500000)⟩, pieceIndex := 25 },
    { box := ⟨(15371317/500000), (7965/256)⟩, pieceIndex := 26 }
  ]
}

def scalarCert564 : MacroScalarCert 56 := {
  box := ⟨(7729/256), (1003/32)⟩
  a := (37896421104977184428389275321/1250000000000000000000000000000000)
  segments := [
    { box := ⟨(7729/256), (15371317/500000)⟩, pieceIndex := 25 },
    { box := ⟨(15371317/500000), (15558817/500000)⟩, pieceIndex := 26 },
    { box := ⟨(15558817/500000), (1003/32)⟩, pieceIndex := 27 }
  ]
}

def scalarCert565 : MacroScalarCert 56 := {
  box := ⟨(7729/256), (7965/256)⟩
  a := (1624834442189069327106291141707521/8000000000000000000000000000000000000)
  segments := [
    { box := ⟨(7729/256), (15371317/500000)⟩, pieceIndex := 25 },
    { box := ⟨(15371317/500000), (7965/256)⟩, pieceIndex := 26 }
  ]
}

def scalarCert566 : MacroScalarCert 56 := {
  box := ⟨(1947/64), (7965/256)⟩
  a := (1624834442189069327106291141707521/8000000000000000000000000000000000000)
  segments := [
    { box := ⟨(1947/64), (15371317/500000)⟩, pieceIndex := 25 },
    { box := ⟨(15371317/500000), (7965/256)⟩, pieceIndex := 26 }
  ]
}

def scalarCert567 : MacroScalarCert 56 := {
  box := ⟨(7847/256), (15989/512)⟩
  a := (122123177780190359515549805444329/1280000000000000000000000000000000000)
  segments := [
    { box := ⟨(7847/256), (15371317/500000)⟩, pieceIndex := 25 },
    { box := ⟨(15371317/500000), (15558817/500000)⟩, pieceIndex := 26 },
    { box := ⟨(15558817/500000), (15989/512)⟩, pieceIndex := 27 }
  ]
}

def scalarCert568 : MacroScalarCert 56 := {
  box := ⟨(15753/512), (1003/32)⟩
  a := (37896421104977184428389275321/1250000000000000000000000000000000)
  segments := [
    { box := ⟨(15753/512), (15558817/500000)⟩, pieceIndex := 26 },
    { box := ⟨(15558817/500000), (1003/32)⟩, pieceIndex := 27 }
  ]
}

def scalarCert569 : MacroScalarCert 56 := {
  box := ⟨(7965/256), (32155/1024)⟩
  a := (58329686341077893138301782230441/5120000000000000000000000000000000000)
  segments := [
    { box := ⟨(7965/256), (15558817/500000)⟩, pieceIndex := 26 },
    { box := ⟨(15558817/500000), (32155/1024)⟩, pieceIndex := 27 }
  ]
}

def scalarCert570 : MacroScalarCert 56 := {
  box := ⟨(15871/512), (1003/32)⟩
  a := (37896421104977184428389275321/1250000000000000000000000000000000)
  segments := [
    { box := ⟨(15871/512), (15558817/500000)⟩, pieceIndex := 26 },
    { box := ⟨(15558817/500000), (1003/32)⟩, pieceIndex := 27 }
  ]
}

def scalarCert571 : MacroScalarCert 56 := {
  box := ⟨(45607/1024), (22951/512)⟩
  a := (1317975791431150018325352729749449/8000000000000000000000000000000000000)
  segments := [
    { box := ⟨(45607/1024), (1399599/31250)⟩, pieceIndex := 42 },
    { box := ⟨(1399599/31250), (22951/512)⟩, pieceIndex := 43 }
  ]
}

def scalarCert572 : MacroScalarCert 56 := {
  box := ⟨(22833/512), (45961/1024)⟩
  a := (403384292552130139662239000449081/2000000000000000000000000000000000000)
  segments := [
    { box := ⟨(22833/512), (1399599/31250)⟩, pieceIndex := 42 },
    { box := ⟨(1399599/31250), (45961/1024)⟩, pieceIndex := 43 }
  ]
}

def scalarCert573 : MacroScalarCert 56 := {
  box := ⟨(13039/512), (52451/2048)⟩
  a := (8807754158064216214287607996609/80000000000000000000000000000000000)
  segments := [
    { box := ⟨(13039/512), (2560347/100000)⟩, pieceIndex := 23 },
    { box := ⟨(2560347/100000), (52451/2048)⟩, pieceIndex := 24 }
  ]
}

def scalarCert574 : MacroScalarCert 56 := {
  box := ⟨(38881/1024), (78175/2048)⟩
  a := (4812837764803654107675019035354201/128000000000000000000000000000000000000)
  segments := [
    { box := ⟨(38881/1024), (38138093/1000000)⟩, pieceIndex := 35 },
    { box := ⟨(38138093/1000000), (78175/2048)⟩, pieceIndex := 36 }
  ]
}

def scalarCert575 : MacroScalarCert 56 := {
  box := ⟨(45607/1024), (91745/2048)⟩
  a := (1317975791431150018325352729749449/8000000000000000000000000000000000000)
  segments := [
    { box := ⟨(45607/1024), (1399599/31250)⟩, pieceIndex := 42 },
    { box := ⟨(1399599/31250), (91745/2048)⟩, pieceIndex := 43 }
  ]
}

def scalarCert576 : MacroScalarCert 56 := {
  box := ⟨(52215/2048), (26255/1024)⟩
  a := (177052464914037556222753657636369/1280000000000000000000000000000000000)
  segments := [
    { box := ⟨(52215/2048), (2560347/100000)⟩, pieceIndex := 23 },
    { box := ⟨(2560347/100000), (26255/1024)⟩, pieceIndex := 24 }
  ]
}

def scalarCert577 : MacroScalarCert 56 := {
  box := ⟨(77821/2048), (39117/1024)⟩
  a := (24993524701536833159244342492244929/512000000000000000000000000000000000000)
  segments := [
    { box := ⟨(77821/2048), (38138093/1000000)⟩, pieceIndex := 35 },
    { box := ⟨(38138093/1000000), (39117/1024)⟩, pieceIndex := 36 }
  ]
}

def scalarCert578 : MacroScalarCert 56 := {
  box := ⟨(91273/2048), (22951/512)⟩
  a := (5848088301938050798969125031450921/32000000000000000000000000000000000000)
  segments := [
    { box := ⟨(91273/2048), (1399599/31250)⟩, pieceIndex := 42 },
    { box := ⟨(1399599/31250), (22951/512)⟩, pieceIndex := 43 }
  ]
}

def scalarCert579 : MacroScalarCert 56 := {
  box := ⟨(22833/512), (11505/256)⟩
  a := (403384292552130139662239000449081/2000000000000000000000000000000000000)
  segments := [
    { box := ⟨(22833/512), (1399599/31250)⟩, pieceIndex := 42 },
    { box := ⟨(1399599/31250), (11505/256)⟩, pieceIndex := 43 }
  ]
}

def scalarCert580 : MacroScalarCert 56 := {
  box := ⟨(45725/1024), (11505/256)⟩
  a := (236947891/1000000000000)
  segments := [
    { box := ⟨(45725/1024), (1399599/31250)⟩, pieceIndex := 42 },
    { box := ⟨(1399599/31250), (11505/256)⟩, pieceIndex := 43 }
  ]
}

def scalarCert581 : MacroScalarCert 56 := {
  box := ⟨(22715/512), (5723/128)⟩
  a := (140156038325279709457315581152761/2000000000000000000000000000000000000)
  segments := [
    { box := ⟨(22715/512), (5551521/125000)⟩, pieceIndex := 41 },
    { box := ⟨(5551521/125000), (5723/128)⟩, pieceIndex := 42 }
  ]
}

def scalarCert582 : MacroScalarCert 56 := {
  box := ⟨(38999/1024), (39235/1024)⟩
  a := (11677601791109548745136801743604201/128000000000000000000000000000000000000)
  segments := [
    { box := ⟨(38999/1024), (38138093/1000000)⟩, pieceIndex := 35 },
    { box := ⟨(38138093/1000000), (39235/1024)⟩, pieceIndex := 36 }
  ]
}

def scalarCert583 : MacroScalarCert 56 := {
  box := ⟨(9735/256), (78293/2048)⟩
  a := (491938936455960966047921141896161/8000000000000000000000000000000000000)
  segments := [
    { box := ⟨(9735/256), (38138093/1000000)⟩, pieceIndex := 35 },
    { box := ⟨(38138093/1000000), (78293/2048)⟩, pieceIndex := 36 }
  ]
}

def scalarCert584 : MacroScalarCert 56 := {
  box := ⟨(77939/2048), (4897/128)⟩
  a := (38723052754148622434167907908744929/512000000000000000000000000000000000000)
  segments := [
    { box := ⟨(77939/2048), (38138093/1000000)⟩, pieceIndex := 35 },
    { box := ⟨(38138093/1000000), (4897/128)⟩, pieceIndex := 36 }
  ]
}

def scalarCert585 : MacroScalarCert 56 := {
  box := ⟨(45725/1024), (46079/1024)⟩
  a := (236947891/1000000000000)
  segments := [
    { box := ⟨(45725/1024), (1399599/31250)⟩, pieceIndex := 42 },
    { box := ⟨(1399599/31250), (46079/1024)⟩, pieceIndex := 43 }
  ]
}

def scalarCert586 : MacroScalarCert 56 := {
  box := ⟨(9853/512), (1239/64)⟩
  a := (308609266148826216472188856757689/1280000000000000000000000000000000000)
  segments := [
    { box := ⟨(9853/512), (19351747/1000000)⟩, pieceIndex := 17 },
    { box := ⟨(19351747/1000000), (1239/64)⟩, pieceIndex := 18 }
  ]
}

def scalarCert587 : MacroScalarCert 56 := {
  box := ⟨(5723/128), (23069/512)⟩
  a := (236947891/1000000000000)
  segments := [
    { box := ⟨(5723/128), (1399599/31250)⟩, pieceIndex := 42 },
    { box := ⟨(1399599/31250), (23069/512)⟩, pieceIndex := 43 }
  ]
}

def scalarCert588 : MacroScalarCert 56 := {
  box := ⟨(5723/128), (46197/1024)⟩
  a := (236947891/1000000000000)
  segments := [
    { box := ⟨(5723/128), (1399599/31250)⟩, pieceIndex := 42 },
    { box := ⟨(1399599/31250), (46197/1024)⟩, pieceIndex := 43 }
  ]
}

def scalarCert589 : MacroScalarCert 56 := {
  box := ⟨(5723/128), (2891/64)⟩
  a := (236947891/1000000000000)
  segments := [
    { box := ⟨(5723/128), (1399599/31250)⟩, pieceIndex := 42 },
    { box := ⟨(1399599/31250), (2891/64)⟩, pieceIndex := 43 }
  ]
}

def scalarCert590 : MacroScalarCert 56 := {
  box := ⟨(16225/512), (16343/512)⟩
  a := (3895225326904878308147162909841/80000000000000000000000000000000000)
  segments := [
    { box := ⟨(16225/512), (6373527/200000)⟩, pieceIndex := 29 },
    { box := ⟨(6373527/200000), (16343/512)⟩, pieceIndex := 30 }
  ]
}

def scalarCert591 : MacroScalarCert 56 := {
  box := ⟨(39117/1024), (39471/1024)⟩
  a := (890431430789413157949114897032401/5120000000000000000000000000000000000)
  segments := [
    { box := ⟨(39117/1024), (38513093/1000000)⟩, pieceIndex := 36 },
    { box := ⟨(38513093/1000000), (39471/1024)⟩, pieceIndex := 37 }
  ]
}

def scalarCert592 : MacroScalarCert 56 := {
  box := ⟨(4897/128), (19765/512)⟩
  a := (17456552780050285252554156310809/80000000000000000000000000000000000)
  segments := [
    { box := ⟨(4897/128), (38513093/1000000)⟩, pieceIndex := 36 },
    { box := ⟨(38513093/1000000), (19765/512)⟩, pieceIndex := 37 }
  ]
}

def scalarCert593 : MacroScalarCert 56 := {
  box := ⟨(16225/512), (32745/1024)⟩
  a := (3895225326904878308147162909841/80000000000000000000000000000000000)
  segments := [
    { box := ⟨(16225/512), (6373527/200000)⟩, pieceIndex := 29 },
    { box := ⟨(6373527/200000), (32745/1024)⟩, pieceIndex := 30 }
  ]
}

def scalarCert594 : MacroScalarCert 56 := {
  box := ⟨(45371/1024), (45725/1024)⟩
  a := (380995896373736237860712551314169/8000000000000000000000000000000000000)
  segments := [
    { box := ⟨(45371/1024), (5551521/125000)⟩, pieceIndex := 41 },
    { box := ⟨(5551521/125000), (45725/1024)⟩, pieceIndex := 42 }
  ]
}

def scalarCert595 : MacroScalarCert 56 := {
  box := ⟨(3953/128), (1003/32)⟩
  a := (37896421104977184428389275321/1250000000000000000000000000000000)
  segments := [
    { box := ⟨(3953/128), (15558817/500000)⟩, pieceIndex := 26 },
    { box := ⟨(15558817/500000), (1003/32)⟩, pieceIndex := 27 }
  ]
}

def scalarCert596 : MacroScalarCert 56 := {
  box := ⟨(3953/128), (15989/512)⟩
  a := (122123177780190359515549805444329/1280000000000000000000000000000000000)
  segments := [
    { box := ⟨(3953/128), (15558817/500000)⟩, pieceIndex := 26 },
    { box := ⟨(15558817/500000), (15989/512)⟩, pieceIndex := 27 }
  ]
}

def scalarCert597 : MacroScalarCert 56 := {
  box := ⟨(45135/1024), (45607/1024)⟩
  a := (8326505390882798349213653439169/8000000000000000000000000000000000000)
  segments := [
    { box := ⟨(45135/1024), (5551521/125000)⟩, pieceIndex := 41 },
    { box := ⟨(5551521/125000), (45607/1024)⟩, pieceIndex := 42 }
  ]
}

def scalarCert598 : MacroScalarCert 56 := {
  box := ⟨(22597/512), (45607/1024)⟩
  a := (12404326906898653543170837152761/2000000000000000000000000000000000000)
  segments := [
    { box := ⟨(22597/512), (5551521/125000)⟩, pieceIndex := 41 },
    { box := ⟨(5551521/125000), (45607/1024)⟩, pieceIndex := 42 }
  ]
}

def scalarCert599 : MacroScalarCert 56 := {
  box := ⟨(45253/1024), (45607/1024)⟩
  a := (125492473536974126032423063314169/8000000000000000000000000000000000000)
  segments := [
    { box := ⟨(45253/1024), (5551521/125000)⟩, pieceIndex := 41 },
    { box := ⟨(5551521/125000), (45607/1024)⟩, pieceIndex := 42 }
  ]
}

def scalarCert600 : MacroScalarCert 56 := {
  box := ⟨(177/4), (22833/512)⟩
  a := (3600341844467488615851330529/122070312500000000000000000000000)
  segments := [
    { box := ⟨(177/4), (5551521/125000)⟩, pieceIndex := 41 },
    { box := ⟨(5551521/125000), (22833/512)⟩, pieceIndex := 42 }
  ]
}

def scalarCert601 : MacroScalarCert 56 := {
  box := ⟨(7965/256), (1003/32)⟩
  a := (37896421104977184428389275321/1250000000000000000000000000000000)
  segments := [
    { box := ⟨(7965/256), (15558817/500000)⟩, pieceIndex := 26 },
    { box := ⟨(15558817/500000), (1003/32)⟩, pieceIndex := 27 }
  ]
}

def scalarCert602 : MacroScalarCert 56 := {
  box := ⟨(45371/1024), (22833/512)⟩
  a := (380995896373736237860712551314169/8000000000000000000000000000000000000)
  segments := [
    { box := ⟨(45371/1024), (5551521/125000)⟩, pieceIndex := 41 },
    { box := ⟨(5551521/125000), (22833/512)⟩, pieceIndex := 42 }
  ]
}

def scalarCert603 : MacroScalarCert 56 := {
  box := ⟨(22715/512), (45725/1024)⟩
  a := (140156038325279709457315581152761/2000000000000000000000000000000000000)
  segments := [
    { box := ⟨(22715/512), (5551521/125000)⟩, pieceIndex := 41 },
    { box := ⟨(5551521/125000), (45725/1024)⟩, pieceIndex := 42 }
  ]
}

def scalarCert604 : MacroScalarCert 56 := {
  box := ⟨(45371/1024), (91273/2048)⟩
  a := (380995896373736237860712551314169/8000000000000000000000000000000000000)
  segments := [
    { box := ⟨(45371/1024), (5551521/125000)⟩, pieceIndex := 41 },
    { box := ⟨(5551521/125000), (91273/2048)⟩, pieceIndex := 42 }
  ]
}

def scalarCert605 : MacroScalarCert 56 := {
  box := ⟨(90801/2048), (22833/512)⟩
  a := (1865947917513376303361814742084801/32000000000000000000000000000000000000)
  segments := [
    { box := ⟨(90801/2048), (5551521/125000)⟩, pieceIndex := 41 },
    { box := ⟨(5551521/125000), (22833/512)⟩, pieceIndex := 42 }
  ]
}

def scalarCert606 : MacroScalarCert 56 := {
  box := ⟨(22715/512), (91391/2048)⟩
  a := (140156038325279709457315581152761/2000000000000000000000000000000000000)
  segments := [
    { box := ⟨(22715/512), (5551521/125000)⟩, pieceIndex := 41 },
    { box := ⟨(5551521/125000), (91391/2048)⟩, pieceIndex := 42 }
  ]
}

def scalarCert607 : MacroScalarCert 56 := {
  box := ⟨(22715/512), (22833/512)⟩
  a := (140156038325279709457315581152761/2000000000000000000000000000000000000)
  segments := [
    { box := ⟨(22715/512), (5551521/125000)⟩, pieceIndex := 41 },
    { box := ⟨(5551521/125000), (22833/512)⟩, pieceIndex := 42 }
  ]
}

def scalarCert608 : MacroScalarCert 56 := {
  box := ⟨(90919/2048), (91391/2048)⟩
  a := (2653629672568242095308553874334801/32000000000000000000000000000000000000)
  segments := [
    { box := ⟨(90919/2048), (5551521/125000)⟩, pieceIndex := 41 },
    { box := ⟨(5551521/125000), (91391/2048)⟩, pieceIndex := 42 }
  ]
}

def scalarCert609 : MacroScalarCert 56 := {
  box := ⟨(90919/2048), (22833/512)⟩
  a := (2653629672568242095308553874334801/32000000000000000000000000000000000000)
  segments := [
    { box := ⟨(90919/2048), (5551521/125000)⟩, pieceIndex := 41 },
    { box := ⟨(5551521/125000), (22833/512)⟩, pieceIndex := 42 }
  ]
}

def scalarCert610 : MacroScalarCert 56 := {
  box := ⟨(52215/2048), (52451/2048)⟩
  a := (177052464914037556222753657636369/1280000000000000000000000000000000000)
  segments := [
    { box := ⟨(52215/2048), (2560347/100000)⟩, pieceIndex := 23 },
    { box := ⟨(2560347/100000), (52451/2048)⟩, pieceIndex := 24 }
  ]
}

def scalarCert611 : MacroScalarCert 56 := {
  box := ⟨(90919/2048), (45725/1024)⟩
  a := (2653629672568242095308553874334801/32000000000000000000000000000000000000)
  segments := [
    { box := ⟨(90919/2048), (5551521/125000)⟩, pieceIndex := 41 },
    { box := ⟨(5551521/125000), (45725/1024)⟩, pieceIndex := 42 }
  ]
}

def scalarCert612 : MacroScalarCert 56 := {
  box := ⟨(177/4), (45607/1024)⟩
  a := (3600341844467488615851330529/122070312500000000000000000000000)
  segments := [
    { box := ⟨(177/4), (5551521/125000)⟩, pieceIndex := 41 },
    { box := ⟨(5551521/125000), (45607/1024)⟩, pieceIndex := 42 }
  ]
}

def scalarCert613 : MacroScalarCert 56 := {
  box := ⟨(26137/1024), (26255/1024)⟩
  a := (54324773825972371723691245464561/320000000000000000000000000000000000)
  segments := [
    { box := ⟨(26137/1024), (2560347/100000)⟩, pieceIndex := 23 },
    { box := ⟨(2560347/100000), (26255/1024)⟩, pieceIndex := 24 }
  ]
}

def scalarCert614 : MacroScalarCert 56 := {
  box := ⟨(25311/2048), (12685/1024)⟩
  a := (5885991482681207829900684848390449/5120000000000000000000000000000000000)
  segments := [
    { box := ⟨(25311/2048), (1238029/100000)⟩, pieceIndex := 8 },
    { box := ⟨(1238029/100000), (12685/1024)⟩, pieceIndex := 9 }
  ]
}

def scalarCert615 : MacroScalarCert 56 := {
  box := ⟨(26137/1024), (52451/2048)⟩
  a := (54324773825972371723691245464561/320000000000000000000000000000000000)
  segments := [
    { box := ⟨(26137/1024), (2560347/100000)⟩, pieceIndex := 23 },
    { box := ⟨(2560347/100000), (52451/2048)⟩, pieceIndex := 24 }
  ]
}

def scalarCert616 : MacroScalarCert 56 := {
  box := ⟨(52333/2048), (26255/1024)⟩
  a := (261663957698583251444635700611369/1280000000000000000000000000000000000)
  segments := [
    { box := ⟨(52333/2048), (2560347/100000)⟩, pieceIndex := 23 },
    { box := ⟨(2560347/100000), (26255/1024)⟩, pieceIndex := 24 }
  ]
}

def scalarCert617 : MacroScalarCert 56 := {
  box := ⟨(26137/1024), (52569/2048)⟩
  a := (54324773825972371723691245464561/320000000000000000000000000000000000)
  segments := [
    { box := ⟨(26137/1024), (2560347/100000)⟩, pieceIndex := 23 },
    { box := ⟨(2560347/100000), (52569/2048)⟩, pieceIndex := 24 }
  ]
}

def scalarCert618 : MacroScalarCert 56 := {
  box := ⟨(77703/2048), (19529/512)⟩
  a := (14257571006214851641434154028869929/512000000000000000000000000000000000000)
  segments := [
    { box := ⟨(77703/2048), (38138093/1000000)⟩, pieceIndex := 35 },
    { box := ⟨(38138093/1000000), (19529/512)⟩, pieceIndex := 36 }
  ]
}

def scalarCert619 : MacroScalarCert 56 := {
  box := ⟨(52333/2048), (13157/512)⟩
  a := (261663957698583251444635700611369/1280000000000000000000000000000000000)
  segments := [
    { box := ⟨(52333/2048), (2560347/100000)⟩, pieceIndex := 23 },
    { box := ⟨(2560347/100000), (13157/512)⟩, pieceIndex := 24 }
  ]
}

def scalarCert620 : MacroScalarCert 56 := {
  box := ⟨(38881/1024), (19529/512)⟩
  a := (4812837764803654107675019035354201/128000000000000000000000000000000000000)
  segments := [
    { box := ⟨(38881/1024), (38138093/1000000)⟩, pieceIndex := 35 },
    { box := ⟨(38138093/1000000), (19529/512)⟩, pieceIndex := 36 }
  ]
}

def scalarCert621 : MacroScalarCert 56 := {
  box := ⟨(52333/2048), (52569/2048)⟩
  a := (261663957698583251444635700611369/1280000000000000000000000000000000000)
  segments := [
    { box := ⟨(52333/2048), (2560347/100000)⟩, pieceIndex := 23 },
    { box := ⟨(2560347/100000), (52569/2048)⟩, pieceIndex := 24 }
  ]
}

def scalarCert622 : MacroScalarCert 56 := {
  box := ⟨(77821/2048), (19529/512)⟩
  a := (24993524701536833159244342492244929/512000000000000000000000000000000000000)
  segments := [
    { box := ⟨(77821/2048), (38138093/1000000)⟩, pieceIndex := 35 },
    { box := ⟨(38138093/1000000), (19529/512)⟩, pieceIndex := 36 }
  ]
}

def scalarCert623 : MacroScalarCert 56 := {
  box := ⟨(6549/256), (13157/512)⟩
  a := (4846047689033107029255715842121/20000000000000000000000000000000000)
  segments := [
    { box := ⟨(6549/256), (2560347/100000)⟩, pieceIndex := 23 },
    { box := ⟨(2560347/100000), (13157/512)⟩, pieceIndex := 24 }
  ]
}

def scalarCert624 : MacroScalarCert 56 := {
  box := ⟨(91273/2048), (91745/2048)⟩
  a := (5848088301938050798969125031450921/32000000000000000000000000000000000000)
  segments := [
    { box := ⟨(91273/2048), (1399599/31250)⟩, pieceIndex := 42 },
    { box := ⟨(1399599/31250), (91745/2048)⟩, pieceIndex := 43 }
  ]
}

def scalarCert625 : MacroScalarCert 56 := {
  box := ⟨(22833/512), (22951/512)⟩
  a := (403384292552130139662239000449081/2000000000000000000000000000000000000)
  segments := [
    { box := ⟨(22833/512), (1399599/31250)⟩, pieceIndex := 42 },
    { box := ⟨(1399599/31250), (22951/512)⟩, pieceIndex := 43 }
  ]
}

def scalarCert626 : MacroScalarCert 56 := {
  box := ⟨(22833/512), (91745/2048)⟩
  a := (403384292552130139662239000449081/2000000000000000000000000000000000000)
  segments := [
    { box := ⟨(22833/512), (1399599/31250)⟩, pieceIndex := 42 },
    { box := ⟨(1399599/31250), (91745/2048)⟩, pieceIndex := 43 }
  ]
}

def scalarCert627 : MacroScalarCert 56 := {
  box := ⟨(91391/2048), (22951/512)⟩
  a := (7090084302412694380181507846200921/32000000000000000000000000000000000000)
  segments := [
    { box := ⟨(91391/2048), (1399599/31250)⟩, pieceIndex := 42 },
    { box := ⟨(1399599/31250), (22951/512)⟩, pieceIndex := 43 }
  ]
}

def scalarCert628 : MacroScalarCert 56 := {
  box := ⟨(6549/256), (52569/2048)⟩
  a := (4846047689033107029255715842121/20000000000000000000000000000000000)
  segments := [
    { box := ⟨(6549/256), (2560347/100000)⟩, pieceIndex := 23 },
    { box := ⟨(2560347/100000), (52569/2048)⟩, pieceIndex := 24 }
  ]
}

def scalarCert629 : MacroScalarCert 56 := {
  box := ⟨(91391/2048), (91745/2048)⟩
  a := (7090084302412694380181507846200921/32000000000000000000000000000000000000)
  segments := [
    { box := ⟨(91391/2048), (1399599/31250)⟩, pieceIndex := 42 },
    { box := ⟨(1399599/31250), (91745/2048)⟩, pieceIndex := 43 }
  ]
}

def scalarCert630 : MacroScalarCert 56 := {
  box := ⟨(9735/256), (19529/512)⟩
  a := (491938936455960966047921141896161/8000000000000000000000000000000000000)
  segments := [
    { box := ⟨(9735/256), (38138093/1000000)⟩, pieceIndex := 35 },
    { box := ⟨(38138093/1000000), (19529/512)⟩, pieceIndex := 36 }
  ]
}

def scalarCert631 : MacroScalarCert 56 := {
  box := ⟨(45725/1024), (22951/512)⟩
  a := (236947891/1000000000000)
  segments := [
    { box := ⟨(45725/1024), (1399599/31250)⟩, pieceIndex := 42 },
    { box := ⟨(1399599/31250), (22951/512)⟩, pieceIndex := 43 }
  ]
}

def scalarCert632 : MacroScalarCert 56 := {
  box := ⟨(6549/256), (52687/2048)⟩
  a := (4846047689033107029255715842121/20000000000000000000000000000000000)
  segments := [
    { box := ⟨(6549/256), (2560347/100000)⟩, pieceIndex := 23 },
    { box := ⟨(2560347/100000), (52687/2048)⟩, pieceIndex := 24 }
  ]
}

def scalarCert633 : MacroScalarCert 56 := {
  box := ⟨(77821/2048), (78175/2048)⟩
  a := (24993524701536833159244342492244929/512000000000000000000000000000000000000)
  segments := [
    { box := ⟨(77821/2048), (38138093/1000000)⟩, pieceIndex := 35 },
    { box := ⟨(38138093/1000000), (78175/2048)⟩, pieceIndex := 36 }
  ]
}

def scalarCert634 : MacroScalarCert 56 := {
  box := ⟨(9735/256), (78175/2048)⟩
  a := (491938936455960966047921141896161/8000000000000000000000000000000000000)
  segments := [
    { box := ⟨(9735/256), (38138093/1000000)⟩, pieceIndex := 35 },
    { box := ⟨(38138093/1000000), (78175/2048)⟩, pieceIndex := 36 }
  ]
}

def scalarCert635 : MacroScalarCert 56 := {
  box := ⟨(9735/256), (39117/1024)⟩
  a := (491938936455960966047921141896161/8000000000000000000000000000000000000)
  segments := [
    { box := ⟨(9735/256), (38138093/1000000)⟩, pieceIndex := 35 },
    { box := ⟨(38138093/1000000), (39117/1024)⟩, pieceIndex := 36 }
  ]
}

def scalarCert636 : MacroScalarCert 56 := {
  box := ⟨(77939/2048), (39117/1024)⟩
  a := (38723052754148622434167907908744929/512000000000000000000000000000000000000)
  segments := [
    { box := ⟨(77939/2048), (38138093/1000000)⟩, pieceIndex := 35 },
    { box := ⟨(38138093/1000000), (39117/1024)⟩, pieceIndex := 36 }
  ]
}

def scalarCert637 : MacroScalarCert 56 := {
  box := ⟨(22833/512), (91863/2048)⟩
  a := (403384292552130139662239000449081/2000000000000000000000000000000000000)
  segments := [
    { box := ⟨(22833/512), (1399599/31250)⟩, pieceIndex := 42 },
    { box := ⟨(1399599/31250), (91863/2048)⟩, pieceIndex := 43 }
  ]
}

def scalarCert638 : MacroScalarCert 56 := {
  box := ⟨(91391/2048), (91863/2048)⟩
  a := (7090084302412694380181507846200921/32000000000000000000000000000000000000)
  segments := [
    { box := ⟨(91391/2048), (1399599/31250)⟩, pieceIndex := 42 },
    { box := ⟨(1399599/31250), (91863/2048)⟩, pieceIndex := 43 }
  ]
}

def scalarCert639 : MacroScalarCert 56 := {
  box := ⟨(91391/2048), (45961/1024)⟩
  a := (7090084302412694380181507846200921/32000000000000000000000000000000000000)
  segments := [
    { box := ⟨(91391/2048), (1399599/31250)⟩, pieceIndex := 42 },
    { box := ⟨(1399599/31250), (45961/1024)⟩, pieceIndex := 43 }
  ]
}

def scalarCert640 : MacroScalarCert 56 := {
  box := ⟨(90801/2048), (91273/2048)⟩
  a := (1865947917513376303361814742084801/32000000000000000000000000000000000000)
  segments := [
    { box := ⟨(90801/2048), (5551521/125000)⟩, pieceIndex := 41 },
    { box := ⟨(5551521/125000), (91273/2048)⟩, pieceIndex := 42 }
  ]
}

def scalarCert641 : MacroScalarCert 56 := {
  box := ⟨(22715/512), (91273/2048)⟩
  a := (140156038325279709457315581152761/2000000000000000000000000000000000000)
  segments := [
    { box := ⟨(22715/512), (5551521/125000)⟩, pieceIndex := 41 },
    { box := ⟨(5551521/125000), (91273/2048)⟩, pieceIndex := 42 }
  ]
}

def scalarCert642 : MacroScalarCert 56 := {
  box := ⟨(52333/2048), (104961/4096)⟩
  a := (261663957698583251444635700611369/1280000000000000000000000000000000000)
  segments := [
    { box := ⟨(52333/2048), (2560347/100000)⟩, pieceIndex := 23 },
    { box := ⟨(2560347/100000), (104961/4096)⟩, pieceIndex := 24 }
  ]
}

def scalarCert643 : MacroScalarCert 56 := {
  box := ⟨(104607/4096), (52451/2048)⟩
  a := (955866990002524559739871667673601/5120000000000000000000000000000000000)
  segments := [
    { box := ⟨(104607/4096), (2560347/100000)⟩, pieceIndex := 23 },
    { box := ⟨(2560347/100000), (52451/2048)⟩, pieceIndex := 24 }
  ]
}

def scalarCert644 : MacroScalarCert 56 := {
  box := ⟨(104725/4096), (26255/1024)⟩
  a := (1141562903590983285695073331748601/5120000000000000000000000000000000000)
  segments := [
    { box := ⟨(104725/4096), (2560347/100000)⟩, pieceIndex := 23 },
    { box := ⟨(2560347/100000), (26255/1024)⟩, pieceIndex := 24 }
  ]
}

def scalarCert645 : MacroScalarCert 56 := {
  box := ⟨(155819/4096), (19529/512)⟩
  a := (140040092579999022552830549861057841/2048000000000000000000000000000000000000)
  segments := [
    { box := ⟨(155819/4096), (38138093/1000000)⟩, pieceIndex := 35 },
    { box := ⟨(38138093/1000000), (19529/512)⟩, pieceIndex := 36 }
  ]
}

def scalarCert646 : MacroScalarCert 56 := {
  box := ⟨(77939/2048), (78175/2048)⟩
  a := (38723052754148622434167907908744929/512000000000000000000000000000000000000)
  segments := [
    { box := ⟨(77939/2048), (38138093/1000000)⟩, pieceIndex := 35 },
    { box := ⟨(38138093/1000000), (78175/2048)⟩, pieceIndex := 36 }
  ]
}

def scalarCert647 : MacroScalarCert 56 := {
  box := ⟨(38999/1024), (39117/1024)⟩
  a := (11677601791109548745136801743604201/128000000000000000000000000000000000000)
  segments := [
    { box := ⟨(38999/1024), (38138093/1000000)⟩, pieceIndex := 35 },
    { box := ⟨(38138093/1000000), (39117/1024)⟩, pieceIndex := 36 }
  ]
}

def scalarCert648 : MacroScalarCert 56 := {
  box := ⟨(6549/256), (105079/4096)⟩
  a := (4846047689033107029255715842121/20000000000000000000000000000000000)
  segments := [
    { box := ⟨(6549/256), (2560347/100000)⟩, pieceIndex := 23 },
    { box := ⟨(2560347/100000), (105079/4096)⟩, pieceIndex := 24 }
  ]
}

def scalarCert649 : MacroScalarCert 56 := {
  box := ⟨(104843/4096), (52569/2048)⟩
  a := (1343731745198809347161712573948601/5120000000000000000000000000000000000)
  segments := [
    { box := ⟨(104843/4096), (2560347/100000)⟩, pieceIndex := 23 },
    { box := ⟨(2560347/100000), (52569/2048)⟩, pieceIndex := 24 }
  ]
}

def scalarCert650 : MacroScalarCert 56 := {
  box := ⟨(77939/2048), (156291/4096)⟩
  a := (38723052754148622434167907908744929/512000000000000000000000000000000000000)
  segments := [
    { box := ⟨(77939/2048), (38138093/1000000)⟩, pieceIndex := 35 },
    { box := ⟨(38138093/1000000), (156291/4096)⟩, pieceIndex := 36 }
  ]
}

def scalarCert651 : MacroScalarCert 56 := {
  box := ⟨(155937/4096), (78175/2048)⟩
  a := (170492723042512408859791057647182841/2048000000000000000000000000000000000000)
  segments := [
    { box := ⟨(155937/4096), (38138093/1000000)⟩, pieceIndex := 35 },
    { box := ⟨(38138093/1000000), (78175/2048)⟩, pieceIndex := 36 }
  ]
}

def scalarCert652 : MacroScalarCert 56 := {
  box := ⟨(77939/2048), (78293/2048)⟩
  a := (38723052754148622434167907908744929/512000000000000000000000000000000000000)
  segments := [
    { box := ⟨(77939/2048), (38138093/1000000)⟩, pieceIndex := 35 },
    { box := ⟨(38138093/1000000), (78293/2048)⟩, pieceIndex := 36 }
  ]
}

def scalarCert653 : MacroScalarCert 56 := {
  box := ⟨(38999/1024), (78293/2048)⟩
  a := (11677601791109548745136801743604201/128000000000000000000000000000000000000)
  segments := [
    { box := ⟨(38999/1024), (38138093/1000000)⟩, pieceIndex := 35 },
    { box := ⟨(38138093/1000000), (78293/2048)⟩, pieceIndex := 36 }
  ]
}

def scalarCert654 : MacroScalarCert 56 := {
  box := ⟨(78057/2048), (78293/2048)⟩
  a := (55446155164050219466204850278369929/512000000000000000000000000000000000000)
  segments := [
    { box := ⟨(78057/2048), (38138093/1000000)⟩, pieceIndex := 35 },
    { box := ⟨(38138093/1000000), (78293/2048)⟩, pieceIndex := 36 }
  ]
}

def scalarCert655 : MacroScalarCert 56 := {
  box := ⟨(38999/1024), (4897/128)⟩
  a := (11677601791109548745136801743604201/128000000000000000000000000000000000000)
  segments := [
    { box := ⟨(38999/1024), (38138093/1000000)⟩, pieceIndex := 35 },
    { box := ⟨(38138093/1000000), (4897/128)⟩, pieceIndex := 36 }
  ]
}

def scalarCert656 : MacroScalarCert 56 := {
  box := ⟨(78057/2048), (4897/128)⟩
  a := (55446155164050219466204850278369929/512000000000000000000000000000000000000)
  segments := [
    { box := ⟨(78057/2048), (38138093/1000000)⟩, pieceIndex := 35 },
    { box := ⟨(38138093/1000000), (4897/128)⟩, pieceIndex := 36 }
  ]
}

def scalarCert657 : MacroScalarCert 56 := {
  box := ⟨(45725/1024), (91745/2048)⟩
  a := (236947891/1000000000000)
  segments := [
    { box := ⟨(45725/1024), (1399599/31250)⟩, pieceIndex := 42 },
    { box := ⟨(1399599/31250), (91745/2048)⟩, pieceIndex := 43 }
  ]
}

def scalarCert658 : MacroScalarCert 56 := {
  box := ⟨(45725/1024), (91863/2048)⟩
  a := (236947891/1000000000000)
  segments := [
    { box := ⟨(45725/1024), (1399599/31250)⟩, pieceIndex := 42 },
    { box := ⟨(1399599/31250), (91863/2048)⟩, pieceIndex := 43 }
  ]
}

def scalarCert659 : MacroScalarCert 56 := {
  box := ⟨(45725/1024), (45961/1024)⟩
  a := (236947891/1000000000000)
  segments := [
    { box := ⟨(45725/1024), (1399599/31250)⟩, pieceIndex := 42 },
    { box := ⟨(1399599/31250), (45961/1024)⟩, pieceIndex := 43 }
  ]
}

def scalarCert660 : MacroScalarCert 56 := {
  box := ⟨(91509/2048), (91863/2048)⟩
  a := (236947891/1000000000000)
  segments := [
    { box := ⟨(91509/2048), (1399599/31250)⟩, pieceIndex := 42 },
    { box := ⟨(1399599/31250), (91863/2048)⟩, pieceIndex := 43 }
  ]
}

def scalarCert661 : MacroScalarCert 56 := {
  box := ⟨(91509/2048), (45961/1024)⟩
  a := (236947891/1000000000000)
  segments := [
    { box := ⟨(91509/2048), (1399599/31250)⟩, pieceIndex := 42 },
    { box := ⟨(1399599/31250), (45961/1024)⟩, pieceIndex := 43 }
  ]
}

def scalarCert662 : MacroScalarCert 56 := {
  box := ⟨(91509/2048), (22951/512)⟩
  a := (236947891/1000000000000)
  segments := [
    { box := ⟨(91509/2048), (1399599/31250)⟩, pieceIndex := 42 },
    { box := ⟨(1399599/31250), (22951/512)⟩, pieceIndex := 43 }
  ]
}

def scalarCert663 : MacroScalarCert 56 := {
  box := ⟨(45725/1024), (91981/2048)⟩
  a := (236947891/1000000000000)
  segments := [
    { box := ⟨(45725/1024), (1399599/31250)⟩, pieceIndex := 42 },
    { box := ⟨(1399599/31250), (91981/2048)⟩, pieceIndex := 43 }
  ]
}

def scalarCert664 : MacroScalarCert 56 := {
  box := ⟨(91509/2048), (11505/256)⟩
  a := (236947891/1000000000000)
  segments := [
    { box := ⟨(91509/2048), (1399599/31250)⟩, pieceIndex := 42 },
    { box := ⟨(1399599/31250), (11505/256)⟩, pieceIndex := 43 }
  ]
}

def scalarCert665 : MacroScalarCert 56 := {
  box := ⟨(38999/1024), (78411/2048)⟩
  a := (11677601791109548745136801743604201/128000000000000000000000000000000000000)
  segments := [
    { box := ⟨(38999/1024), (38138093/1000000)⟩, pieceIndex := 35 },
    { box := ⟨(38138093/1000000), (78411/2048)⟩, pieceIndex := 36 }
  ]
}

def scalarCert666 : MacroScalarCert 56 := {
  box := ⟨(78057/2048), (39235/1024)⟩
  a := (55446155164050219466204850278369929/512000000000000000000000000000000000000)
  segments := [
    { box := ⟨(78057/2048), (38138093/1000000)⟩, pieceIndex := 35 },
    { box := ⟨(38138093/1000000), (39235/1024)⟩, pieceIndex := 36 }
  ]
}

def scalarCert667 : MacroScalarCert 56 := {
  box := ⟨(78057/2048), (78411/2048)⟩
  a := (55446155164050219466204850278369929/512000000000000000000000000000000000000)
  segments := [
    { box := ⟨(78057/2048), (38138093/1000000)⟩, pieceIndex := 35 },
    { box := ⟨(38138093/1000000), (78411/2048)⟩, pieceIndex := 36 }
  ]
}

def scalarCert668 : MacroScalarCert 56 := {
  box := ⟨(91509/2048), (91981/2048)⟩
  a := (236947891/1000000000000)
  segments := [
    { box := ⟨(91509/2048), (1399599/31250)⟩, pieceIndex := 42 },
    { box := ⟨(1399599/31250), (91981/2048)⟩, pieceIndex := 43 }
  ]
}

def scalarCert669 : MacroScalarCert 56 := {
  box := ⟨(5723/128), (11505/256)⟩
  a := (236947891/1000000000000)
  segments := [
    { box := ⟨(5723/128), (1399599/31250)⟩, pieceIndex := 42 },
    { box := ⟨(1399599/31250), (11505/256)⟩, pieceIndex := 43 }
  ]
}

def scalarCert670 : MacroScalarCert 56 := {
  box := ⟨(5723/128), (46079/1024)⟩
  a := (236947891/1000000000000)
  segments := [
    { box := ⟨(5723/128), (1399599/31250)⟩, pieceIndex := 42 },
    { box := ⟨(1399599/31250), (46079/1024)⟩, pieceIndex := 43 }
  ]
}

def scalarCert671 : MacroScalarCert 56 := {
  box := ⟨(413/16), (6667/256)⟩
  a := (148698801/250000000000)
  segments := [
    { box := ⟨(413/16), (2597847/100000)⟩, pieceIndex := 24 },
    { box := ⟨(2597847/100000), (6667/256)⟩, pieceIndex := 25 }
  ]
}

def scalarCert672 : MacroScalarCert 56 := {
  box := ⟨(413/16), (26727/1024)⟩
  a := (148698801/250000000000)
  segments := [
    { box := ⟨(413/16), (2597847/100000)⟩, pieceIndex := 24 },
    { box := ⟨(2597847/100000), (26727/1024)⟩, pieceIndex := 25 }
  ]
}

def scalarCert673 : MacroScalarCert 56 := {
  box := ⟨(26491/1024), (13393/512)⟩
  a := (148698801/250000000000)
  segments := [
    { box := ⟨(26491/1024), (2597847/100000)⟩, pieceIndex := 24 },
    { box := ⟨(2597847/100000), (13393/512)⟩, pieceIndex := 25 }
  ]
}

def scalarCert674 : MacroScalarCert 56 := {
  box := ⟨(45843/1024), (46315/1024)⟩
  a := (236947891/1000000000000)
  segments := [
    { box := ⟨(45843/1024), (1399599/31250)⟩, pieceIndex := 42 },
    { box := ⟨(1399599/31250), (46315/1024)⟩, pieceIndex := 43 }
  ]
}

def scalarCert675 : MacroScalarCert 56 := {
  box := ⟨(9853/512), (19883/1024)⟩
  a := (308609266148826216472188856757689/1280000000000000000000000000000000000)
  segments := [
    { box := ⟨(9853/512), (19351747/1000000)⟩, pieceIndex := 17 },
    { box := ⟨(19351747/1000000), (19883/1024)⟩, pieceIndex := 18 }
  ]
}

def scalarCert676 : MacroScalarCert 56 := {
  box := ⟨(19765/1024), (9971/512)⟩
  a := (1823736530063038278523442761733881/5120000000000000000000000000000000000)
  segments := [
    { box := ⟨(19765/1024), (19351747/1000000)⟩, pieceIndex := 17 },
    { box := ⟨(19351747/1000000), (9971/512)⟩, pieceIndex := 18 }
  ]
}

def scalarCert677 : MacroScalarCert 56 := {
  box := ⟨(19765/1024), (19883/1024)⟩
  a := (1823736530063038278523442761733881/5120000000000000000000000000000000000)
  segments := [
    { box := ⟨(19765/1024), (19351747/1000000)⟩, pieceIndex := 17 },
    { box := ⟨(19351747/1000000), (19883/1024)⟩, pieceIndex := 18 }
  ]
}

def scalarCert678 : MacroScalarCert 56 := {
  box := ⟨(4897/128), (39471/1024)⟩
  a := (17456552780050285252554156310809/80000000000000000000000000000000000)
  segments := [
    { box := ⟨(4897/128), (38513093/1000000)⟩, pieceIndex := 36 },
    { box := ⟨(38513093/1000000), (39471/1024)⟩, pieceIndex := 37 }
  ]
}

def scalarCert679 : MacroScalarCert 56 := {
  box := ⟨(39235/1024), (39589/1024)⟩
  a := (1369707961552329895632137911532401/5120000000000000000000000000000000000)
  segments := [
    { box := ⟨(39235/1024), (38513093/1000000)⟩, pieceIndex := 36 },
    { box := ⟨(38513093/1000000), (39589/1024)⟩, pieceIndex := 37 }
  ]
}

def scalarCert680 : MacroScalarCert 56 := {
  box := ⟨(5723/128), (91981/2048)⟩
  a := (236947891/1000000000000)
  segments := [
    { box := ⟨(5723/128), (1399599/31250)⟩, pieceIndex := 42 },
    { box := ⟨(1399599/31250), (91981/2048)⟩, pieceIndex := 43 }
  ]
}

def scalarCert681 : MacroScalarCert 56 := {
  box := ⟨(413/16), (26609/1024)⟩
  a := (148698801/250000000000)
  segments := [
    { box := ⟨(413/16), (2597847/100000)⟩, pieceIndex := 24 },
    { box := ⟨(2597847/100000), (26609/1024)⟩, pieceIndex := 25 }
  ]
}

def scalarCert682 : MacroScalarCert 56 := {
  box := ⟨(45843/1024), (2891/64)⟩
  a := (236947891/1000000000000)
  segments := [
    { box := ⟨(45843/1024), (1399599/31250)⟩, pieceIndex := 42 },
    { box := ⟨(1399599/31250), (2891/64)⟩, pieceIndex := 43 }
  ]
}

def scalarCert683 : MacroScalarCert 56 := {
  box := ⟨(26491/1024), (26727/1024)⟩
  a := (148698801/250000000000)
  segments := [
    { box := ⟨(26491/1024), (2597847/100000)⟩, pieceIndex := 24 },
    { box := ⟨(2597847/100000), (26727/1024)⟩, pieceIndex := 25 }
  ]
}

def scalarCert684 : MacroScalarCert 56 := {
  box := ⟨(13275/512), (13393/512)⟩
  a := (148698801/250000000000)
  segments := [
    { box := ⟨(13275/512), (2597847/100000)⟩, pieceIndex := 24 },
    { box := ⟨(2597847/100000), (13393/512)⟩, pieceIndex := 25 }
  ]
}

def scalarCert685 : MacroScalarCert 56 := {
  box := ⟨(104725/4096), (104961/4096)⟩
  a := (1141562903590983285695073331748601/5120000000000000000000000000000000000)
  segments := [
    { box := ⟨(104725/4096), (2560347/100000)⟩, pieceIndex := 23 },
    { box := ⟨(2560347/100000), (104961/4096)⟩, pieceIndex := 24 }
  ]
}

def scalarCert686 : MacroScalarCert 56 := {
  box := ⟨(6549/256), (26255/1024)⟩
  a := (4846047689033107029255715842121/20000000000000000000000000000000000)
  segments := [
    { box := ⟨(6549/256), (2560347/100000)⟩, pieceIndex := 23 },
    { box := ⟨(2560347/100000), (26255/1024)⟩, pieceIndex := 24 }
  ]
}

def scalarCert687 : MacroScalarCert 56 := {
  box := ⟨(77939/2048), (19529/512)⟩
  a := (38723052754148622434167907908744929/512000000000000000000000000000000000000)
  segments := [
    { box := ⟨(77939/2048), (38138093/1000000)⟩, pieceIndex := 35 },
    { box := ⟨(38138093/1000000), (19529/512)⟩, pieceIndex := 36 }
  ]
}

def scalarCert688 : MacroScalarCert 56 := {
  box := ⟨(155937/4096), (19529/512)⟩
  a := (170492723042512408859791057647182841/2048000000000000000000000000000000000000)
  segments := [
    { box := ⟨(155937/4096), (38138093/1000000)⟩, pieceIndex := 35 },
    { box := ⟨(38138093/1000000), (19529/512)⟩, pieceIndex := 36 }
  ]
}

def scalarCert689 : MacroScalarCert 56 := {
  box := ⟨(6549/256), (104961/4096)⟩
  a := (4846047689033107029255715842121/20000000000000000000000000000000000)
  segments := [
    { box := ⟨(6549/256), (2560347/100000)⟩, pieceIndex := 23 },
    { box := ⟨(2560347/100000), (104961/4096)⟩, pieceIndex := 24 }
  ]
}

def scalarCert690 : MacroScalarCert 56 := {
  box := ⟨(104843/4096), (26255/1024)⟩
  a := (1343731745198809347161712573948601/5120000000000000000000000000000000000)
  segments := [
    { box := ⟨(104843/4096), (2560347/100000)⟩, pieceIndex := 23 },
    { box := ⟨(2560347/100000), (26255/1024)⟩, pieceIndex := 24 }
  ]
}

def scalarCert691 : MacroScalarCert 56 := {
  box := ⟨(38999/1024), (19529/512)⟩
  a := (11677601791109548745136801743604201/128000000000000000000000000000000000000)
  segments := [
    { box := ⟨(38999/1024), (38138093/1000000)⟩, pieceIndex := 35 },
    { box := ⟨(38138093/1000000), (19529/512)⟩, pieceIndex := 36 }
  ]
}

def scalarCert692 : MacroScalarCert 56 := {
  box := ⟨(52333/2048), (52451/2048)⟩
  a := (261663957698583251444635700611369/1280000000000000000000000000000000000)
  segments := [
    { box := ⟨(52333/2048), (2560347/100000)⟩, pieceIndex := 23 },
    { box := ⟨(2560347/100000), (52451/2048)⟩, pieceIndex := 24 }
  ]
}

def scalarCert693 : MacroScalarCert 56 := {
  box := ⟨(104843/4096), (105079/4096)⟩
  a := (1343731745198809347161712573948601/5120000000000000000000000000000000000)
  segments := [
    { box := ⟨(104843/4096), (2560347/100000)⟩, pieceIndex := 23 },
    { box := ⟨(2560347/100000), (105079/4096)⟩, pieceIndex := 24 }
  ]
}

def scalarCert694 : MacroScalarCert 56 := {
  box := ⟨(155937/4096), (156291/4096)⟩
  a := (170492723042512408859791057647182841/2048000000000000000000000000000000000000)
  segments := [
    { box := ⟨(155937/4096), (38138093/1000000)⟩, pieceIndex := 35 },
    { box := ⟨(38138093/1000000), (156291/4096)⟩, pieceIndex := 36 }
  ]
}

def scalarCert695 : MacroScalarCert 56 := {
  box := ⟨(38999/1024), (156291/4096)⟩
  a := (11677601791109548745136801743604201/128000000000000000000000000000000000000)
  segments := [
    { box := ⟨(38999/1024), (38138093/1000000)⟩, pieceIndex := 35 },
    { box := ⟨(38138093/1000000), (156291/4096)⟩, pieceIndex := 36 }
  ]
}

def scalarCert696 : MacroScalarCert 56 := {
  box := ⟨(38999/1024), (78175/2048)⟩
  a := (11677601791109548745136801743604201/128000000000000000000000000000000000000)
  segments := [
    { box := ⟨(38999/1024), (38138093/1000000)⟩, pieceIndex := 35 },
    { box := ⟨(38138093/1000000), (78175/2048)⟩, pieceIndex := 36 }
  ]
}

def scalarCert697 : MacroScalarCert 56 := {
  box := ⟨(156055/4096), (78175/2048)⟩
  a := (203938927862315602923864942386432841/2048000000000000000000000000000000000000)
  segments := [
    { box := ⟨(156055/4096), (38138093/1000000)⟩, pieceIndex := 35 },
    { box := ⟨(38138093/1000000), (78175/2048)⟩, pieceIndex := 36 }
  ]
}

def scalarCert698 : MacroScalarCert 56 := {
  box := ⟨(38999/1024), (156409/4096)⟩
  a := (11677601791109548745136801743604201/128000000000000000000000000000000000000)
  segments := [
    { box := ⟨(38999/1024), (38138093/1000000)⟩, pieceIndex := 35 },
    { box := ⟨(38138093/1000000), (156409/4096)⟩, pieceIndex := 36 }
  ]
}

def scalarCert699 : MacroScalarCert 56 := {
  box := ⟨(156055/4096), (39117/1024)⟩
  a := (203938927862315602923864942386432841/2048000000000000000000000000000000000000)
  segments := [
    { box := ⟨(156055/4096), (38138093/1000000)⟩, pieceIndex := 35 },
    { box := ⟨(38138093/1000000), (39117/1024)⟩, pieceIndex := 36 }
  ]
}

def scalarCert700 : MacroScalarCert 56 := {
  box := ⟨(78057/2048), (156527/4096)⟩
  a := (55446155164050219466204850278369929/512000000000000000000000000000000000000)
  segments := [
    { box := ⟨(78057/2048), (38138093/1000000)⟩, pieceIndex := 35 },
    { box := ⟨(38138093/1000000), (156527/4096)⟩, pieceIndex := 36 }
  ]
}

def scalarCert701 : MacroScalarCert 56 := {
  box := ⟨(156173/4096), (78293/2048)⟩
  a := (240378707039408604745052204078807841/2048000000000000000000000000000000000000)
  segments := [
    { box := ⟨(156173/4096), (38138093/1000000)⟩, pieceIndex := 35 },
    { box := ⟨(38138093/1000000), (78293/2048)⟩, pieceIndex := 36 }
  ]
}

def scalarCert702 : MacroScalarCert 56 := {
  box := ⟨(182959/4096), (91745/2048)⟩
  a := (236947891/1000000000000)
  segments := [
    { box := ⟨(182959/4096), (1399599/31250)⟩, pieceIndex := 42 },
    { box := ⟨(1399599/31250), (91745/2048)⟩, pieceIndex := 43 }
  ]
}

def scalarCert703 : MacroScalarCert 56 := {
  box := ⟨(156173/4096), (156527/4096)⟩
  a := (240378707039408604745052204078807841/2048000000000000000000000000000000000000)
  segments := [
    { box := ⟨(156173/4096), (38138093/1000000)⟩, pieceIndex := 35 },
    { box := ⟨(38138093/1000000), (156527/4096)⟩, pieceIndex := 36 }
  ]
}

def scalarCert704 : MacroScalarCert 56 := {
  box := ⟨(91509/2048), (91745/2048)⟩
  a := (236947891/1000000000000)
  segments := [
    { box := ⟨(91509/2048), (1399599/31250)⟩, pieceIndex := 42 },
    { box := ⟨(1399599/31250), (91745/2048)⟩, pieceIndex := 43 }
  ]
}

def scalarCert705 : MacroScalarCert 56 := {
  box := ⟨(156055/4096), (156409/4096)⟩
  a := (203938927862315602923864942386432841/2048000000000000000000000000000000000000)
  segments := [
    { box := ⟨(156055/4096), (38138093/1000000)⟩, pieceIndex := 35 },
    { box := ⟨(38138093/1000000), (156409/4096)⟩, pieceIndex := 36 }
  ]
}

def scalarCert706 : MacroScalarCert 56 := {
  box := ⟨(78057/2048), (39117/1024)⟩
  a := (55446155164050219466204850278369929/512000000000000000000000000000000000000)
  segments := [
    { box := ⟨(78057/2048), (38138093/1000000)⟩, pieceIndex := 35 },
    { box := ⟨(38138093/1000000), (39117/1024)⟩, pieceIndex := 36 }
  ]
}

def scalarCert707 : MacroScalarCert 56 := {
  box := ⟨(78057/2048), (156409/4096)⟩
  a := (55446155164050219466204850278369929/512000000000000000000000000000000000000)
  segments := [
    { box := ⟨(78057/2048), (38138093/1000000)⟩, pieceIndex := 35 },
    { box := ⟨(38138093/1000000), (156409/4096)⟩, pieceIndex := 36 }
  ]
}

def scalarCert708 : MacroScalarCert 56 := {
  box := ⟨(156055/4096), (156291/4096)⟩
  a := (203938927862315602923864942386432841/2048000000000000000000000000000000000000)
  segments := [
    { box := ⟨(156055/4096), (38138093/1000000)⟩, pieceIndex := 35 },
    { box := ⟨(38138093/1000000), (156291/4096)⟩, pieceIndex := 36 }
  ]
}

def scalarCert709 : MacroScalarCert 56 := {
  box := ⟨(78057/2048), (78175/2048)⟩
  a := (55446155164050219466204850278369929/512000000000000000000000000000000000000)
  segments := [
    { box := ⟨(78057/2048), (38138093/1000000)⟩, pieceIndex := 35 },
    { box := ⟨(38138093/1000000), (78175/2048)⟩, pieceIndex := 36 }
  ]
}

def scalarCert710 : MacroScalarCert 56 := {
  box := ⟨(91509/2048), (183549/4096)⟩
  a := (236947891/1000000000000)
  segments := [
    { box := ⟨(91509/2048), (1399599/31250)⟩, pieceIndex := 42 },
    { box := ⟨(1399599/31250), (183549/4096)⟩, pieceIndex := 43 }
  ]
}

def scalarCert711 : MacroScalarCert 56 := {
  box := ⟨(183077/4096), (22951/512)⟩
  a := (236947891/1000000000000)
  segments := [
    { box := ⟨(183077/4096), (1399599/31250)⟩, pieceIndex := 42 },
    { box := ⟨(1399599/31250), (22951/512)⟩, pieceIndex := 43 }
  ]
}

def scalarCert712 : MacroScalarCert 56 := {
  box := ⟨(5723/128), (91863/2048)⟩
  a := (236947891/1000000000000)
  segments := [
    { box := ⟨(5723/128), (1399599/31250)⟩, pieceIndex := 42 },
    { box := ⟨(1399599/31250), (91863/2048)⟩, pieceIndex := 43 }
  ]
}

def scalarCert713 : MacroScalarCert 56 := {
  box := ⟨(5723/128), (45961/1024)⟩
  a := (236947891/1000000000000)
  segments := [
    { box := ⟨(5723/128), (1399599/31250)⟩, pieceIndex := 42 },
    { box := ⟨(1399599/31250), (45961/1024)⟩, pieceIndex := 43 }
  ]
}

def scalarCert714 : MacroScalarCert 56 := {
  box := ⟨(183077/4096), (91745/2048)⟩
  a := (236947891/1000000000000)
  segments := [
    { box := ⟨(183077/4096), (1399599/31250)⟩, pieceIndex := 42 },
    { box := ⟨(1399599/31250), (91745/2048)⟩, pieceIndex := 43 }
  ]
}

def scalarCert715 : MacroScalarCert 56 := {
  box := ⟨(156173/4096), (39117/1024)⟩
  a := (240378707039408604745052204078807841/2048000000000000000000000000000000000000)
  segments := [
    { box := ⟨(156173/4096), (38138093/1000000)⟩, pieceIndex := 35 },
    { box := ⟨(38138093/1000000), (39117/1024)⟩, pieceIndex := 36 }
  ]
}

def scalarCert716 : MacroScalarCert 56 := {
  box := ⟨(183077/4096), (183549/4096)⟩
  a := (236947891/1000000000000)
  segments := [
    { box := ⟨(183077/4096), (1399599/31250)⟩, pieceIndex := 42 },
    { box := ⟨(1399599/31250), (183549/4096)⟩, pieceIndex := 43 }
  ]
}

def scalarCert717 : MacroScalarCert 56 := {
  box := ⟨(5723/128), (22951/512)⟩
  a := (236947891/1000000000000)
  segments := [
    { box := ⟨(5723/128), (1399599/31250)⟩, pieceIndex := 42 },
    { box := ⟨(1399599/31250), (22951/512)⟩, pieceIndex := 43 }
  ]
}

def scalarCert718 : MacroScalarCert 56 := {
  box := ⟨(5723/128), (92099/2048)⟩
  a := (236947891/1000000000000)
  segments := [
    { box := ⟨(5723/128), (1399599/31250)⟩, pieceIndex := 42 },
    { box := ⟨(1399599/31250), (92099/2048)⟩, pieceIndex := 43 }
  ]
}

def scalarCert719 : MacroScalarCert 56 := {
  box := ⟨(91627/2048), (46079/1024)⟩
  a := (236947891/1000000000000)
  segments := [
    { box := ⟨(91627/2048), (1399599/31250)⟩, pieceIndex := 42 },
    { box := ⟨(1399599/31250), (46079/1024)⟩, pieceIndex := 43 }
  ]
}

def scalarCert720 : MacroScalarCert 56 := {
  box := ⟨(5723/128), (183549/4096)⟩
  a := (236947891/1000000000000)
  segments := [
    { box := ⟨(5723/128), (1399599/31250)⟩, pieceIndex := 42 },
    { box := ⟨(1399599/31250), (183549/4096)⟩, pieceIndex := 43 }
  ]
}

def scalarCert721 : MacroScalarCert 56 := {
  box := ⟨(104725/4096), (52451/2048)⟩
  a := (1141562903590983285695073331748601/5120000000000000000000000000000000000)
  segments := [
    { box := ⟨(104725/4096), (2560347/100000)⟩, pieceIndex := 23 },
    { box := ⟨(2560347/100000), (52451/2048)⟩, pieceIndex := 24 }
  ]
}

def scalarCert722 : MacroScalarCert 56 := {
  box := ⟨(91627/2048), (92099/2048)⟩
  a := (236947891/1000000000000)
  segments := [
    { box := ⟨(91627/2048), (1399599/31250)⟩, pieceIndex := 42 },
    { box := ⟨(1399599/31250), (92099/2048)⟩, pieceIndex := 43 }
  ]
}

def scalarCert723 : MacroScalarCert 56 := {
  box := ⟨(91627/2048), (11505/256)⟩
  a := (236947891/1000000000000)
  segments := [
    { box := ⟨(91627/2048), (1399599/31250)⟩, pieceIndex := 42 },
    { box := ⟨(1399599/31250), (11505/256)⟩, pieceIndex := 43 }
  ]
}

def scalarCert724 : MacroScalarCert 56 := {
  box := ⟨(45843/1024), (92099/2048)⟩
  a := (236947891/1000000000000)
  segments := [
    { box := ⟨(45843/1024), (1399599/31250)⟩, pieceIndex := 42 },
    { box := ⟨(1399599/31250), (92099/2048)⟩, pieceIndex := 43 }
  ]
}

def scalarCert725 : MacroScalarCert 56 := {
  box := ⟨(45843/1024), (23069/512)⟩
  a := (236947891/1000000000000)
  segments := [
    { box := ⟨(45843/1024), (1399599/31250)⟩, pieceIndex := 42 },
    { box := ⟨(1399599/31250), (23069/512)⟩, pieceIndex := 43 }
  ]
}

def scalarCert726 : MacroScalarCert 56 := {
  box := ⟨(45843/1024), (46197/1024)⟩
  a := (236947891/1000000000000)
  segments := [
    { box := ⟨(45843/1024), (1399599/31250)⟩, pieceIndex := 42 },
    { box := ⟨(1399599/31250), (46197/1024)⟩, pieceIndex := 43 }
  ]
}

def scalarCert727 : MacroScalarCert 56 := {
  box := ⟨(32509/1024), (16343/512)⟩
  a := (26038539485972255876043813792489/320000000000000000000000000000000000)
  segments := [
    { box := ⟨(32509/1024), (6373527/200000)⟩, pieceIndex := 29 },
    { box := ⟨(6373527/200000), (16343/512)⟩, pieceIndex := 30 }
  ]
}

def scalarCert728 : MacroScalarCert 56 := {
  box := ⟨(39235/1024), (19765/512)⟩
  a := (1369707961552329895632137911532401/5120000000000000000000000000000000000)
  segments := [
    { box := ⟨(39235/1024), (38513093/1000000)⟩, pieceIndex := 36 },
    { box := ⟨(38513093/1000000), (19765/512)⟩, pieceIndex := 37 }
  ]
}

def scalarCert729 : MacroScalarCert 56 := {
  box := ⟨(32509/1024), (32745/1024)⟩
  a := (26038539485972255876043813792489/320000000000000000000000000000000000)
  segments := [
    { box := ⟨(32509/1024), (6373527/200000)⟩, pieceIndex := 29 },
    { box := ⟨(6373527/200000), (32745/1024)⟩, pieceIndex := 30 }
  ]
}

def scalarCert730 : MacroScalarCert 56 := {
  box := ⟨(19647/512), (1239/32)⟩
  a := (76986939/250000000000)
  segments := [
    { box := ⟨(19647/512), (38513093/1000000)⟩, pieceIndex := 36 },
    { box := ⟨(38513093/1000000), (1239/32)⟩, pieceIndex := 37 }
  ]
}

def scalarCert731 : MacroScalarCert 56 := {
  box := ⟨(4071/128), (8201/256)⟩
  a := (611979482867143614802669851201/5000000000000000000000000000000000)
  segments := [
    { box := ⟨(4071/128), (6373527/200000)⟩, pieceIndex := 29 },
    { box := ⟨(6373527/200000), (8201/256)⟩, pieceIndex := 30 }
  ]
}

def scalarCert732 : MacroScalarCert 56 := {
  box := ⟨(39235/1024), (39471/1024)⟩
  a := (1369707961552329895632137911532401/5120000000000000000000000000000000000)
  segments := [
    { box := ⟨(39235/1024), (38513093/1000000)⟩, pieceIndex := 36 },
    { box := ⟨(38513093/1000000), (39471/1024)⟩, pieceIndex := 37 }
  ]
}

def scalarCert733 : MacroScalarCert 56 := {
  box := ⟨(4071/128), (32745/1024)⟩
  a := (611979482867143614802669851201/5000000000000000000000000000000000)
  segments := [
    { box := ⟨(4071/128), (6373527/200000)⟩, pieceIndex := 29 },
    { box := ⟨(6373527/200000), (32745/1024)⟩, pieceIndex := 30 }
  ]
}

def scalarCert734 : MacroScalarCert 56 := {
  box := ⟨(45135/1024), (11387/256)⟩
  a := (8326505390882798349213653439169/8000000000000000000000000000000000000)
  segments := [
    { box := ⟨(45135/1024), (5551521/125000)⟩, pieceIndex := 41 },
    { box := ⟨(5551521/125000), (11387/256)⟩, pieceIndex := 42 }
  ]
}

def scalarCert735 : MacroScalarCert 56 := {
  box := ⟨(25901/512), (52333/1024)⟩
  a := (3016845497858850148660534470361/80000000000000000000000000000000000)
  segments := [
    { box := ⟨(25901/512), (50688511/1000000)⟩, pieceIndex := 47 },
    { box := ⟨(50688511/1000000), (51063511/1000000)⟩, pieceIndex := 48 },
    { box := ⟨(51063511/1000000), (52333/1024)⟩, pieceIndex := 49 }
  ]
}

def scalarCert736 : MacroScalarCert 56 := {
  box := ⟨(51861/1024), (6549/128)⟩
  a := (17667571024850201693389455584569/320000000000000000000000000000000000)
  segments := [
    { box := ⟨(51861/1024), (50688511/1000000)⟩, pieceIndex := 47 },
    { box := ⟨(50688511/1000000), (51063511/1000000)⟩, pieceIndex := 48 },
    { box := ⟨(51063511/1000000), (6549/128)⟩, pieceIndex := 49 }
  ]
}

def scalarCert737 : MacroScalarCert 56 := {
  box := ⟨(3245/64), (52451/1024)⟩
  a := (9965930645410815779513042967721/125000000000000000000000000000000000)
  segments := [
    { box := ⟨(3245/64), (51063511/1000000)⟩, pieceIndex := 48 },
    { box := ⟨(51063511/1000000), (52451/1024)⟩, pieceIndex := 49 }
  ]
}

def scalarCert738 : MacroScalarCert 56 := {
  box := ⟨(51979/1024), (26255/512)⟩
  a := (13135780216075039115731298598211929/128000000000000000000000000000000000000)
  segments := [
    { box := ⟨(51979/1024), (51063511/1000000)⟩, pieceIndex := 48 },
    { box := ⟨(51063511/1000000), (26255/512)⟩, pieceIndex := 49 }
  ]
}

def scalarCert739 : MacroScalarCert 56 := {
  box := ⟨(26019/512), (13157/256)⟩
  a := (4108970484551816539322694210502201/32000000000000000000000000000000000000)
  segments := [
    { box := ⟨(26019/512), (51063511/1000000)⟩, pieceIndex := 48 },
    { box := ⟨(51063511/1000000), (13157/256)⟩, pieceIndex := 49 }
  ]
}

def scalarCert740 : MacroScalarCert 56 := {
  box := ⟨(51625/1024), (52097/1024)⟩
  a := (1652284170473624845145301959569/320000000000000000000000000000000000)
  segments := [
    { box := ⟨(51625/1024), (50688511/1000000)⟩, pieceIndex := 47 },
    { box := ⟨(50688511/1000000), (52097/1024)⟩, pieceIndex := 48 }
  ]
}

def scalarCert741 : MacroScalarCert 56 := {
  box := ⟨(12921/256), (13039/256)⟩
  a := (253733660265444510657503816809/20000000000000000000000000000000000)
  segments := [
    { box := ⟨(12921/256), (50688511/1000000)⟩, pieceIndex := 47 },
    { box := ⟨(50688511/1000000), (13039/256)⟩, pieceIndex := 48 }
  ]
}

def scalarCert742 : MacroScalarCert 56 := {
  box := ⟨(51743/1024), (52215/1024)⟩
  a := (7531437837901037420352339709569/320000000000000000000000000000000000)
  segments := [
    { box := ⟨(51743/1024), (50688511/1000000)⟩, pieceIndex := 47 },
    { box := ⟨(50688511/1000000), (52215/1024)⟩, pieceIndex := 48 }
  ]
}

def scalarCert743 : MacroScalarCert 56 := {
  box := ⟨(25901/512), (26137/512)⟩
  a := (3016845497858850148660534470361/80000000000000000000000000000000000)
  segments := [
    { box := ⟨(25901/512), (50688511/1000000)⟩, pieceIndex := 47 },
    { box := ⟨(50688511/1000000), (26137/512)⟩, pieceIndex := 48 }
  ]
}

def scalarCert744 : MacroScalarCert 56 := {
  box := ⟨(45135/1024), (45489/1024)⟩
  a := (8326505390882798349213653439169/8000000000000000000000000000000000000)
  segments := [
    { box := ⟨(45135/1024), (5551521/125000)⟩, pieceIndex := 41 },
    { box := ⟨(5551521/125000), (45489/1024)⟩, pieceIndex := 42 }
  ]
}

def scalarCert745 : MacroScalarCert 56 := {
  box := ⟨(22597/512), (11387/256)⟩
  a := (12404326906898653543170837152761/2000000000000000000000000000000000000)
  segments := [
    { box := ⟨(22597/512), (5551521/125000)⟩, pieceIndex := 41 },
    { box := ⟨(5551521/125000), (11387/256)⟩, pieceIndex := 42 }
  ]
}

def scalarCert746 : MacroScalarCert 56 := {
  box := ⟨(51743/1024), (13039/256)⟩
  a := (7531437837901037420352339709569/320000000000000000000000000000000000)
  segments := [
    { box := ⟨(51743/1024), (50688511/1000000)⟩, pieceIndex := 47 },
    { box := ⟨(50688511/1000000), (13039/256)⟩, pieceIndex := 48 }
  ]
}

def scalarCert747 : MacroScalarCert 56 := {
  box := ⟨(25901/512), (52215/1024)⟩
  a := (3016845497858850148660534470361/80000000000000000000000000000000000)
  segments := [
    { box := ⟨(25901/512), (50688511/1000000)⟩, pieceIndex := 47 },
    { box := ⟨(50688511/1000000), (52215/1024)⟩, pieceIndex := 48 }
  ]
}

def scalarCert748 : MacroScalarCert 56 := {
  box := ⟨(22597/512), (45489/1024)⟩
  a := (12404326906898653543170837152761/2000000000000000000000000000000000000)
  segments := [
    { box := ⟨(22597/512), (5551521/125000)⟩, pieceIndex := 41 },
    { box := ⟨(5551521/125000), (45489/1024)⟩, pieceIndex := 42 }
  ]
}

def scalarCert749 : MacroScalarCert 56 := {
  box := ⟨(51861/1024), (26137/512)⟩
  a := (17667571024850201693389455584569/320000000000000000000000000000000000)
  segments := [
    { box := ⟨(51861/1024), (50688511/1000000)⟩, pieceIndex := 47 },
    { box := ⟨(50688511/1000000), (26137/512)⟩, pieceIndex := 48 }
  ]
}

def scalarCert750 : MacroScalarCert 56 := {
  box := ⟨(45253/1024), (11387/256)⟩
  a := (125492473536974126032423063314169/8000000000000000000000000000000000000)
  segments := [
    { box := ⟨(45253/1024), (5551521/125000)⟩, pieceIndex := 41 },
    { box := ⟨(5551521/125000), (11387/256)⟩, pieceIndex := 42 }
  ]
}

def scalarCert751 : MacroScalarCert 56 := {
  box := ⟨(51861/1024), (52333/1024)⟩
  a := (17667571024850201693389455584569/320000000000000000000000000000000000)
  segments := [
    { box := ⟨(51861/1024), (50688511/1000000)⟩, pieceIndex := 47 },
    { box := ⟨(50688511/1000000), (51063511/1000000)⟩, pieceIndex := 48 },
    { box := ⟨(51063511/1000000), (52333/1024)⟩, pieceIndex := 49 }
  ]
}

def scalarCert752 : MacroScalarCert 56 := {
  box := ⟨(3245/64), (6549/128)⟩
  a := (9965930645410815779513042967721/125000000000000000000000000000000000)
  segments := [
    { box := ⟨(3245/64), (51063511/1000000)⟩, pieceIndex := 48 },
    { box := ⟨(51063511/1000000), (6549/128)⟩, pieceIndex := 49 }
  ]
}

def scalarCert753 : MacroScalarCert 56 := {
  box := ⟨(26019/512), (26373/512)⟩
  a := (4108970484551816539322694210502201/32000000000000000000000000000000000000)
  segments := [
    { box := ⟨(26019/512), (51063511/1000000)⟩, pieceIndex := 48 },
    { box := ⟨(51063511/1000000), (26373/512)⟩, pieceIndex := 49 }
  ]
}

def scalarCert754 : MacroScalarCert 56 := {
  box := ⟨(26019/512), (52569/1024)⟩
  a := (4108970484551816539322694210502201/32000000000000000000000000000000000000)
  segments := [
    { box := ⟨(26019/512), (51063511/1000000)⟩, pieceIndex := 48 },
    { box := ⟨(51063511/1000000), (52569/1024)⟩, pieceIndex := 49 }
  ]
}

def scalarCert755 : MacroScalarCert 56 := {
  box := ⟨(52097/1024), (13157/256)⟩
  a := (20105418147297356482899790730336929/128000000000000000000000000000000000000)
  segments := [
    { box := ⟨(52097/1024), (51063511/1000000)⟩, pieceIndex := 48 },
    { box := ⟨(51063511/1000000), (13157/256)⟩, pieceIndex := 49 }
  ]
}

def scalarCert756 : MacroScalarCert 56 := {
  box := ⟨(13039/256), (26373/512)⟩
  a := (587393/3125000000)
  segments := [
    { box := ⟨(13039/256), (51063511/1000000)⟩, pieceIndex := 48 },
    { box := ⟨(51063511/1000000), (26373/512)⟩, pieceIndex := 49 }
  ]
}

def scalarCert757 : MacroScalarCert 56 := {
  box := ⟨(13039/256), (413/8)⟩
  a := (587393/3125000000)
  segments := [
    { box := ⟨(13039/256), (51063511/1000000)⟩, pieceIndex := 48 },
    { box := ⟨(51063511/1000000), (413/8)⟩, pieceIndex := 49 }
  ]
}

def scalarCert758 : MacroScalarCert 56 := {
  box := ⟨(13039/256), (13275/256)⟩
  a := (587393/3125000000)
  segments := [
    { box := ⟨(13039/256), (51063511/1000000)⟩, pieceIndex := 48 },
    { box := ⟨(51063511/1000000), (13275/256)⟩, pieceIndex := 49 }
  ]
}

def scalarCert759 : MacroScalarCert 56 := {
  box := ⟨(13039/256), (26491/512)⟩
  a := (587393/3125000000)
  segments := [
    { box := ⟨(13039/256), (51063511/1000000)⟩, pieceIndex := 48 },
    { box := ⟨(51063511/1000000), (26491/512)⟩, pieceIndex := 49 }
  ]
}

def scalarCert760 : MacroScalarCert 56 := {
  box := ⟨(13039/256), (26609/512)⟩
  a := (587393/3125000000)
  segments := [
    { box := ⟨(13039/256), (51063511/1000000)⟩, pieceIndex := 48 },
    { box := ⟨(51063511/1000000), (26609/512)⟩, pieceIndex := 49 }
  ]
}

def scalarCert761 : MacroScalarCert 56 := {
  box := ⟨(26137/512), (6667/128)⟩
  a := (587393/3125000000)
  segments := [
    { box := ⟨(26137/512), (51063511/1000000)⟩, pieceIndex := 48 },
    { box := ⟨(51063511/1000000), (6667/128)⟩, pieceIndex := 49 }
  ]
}

def scalarCert762 : MacroScalarCert 56 := {
  box := ⟨(26137/512), (13275/256)⟩
  a := (587393/3125000000)
  segments := [
    { box := ⟨(26137/512), (51063511/1000000)⟩, pieceIndex := 48 },
    { box := ⟨(51063511/1000000), (13275/256)⟩, pieceIndex := 49 }
  ]
}

def scalarCert763 : MacroScalarCert 56 := {
  box := ⟨(7257/128), (62500000/1094977)⟩
  a := (1341291391080906536525222929/312500000000000000000000000000000)
  segments := [
    { box := ⟨(7257/128), (5696637/100000)⟩, pieceIndex := 53 },
    { box := ⟨(5696637/100000), (62500000/1094977)⟩, pieceIndex := 54 }
  ]
}

def scalarCert764 : MacroScalarCert 56 := {
  box := ⟨(19411/512), (39353/1024)⟩
  a := (625761533908596174465411009662769/32000000000000000000000000000000000000)
  segments := [
    { box := ⟨(19411/512), (38138093/1000000)⟩, pieceIndex := 35 },
    { box := ⟨(38138093/1000000), (39353/1024)⟩, pieceIndex := 36 }
  ]
}

def scalarCert765 : MacroScalarCert 56 := {
  box := ⟨(38881/1024), (9853/256)⟩
  a := (4812837764803654107675019035354201/128000000000000000000000000000000000000)
  segments := [
    { box := ⟨(38881/1024), (38138093/1000000)⟩, pieceIndex := 35 },
    { box := ⟨(38138093/1000000), (9853/256)⟩, pieceIndex := 36 }
  ]
}

def scalarCert766 : MacroScalarCert 56 := {
  box := ⟨(9499/512), (19175/1024)⟩
  a := (30605320513697079304403802721444329/128000000000000000000000000000000000000)
  segments := [
    { box := ⟨(9499/512), (9300873/500000)⟩, pieceIndex := 14 },
    { box := ⟨(9300873/500000), (19175/1024)⟩, pieceIndex := 15 }
  ]
}

def scalarCert767 : MacroScalarCert 56 := {
  box := ⟨(32627/1024), (32863/1024)⟩
  a := (54965343560194319646569821692489/320000000000000000000000000000000000)
  segments := [
    { box := ⟨(32627/1024), (6373527/200000)⟩, pieceIndex := 29 },
    { box := ⟨(6373527/200000), (32863/1024)⟩, pieceIndex := 30 }
  ]
}

def scalarCert768 : MacroScalarCert 56 := {
  box := ⟨(39353/1024), (39707/1024)⟩
  a := (76986939/250000000000)
  segments := [
    { box := ⟨(39353/1024), (38513093/1000000)⟩, pieceIndex := 36 },
    { box := ⟨(38513093/1000000), (39707/1024)⟩, pieceIndex := 37 }
  ]
}

def scalarCert769 : MacroScalarCert 56 := {
  box := ⟨(9853/256), (19883/512)⟩
  a := (76986939/250000000000)
  segments := [
    { box := ⟨(9853/256), (38513093/1000000)⟩, pieceIndex := 36 },
    { box := ⟨(38513093/1000000), (19883/512)⟩, pieceIndex := 37 }
  ]
}

def scalarCert770 : MacroScalarCert 56 := {
  box := ⟨(16461/512), (8319/256)⟩
  a := (104124691/250000000000)
  segments := [
    { box := ⟨(16461/512), (6448527/200000)⟩, pieceIndex := 30 },
    { box := ⟨(6448527/200000), (8319/256)⟩, pieceIndex := 31 }
  ]
}

def scalarCert771 : MacroScalarCert 56 := {
  box := ⟨(19647/512), (39589/1024)⟩
  a := (76986939/250000000000)
  segments := [
    { box := ⟨(19647/512), (38513093/1000000)⟩, pieceIndex := 36 },
    { box := ⟨(38513093/1000000), (39589/1024)⟩, pieceIndex := 37 }
  ]
}

def scalarCert772 : MacroScalarCert 56 := {
  box := ⟨(32627/1024), (65667/2048)⟩
  a := (54965343560194319646569821692489/320000000000000000000000000000000000)
  segments := [
    { box := ⟨(32627/1024), (6373527/200000)⟩, pieceIndex := 29 },
    { box := ⟨(6373527/200000), (65667/2048)⟩, pieceIndex := 30 }
  ]
}

def scalarCert773 : MacroScalarCert 56 := {
  box := ⟨(19647/512), (79119/2048)⟩
  a := (76986939/250000000000)
  segments := [
    { box := ⟨(19647/512), (38513093/1000000)⟩, pieceIndex := 36 },
    { box := ⟨(38513093/1000000), (79119/2048)⟩, pieceIndex := 37 }
  ]
}

def scalarCert774 : MacroScalarCert 56 := {
  box := ⟨(78647/2048), (39589/1024)⟩
  a := (76986939/250000000000)
  segments := [
    { box := ⟨(78647/2048), (38513093/1000000)⟩, pieceIndex := 36 },
    { box := ⟨(38513093/1000000), (39589/1024)⟩, pieceIndex := 37 }
  ]
}

def scalarCert775 : MacroScalarCert 56 := {
  box := ⟨(9853/256), (39707/1024)⟩
  a := (76986939/250000000000)
  segments := [
    { box := ⟨(9853/256), (38513093/1000000)⟩, pieceIndex := 36 },
    { box := ⟨(38513093/1000000), (39707/1024)⟩, pieceIndex := 37 }
  ]
}

def scalarCert776 : MacroScalarCert 56 := {
  box := ⟨(1711/128), (3481/256)⟩
  a := (1610977803/1000000000000)
  segments := [
    { box := ⟨(1711/128), (13505291/1000000)⟩, pieceIndex := 12 },
    { box := ⟨(13505291/1000000), (3481/256)⟩, pieceIndex := 13 }
  ]
}

def scalarCert777 : MacroScalarCert 56 := {
  box := ⟨(39353/1024), (1239/32)⟩
  a := (76986939/250000000000)
  segments := [
    { box := ⟨(39353/1024), (38513093/1000000)⟩, pieceIndex := 36 },
    { box := ⟨(38513093/1000000), (1239/32)⟩, pieceIndex := 37 }
  ]
}

def scalarCert778 : MacroScalarCert 56 := {
  box := ⟨(65667/2048), (2065/64)⟩
  a := (521331652913686265731490975482681/1280000000000000000000000000000000000)
  segments := [
    { box := ⟨(65667/2048), (6448527/200000)⟩, pieceIndex := 30 },
    { box := ⟨(6448527/200000), (2065/64)⟩, pieceIndex := 31 }
  ]
}

def scalarCert779 : MacroScalarCert 56 := {
  box := ⟨(26727/2048), (3363/256)⟩
  a := (80864734612032863947739505791316289/128000000000000000000000000000000000000)
  segments := [
    { box := ⟨(26727/2048), (13130291/1000000)⟩, pieceIndex := 11 },
    { box := ⟨(13130291/1000000), (3363/256)⟩, pieceIndex := 12 }
  ]
}

def scalarCert780 : MacroScalarCert 56 := {
  box := ⟨(32863/1024), (2065/64)⟩
  a := (104124691/250000000000)
  segments := [
    { box := ⟨(32863/1024), (6448527/200000)⟩, pieceIndex := 30 },
    { box := ⟨(6448527/200000), (2065/64)⟩, pieceIndex := 31 }
  ]
}

def scalarCert781 : MacroScalarCert 56 := {
  box := ⟨(16461/512), (16579/512)⟩
  a := (104124691/250000000000)
  segments := [
    { box := ⟨(16461/512), (6448527/200000)⟩, pieceIndex := 30 },
    { box := ⟨(6448527/200000), (16579/512)⟩, pieceIndex := 31 }
  ]
}

def scalarCert782 : MacroScalarCert 56 := {
  box := ⟨(16461/512), (33217/1024)⟩
  a := (104124691/250000000000)
  segments := [
    { box := ⟨(16461/512), (6448527/200000)⟩, pieceIndex := 30 },
    { box := ⟨(6448527/200000), (33217/1024)⟩, pieceIndex := 31 }
  ]
}

def scalarCert783 : MacroScalarCert 56 := {
  box := ⟨(32981/1024), (33217/1024)⟩
  a := (104124691/250000000000)
  segments := [
    { box := ⟨(32981/1024), (6448527/200000)⟩, pieceIndex := 30 },
    { box := ⟨(6448527/200000), (33217/1024)⟩, pieceIndex := 31 }
  ]
}

def scalarCert784 : MacroScalarCert 56 := {
  box := ⟨(32981/1024), (8319/256)⟩
  a := (104124691/250000000000)
  segments := [
    { box := ⟨(32981/1024), (6448527/200000)⟩, pieceIndex := 30 },
    { box := ⟨(6448527/200000), (8319/256)⟩, pieceIndex := 31 }
  ]
}

def scalarCert785 : MacroScalarCert 56 := {
  box := ⟨(32981/1024), (33335/1024)⟩
  a := (104124691/250000000000)
  segments := [
    { box := ⟨(32981/1024), (6448527/200000)⟩, pieceIndex := 30 },
    { box := ⟨(6448527/200000), (33335/1024)⟩, pieceIndex := 31 }
  ]
}

def scalarCert786 : MacroScalarCert 56 := {
  box := ⟨(51979/1024), (52451/1024)⟩
  a := (13135780216075039115731298598211929/128000000000000000000000000000000000000)
  segments := [
    { box := ⟨(51979/1024), (51063511/1000000)⟩, pieceIndex := 48 },
    { box := ⟨(51063511/1000000), (52451/1024)⟩, pieceIndex := 49 }
  ]
}

def scalarCert787 : MacroScalarCert 56 := {
  box := ⟨(26019/512), (26255/512)⟩
  a := (4108970484551816539322694210502201/32000000000000000000000000000000000000)
  segments := [
    { box := ⟨(26019/512), (51063511/1000000)⟩, pieceIndex := 48 },
    { box := ⟨(51063511/1000000), (26255/512)⟩, pieceIndex := 49 }
  ]
}

def scalarCert788 : MacroScalarCert 56 := {
  box := ⟨(3245/64), (3481/64)⟩
  a := (9965930645410815779513042967721/125000000000000000000000000000000000)
  segments := [
    { box := ⟨(3245/64), (51063511/1000000)⟩, pieceIndex := 48 },
    { box := ⟨(51063511/1000000), (3481/64)⟩, pieceIndex := 49 }
  ]
}

def scalarCert789 : MacroScalarCert 56 := {
  box := ⟨(12685/512), (25547/1024)⟩
  a := (83827002079925057429895526208721/500000000000000000000000000000000000)
  segments := [
    { box := ⟨(12685/512), (24853469/1000000)⟩, pieceIndex := 20 },
    { box := ⟨(24853469/1000000), (25547/1024)⟩, pieceIndex := 21 }
  ]
}

def scalarCert790 : MacroScalarCert 56 := {
  box := ⟨(25429/1024), (12803/512)⟩
  a := (13224910662800597294854280157649/125000000000000000000000000000000000)
  segments := [
    { box := ⟨(25429/1024), (24853469/1000000)⟩, pieceIndex := 20 },
    { box := ⟨(24853469/1000000), (12803/512)⟩, pieceIndex := 21 }
  ]
}

def scalarCert791 : MacroScalarCert 56 := {
  box := ⟨(3127/128), (12685/512)⟩
  a := (3618639448549524540551593999563489/8000000000000000000000000000000000000)
  segments := [
    { box := ⟨(3127/128), (24478469/1000000)⟩, pieceIndex := 19 },
    { box := ⟨(24478469/1000000), (12685/512)⟩, pieceIndex := 20 }
  ]
}

def scalarCert792 : MacroScalarCert 56 := {
  box := ⟨(12567/512), (1593/64)⟩
  a := (1859160367141373243742933961/7629394531250000000000000000000)
  segments := [
    { box := ⟨(12567/512), (24853469/1000000)⟩, pieceIndex := 20 },
    { box := ⟨(24853469/1000000), (1593/64)⟩, pieceIndex := 21 }
  ]
}

def scalarCert793 : MacroScalarCert 56 := {
  box := ⟨(25311/1024), (1593/64)⟩
  a := (1859160367141373243742933961/7629394531250000000000000000000)
  segments := [
    { box := ⟨(25311/1024), (24853469/1000000)⟩, pieceIndex := 20 },
    { box := ⟨(24853469/1000000), (1593/64)⟩, pieceIndex := 21 }
  ]
}

def scalarCert794 : MacroScalarCert 56 := {
  box := ⟨(12685/512), (1593/64)⟩
  a := (1859160367141373243742933961/7629394531250000000000000000000)
  segments := [
    { box := ⟨(12685/512), (24853469/1000000)⟩, pieceIndex := 20 },
    { box := ⟨(24853469/1000000), (1593/64)⟩, pieceIndex := 21 }
  ]
}

def scalarCert795 : MacroScalarCert 56 := {
  box := ⟨(25429/1024), (25547/1024)⟩
  a := (83827002079925057429895526208721/500000000000000000000000000000000000)
  segments := [
    { box := ⟨(25429/1024), (24853469/1000000)⟩, pieceIndex := 20 },
    { box := ⟨(24853469/1000000), (25547/1024)⟩, pieceIndex := 21 }
  ]
}

def scalarCert796 : MacroScalarCert 56 := {
  box := ⟨(32627/1024), (8201/256)⟩
  a := (54965343560194319646569821692489/320000000000000000000000000000000000)
  segments := [
    { box := ⟨(32627/1024), (6373527/200000)⟩, pieceIndex := 29 },
    { box := ⟨(6373527/200000), (8201/256)⟩, pieceIndex := 30 }
  ]
}

def scalarCert797 : MacroScalarCert 56 := {
  box := ⟨(9499/256), (19293/512)⟩
  a := (201784954112817680932822514341729/32000000000000000000000000000000000000)
  segments := [
    { box := ⟨(9499/256), (9347023/250000)⟩, pieceIndex := 32 },
    { box := ⟨(9347023/250000), (19293/512)⟩, pieceIndex := 33 }
  ]
}

def scalarCert798 : MacroScalarCert 56 := {
  box := ⟨(19057/512), (19293/512)⟩
  a := (201784954112817680932822514341729/32000000000000000000000000000000000000)
  segments := [
    { box := ⟨(19057/512), (9347023/250000)⟩, pieceIndex := 32 },
    { box := ⟨(9347023/250000), (19293/512)⟩, pieceIndex := 33 }
  ]
}

def scalarCert799 : MacroScalarCert 56 := {
  box := ⟨(295/8), (9617/256)⟩
  a := (294155184355193927474896755253401/8000000000000000000000000000000000000)
  segments := [
    { box := ⟨(295/8), (9253273/250000)⟩, pieceIndex := 31 },
    { box := ⟨(9253273/250000), (9347023/250000)⟩, pieceIndex := 32 },
    { box := ⟨(9347023/250000), (9617/256)⟩, pieceIndex := 33 }
  ]
}

def scalarCert800 : MacroScalarCert 56 := {
  box := ⟨(4779/128), (19293/512)⟩
  a := (201784954112817680932822514341729/32000000000000000000000000000000000000)
  segments := [
    { box := ⟨(4779/128), (9347023/250000)⟩, pieceIndex := 32 },
    { box := ⟨(9347023/250000), (19293/512)⟩, pieceIndex := 33 }
  ]
}

def scalarCert801 : MacroScalarCert 56 := {
  box := ⟨(26137/512), (26609/512)⟩
  a := (587393/3125000000)
  segments := [
    { box := ⟨(26137/512), (51063511/1000000)⟩, pieceIndex := 48 },
    { box := ⟨(51063511/1000000), (26609/512)⟩, pieceIndex := 49 }
  ]
}

def scalarCert802 : MacroScalarCert 56 := {
  box := ⟨(3245/64), (7021/128)⟩
  a := (9965930645410815779513042967721/125000000000000000000000000000000000)
  segments := [
    { box := ⟨(3245/64), (51063511/1000000)⟩, pieceIndex := 48 },
    { box := ⟨(51063511/1000000), (7021/128)⟩, pieceIndex := 49 }
  ]
}

def scalarCert803 : MacroScalarCert 56 := {
  box := ⟨(413/8), (3599/64)⟩
  a := (6679430045452291605179741688609/125000000000000000000000000000000000)
  segments := [
    { box := ⟨(413/8), (55841369/1000000)⟩, pieceIndex := 49 },
    { box := ⟨(55841369/1000000), (56216369/1000000)⟩, pieceIndex := 50 },
    { box := ⟨(56216369/1000000), (3599/64)⟩, pieceIndex := 51 }
  ]
}

def scalarCert804 : MacroScalarCert 56 := {
  box := ⟨(26019/512), (52451/1024)⟩
  a := (4108970484551816539322694210502201/32000000000000000000000000000000000000)
  segments := [
    { box := ⟨(26019/512), (51063511/1000000)⟩, pieceIndex := 48 },
    { box := ⟨(51063511/1000000), (52451/1024)⟩, pieceIndex := 49 }
  ]
}

def scalarCert805 : MacroScalarCert 56 := {
  box := ⟨(52097/1024), (26255/512)⟩
  a := (20105418147297356482899790730336929/128000000000000000000000000000000000000)
  segments := [
    { box := ⟨(52097/1024), (51063511/1000000)⟩, pieceIndex := 48 },
    { box := ⟨(51063511/1000000), (26255/512)⟩, pieceIndex := 49 }
  ]
}

def scalarCert806 : MacroScalarCert 56 := {
  box := ⟨(25783/512), (26019/512)⟩
  a := (77268664145143861057015595361/80000000000000000000000000000000000)
  segments := [
    { box := ⟨(25783/512), (50688511/1000000)⟩, pieceIndex := 47 },
    { box := ⟨(50688511/1000000), (26019/512)⟩, pieceIndex := 48 }
  ]
}

def scalarCert807 : MacroScalarCert 56 := {
  box := ⟨(52097/1024), (52569/1024)⟩
  a := (20105418147297356482899790730336929/128000000000000000000000000000000000000)
  segments := [
    { box := ⟨(52097/1024), (51063511/1000000)⟩, pieceIndex := 48 },
    { box := ⟨(51063511/1000000), (52569/1024)⟩, pieceIndex := 49 }
  ]
}

def scalarCert808 : MacroScalarCert 56 := {
  box := ⟨(13039/256), (13157/256)⟩
  a := (587393/3125000000)
  segments := [
    { box := ⟨(13039/256), (51063511/1000000)⟩, pieceIndex := 48 },
    { box := ⟨(51063511/1000000), (13157/256)⟩, pieceIndex := 49 }
  ]
}

def scalarCert809 : MacroScalarCert 56 := {
  box := ⟨(13039/256), (52687/1024)⟩
  a := (587393/3125000000)
  segments := [
    { box := ⟨(13039/256), (51063511/1000000)⟩, pieceIndex := 48 },
    { box := ⟨(51063511/1000000), (52687/1024)⟩, pieceIndex := 49 }
  ]
}

def scalarCert810 : MacroScalarCert 56 := {
  box := ⟨(52215/1024), (26373/512)⟩
  a := (587393/3125000000)
  segments := [
    { box := ⟨(52215/1024), (51063511/1000000)⟩, pieceIndex := 48 },
    { box := ⟨(51063511/1000000), (26373/512)⟩, pieceIndex := 49 }
  ]
}

def scalarCert811 : MacroScalarCert 56 := {
  box := ⟨(26137/512), (413/8)⟩
  a := (587393/3125000000)
  segments := [
    { box := ⟨(26137/512), (51063511/1000000)⟩, pieceIndex := 48 },
    { box := ⟨(51063511/1000000), (413/8)⟩, pieceIndex := 49 }
  ]
}

def scalarCert812 : MacroScalarCert 56 := {
  box := ⟨(26137/512), (26491/512)⟩
  a := (587393/3125000000)
  segments := [
    { box := ⟨(26137/512), (51063511/1000000)⟩, pieceIndex := 48 },
    { box := ⟨(51063511/1000000), (26491/512)⟩, pieceIndex := 49 }
  ]
}

def scalarCert813 : MacroScalarCert 56 := {
  box := ⟨(59/2), (3953/128)⟩
  a := (1019479061325538470064869171844849/2000000000000000000000000000000000000)
  segments := [
    { box := ⟨(59/2), (15371317/500000)⟩, pieceIndex := 25 },
    { box := ⟨(15371317/500000), (3953/128)⟩, pieceIndex := 26 }
  ]
}

def scalarCert814 : MacroScalarCert 56 := {
  box := ⟨(19647/512), (19765/512)⟩
  a := (76986939/250000000000)
  segments := [
    { box := ⟨(19647/512), (38513093/1000000)⟩, pieceIndex := 36 },
    { box := ⟨(38513093/1000000), (19765/512)⟩, pieceIndex := 37 }
  ]
}

def scalarCert815 : MacroScalarCert 56 := {
  box := ⟨(39353/1024), (39589/1024)⟩
  a := (76986939/250000000000)
  segments := [
    { box := ⟨(39353/1024), (38513093/1000000)⟩, pieceIndex := 36 },
    { box := ⟨(38513093/1000000), (39589/1024)⟩, pieceIndex := 37 }
  ]
}

def scalarCert816 : MacroScalarCert 56 := {
  box := ⟨(51979/1024), (6549/128)⟩
  a := (13135780216075039115731298598211929/128000000000000000000000000000000000000)
  segments := [
    { box := ⟨(51979/1024), (51063511/1000000)⟩, pieceIndex := 48 },
    { box := ⟨(51063511/1000000), (6549/128)⟩, pieceIndex := 49 }
  ]
}

def scalarCert817 : MacroScalarCert 56 := {
  box := ⟨(3245/64), (52333/1024)⟩
  a := (9965930645410815779513042967721/125000000000000000000000000000000000)
  segments := [
    { box := ⟨(3245/64), (51063511/1000000)⟩, pieceIndex := 48 },
    { box := ⟨(51063511/1000000), (52333/1024)⟩, pieceIndex := 49 }
  ]
}

def scalarCert818 : MacroScalarCert 56 := {
  box := ⟨(9499/256), (9617/256)⟩
  a := (294155184355193927474896755253401/8000000000000000000000000000000000000)
  segments := [
    { box := ⟨(9499/256), (9347023/250000)⟩, pieceIndex := 32 },
    { box := ⟨(9347023/250000), (9617/256)⟩, pieceIndex := 33 }
  ]
}

def scalarCert819 : MacroScalarCert 56 := {
  box := ⟨(19057/512), (9617/256)⟩
  a := (294155184355193927474896755253401/8000000000000000000000000000000000000)
  segments := [
    { box := ⟨(19057/512), (9347023/250000)⟩, pieceIndex := 32 },
    { box := ⟨(9347023/250000), (9617/256)⟩, pieceIndex := 33 }
  ]
}

def scalarCert820 : MacroScalarCert 56 := {
  box := ⟨(4661/128), (9617/256)⟩
  a := (294155184355193927474896755253401/8000000000000000000000000000000000000)
  segments := [
    { box := ⟨(4661/128), (9253273/250000)⟩, pieceIndex := 31 },
    { box := ⟨(9253273/250000), (9347023/250000)⟩, pieceIndex := 32 },
    { box := ⟨(9347023/250000), (9617/256)⟩, pieceIndex := 33 }
  ]
}

def scalarCert821 : MacroScalarCert 56 := {
  box := ⟨(9381/256), (9617/256)⟩
  a := (294155184355193927474896755253401/8000000000000000000000000000000000000)
  segments := [
    { box := ⟨(9381/256), (9253273/250000)⟩, pieceIndex := 31 },
    { box := ⟨(9253273/250000), (9347023/250000)⟩, pieceIndex := 32 },
    { box := ⟨(9347023/250000), (9617/256)⟩, pieceIndex := 33 }
  ]
}

def scalarCert822 : MacroScalarCert 56 := {
  box := ⟨(4779/128), (38527/1024)⟩
  a := (2352929906745592990941779764070041/128000000000000000000000000000000000000)
  segments := [
    { box := ⟨(4779/128), (9347023/250000)⟩, pieceIndex := 32 },
    { box := ⟨(9347023/250000), (38527/1024)⟩, pieceIndex := 33 }
  ]
}

def scalarCert823 : MacroScalarCert 56 := {
  box := ⟨(12921/256), (52097/1024)⟩
  a := (253733660265444510657503816809/20000000000000000000000000000000000)
  segments := [
    { box := ⟨(12921/256), (50688511/1000000)⟩, pieceIndex := 47 },
    { box := ⟨(50688511/1000000), (52097/1024)⟩, pieceIndex := 48 }
  ]
}

def scalarCert824 : MacroScalarCert 56 := {
  box := ⟨(25901/512), (13039/256)⟩
  a := (3016845497858850148660534470361/80000000000000000000000000000000000)
  segments := [
    { box := ⟨(25901/512), (50688511/1000000)⟩, pieceIndex := 47 },
    { box := ⟨(50688511/1000000), (13039/256)⟩, pieceIndex := 48 }
  ]
}

def scalarCert825 : MacroScalarCert 56 := {
  box := ⟨(51861/1024), (52215/1024)⟩
  a := (17667571024850201693389455584569/320000000000000000000000000000000000)
  segments := [
    { box := ⟨(51861/1024), (50688511/1000000)⟩, pieceIndex := 47 },
    { box := ⟨(50688511/1000000), (52215/1024)⟩, pieceIndex := 48 }
  ]
}

def scalarCert826 : MacroScalarCert 56 := {
  box := ⟨(45253/1024), (45489/1024)⟩
  a := (125492473536974126032423063314169/8000000000000000000000000000000000000)
  segments := [
    { box := ⟨(45253/1024), (5551521/125000)⟩, pieceIndex := 41 },
    { box := ⟨(5551521/125000), (45489/1024)⟩, pieceIndex := 42 }
  ]
}

def scalarCert827 : MacroScalarCert 56 := {
  box := ⟨(51979/1024), (52333/1024)⟩
  a := (13135780216075039115731298598211929/128000000000000000000000000000000000000)
  segments := [
    { box := ⟨(51979/1024), (51063511/1000000)⟩, pieceIndex := 48 },
    { box := ⟨(51063511/1000000), (52333/1024)⟩, pieceIndex := 49 }
  ]
}

def scalarCert828 : MacroScalarCert 56 := {
  box := ⟨(26019/512), (52333/1024)⟩
  a := (4108970484551816539322694210502201/32000000000000000000000000000000000000)
  segments := [
    { box := ⟨(26019/512), (51063511/1000000)⟩, pieceIndex := 48 },
    { box := ⟨(51063511/1000000), (52333/1024)⟩, pieceIndex := 49 }
  ]
}

def scalarCert829 : MacroScalarCert 56 := {
  box := ⟨(177/4), (11387/256)⟩
  a := (3600341844467488615851330529/122070312500000000000000000000000)
  segments := [
    { box := ⟨(177/4), (5551521/125000)⟩, pieceIndex := 41 },
    { box := ⟨(5551521/125000), (11387/256)⟩, pieceIndex := 42 }
  ]
}

def scalarCert830 : MacroScalarCert 56 := {
  box := ⟨(26019/512), (6549/128)⟩
  a := (4108970484551816539322694210502201/32000000000000000000000000000000000000)
  segments := [
    { box := ⟨(26019/512), (51063511/1000000)⟩, pieceIndex := 48 },
    { box := ⟨(51063511/1000000), (6549/128)⟩, pieceIndex := 49 }
  ]
}

def scalarCert831 : MacroScalarCert 56 := {
  box := ⟨(52097/1024), (6549/128)⟩
  a := (20105418147297356482899790730336929/128000000000000000000000000000000000000)
  segments := [
    { box := ⟨(52097/1024), (51063511/1000000)⟩, pieceIndex := 48 },
    { box := ⟨(51063511/1000000), (6549/128)⟩, pieceIndex := 49 }
  ]
}

def scalarCert832 : MacroScalarCert 56 := {
  box := ⟨(45371/1024), (45607/1024)⟩
  a := (380995896373736237860712551314169/8000000000000000000000000000000000000)
  segments := [
    { box := ⟨(45371/1024), (5551521/125000)⟩, pieceIndex := 41 },
    { box := ⟨(5551521/125000), (45607/1024)⟩, pieceIndex := 42 }
  ]
}

def scalarCert833 : MacroScalarCert 56 := {
  box := ⟨(52097/1024), (52451/1024)⟩
  a := (20105418147297356482899790730336929/128000000000000000000000000000000000000)
  segments := [
    { box := ⟨(52097/1024), (51063511/1000000)⟩, pieceIndex := 48 },
    { box := ⟨(51063511/1000000), (52451/1024)⟩, pieceIndex := 49 }
  ]
}

def scalarCert834 : MacroScalarCert 56 := {
  box := ⟨(13039/256), (26255/512)⟩
  a := (587393/3125000000)
  segments := [
    { box := ⟨(13039/256), (51063511/1000000)⟩, pieceIndex := 48 },
    { box := ⟨(51063511/1000000), (26255/512)⟩, pieceIndex := 49 }
  ]
}

def scalarCert835 : MacroScalarCert 56 := {
  box := ⟨(13039/256), (52451/1024)⟩
  a := (587393/3125000000)
  segments := [
    { box := ⟨(13039/256), (51063511/1000000)⟩, pieceIndex := 48 },
    { box := ⟨(51063511/1000000), (52451/1024)⟩, pieceIndex := 49 }
  ]
}

def scalarCert836 : MacroScalarCert 56 := {
  box := ⟨(52215/1024), (26255/512)⟩
  a := (587393/3125000000)
  segments := [
    { box := ⟨(52215/1024), (51063511/1000000)⟩, pieceIndex := 48 },
    { box := ⟨(51063511/1000000), (26255/512)⟩, pieceIndex := 49 }
  ]
}

def scalarCert837 : MacroScalarCert 56 := {
  box := ⟨(51625/1024), (26019/512)⟩
  a := (1652284170473624845145301959569/320000000000000000000000000000000000)
  segments := [
    { box := ⟨(51625/1024), (50688511/1000000)⟩, pieceIndex := 47 },
    { box := ⟨(50688511/1000000), (26019/512)⟩, pieceIndex := 48 }
  ]
}

def scalarCert838 : MacroScalarCert 56 := {
  box := ⟨(13039/256), (52569/1024)⟩
  a := (587393/3125000000)
  segments := [
    { box := ⟨(13039/256), (51063511/1000000)⟩, pieceIndex := 48 },
    { box := ⟨(51063511/1000000), (52569/1024)⟩, pieceIndex := 49 }
  ]
}

def scalarCert839 : MacroScalarCert 56 := {
  box := ⟨(52215/1024), (52569/1024)⟩
  a := (587393/3125000000)
  segments := [
    { box := ⟨(52215/1024), (51063511/1000000)⟩, pieceIndex := 48 },
    { box := ⟨(51063511/1000000), (52569/1024)⟩, pieceIndex := 49 }
  ]
}

def scalarCert840 : MacroScalarCert 56 := {
  box := ⟨(32509/1024), (65313/2048)⟩
  a := (26038539485972255876043813792489/320000000000000000000000000000000000)
  segments := [
    { box := ⟨(32509/1024), (6373527/200000)⟩, pieceIndex := 29 },
    { box := ⟨(6373527/200000), (65313/2048)⟩, pieceIndex := 30 }
  ]
}

def scalarCert841 : MacroScalarCert 56 := {
  box := ⟨(45371/1024), (91155/2048)⟩
  a := (380995896373736237860712551314169/8000000000000000000000000000000000000)
  segments := [
    { box := ⟨(45371/1024), (5551521/125000)⟩, pieceIndex := 41 },
    { box := ⟨(5551521/125000), (91155/2048)⟩, pieceIndex := 42 }
  ]
}

def scalarCert842 : MacroScalarCert 56 := {
  box := ⟨(52097/1024), (104725/2048)⟩
  a := (20105418147297356482899790730336929/128000000000000000000000000000000000000)
  segments := [
    { box := ⟨(52097/1024), (51063511/1000000)⟩, pieceIndex := 48 },
    { box := ⟨(51063511/1000000), (104725/2048)⟩, pieceIndex := 49 }
  ]
}

def scalarCert843 : MacroScalarCert 56 := {
  box := ⟨(65077/2048), (16343/512)⟩
  a := (129075198159352798032893421273081/1280000000000000000000000000000000000)
  segments := [
    { box := ⟨(65077/2048), (6373527/200000)⟩, pieceIndex := 29 },
    { box := ⟨(6373527/200000), (16343/512)⟩, pieceIndex := 30 }
  ]
}

def scalarCert844 : MacroScalarCert 56 := {
  box := ⟨(90801/2048), (45607/1024)⟩
  a := (1865947917513376303361814742084801/32000000000000000000000000000000000000)
  segments := [
    { box := ⟨(90801/2048), (5551521/125000)⟩, pieceIndex := 41 },
    { box := ⟨(5551521/125000), (45607/1024)⟩, pieceIndex := 42 }
  ]
}

def scalarCert845 : MacroScalarCert 56 := {
  box := ⟨(104253/2048), (6549/128)⟩
  a := (88314896737806401508891494164800841/512000000000000000000000000000000000000)
  segments := [
    { box := ⟨(104253/2048), (51063511/1000000)⟩, pieceIndex := 48 },
    { box := ⟨(51063511/1000000), (6549/128)⟩, pieceIndex := 49 }
  ]
}

def scalarCert846 : MacroScalarCert 56 := {
  box := ⟨(52215/1024), (13157/256)⟩
  a := (587393/3125000000)
  segments := [
    { box := ⟨(52215/1024), (51063511/1000000)⟩, pieceIndex := 48 },
    { box := ⟨(51063511/1000000), (13157/256)⟩, pieceIndex := 49 }
  ]
}

def scalarCert847 : MacroScalarCert 56 := {
  box := ⟨(52215/1024), (52687/1024)⟩
  a := (587393/3125000000)
  segments := [
    { box := ⟨(52215/1024), (51063511/1000000)⟩, pieceIndex := 48 },
    { box := ⟨(51063511/1000000), (52687/1024)⟩, pieceIndex := 49 }
  ]
}

def scalarCert848 : MacroScalarCert 56 := {
  box := ⟨(26137/512), (26373/512)⟩
  a := (587393/3125000000)
  segments := [
    { box := ⟨(26137/512), (51063511/1000000)⟩, pieceIndex := 48 },
    { box := ⟨(51063511/1000000), (26373/512)⟩, pieceIndex := 49 }
  ]
}

def scalarCert849 : MacroScalarCert 56 := {
  box := ⟨(26137/512), (52805/1024)⟩
  a := (587393/3125000000)
  segments := [
    { box := ⟨(26137/512), (51063511/1000000)⟩, pieceIndex := 48 },
    { box := ⟨(51063511/1000000), (52805/1024)⟩, pieceIndex := 49 }
  ]
}

def scalarCert850 : MacroScalarCert 56 := {
  box := ⟨(14573/256), (62500000/1094977)⟩
  a := (55533615788628111515970569841/1250000000000000000000000000000000)
  segments := [
    { box := ⟨(14573/256), (5696637/100000)⟩, pieceIndex := 53 },
    { box := ⟨(5696637/100000), (62500000/1094977)⟩, pieceIndex := 54 }
  ]
}

def scalarCert851 : MacroScalarCert 56 := {
  box := ⟨(1829/64), (3953/128)⟩
  a := (1019479061325538470064869171844849/2000000000000000000000000000000000000)
  segments := [
    { box := ⟨(1829/64), (15371317/500000)⟩, pieceIndex := 25 },
    { box := ⟨(15371317/500000), (3953/128)⟩, pieceIndex := 26 }
  ]
}

def scalarCert852 : MacroScalarCert 56 := {
  box := ⟨(3717/128), (3953/128)⟩
  a := (1019479061325538470064869171844849/2000000000000000000000000000000000000)
  segments := [
    { box := ⟨(3717/128), (15371317/500000)⟩, pieceIndex := 25 },
    { box := ⟨(15371317/500000), (3953/128)⟩, pieceIndex := 26 }
  ]
}

def scalarCert853 : MacroScalarCert 56 := {
  box := ⟨(2301/128), (295/16)⟩
  a := (361710019498569118941886428649/312500000000000000000000000000000)
  segments := [
    { box := ⟨(2301/128), (9113373/500000)⟩, pieceIndex := 13 },
    { box := ⟨(9113373/500000), (295/16)⟩, pieceIndex := 14 }
  ]
}

def scalarCert854 : MacroScalarCert 56 := {
  box := ⟨(4661/256), (295/16)⟩
  a := (361710019498569118941886428649/312500000000000000000000000000000)
  segments := [
    { box := ⟨(4661/256), (9113373/500000)⟩, pieceIndex := 13 },
    { box := ⟨(9113373/500000), (295/16)⟩, pieceIndex := 14 }
  ]
}

def scalarCert855 : MacroScalarCert 56 := {
  box := ⟨(2537/64), (2773/64)⟩
  a := (76986939/250000000000)
  segments := [
    { box := ⟨(2537/64), (43287167/1000000)⟩, pieceIndex := 37 },
    { box := ⟨(43287167/1000000), (2773/64)⟩, pieceIndex := 38 }
  ]
}

def scalarCert856 : MacroScalarCert 56 := {
  box := ⟨(9499/512), (4779/256)⟩
  a := (2891119993742916046127024249511169/8000000000000000000000000000000000000)
  segments := [
    { box := ⟨(9499/512), (9300873/500000)⟩, pieceIndex := 14 },
    { box := ⟨(9300873/500000), (4779/256)⟩, pieceIndex := 15 }
  ]
}

def scalarCert857 : MacroScalarCert 56 := {
  box := ⟨(649/16), (2773/64)⟩
  a := (76986939/250000000000)
  segments := [
    { box := ⟨(649/16), (43287167/1000000)⟩, pieceIndex := 37 },
    { box := ⟨(43287167/1000000), (2773/64)⟩, pieceIndex := 38 }
  ]
}

def scalarCert858 : MacroScalarCert 56 := {
  box := ⟨(4661/256), (9381/512)⟩
  a := (1610977803/1000000000000)
  segments := [
    { box := ⟨(4661/256), (9113373/500000)⟩, pieceIndex := 13 },
    { box := ⟨(9113373/500000), (9381/512)⟩, pieceIndex := 14 }
  ]
}

def scalarCert859 : MacroScalarCert 56 := {
  box := ⟨(3835/128), (3953/128)⟩
  a := (1019479061325538470064869171844849/2000000000000000000000000000000000000)
  segments := [
    { box := ⟨(3835/128), (15371317/500000)⟩, pieceIndex := 25 },
    { box := ⟨(15371317/500000), (3953/128)⟩, pieceIndex := 26 }
  ]
}

def scalarCert860 : MacroScalarCert 56 := {
  box := ⟨(3127/128), (6313/256)⟩
  a := (1408273486016716753984882108683841/2000000000000000000000000000000000000)
  segments := [
    { box := ⟨(3127/128), (24478469/1000000)⟩, pieceIndex := 19 },
    { box := ⟨(24478469/1000000), (6313/256)⟩, pieceIndex := 20 }
  ]
}

def scalarCert861 : MacroScalarCert 56 := {
  box := ⟨(9499/512), (19057/1024)⟩
  a := (65131799414638878784077755001194329/128000000000000000000000000000000000000)
  segments := [
    { box := ⟨(9499/512), (9300873/500000)⟩, pieceIndex := 14 },
    { box := ⟨(9300873/500000), (19057/1024)⟩, pieceIndex := 15 }
  ]
}

def scalarCert862 : MacroScalarCert 56 := {
  box := ⟨(7847/256), (7965/256)⟩
  a := (1624834442189069327106291141707521/8000000000000000000000000000000000000)
  segments := [
    { box := ⟨(7847/256), (15371317/500000)⟩, pieceIndex := 25 },
    { box := ⟨(15371317/500000), (7965/256)⟩, pieceIndex := 26 }
  ]
}

def scalarCert863 : MacroScalarCert 56 := {
  box := ⟨(7847/256), (15871/512)⟩
  a := (10850930469794583755741281507783209/32000000000000000000000000000000000000)
  segments := [
    { box := ⟨(7847/256), (15371317/500000)⟩, pieceIndex := 25 },
    { box := ⟨(15371317/500000), (15871/512)⟩, pieceIndex := 26 }
  ]
}

def scalarCert864 : MacroScalarCert 56 := {
  box := ⟨(15871/512), (15989/512)⟩
  a := (122123177780190359515549805444329/1280000000000000000000000000000000000)
  segments := [
    { box := ⟨(15871/512), (15558817/500000)⟩, pieceIndex := 26 },
    { box := ⟨(15558817/500000), (15989/512)⟩, pieceIndex := 27 }
  ]
}

def scalarCert865 : MacroScalarCert 56 := {
  box := ⟨(15871/512), (31919/1024)⟩
  a := (724867626890627674425335282355441/5120000000000000000000000000000000000)
  segments := [
    { box := ⟨(15871/512), (15558817/500000)⟩, pieceIndex := 26 },
    { box := ⟨(15558817/500000), (31919/1024)⟩, pieceIndex := 27 }
  ]
}

def scalarCert866 : MacroScalarCert 56 := {
  box := ⟨(31801/1024), (15989/512)⟩
  a := (122123177780190359515549805444329/1280000000000000000000000000000000000)
  segments := [
    { box := ⟨(31801/1024), (15558817/500000)⟩, pieceIndex := 26 },
    { box := ⟨(15558817/500000), (15989/512)⟩, pieceIndex := 27 }
  ]
}

def scalarCert867 : MacroScalarCert 56 := {
  box := ⟨(7965/256), (32037/1024)⟩
  a := (298611415772547729059981618230441/5120000000000000000000000000000000000)
  segments := [
    { box := ⟨(7965/256), (15558817/500000)⟩, pieceIndex := 26 },
    { box := ⟨(15558817/500000), (32037/1024)⟩, pieceIndex := 27 }
  ]
}

def scalarCert868 : MacroScalarCert 56 := {
  box := ⟨(1947/64), (3953/128)⟩
  a := (1019479061325538470064869171844849/2000000000000000000000000000000000000)
  segments := [
    { box := ⟨(1947/64), (15371317/500000)⟩, pieceIndex := 25 },
    { box := ⟨(15371317/500000), (3953/128)⟩, pieceIndex := 26 }
  ]
}

def scalarCert869 : MacroScalarCert 56 := {
  box := ⟨(7965/256), (15989/512)⟩
  a := (122123177780190359515549805444329/1280000000000000000000000000000000000)
  segments := [
    { box := ⟨(7965/256), (15558817/500000)⟩, pieceIndex := 26 },
    { box := ⟨(15558817/500000), (15989/512)⟩, pieceIndex := 27 }
  ]
}

def scalarCert870 : MacroScalarCert 56 := {
  box := ⟨(3127/128), (12567/512)⟩
  a := (459565243/500000000000)
  segments := [
    { box := ⟨(3127/128), (24478469/1000000)⟩, pieceIndex := 19 },
    { box := ⟨(24478469/1000000), (12567/512)⟩, pieceIndex := 20 }
  ]
}

lemma scalarCert0_check : scalarCert0.check stableMacroTable = true := by
  norm_num [scalarCert0, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece0, macroPiece1]
lemma scalarCert1_check : scalarCert1.check stableMacroTable = true := by
  norm_num [scalarCert1, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece1, macroPiece2, macroPiece3]
lemma scalarCert2_check : scalarCert2.check stableMacroTable = true := by
  norm_num [scalarCert2, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece13, macroPiece14, macroPiece15]
lemma scalarCert3_check : scalarCert3.check stableMacroTable = true := by
  norm_num [scalarCert3, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece7, macroPiece8, macroPiece9]
lemma scalarCert4_check : scalarCert4.check stableMacroTable = true := by
  norm_num [scalarCert4, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece1, macroPiece2]
lemma scalarCert5_check : scalarCert5.check stableMacroTable = true := by
  norm_num [scalarCert5, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece2, macroPiece3]
lemma scalarCert6_check : scalarCert6.check stableMacroTable = true := by
  norm_num [scalarCert6, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece13, macroPiece14, macroPiece15]
lemma scalarCert7_check : scalarCert7.check stableMacroTable = true := by
  norm_num [scalarCert7, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece7, macroPiece8, macroPiece9]
lemma scalarCert8_check : scalarCert8.check stableMacroTable = true := by
  norm_num [scalarCert8, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece13, macroPiece14, macroPiece15]
lemma scalarCert9_check : scalarCert9.check stableMacroTable = true := by
  norm_num [scalarCert9, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece7, macroPiece8, macroPiece9]
lemma scalarCert10_check : scalarCert10.check stableMacroTable = true := by
  norm_num [scalarCert10, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece2, macroPiece3]
lemma scalarCert11_check : scalarCert11.check stableMacroTable = true := by
  norm_num [scalarCert11, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece8, macroPiece9]
lemma scalarCert12_check : scalarCert12.check stableMacroTable = true := by
  norm_num [scalarCert12, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece2, macroPiece3]
lemma scalarCert13_check : scalarCert13.check stableMacroTable = true := by
  norm_num [scalarCert13, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece23, macroPiece24, macroPiece25]
lemma scalarCert14_check : scalarCert14.check stableMacroTable = true := by
  norm_num [scalarCert14, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece17, macroPiece18]
lemma scalarCert15_check : scalarCert15.check stableMacroTable = true := by
  norm_num [scalarCert15, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece23, macroPiece24]
lemma scalarCert16_check : scalarCert16.check stableMacroTable = true := by
  norm_num [scalarCert16, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece29, macroPiece30, macroPiece31]
lemma scalarCert17_check : scalarCert17.check stableMacroTable = true := by
  norm_num [scalarCert17, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece23, macroPiece24, macroPiece25]
lemma scalarCert18_check : scalarCert18.check stableMacroTable = true := by
  norm_num [scalarCert18, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece29, macroPiece30, macroPiece31]
lemma scalarCert19_check : scalarCert19.check stableMacroTable = true := by
  norm_num [scalarCert19, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece23, macroPiece24]
lemma scalarCert20_check : scalarCert20.check stableMacroTable = true := by
  norm_num [scalarCert20, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece17, macroPiece18]
lemma scalarCert21_check : scalarCert21.check stableMacroTable = true := by
  norm_num [scalarCert21, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece23, macroPiece24]
lemma scalarCert22_check : scalarCert22.check stableMacroTable = true := by
  norm_num [scalarCert22, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece29, macroPiece30, macroPiece31]
lemma scalarCert23_check : scalarCert23.check stableMacroTable = true := by
  norm_num [scalarCert23, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece17, macroPiece18]
lemma scalarCert24_check : scalarCert24.check stableMacroTable = true := by
  norm_num [scalarCert24, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece23, macroPiece24, macroPiece25]
lemma scalarCert25_check : scalarCert25.check stableMacroTable = true := by
  norm_num [scalarCert25, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece17, macroPiece18]
lemma scalarCert26_check : scalarCert26.check stableMacroTable = true := by
  norm_num [scalarCert26, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece11, macroPiece12]
lemma scalarCert27_check : scalarCert27.check stableMacroTable = true := by
  norm_num [scalarCert27, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece23, macroPiece24]
lemma scalarCert28_check : scalarCert28.check stableMacroTable = true := by
  norm_num [scalarCert28, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece29, macroPiece30, macroPiece31]
lemma scalarCert29_check : scalarCert29.check stableMacroTable = true := by
  norm_num [scalarCert29, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece23, macroPiece24]
lemma scalarCert30_check : scalarCert30.check stableMacroTable = true := by
  norm_num [scalarCert30, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece29, macroPiece30, macroPiece31]
lemma scalarCert31_check : scalarCert31.check stableMacroTable = true := by
  norm_num [scalarCert31, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece29, macroPiece30, macroPiece31]
lemma scalarCert32_check : scalarCert32.check stableMacroTable = true := by
  norm_num [scalarCert32, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece23, macroPiece24]
lemma scalarCert33_check : scalarCert33.check stableMacroTable = true := by
  norm_num [scalarCert33, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece17, macroPiece18]
lemma scalarCert34_check : scalarCert34.check stableMacroTable = true := by
  norm_num [scalarCert34, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece30, macroPiece31]
lemma scalarCert35_check : scalarCert35.check stableMacroTable = true := by
  norm_num [scalarCert35, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece23, macroPiece24, macroPiece25]
lemma scalarCert36_check : scalarCert36.check stableMacroTable = true := by
  norm_num [scalarCert36, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece17, macroPiece18]
lemma scalarCert37_check : scalarCert37.check stableMacroTable = true := by
  norm_num [scalarCert37, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece11, macroPiece12]
lemma scalarCert38_check : scalarCert38.check stableMacroTable = true := by
  norm_num [scalarCert38, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece29, macroPiece30, macroPiece31]
lemma scalarCert39_check : scalarCert39.check stableMacroTable = true := by
  norm_num [scalarCert39, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece23, macroPiece24, macroPiece25]
lemma scalarCert40_check : scalarCert40.check stableMacroTable = true := by
  norm_num [scalarCert40, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece17, macroPiece18, macroPiece19]
lemma scalarCert41_check : scalarCert41.check stableMacroTable = true := by
  norm_num [scalarCert41, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece11, macroPiece12]
lemma scalarCert42_check : scalarCert42.check stableMacroTable = true := by
  norm_num [scalarCert42, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece29, macroPiece30, macroPiece31]
lemma scalarCert43_check : scalarCert43.check stableMacroTable = true := by
  norm_num [scalarCert43, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece23, macroPiece24, macroPiece25]
lemma scalarCert44_check : scalarCert44.check stableMacroTable = true := by
  norm_num [scalarCert44, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece17, macroPiece18]
lemma scalarCert45_check : scalarCert45.check stableMacroTable = true := by
  norm_num [scalarCert45, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece29, macroPiece30, macroPiece31]
lemma scalarCert46_check : scalarCert46.check stableMacroTable = true := by
  norm_num [scalarCert46, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece23, macroPiece24, macroPiece25]
lemma scalarCert47_check : scalarCert47.check stableMacroTable = true := by
  norm_num [scalarCert47, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece17, macroPiece18, macroPiece19]
lemma scalarCert48_check : scalarCert48.check stableMacroTable = true := by
  norm_num [scalarCert48, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece29, macroPiece30, macroPiece31]
lemma scalarCert49_check : scalarCert49.check stableMacroTable = true := by
  norm_num [scalarCert49, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece23, macroPiece24, macroPiece25]
lemma scalarCert50_check : scalarCert50.check stableMacroTable = true := by
  norm_num [scalarCert50, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece29, macroPiece30, macroPiece31]
lemma scalarCert51_check : scalarCert51.check stableMacroTable = true := by
  norm_num [scalarCert51, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece23, macroPiece24, macroPiece25]
lemma scalarCert52_check : scalarCert52.check stableMacroTable = true := by
  norm_num [scalarCert52, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece11, macroPiece12, macroPiece13]
lemma scalarCert53_check : scalarCert53.check stableMacroTable = true := by
  norm_num [scalarCert53, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece5, macroPiece6]
lemma scalarCert54_check : scalarCert54.check stableMacroTable = true := by
  norm_num [scalarCert54, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece11, macroPiece12]
lemma scalarCert55_check : scalarCert55.check stableMacroTable = true := by
  norm_num [scalarCert55, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece17, macroPiece18]
lemma scalarCert56_check : scalarCert56.check stableMacroTable = true := by
  norm_num [scalarCert56, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece11, macroPiece12]
lemma scalarCert57_check : scalarCert57.check stableMacroTable = true := by
  norm_num [scalarCert57, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece18, macroPiece19]
lemma scalarCert58_check : scalarCert58.check stableMacroTable = true := by
  norm_num [scalarCert58, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece29, macroPiece30, macroPiece31]
lemma scalarCert59_check : scalarCert59.check stableMacroTable = true := by
  norm_num [scalarCert59, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece29, macroPiece30, macroPiece31]
lemma scalarCert60_check : scalarCert60.check stableMacroTable = true := by
  norm_num [scalarCert60, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece29, macroPiece30, macroPiece31]
lemma scalarCert61_check : scalarCert61.check stableMacroTable = true := by
  norm_num [scalarCert61, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece30, macroPiece31]
lemma scalarCert62_check : scalarCert62.check stableMacroTable = true := by
  norm_num [scalarCert62, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece30, macroPiece31]
lemma scalarCert63_check : scalarCert63.check stableMacroTable = true := by
  norm_num [scalarCert63, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece30, macroPiece31]
lemma scalarCert64_check : scalarCert64.check stableMacroTable = true := by
  norm_num [scalarCert64, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece30, macroPiece31]
lemma scalarCert65_check : scalarCert65.check stableMacroTable = true := by
  norm_num [scalarCert65, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece30, macroPiece31]
lemma scalarCert66_check : scalarCert66.check stableMacroTable = true := by
  norm_num [scalarCert66, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece17, macroPiece18]
lemma scalarCert67_check : scalarCert67.check stableMacroTable = true := by
  norm_num [scalarCert67, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece23, macroPiece24, macroPiece25]
lemma scalarCert68_check : scalarCert68.check stableMacroTable = true := by
  norm_num [scalarCert68, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece30, macroPiece31]
lemma scalarCert69_check : scalarCert69.check stableMacroTable = true := by
  norm_num [scalarCert69, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece17, macroPiece18]
lemma scalarCert70_check : scalarCert70.check stableMacroTable = true := by
  norm_num [scalarCert70, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece24, macroPiece25]
lemma scalarCert71_check : scalarCert71.check stableMacroTable = true := by
  norm_num [scalarCert71, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece30, macroPiece31]
lemma scalarCert72_check : scalarCert72.check stableMacroTable = true := by
  norm_num [scalarCert72, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece17, macroPiece18]
lemma scalarCert73_check : scalarCert73.check stableMacroTable = true := by
  norm_num [scalarCert73, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece29, macroPiece30, macroPiece31]
lemma scalarCert74_check : scalarCert74.check stableMacroTable = true := by
  norm_num [scalarCert74, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece29, macroPiece30, macroPiece31]
lemma scalarCert75_check : scalarCert75.check stableMacroTable = true := by
  norm_num [scalarCert75, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece30, macroPiece31]
lemma scalarCert76_check : scalarCert76.check stableMacroTable = true := by
  norm_num [scalarCert76, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece30, macroPiece31]
lemma scalarCert77_check : scalarCert77.check stableMacroTable = true := by
  norm_num [scalarCert77, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece30, macroPiece31]
lemma scalarCert78_check : scalarCert78.check stableMacroTable = true := by
  norm_num [scalarCert78, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece30, macroPiece31]
lemma scalarCert79_check : scalarCert79.check stableMacroTable = true := by
  norm_num [scalarCert79, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece23, macroPiece24, macroPiece25]
lemma scalarCert80_check : scalarCert80.check stableMacroTable = true := by
  norm_num [scalarCert80, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece30, macroPiece31]
lemma scalarCert81_check : scalarCert81.check stableMacroTable = true := by
  norm_num [scalarCert81, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece24, macroPiece25]
lemma scalarCert82_check : scalarCert82.check stableMacroTable = true := by
  norm_num [scalarCert82, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece29, macroPiece30, macroPiece31]
lemma scalarCert83_check : scalarCert83.check stableMacroTable = true := by
  norm_num [scalarCert83, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece30, macroPiece31]
lemma scalarCert84_check : scalarCert84.check stableMacroTable = true := by
  norm_num [scalarCert84, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece30, macroPiece31]
lemma scalarCert85_check : scalarCert85.check stableMacroTable = true := by
  norm_num [scalarCert85, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece30, macroPiece31]
lemma scalarCert86_check : scalarCert86.check stableMacroTable = true := by
  norm_num [scalarCert86, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece30, macroPiece31]
lemma scalarCert87_check : scalarCert87.check stableMacroTable = true := by
  norm_num [scalarCert87, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece29, macroPiece30, macroPiece31]
lemma scalarCert88_check : scalarCert88.check stableMacroTable = true := by
  norm_num [scalarCert88, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece17, macroPiece18, macroPiece19]
lemma scalarCert89_check : scalarCert89.check stableMacroTable = true := by
  norm_num [scalarCert89, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece29, macroPiece30, macroPiece31]
lemma scalarCert90_check : scalarCert90.check stableMacroTable = true := by
  norm_num [scalarCert90, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece11, macroPiece12, macroPiece13]
lemma scalarCert91_check : scalarCert91.check stableMacroTable = true := by
  norm_num [scalarCert91, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece11, macroPiece12, macroPiece13]
lemma scalarCert92_check : scalarCert92.check stableMacroTable = true := by
  norm_num [scalarCert92, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece23, macroPiece24, macroPiece25]
lemma scalarCert93_check : scalarCert93.check stableMacroTable = true := by
  norm_num [scalarCert93, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece23, macroPiece24, macroPiece25]
lemma scalarCert94_check : scalarCert94.check stableMacroTable = true := by
  norm_num [scalarCert94, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece17, macroPiece18, macroPiece19]
lemma scalarCert95_check : scalarCert95.check stableMacroTable = true := by
  norm_num [scalarCert95, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece11, macroPiece12, macroPiece13]
lemma scalarCert96_check : scalarCert96.check stableMacroTable = true := by
  norm_num [scalarCert96, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece24, macroPiece25]
lemma scalarCert97_check : scalarCert97.check stableMacroTable = true := by
  norm_num [scalarCert97, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece11, macroPiece12]
lemma scalarCert98_check : scalarCert98.check stableMacroTable = true := by
  norm_num [scalarCert98, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece23, macroPiece24, macroPiece25]
lemma scalarCert99_check : scalarCert99.check stableMacroTable = true := by
  norm_num [scalarCert99, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece18, macroPiece19]
lemma scalarCert100_check : scalarCert100.check stableMacroTable = true := by
  norm_num [scalarCert100, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece12, macroPiece13]
lemma scalarCert101_check : scalarCert101.check stableMacroTable = true := by
  norm_num [scalarCert101, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece23, macroPiece24, macroPiece25]
lemma scalarCert102_check : scalarCert102.check stableMacroTable = true := by
  norm_num [scalarCert102, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece18, macroPiece19]
lemma scalarCert103_check : scalarCert103.check stableMacroTable = true := by
  norm_num [scalarCert103, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece12, macroPiece13]
lemma scalarCert104_check : scalarCert104.check stableMacroTable = true := by
  norm_num [scalarCert104, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece23, macroPiece24, macroPiece25]
lemma scalarCert105_check : scalarCert105.check stableMacroTable = true := by
  norm_num [scalarCert105, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece18, macroPiece19]
lemma scalarCert106_check : scalarCert106.check stableMacroTable = true := by
  norm_num [scalarCert106, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece12, macroPiece13]
lemma scalarCert107_check : scalarCert107.check stableMacroTable = true := by
  norm_num [scalarCert107, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece23, macroPiece24, macroPiece25]
lemma scalarCert108_check : scalarCert108.check stableMacroTable = true := by
  norm_num [scalarCert108, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece18, macroPiece19]
lemma scalarCert109_check : scalarCert109.check stableMacroTable = true := by
  norm_num [scalarCert109, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece12, macroPiece13]
lemma scalarCert110_check : scalarCert110.check stableMacroTable = true := by
  norm_num [scalarCert110, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece24, macroPiece25]
lemma scalarCert111_check : scalarCert111.check stableMacroTable = true := by
  norm_num [scalarCert111, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece23, macroPiece24, macroPiece25]
lemma scalarCert112_check : scalarCert112.check stableMacroTable = true := by
  norm_num [scalarCert112, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece24, macroPiece25]
lemma scalarCert113_check : scalarCert113.check stableMacroTable = true := by
  norm_num [scalarCert113, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece24, macroPiece25]
lemma scalarCert114_check : scalarCert114.check stableMacroTable = true := by
  norm_num [scalarCert114, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece24, macroPiece25]
lemma scalarCert115_check : scalarCert115.check stableMacroTable = true := by
  norm_num [scalarCert115, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece24, macroPiece25]
lemma scalarCert116_check : scalarCert116.check stableMacroTable = true := by
  norm_num [scalarCert116, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece24, macroPiece25]
lemma scalarCert117_check : scalarCert117.check stableMacroTable = true := by
  norm_num [scalarCert117, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece24, macroPiece25]
lemma scalarCert118_check : scalarCert118.check stableMacroTable = true := by
  norm_num [scalarCert118, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece23, macroPiece24, macroPiece25]
lemma scalarCert119_check : scalarCert119.check stableMacroTable = true := by
  norm_num [scalarCert119, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece23, macroPiece24, macroPiece25]
lemma scalarCert120_check : scalarCert120.check stableMacroTable = true := by
  norm_num [scalarCert120, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece24, macroPiece25]
lemma scalarCert121_check : scalarCert121.check stableMacroTable = true := by
  norm_num [scalarCert121, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece29, macroPiece30, macroPiece31]
lemma scalarCert122_check : scalarCert122.check stableMacroTable = true := by
  norm_num [scalarCert122, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece29, macroPiece30, macroPiece31]
lemma scalarCert123_check : scalarCert123.check stableMacroTable = true := by
  norm_num [scalarCert123, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece29, macroPiece30, macroPiece31]
lemma scalarCert124_check : scalarCert124.check stableMacroTable = true := by
  norm_num [scalarCert124, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece30, macroPiece31]
lemma scalarCert125_check : scalarCert125.check stableMacroTable = true := by
  norm_num [scalarCert125, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece24, macroPiece25]
lemma scalarCert126_check : scalarCert126.check stableMacroTable = true := by
  norm_num [scalarCert126, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece17, macroPiece18]
lemma scalarCert127_check : scalarCert127.check stableMacroTable = true := by
  norm_num [scalarCert127, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece24, macroPiece25]
lemma scalarCert128_check : scalarCert128.check stableMacroTable = true := by
  norm_num [scalarCert128, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece17, macroPiece18]
lemma scalarCert129_check : scalarCert129.check stableMacroTable = true := by
  norm_num [scalarCert129, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece18, macroPiece19]
lemma scalarCert130_check : scalarCert130.check stableMacroTable = true := by
  norm_num [scalarCert130, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece18, macroPiece19]
lemma scalarCert131_check : scalarCert131.check stableMacroTable = true := by
  norm_num [scalarCert131, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece30, macroPiece31]
lemma scalarCert132_check : scalarCert132.check stableMacroTable = true := by
  norm_num [scalarCert132, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece24, macroPiece25]
lemma scalarCert133_check : scalarCert133.check stableMacroTable = true := by
  norm_num [scalarCert133, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece24, macroPiece25]
lemma scalarCert134_check : scalarCert134.check stableMacroTable = true := by
  norm_num [scalarCert134, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece30, macroPiece31]
lemma scalarCert135_check : scalarCert135.check stableMacroTable = true := by
  norm_num [scalarCert135, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece18, macroPiece19]
lemma scalarCert136_check : scalarCert136.check stableMacroTable = true := by
  norm_num [scalarCert136, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece12, macroPiece13]
lemma scalarCert137_check : scalarCert137.check stableMacroTable = true := by
  norm_num [scalarCert137, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece29, macroPiece30, macroPiece31]
lemma scalarCert138_check : scalarCert138.check stableMacroTable = true := by
  norm_num [scalarCert138, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece29, macroPiece30, macroPiece31]
lemma scalarCert139_check : scalarCert139.check stableMacroTable = true := by
  norm_num [scalarCert139, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece30, macroPiece31]
lemma scalarCert140_check : scalarCert140.check stableMacroTable = true := by
  norm_num [scalarCert140, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece23, macroPiece24, macroPiece25]
lemma scalarCert141_check : scalarCert141.check stableMacroTable = true := by
  norm_num [scalarCert141, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece30, macroPiece31]
lemma scalarCert142_check : scalarCert142.check stableMacroTable = true := by
  norm_num [scalarCert142, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece24, macroPiece25]
lemma scalarCert143_check : scalarCert143.check stableMacroTable = true := by
  norm_num [scalarCert143, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece29, macroPiece30, macroPiece31]
lemma scalarCert144_check : scalarCert144.check stableMacroTable = true := by
  norm_num [scalarCert144, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece18, macroPiece19]
lemma scalarCert145_check : scalarCert145.check stableMacroTable = true := by
  norm_num [scalarCert145, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece24, macroPiece25]
lemma scalarCert146_check : scalarCert146.check stableMacroTable = true := by
  norm_num [scalarCert146, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece23, macroPiece24, macroPiece25]
lemma scalarCert147_check : scalarCert147.check stableMacroTable = true := by
  norm_num [scalarCert147, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece23, macroPiece24, macroPiece25]
lemma scalarCert148_check : scalarCert148.check stableMacroTable = true := by
  norm_num [scalarCert148, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece24, macroPiece25]
lemma scalarCert149_check : scalarCert149.check stableMacroTable = true := by
  norm_num [scalarCert149, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece24, macroPiece25]
lemma scalarCert150_check : scalarCert150.check stableMacroTable = true := by
  norm_num [scalarCert150, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece29, macroPiece30, macroPiece31]
lemma scalarCert151_check : scalarCert151.check stableMacroTable = true := by
  norm_num [scalarCert151, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece29, macroPiece30, macroPiece31]
lemma scalarCert152_check : scalarCert152.check stableMacroTable = true := by
  norm_num [scalarCert152, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece30, macroPiece31]
lemma scalarCert153_check : scalarCert153.check stableMacroTable = true := by
  norm_num [scalarCert153, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece2, macroPiece3]
lemma scalarCert154_check : scalarCert154.check stableMacroTable = true := by
  norm_num [scalarCert154, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece30, macroPiece31]
lemma scalarCert155_check : scalarCert155.check stableMacroTable = true := by
  norm_num [scalarCert155, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece18, macroPiece19]
lemma scalarCert156_check : scalarCert156.check stableMacroTable = true := by
  norm_num [scalarCert156, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece18, macroPiece19]
lemma scalarCert157_check : scalarCert157.check stableMacroTable = true := by
  norm_num [scalarCert157, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece18, macroPiece19]
lemma scalarCert158_check : scalarCert158.check stableMacroTable = true := by
  norm_num [scalarCert158, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece18, macroPiece19]
lemma scalarCert159_check : scalarCert159.check stableMacroTable = true := by
  norm_num [scalarCert159, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece18, macroPiece19]
lemma scalarCert160_check : scalarCert160.check stableMacroTable = true := by
  norm_num [scalarCert160, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece18, macroPiece19]
lemma scalarCert161_check : scalarCert161.check stableMacroTable = true := by
  norm_num [scalarCert161, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece18, macroPiece19]
lemma scalarCert162_check : scalarCert162.check stableMacroTable = true := by
  norm_num [scalarCert162, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece24, macroPiece25]
lemma scalarCert163_check : scalarCert163.check stableMacroTable = true := by
  norm_num [scalarCert163, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece18, macroPiece19]
lemma scalarCert164_check : scalarCert164.check stableMacroTable = true := by
  norm_num [scalarCert164, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece18, macroPiece19]
lemma scalarCert165_check : scalarCert165.check stableMacroTable = true := by
  norm_num [scalarCert165, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece12, macroPiece13]
lemma scalarCert166_check : scalarCert166.check stableMacroTable = true := by
  norm_num [scalarCert166, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece18, macroPiece19]
lemma scalarCert167_check : scalarCert167.check stableMacroTable = true := by
  norm_num [scalarCert167, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece24, macroPiece25]
lemma scalarCert168_check : scalarCert168.check stableMacroTable = true := by
  norm_num [scalarCert168, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece24, macroPiece25]
lemma scalarCert169_check : scalarCert169.check stableMacroTable = true := by
  norm_num [scalarCert169, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece24, macroPiece25]
lemma scalarCert170_check : scalarCert170.check stableMacroTable = true := by
  norm_num [scalarCert170, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece18, macroPiece19]
lemma scalarCert171_check : scalarCert171.check stableMacroTable = true := by
  norm_num [scalarCert171, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece6, macroPiece7]
lemma scalarCert172_check : scalarCert172.check stableMacroTable = true := by
  norm_num [scalarCert172, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece11, macroPiece12, macroPiece13, macroPiece14]
lemma scalarCert173_check : scalarCert173.check stableMacroTable = true := by
  norm_num [scalarCert173, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece11, macroPiece12, macroPiece13]
lemma scalarCert174_check : scalarCert174.check stableMacroTable = true := by
  norm_num [scalarCert174, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece6, macroPiece7]
lemma scalarCert175_check : scalarCert175.check stableMacroTable = true := by
  norm_num [scalarCert175, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece11, macroPiece12, macroPiece13]
lemma scalarCert176_check : scalarCert176.check stableMacroTable = true := by
  norm_num [scalarCert176, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece24, macroPiece25]
lemma scalarCert177_check : scalarCert177.check stableMacroTable = true := by
  norm_num [scalarCert177, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece18, macroPiece19]
lemma scalarCert178_check : scalarCert178.check stableMacroTable = true := by
  norm_num [scalarCert178, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece18, macroPiece19]
lemma scalarCert179_check : scalarCert179.check stableMacroTable = true := by
  norm_num [scalarCert179, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece24, macroPiece25, macroPiece26, macroPiece27]
lemma scalarCert180_check : scalarCert180.check stableMacroTable = true := by
  norm_num [scalarCert180, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece25, macroPiece26, macroPiece27]
lemma scalarCert181_check : scalarCert181.check stableMacroTable = true := by
  norm_num [scalarCert181, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece13, macroPiece14]
lemma scalarCert182_check : scalarCert182.check stableMacroTable = true := by
  norm_num [scalarCert182, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece19, macroPiece20, macroPiece21]
lemma scalarCert183_check : scalarCert183.check stableMacroTable = true := by
  norm_num [scalarCert183, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece19, macroPiece20, macroPiece21]
lemma scalarCert184_check : scalarCert184.check stableMacroTable = true := by
  norm_num [scalarCert184, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece13, macroPiece14]
lemma scalarCert185_check : scalarCert185.check stableMacroTable = true := by
  norm_num [scalarCert185, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece25, macroPiece26, macroPiece27]
lemma scalarCert186_check : scalarCert186.check stableMacroTable = true := by
  norm_num [scalarCert186, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece19, macroPiece20, macroPiece21]
lemma scalarCert187_check : scalarCert187.check stableMacroTable = true := by
  norm_num [scalarCert187, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece13, macroPiece14]
lemma scalarCert188_check : scalarCert188.check stableMacroTable = true := by
  norm_num [scalarCert188, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece13, macroPiece14, macroPiece15]
lemma scalarCert189_check : scalarCert189.check stableMacroTable = true := by
  norm_num [scalarCert189, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece7, macroPiece8, macroPiece9]
lemma scalarCert190_check : scalarCert190.check stableMacroTable = true := by
  norm_num [scalarCert190, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece19, macroPiece20, macroPiece21]
lemma scalarCert191_check : scalarCert191.check stableMacroTable = true := by
  norm_num [scalarCert191, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece35, macroPiece36, macroPiece37]
lemma scalarCert192_check : scalarCert192.check stableMacroTable = true := by
  norm_num [scalarCert192, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece35, macroPiece36, macroPiece37]
lemma scalarCert193_check : scalarCert193.check stableMacroTable = true := by
  norm_num [scalarCert193, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece35, macroPiece36, macroPiece37]
lemma scalarCert194_check : scalarCert194.check stableMacroTable = true := by
  norm_num [scalarCert194, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece35, macroPiece36, macroPiece37]
lemma scalarCert195_check : scalarCert195.check stableMacroTable = true := by
  norm_num [scalarCert195, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece35, macroPiece36, macroPiece37]
lemma scalarCert196_check : scalarCert196.check stableMacroTable = true := by
  norm_num [scalarCert196, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece35, macroPiece36, macroPiece37]
lemma scalarCert197_check : scalarCert197.check stableMacroTable = true := by
  norm_num [scalarCert197, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece35, macroPiece36, macroPiece37]
lemma scalarCert198_check : scalarCert198.check stableMacroTable = true := by
  norm_num [scalarCert198, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece35, macroPiece36, macroPiece37]
lemma scalarCert199_check : scalarCert199.check stableMacroTable = true := by
  norm_num [scalarCert199, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece35, macroPiece36, macroPiece37]
lemma scalarCert200_check : scalarCert200.check stableMacroTable = true := by
  norm_num [scalarCert200, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece35, macroPiece36, macroPiece37]
lemma scalarCert201_check : scalarCert201.check stableMacroTable = true := by
  norm_num [scalarCert201, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece29, macroPiece30, macroPiece31]
lemma scalarCert202_check : scalarCert202.check stableMacroTable = true := by
  norm_num [scalarCert202, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece35, macroPiece36, macroPiece37]
lemma scalarCert203_check : scalarCert203.check stableMacroTable = true := by
  norm_num [scalarCert203, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece29, macroPiece30]
lemma scalarCert204_check : scalarCert204.check stableMacroTable = true := by
  norm_num [scalarCert204, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece36, macroPiece37]
lemma scalarCert205_check : scalarCert205.check stableMacroTable = true := by
  norm_num [scalarCert205, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece29, macroPiece30, macroPiece31]
lemma scalarCert206_check : scalarCert206.check stableMacroTable = true := by
  norm_num [scalarCert206, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece36, macroPiece37]
lemma scalarCert207_check : scalarCert207.check stableMacroTable = true := by
  norm_num [scalarCert207, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece36, macroPiece37]
lemma scalarCert208_check : scalarCert208.check stableMacroTable = true := by
  norm_num [scalarCert208, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece35, macroPiece36, macroPiece37]
lemma scalarCert209_check : scalarCert209.check stableMacroTable = true := by
  norm_num [scalarCert209, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece35, macroPiece36, macroPiece37]
lemma scalarCert210_check : scalarCert210.check stableMacroTable = true := by
  norm_num [scalarCert210, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece35, macroPiece36, macroPiece37]
lemma scalarCert211_check : scalarCert211.check stableMacroTable = true := by
  norm_num [scalarCert211, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece36, macroPiece37]
lemma scalarCert212_check : scalarCert212.check stableMacroTable = true := by
  norm_num [scalarCert212, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece14, macroPiece15]
lemma scalarCert213_check : scalarCert213.check stableMacroTable = true := by
  norm_num [scalarCert213, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece7, macroPiece8]
lemma scalarCert214_check : scalarCert214.check stableMacroTable = true := by
  norm_num [scalarCert214, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece8, macroPiece9]
lemma scalarCert215_check : scalarCert215.check stableMacroTable = true := by
  norm_num [scalarCert215, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece35, macroPiece36, macroPiece37]
lemma scalarCert216_check : scalarCert216.check stableMacroTable = true := by
  norm_num [scalarCert216, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece35, macroPiece36, macroPiece37]
lemma scalarCert217_check : scalarCert217.check stableMacroTable = true := by
  norm_num [scalarCert217, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece36, macroPiece37]
lemma scalarCert218_check : scalarCert218.check stableMacroTable = true := by
  norm_num [scalarCert218, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece36, macroPiece37]
lemma scalarCert219_check : scalarCert219.check stableMacroTable = true := by
  norm_num [scalarCert219, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece36, macroPiece37]
lemma scalarCert220_check : scalarCert220.check stableMacroTable = true := by
  norm_num [scalarCert220, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece36, macroPiece37]
lemma scalarCert221_check : scalarCert221.check stableMacroTable = true := by
  norm_num [scalarCert221, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece36, macroPiece37]
lemma scalarCert222_check : scalarCert222.check stableMacroTable = true := by
  norm_num [scalarCert222, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece35, macroPiece36, macroPiece37]
lemma scalarCert223_check : scalarCert223.check stableMacroTable = true := by
  norm_num [scalarCert223, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece36, macroPiece37]
lemma scalarCert224_check : scalarCert224.check stableMacroTable = true := by
  norm_num [scalarCert224, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece36, macroPiece37]
lemma scalarCert225_check : scalarCert225.check stableMacroTable = true := by
  norm_num [scalarCert225, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece36, macroPiece37]
lemma scalarCert226_check : scalarCert226.check stableMacroTable = true := by
  norm_num [scalarCert226, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece36, macroPiece37]
lemma scalarCert227_check : scalarCert227.check stableMacroTable = true := by
  norm_num [scalarCert227, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece36, macroPiece37]
lemma scalarCert228_check : scalarCert228.check stableMacroTable = true := by
  norm_num [scalarCert228, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece35, macroPiece36, macroPiece37]
lemma scalarCert229_check : scalarCert229.check stableMacroTable = true := by
  norm_num [scalarCert229, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece36, macroPiece37]
lemma scalarCert230_check : scalarCert230.check stableMacroTable = true := by
  norm_num [scalarCert230, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece36, macroPiece37]
lemma scalarCert231_check : scalarCert231.check stableMacroTable = true := by
  norm_num [scalarCert231, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece19, macroPiece20, macroPiece21]
lemma scalarCert232_check : scalarCert232.check stableMacroTable = true := by
  norm_num [scalarCert232, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece13, macroPiece14, macroPiece15]
lemma scalarCert233_check : scalarCert233.check stableMacroTable = true := by
  norm_num [scalarCert233, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece13, macroPiece14, macroPiece15]
lemma scalarCert234_check : scalarCert234.check stableMacroTable = true := by
  norm_num [scalarCert234, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece19, macroPiece20, macroPiece21]
lemma scalarCert235_check : scalarCert235.check stableMacroTable = true := by
  norm_num [scalarCert235, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece13, macroPiece14, macroPiece15]
lemma scalarCert236_check : scalarCert236.check stableMacroTable = true := by
  norm_num [scalarCert236, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece35, macroPiece36, macroPiece37]
lemma scalarCert237_check : scalarCert237.check stableMacroTable = true := by
  norm_num [scalarCert237, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece35, macroPiece36, macroPiece37]
lemma scalarCert238_check : scalarCert238.check stableMacroTable = true := by
  norm_num [scalarCert238, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece35, macroPiece36, macroPiece37]
lemma scalarCert239_check : scalarCert239.check stableMacroTable = true := by
  norm_num [scalarCert239, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece35, macroPiece36, macroPiece37]
lemma scalarCert240_check : scalarCert240.check stableMacroTable = true := by
  norm_num [scalarCert240, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece36, macroPiece37]
lemma scalarCert241_check : scalarCert241.check stableMacroTable = true := by
  norm_num [scalarCert241, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece36, macroPiece37]
lemma scalarCert242_check : scalarCert242.check stableMacroTable = true := by
  norm_num [scalarCert242, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece36, macroPiece37]
lemma scalarCert243_check : scalarCert243.check stableMacroTable = true := by
  norm_num [scalarCert243, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece36, macroPiece37]
lemma scalarCert244_check : scalarCert244.check stableMacroTable = true := by
  norm_num [scalarCert244, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece35, macroPiece36, macroPiece37]
lemma scalarCert245_check : scalarCert245.check stableMacroTable = true := by
  norm_num [scalarCert245, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece35, macroPiece36, macroPiece37]
lemma scalarCert246_check : scalarCert246.check stableMacroTable = true := by
  norm_num [scalarCert246, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece35, macroPiece36, macroPiece37]
lemma scalarCert247_check : scalarCert247.check stableMacroTable = true := by
  norm_num [scalarCert247, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece36, macroPiece37]
lemma scalarCert248_check : scalarCert248.check stableMacroTable = true := by
  norm_num [scalarCert248, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece14, macroPiece15]
lemma scalarCert249_check : scalarCert249.check stableMacroTable = true := by
  norm_num [scalarCert249, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece14, macroPiece15]
lemma scalarCert250_check : scalarCert250.check stableMacroTable = true := by
  norm_num [scalarCert250, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece35, macroPiece36, macroPiece37]
lemma scalarCert251_check : scalarCert251.check stableMacroTable = true := by
  norm_num [scalarCert251, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece35, macroPiece36, macroPiece37]
lemma scalarCert252_check : scalarCert252.check stableMacroTable = true := by
  norm_num [scalarCert252, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece36, macroPiece37]
lemma scalarCert253_check : scalarCert253.check stableMacroTable = true := by
  norm_num [scalarCert253, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece36, macroPiece37]
lemma scalarCert254_check : scalarCert254.check stableMacroTable = true := by
  norm_num [scalarCert254, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece24, macroPiece25]
lemma scalarCert255_check : scalarCert255.check stableMacroTable = true := by
  norm_num [scalarCert255, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece36, macroPiece37]
lemma scalarCert256_check : scalarCert256.check stableMacroTable = true := by
  norm_num [scalarCert256, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece36, macroPiece37]
lemma scalarCert257_check : scalarCert257.check stableMacroTable = true := by
  norm_num [scalarCert257, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece36, macroPiece37]
lemma scalarCert258_check : scalarCert258.check stableMacroTable = true := by
  norm_num [scalarCert258, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece36, macroPiece37]
lemma scalarCert259_check : scalarCert259.check stableMacroTable = true := by
  norm_num [scalarCert259, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece36, macroPiece37]
lemma scalarCert260_check : scalarCert260.check stableMacroTable = true := by
  norm_num [scalarCert260, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece36, macroPiece37]
lemma scalarCert261_check : scalarCert261.check stableMacroTable = true := by
  norm_num [scalarCert261, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece36, macroPiece37]
lemma scalarCert262_check : scalarCert262.check stableMacroTable = true := by
  norm_num [scalarCert262, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece36, macroPiece37]
lemma scalarCert263_check : scalarCert263.check stableMacroTable = true := by
  norm_num [scalarCert263, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece35, macroPiece36, macroPiece37, macroPiece38]
lemma scalarCert264_check : scalarCert264.check stableMacroTable = true := by
  norm_num [scalarCert264, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece37, macroPiece38]
lemma scalarCert265_check : scalarCert265.check stableMacroTable = true := by
  norm_num [scalarCert265, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece29, macroPiece30]
lemma scalarCert266_check : scalarCert266.check stableMacroTable = true := by
  norm_num [scalarCert266, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece23, macroPiece24]
lemma scalarCert267_check : scalarCert267.check stableMacroTable = true := by
  norm_num [scalarCert267, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece29, macroPiece30]
lemma scalarCert268_check : scalarCert268.check stableMacroTable = true := by
  norm_num [scalarCert268, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece17, macroPiece18]
lemma scalarCert269_check : scalarCert269.check stableMacroTable = true := by
  norm_num [scalarCert269, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece23, macroPiece24]
lemma scalarCert270_check : scalarCert270.check stableMacroTable = true := by
  norm_num [scalarCert270, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece29, macroPiece30, macroPiece31]
lemma scalarCert271_check : scalarCert271.check stableMacroTable = true := by
  norm_num [scalarCert271, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece36, macroPiece37]
lemma scalarCert272_check : scalarCert272.check stableMacroTable = true := by
  norm_num [scalarCert272, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece36, macroPiece37]
lemma scalarCert273_check : scalarCert273.check stableMacroTable = true := by
  norm_num [scalarCert273, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece36, macroPiece37]
lemma scalarCert274_check : scalarCert274.check stableMacroTable = true := by
  norm_num [scalarCert274, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece17, macroPiece18]
lemma scalarCert275_check : scalarCert275.check stableMacroTable = true := by
  norm_num [scalarCert275, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece23, macroPiece24]
lemma scalarCert276_check : scalarCert276.check stableMacroTable = true := by
  norm_num [scalarCert276, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece30, macroPiece31]
lemma scalarCert277_check : scalarCert277.check stableMacroTable = true := by
  norm_num [scalarCert277, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece8, macroPiece9]
lemma scalarCert278_check : scalarCert278.check stableMacroTable = true := by
  norm_num [scalarCert278, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece30, macroPiece31]
lemma scalarCert279_check : scalarCert279.check stableMacroTable = true := by
  norm_num [scalarCert279, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece41, macroPiece42, macroPiece43]
lemma scalarCert280_check : scalarCert280.check stableMacroTable = true := by
  norm_num [scalarCert280, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece41, macroPiece42, macroPiece43]
lemma scalarCert281_check : scalarCert281.check stableMacroTable = true := by
  norm_num [scalarCert281, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece41, macroPiece42, macroPiece43]
lemma scalarCert282_check : scalarCert282.check stableMacroTable = true := by
  norm_num [scalarCert282, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece41, macroPiece42, macroPiece43]
lemma scalarCert283_check : scalarCert283.check stableMacroTable = true := by
  norm_num [scalarCert283, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece41, macroPiece42, macroPiece43]
lemma scalarCert284_check : scalarCert284.check stableMacroTable = true := by
  norm_num [scalarCert284, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece41, macroPiece42, macroPiece43]
lemma scalarCert285_check : scalarCert285.check stableMacroTable = true := by
  norm_num [scalarCert285, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece41, macroPiece42, macroPiece43]
lemma scalarCert286_check : scalarCert286.check stableMacroTable = true := by
  norm_num [scalarCert286, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece41, macroPiece42, macroPiece43]
lemma scalarCert287_check : scalarCert287.check stableMacroTable = true := by
  norm_num [scalarCert287, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece41, macroPiece42, macroPiece43]
lemma scalarCert288_check : scalarCert288.check stableMacroTable = true := by
  norm_num [scalarCert288, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece41, macroPiece42, macroPiece43]
lemma scalarCert289_check : scalarCert289.check stableMacroTable = true := by
  norm_num [scalarCert289, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece41, macroPiece42, macroPiece43]
lemma scalarCert290_check : scalarCert290.check stableMacroTable = true := by
  norm_num [scalarCert290, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece42, macroPiece43]
lemma scalarCert291_check : scalarCert291.check stableMacroTable = true := by
  norm_num [scalarCert291, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece42, macroPiece43]
lemma scalarCert292_check : scalarCert292.check stableMacroTable = true := by
  norm_num [scalarCert292, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece42, macroPiece43]
lemma scalarCert293_check : scalarCert293.check stableMacroTable = true := by
  norm_num [scalarCert293, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece42, macroPiece43]
lemma scalarCert294_check : scalarCert294.check stableMacroTable = true := by
  norm_num [scalarCert294, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece42, macroPiece43]
lemma scalarCert295_check : scalarCert295.check stableMacroTable = true := by
  norm_num [scalarCert295, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece42, macroPiece43]
lemma scalarCert296_check : scalarCert296.check stableMacroTable = true := by
  norm_num [scalarCert296, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece41, macroPiece42, macroPiece43]
lemma scalarCert297_check : scalarCert297.check stableMacroTable = true := by
  norm_num [scalarCert297, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece42, macroPiece43]
lemma scalarCert298_check : scalarCert298.check stableMacroTable = true := by
  norm_num [scalarCert298, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece41, macroPiece42, macroPiece43]
lemma scalarCert299_check : scalarCert299.check stableMacroTable = true := by
  norm_num [scalarCert299, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece42, macroPiece43]
lemma scalarCert300_check : scalarCert300.check stableMacroTable = true := by
  norm_num [scalarCert300, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece42, macroPiece43]
lemma scalarCert301_check : scalarCert301.check stableMacroTable = true := by
  norm_num [scalarCert301, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece42, macroPiece43]
lemma scalarCert302_check : scalarCert302.check stableMacroTable = true := by
  norm_num [scalarCert302, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece41, macroPiece42, macroPiece43]
lemma scalarCert303_check : scalarCert303.check stableMacroTable = true := by
  norm_num [scalarCert303, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece41, macroPiece42, macroPiece43]
lemma scalarCert304_check : scalarCert304.check stableMacroTable = true := by
  norm_num [scalarCert304, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece42, macroPiece43]
lemma scalarCert305_check : scalarCert305.check stableMacroTable = true := by
  norm_num [scalarCert305, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece42, macroPiece43]
lemma scalarCert306_check : scalarCert306.check stableMacroTable = true := by
  norm_num [scalarCert306, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece42, macroPiece43]
lemma scalarCert307_check : scalarCert307.check stableMacroTable = true := by
  norm_num [scalarCert307, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece42, macroPiece43]
lemma scalarCert308_check : scalarCert308.check stableMacroTable = true := by
  norm_num [scalarCert308, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece41, macroPiece42, macroPiece43]
lemma scalarCert309_check : scalarCert309.check stableMacroTable = true := by
  norm_num [scalarCert309, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece42, macroPiece43]
lemma scalarCert310_check : scalarCert310.check stableMacroTable = true := by
  norm_num [scalarCert310, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece42, macroPiece43]
lemma scalarCert311_check : scalarCert311.check stableMacroTable = true := by
  norm_num [scalarCert311, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece42, macroPiece43]
lemma scalarCert312_check : scalarCert312.check stableMacroTable = true := by
  norm_num [scalarCert312, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece42, macroPiece43]
lemma scalarCert313_check : scalarCert313.check stableMacroTable = true := by
  norm_num [scalarCert313, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece41, macroPiece42, macroPiece43]
lemma scalarCert314_check : scalarCert314.check stableMacroTable = true := by
  norm_num [scalarCert314, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece41, macroPiece42, macroPiece43]
lemma scalarCert315_check : scalarCert315.check stableMacroTable = true := by
  norm_num [scalarCert315, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece41, macroPiece42, macroPiece43]
lemma scalarCert316_check : scalarCert316.check stableMacroTable = true := by
  norm_num [scalarCert316, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece41, macroPiece42, macroPiece43, macroPiece44]
lemma scalarCert317_check : scalarCert317.check stableMacroTable = true := by
  norm_num [scalarCert317, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece41, macroPiece42, macroPiece43]
lemma scalarCert318_check : scalarCert318.check stableMacroTable = true := by
  norm_num [scalarCert318, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece42, macroPiece43]
lemma scalarCert319_check : scalarCert319.check stableMacroTable = true := by
  norm_num [scalarCert319, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece42, macroPiece43]
lemma scalarCert320_check : scalarCert320.check stableMacroTable = true := by
  norm_num [scalarCert320, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece42, macroPiece43]
lemma scalarCert321_check : scalarCert321.check stableMacroTable = true := by
  norm_num [scalarCert321, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece42, macroPiece43]
lemma scalarCert322_check : scalarCert322.check stableMacroTable = true := by
  norm_num [scalarCert322, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece43, macroPiece44]
lemma scalarCert323_check : scalarCert323.check stableMacroTable = true := by
  norm_num [scalarCert323, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece6, macroPiece7]
lemma scalarCert324_check : scalarCert324.check stableMacroTable = true := by
  norm_num [scalarCert324, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece25, macroPiece26, macroPiece27]
lemma scalarCert325_check : scalarCert325.check stableMacroTable = true := by
  norm_num [scalarCert325, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece35, macroPiece36]
lemma scalarCert326_check : scalarCert326.check stableMacroTable = true := by
  norm_num [scalarCert326, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece35, macroPiece36]
lemma scalarCert327_check : scalarCert327.check stableMacroTable = true := by
  norm_num [scalarCert327, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece35, macroPiece36, macroPiece37]
lemma scalarCert328_check : scalarCert328.check stableMacroTable = true := by
  norm_num [scalarCert328, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece19, macroPiece20, macroPiece21]
lemma scalarCert329_check : scalarCert329.check stableMacroTable = true := by
  norm_num [scalarCert329, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece13, macroPiece14]
lemma scalarCert330_check : scalarCert330.check stableMacroTable = true := by
  norm_num [scalarCert330, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece14, macroPiece15]
lemma scalarCert331_check : scalarCert331.check stableMacroTable = true := by
  norm_num [scalarCert331, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece29, macroPiece30]
lemma scalarCert332_check : scalarCert332.check stableMacroTable = true := by
  norm_num [scalarCert332, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece35, macroPiece36, macroPiece37]
lemma scalarCert333_check : scalarCert333.check stableMacroTable = true := by
  norm_num [scalarCert333, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece29, macroPiece30]
lemma scalarCert334_check : scalarCert334.check stableMacroTable = true := by
  norm_num [scalarCert334, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece35, macroPiece36, macroPiece37]
lemma scalarCert335_check : scalarCert335.check stableMacroTable = true := by
  norm_num [scalarCert335, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece29, macroPiece30]
lemma scalarCert336_check : scalarCert336.check stableMacroTable = true := by
  norm_num [scalarCert336, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece17, macroPiece18]
lemma scalarCert337_check : scalarCert337.check stableMacroTable = true := by
  norm_num [scalarCert337, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece29, macroPiece30]
lemma scalarCert338_check : scalarCert338.check stableMacroTable = true := by
  norm_num [scalarCert338, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece35, macroPiece36, macroPiece37]
lemma scalarCert339_check : scalarCert339.check stableMacroTable = true := by
  norm_num [scalarCert339, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece11, macroPiece12]
lemma scalarCert340_check : scalarCert340.check stableMacroTable = true := by
  norm_num [scalarCert340, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece29, macroPiece30]
lemma scalarCert341_check : scalarCert341.check stableMacroTable = true := by
  norm_num [scalarCert341, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece36, macroPiece37]
lemma scalarCert342_check : scalarCert342.check stableMacroTable = true := by
  norm_num [scalarCert342, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece29, macroPiece30]
lemma scalarCert343_check : scalarCert343.check stableMacroTable = true := by
  norm_num [scalarCert343, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece36, macroPiece37]
lemma scalarCert344_check : scalarCert344.check stableMacroTable = true := by
  norm_num [scalarCert344, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece36, macroPiece37]
lemma scalarCert345_check : scalarCert345.check stableMacroTable = true := by
  norm_num [scalarCert345, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece29, macroPiece30]
lemma scalarCert346_check : scalarCert346.check stableMacroTable = true := by
  norm_num [scalarCert346, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece23, macroPiece24]
lemma scalarCert347_check : scalarCert347.check stableMacroTable = true := by
  norm_num [scalarCert347, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece29, macroPiece30]
lemma scalarCert348_check : scalarCert348.check stableMacroTable = true := by
  norm_num [scalarCert348, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece23, macroPiece24]
lemma scalarCert349_check : scalarCert349.check stableMacroTable = true := by
  norm_num [scalarCert349, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece17, macroPiece18]
lemma scalarCert350_check : scalarCert350.check stableMacroTable = true := by
  norm_num [scalarCert350, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece36, macroPiece37]
lemma scalarCert351_check : scalarCert351.check stableMacroTable = true := by
  norm_num [scalarCert351, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece29, macroPiece30]
lemma scalarCert352_check : scalarCert352.check stableMacroTable = true := by
  norm_num [scalarCert352, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece36, macroPiece37]
lemma scalarCert353_check : scalarCert353.check stableMacroTable = true := by
  norm_num [scalarCert353, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece29, macroPiece30]
lemma scalarCert354_check : scalarCert354.check stableMacroTable = true := by
  norm_num [scalarCert354, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece36, macroPiece37]
lemma scalarCert355_check : scalarCert355.check stableMacroTable = true := by
  norm_num [scalarCert355, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece36, macroPiece37]
lemma scalarCert356_check : scalarCert356.check stableMacroTable = true := by
  norm_num [scalarCert356, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece36, macroPiece37]
lemma scalarCert357_check : scalarCert357.check stableMacroTable = true := by
  norm_num [scalarCert357, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece36, macroPiece37]
lemma scalarCert358_check : scalarCert358.check stableMacroTable = true := by
  norm_num [scalarCert358, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece29, macroPiece30]
lemma scalarCert359_check : scalarCert359.check stableMacroTable = true := by
  norm_num [scalarCert359, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece29, macroPiece30, macroPiece31]
lemma scalarCert360_check : scalarCert360.check stableMacroTable = true := by
  norm_num [scalarCert360, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece36, macroPiece37]
lemma scalarCert361_check : scalarCert361.check stableMacroTable = true := by
  norm_num [scalarCert361, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece23, macroPiece24]
lemma scalarCert362_check : scalarCert362.check stableMacroTable = true := by
  norm_num [scalarCert362, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece36, macroPiece37]
lemma scalarCert363_check : scalarCert363.check stableMacroTable = true := by
  norm_num [scalarCert363, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece23, macroPiece24]
lemma scalarCert364_check : scalarCert364.check stableMacroTable = true := by
  norm_num [scalarCert364, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece36, macroPiece37]
lemma scalarCert365_check : scalarCert365.check stableMacroTable = true := by
  norm_num [scalarCert365, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece30, macroPiece31]
lemma scalarCert366_check : scalarCert366.check stableMacroTable = true := by
  norm_num [scalarCert366, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece30, macroPiece31]
lemma scalarCert367_check : scalarCert367.check stableMacroTable = true := by
  norm_num [scalarCert367, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece24, macroPiece25]
lemma scalarCert368_check : scalarCert368.check stableMacroTable = true := by
  norm_num [scalarCert368, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece29, macroPiece30]
lemma scalarCert369_check : scalarCert369.check stableMacroTable = true := by
  norm_num [scalarCert369, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece30, macroPiece31]
lemma scalarCert370_check : scalarCert370.check stableMacroTable = true := by
  norm_num [scalarCert370, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece23, macroPiece24]
lemma scalarCert371_check : scalarCert371.check stableMacroTable = true := by
  norm_num [scalarCert371, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece23, macroPiece24]
lemma scalarCert372_check : scalarCert372.check stableMacroTable = true := by
  norm_num [scalarCert372, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece36, macroPiece37]
lemma scalarCert373_check : scalarCert373.check stableMacroTable = true := by
  norm_num [scalarCert373, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece30, macroPiece31]
lemma scalarCert374_check : scalarCert374.check stableMacroTable = true := by
  norm_num [scalarCert374, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece36, macroPiece37]
lemma scalarCert375_check : scalarCert375.check stableMacroTable = true := by
  norm_num [scalarCert375, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece30, macroPiece31]
lemma scalarCert376_check : scalarCert376.check stableMacroTable = true := by
  norm_num [scalarCert376, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece36, macroPiece37]
lemma scalarCert377_check : scalarCert377.check stableMacroTable = true := by
  norm_num [scalarCert377, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece30, macroPiece31]
lemma scalarCert378_check : scalarCert378.check stableMacroTable = true := by
  norm_num [scalarCert378, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece23, macroPiece24]
lemma scalarCert379_check : scalarCert379.check stableMacroTable = true := by
  norm_num [scalarCert379, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece30, macroPiece31]
lemma scalarCert380_check : scalarCert380.check stableMacroTable = true := by
  norm_num [scalarCert380, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece30, macroPiece31]
lemma scalarCert381_check : scalarCert381.check stableMacroTable = true := by
  norm_num [scalarCert381, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece18, macroPiece19]
lemma scalarCert382_check : scalarCert382.check stableMacroTable = true := by
  norm_num [scalarCert382, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece18, macroPiece19]
lemma scalarCert383_check : scalarCert383.check stableMacroTable = true := by
  norm_num [scalarCert383, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece11, macroPiece12]
lemma scalarCert384_check : scalarCert384.check stableMacroTable = true := by
  norm_num [scalarCert384, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece24, macroPiece25]
lemma scalarCert385_check : scalarCert385.check stableMacroTable = true := by
  norm_num [scalarCert385, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece14, macroPiece15]
lemma scalarCert386_check : scalarCert386.check stableMacroTable = true := by
  norm_num [scalarCert386, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece7, macroPiece8]
lemma scalarCert387_check : scalarCert387.check stableMacroTable = true := by
  norm_num [scalarCert387, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece11, macroPiece12]
lemma scalarCert388_check : scalarCert388.check stableMacroTable = true := by
  norm_num [scalarCert388, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece18, macroPiece19]
lemma scalarCert389_check : scalarCert389.check stableMacroTable = true := by
  norm_num [scalarCert389, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece11, macroPiece12]
lemma scalarCert390_check : scalarCert390.check stableMacroTable = true := by
  norm_num [scalarCert390, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece18, macroPiece19]
lemma scalarCert391_check : scalarCert391.check stableMacroTable = true := by
  norm_num [scalarCert391, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece11, macroPiece12]
lemma scalarCert392_check : scalarCert392.check stableMacroTable = true := by
  norm_num [scalarCert392, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece18, macroPiece19]
lemma scalarCert393_check : scalarCert393.check stableMacroTable = true := by
  norm_num [scalarCert393, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece18, macroPiece19]
lemma scalarCert394_check : scalarCert394.check stableMacroTable = true := by
  norm_num [scalarCert394, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece18, macroPiece19]
lemma scalarCert395_check : scalarCert395.check stableMacroTable = true := by
  norm_num [scalarCert395, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece30, macroPiece31]
lemma scalarCert396_check : scalarCert396.check stableMacroTable = true := by
  norm_num [scalarCert396, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece23, macroPiece24]
lemma scalarCert397_check : scalarCert397.check stableMacroTable = true := by
  norm_num [scalarCert397, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece30, macroPiece31]
lemma scalarCert398_check : scalarCert398.check stableMacroTable = true := by
  norm_num [scalarCert398, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece24, macroPiece25]
lemma scalarCert399_check : scalarCert399.check stableMacroTable = true := by
  norm_num [scalarCert399, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece30, macroPiece31]
lemma scalarCert400_check : scalarCert400.check stableMacroTable = true := by
  norm_num [scalarCert400, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece17, macroPiece18]
lemma scalarCert401_check : scalarCert401.check stableMacroTable = true := by
  norm_num [scalarCert401, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece24, macroPiece25]
lemma scalarCert402_check : scalarCert402.check stableMacroTable = true := by
  norm_num [scalarCert402, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece25, macroPiece26, macroPiece27]
lemma scalarCert403_check : scalarCert403.check stableMacroTable = true := by
  norm_num [scalarCert403, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece19, macroPiece20, macroPiece21]
lemma scalarCert404_check : scalarCert404.check stableMacroTable = true := by
  norm_num [scalarCert404, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece35, macroPiece36]
lemma scalarCert405_check : scalarCert405.check stableMacroTable = true := by
  norm_num [scalarCert405, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece25, macroPiece26, macroPiece27]
lemma scalarCert406_check : scalarCert406.check stableMacroTable = true := by
  norm_num [scalarCert406, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece19, macroPiece20, macroPiece21]
lemma scalarCert407_check : scalarCert407.check stableMacroTable = true := by
  norm_num [scalarCert407, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece20, macroPiece21]
lemma scalarCert408_check : scalarCert408.check stableMacroTable = true := by
  norm_num [scalarCert408, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece26, macroPiece27]
lemma scalarCert409_check : scalarCert409.check stableMacroTable = true := by
  norm_num [scalarCert409, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece25, macroPiece26, macroPiece27]
lemma scalarCert410_check : scalarCert410.check stableMacroTable = true := by
  norm_num [scalarCert410, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece19, macroPiece20, macroPiece21]
lemma scalarCert411_check : scalarCert411.check stableMacroTable = true := by
  norm_num [scalarCert411, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece41, macroPiece42, macroPiece43]
lemma scalarCert412_check : scalarCert412.check stableMacroTable = true := by
  norm_num [scalarCert412, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece41, macroPiece42, macroPiece43]
lemma scalarCert413_check : scalarCert413.check stableMacroTable = true := by
  norm_num [scalarCert413, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece42, macroPiece43]
lemma scalarCert414_check : scalarCert414.check stableMacroTable = true := by
  norm_num [scalarCert414, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece20, macroPiece21]
lemma scalarCert415_check : scalarCert415.check stableMacroTable = true := by
  norm_num [scalarCert415, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece20, macroPiece21]
lemma scalarCert416_check : scalarCert416.check stableMacroTable = true := by
  norm_num [scalarCert416, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece41, macroPiece42, macroPiece43]
lemma scalarCert417_check : scalarCert417.check stableMacroTable = true := by
  norm_num [scalarCert417, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece25, macroPiece26, macroPiece27]
lemma scalarCert418_check : scalarCert418.check stableMacroTable = true := by
  norm_num [scalarCert418, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece19, macroPiece20]
lemma scalarCert419_check : scalarCert419.check stableMacroTable = true := by
  norm_num [scalarCert419, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece19, macroPiece20, macroPiece21]
lemma scalarCert420_check : scalarCert420.check stableMacroTable = true := by
  norm_num [scalarCert420, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece19, macroPiece20]
lemma scalarCert421_check : scalarCert421.check stableMacroTable = true := by
  norm_num [scalarCert421, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece41, macroPiece42, macroPiece43]
lemma scalarCert422_check : scalarCert422.check stableMacroTable = true := by
  norm_num [scalarCert422, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece35, macroPiece36]
lemma scalarCert423_check : scalarCert423.check stableMacroTable = true := by
  norm_num [scalarCert423, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece42, macroPiece43]
lemma scalarCert424_check : scalarCert424.check stableMacroTable = true := by
  norm_num [scalarCert424, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece35, macroPiece36]
lemma scalarCert425_check : scalarCert425.check stableMacroTable = true := by
  norm_num [scalarCert425, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece42, macroPiece43]
lemma scalarCert426_check : scalarCert426.check stableMacroTable = true := by
  norm_num [scalarCert426, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece42, macroPiece43]
lemma scalarCert427_check : scalarCert427.check stableMacroTable = true := by
  norm_num [scalarCert427, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece42, macroPiece43]
lemma scalarCert428_check : scalarCert428.check stableMacroTable = true := by
  norm_num [scalarCert428, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece42, macroPiece43]
lemma scalarCert429_check : scalarCert429.check stableMacroTable = true := by
  norm_num [scalarCert429, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece41, macroPiece42, macroPiece43]
lemma scalarCert430_check : scalarCert430.check stableMacroTable = true := by
  norm_num [scalarCert430, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece41, macroPiece42]
lemma scalarCert431_check : scalarCert431.check stableMacroTable = true := by
  norm_num [scalarCert431, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece35, macroPiece36]
lemma scalarCert432_check : scalarCert432.check stableMacroTable = true := by
  norm_num [scalarCert432, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece41, macroPiece42, macroPiece43]
lemma scalarCert433_check : scalarCert433.check stableMacroTable = true := by
  norm_num [scalarCert433, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece35, macroPiece36]
lemma scalarCert434_check : scalarCert434.check stableMacroTable = true := by
  norm_num [scalarCert434, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece42, macroPiece43]
lemma scalarCert435_check : scalarCert435.check stableMacroTable = true := by
  norm_num [scalarCert435, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece35, macroPiece36]
lemma scalarCert436_check : scalarCert436.check stableMacroTable = true := by
  norm_num [scalarCert436, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece35, macroPiece36]
lemma scalarCert437_check : scalarCert437.check stableMacroTable = true := by
  norm_num [scalarCert437, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece42, macroPiece43]
lemma scalarCert438_check : scalarCert438.check stableMacroTable = true := by
  norm_num [scalarCert438, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece42, macroPiece43]
lemma scalarCert439_check : scalarCert439.check stableMacroTable = true := by
  norm_num [scalarCert439, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece35, macroPiece36]
lemma scalarCert440_check : scalarCert440.check stableMacroTable = true := by
  norm_num [scalarCert440, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece35, macroPiece36]
lemma scalarCert441_check : scalarCert441.check stableMacroTable = true := by
  norm_num [scalarCert441, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece35, macroPiece36]
lemma scalarCert442_check : scalarCert442.check stableMacroTable = true := by
  norm_num [scalarCert442, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece42, macroPiece43]
lemma scalarCert443_check : scalarCert443.check stableMacroTable = true := by
  norm_num [scalarCert443, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece42, macroPiece43]
lemma scalarCert444_check : scalarCert444.check stableMacroTable = true := by
  norm_num [scalarCert444, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece42, macroPiece43]
lemma scalarCert445_check : scalarCert445.check stableMacroTable = true := by
  norm_num [scalarCert445, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece42, macroPiece43]
lemma scalarCert446_check : scalarCert446.check stableMacroTable = true := by
  norm_num [scalarCert446, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece41, macroPiece42]
lemma scalarCert447_check : scalarCert447.check stableMacroTable = true := by
  norm_num [scalarCert447, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece41, macroPiece42, macroPiece43]
lemma scalarCert448_check : scalarCert448.check stableMacroTable = true := by
  norm_num [scalarCert448, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece41, macroPiece42]
lemma scalarCert449_check : scalarCert449.check stableMacroTable = true := by
  norm_num [scalarCert449, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece41, macroPiece42]
lemma scalarCert450_check : scalarCert450.check stableMacroTable = true := by
  norm_num [scalarCert450, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece41, macroPiece42]
lemma scalarCert451_check : scalarCert451.check stableMacroTable = true := by
  norm_num [scalarCert451, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece41, macroPiece42]
lemma scalarCert452_check : scalarCert452.check stableMacroTable = true := by
  norm_num [scalarCert452, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece41, macroPiece42]
lemma scalarCert453_check : scalarCert453.check stableMacroTable = true := by
  norm_num [scalarCert453, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece35, macroPiece36]
lemma scalarCert454_check : scalarCert454.check stableMacroTable = true := by
  norm_num [scalarCert454, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece41, macroPiece42]
lemma scalarCert455_check : scalarCert455.check stableMacroTable = true := by
  norm_num [scalarCert455, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece41, macroPiece42]
lemma scalarCert456_check : scalarCert456.check stableMacroTable = true := by
  norm_num [scalarCert456, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece29, macroPiece30]
lemma scalarCert457_check : scalarCert457.check stableMacroTable = true := by
  norm_num [scalarCert457, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece8, macroPiece9]
lemma scalarCert458_check : scalarCert458.check stableMacroTable = true := by
  norm_num [scalarCert458, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece35, macroPiece36]
lemma scalarCert459_check : scalarCert459.check stableMacroTable = true := by
  norm_num [scalarCert459, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece41, macroPiece42]
lemma scalarCert460_check : scalarCert460.check stableMacroTable = true := by
  norm_num [scalarCert460, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece29, macroPiece30]
lemma scalarCert461_check : scalarCert461.check stableMacroTable = true := by
  norm_num [scalarCert461, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece41, macroPiece42]
lemma scalarCert462_check : scalarCert462.check stableMacroTable = true := by
  norm_num [scalarCert462, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece41, macroPiece42, macroPiece43]
lemma scalarCert463_check : scalarCert463.check stableMacroTable = true := by
  norm_num [scalarCert463, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece41, macroPiece42]
lemma scalarCert464_check : scalarCert464.check stableMacroTable = true := by
  norm_num [scalarCert464, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece42, macroPiece43]
lemma scalarCert465_check : scalarCert465.check stableMacroTable = true := by
  norm_num [scalarCert465, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece30, macroPiece31]
lemma scalarCert466_check : scalarCert466.check stableMacroTable = true := by
  norm_num [scalarCert466, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece35, macroPiece36]
lemma scalarCert467_check : scalarCert467.check stableMacroTable = true := by
  norm_num [scalarCert467, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece23, macroPiece24]
lemma scalarCert468_check : scalarCert468.check stableMacroTable = true := by
  norm_num [scalarCert468, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece35, macroPiece36]
lemma scalarCert469_check : scalarCert469.check stableMacroTable = true := by
  norm_num [scalarCert469, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece42, macroPiece43]
lemma scalarCert470_check : scalarCert470.check stableMacroTable = true := by
  norm_num [scalarCert470, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece42, macroPiece43]
lemma scalarCert471_check : scalarCert471.check stableMacroTable = true := by
  norm_num [scalarCert471, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece35, macroPiece36]
lemma scalarCert472_check : scalarCert472.check stableMacroTable = true := by
  norm_num [scalarCert472, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece42, macroPiece43]
lemma scalarCert473_check : scalarCert473.check stableMacroTable = true := by
  norm_num [scalarCert473, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece35, macroPiece36]
lemma scalarCert474_check : scalarCert474.check stableMacroTable = true := by
  norm_num [scalarCert474, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece24, macroPiece25]
lemma scalarCert475_check : scalarCert475.check stableMacroTable = true := by
  norm_num [scalarCert475, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece35, macroPiece36]
lemma scalarCert476_check : scalarCert476.check stableMacroTable = true := by
  norm_num [scalarCert476, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece42, macroPiece43]
lemma scalarCert477_check : scalarCert477.check stableMacroTable = true := by
  norm_num [scalarCert477, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece42, macroPiece43]
lemma scalarCert478_check : scalarCert478.check stableMacroTable = true := by
  norm_num [scalarCert478, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece35, macroPiece36]
lemma scalarCert479_check : scalarCert479.check stableMacroTable = true := by
  norm_num [scalarCert479, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece23, macroPiece24]
lemma scalarCert480_check : scalarCert480.check stableMacroTable = true := by
  norm_num [scalarCert480, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece35, macroPiece36]
lemma scalarCert481_check : scalarCert481.check stableMacroTable = true := by
  norm_num [scalarCert481, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece23, macroPiece24]
lemma scalarCert482_check : scalarCert482.check stableMacroTable = true := by
  norm_num [scalarCert482, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece35, macroPiece36]
lemma scalarCert483_check : scalarCert483.check stableMacroTable = true := by
  norm_num [scalarCert483, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece35, macroPiece36]
lemma scalarCert484_check : scalarCert484.check stableMacroTable = true := by
  norm_num [scalarCert484, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece42, macroPiece43]
lemma scalarCert485_check : scalarCert485.check stableMacroTable = true := by
  norm_num [scalarCert485, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece42, macroPiece43]
lemma scalarCert486_check : scalarCert486.check stableMacroTable = true := by
  norm_num [scalarCert486, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece30, macroPiece31]
lemma scalarCert487_check : scalarCert487.check stableMacroTable = true := by
  norm_num [scalarCert487, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece35, macroPiece36]
lemma scalarCert488_check : scalarCert488.check stableMacroTable = true := by
  norm_num [scalarCert488, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece42, macroPiece43]
lemma scalarCert489_check : scalarCert489.check stableMacroTable = true := by
  norm_num [scalarCert489, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece42, macroPiece43]
lemma scalarCert490_check : scalarCert490.check stableMacroTable = true := by
  norm_num [scalarCert490, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece30, macroPiece31]
lemma scalarCert491_check : scalarCert491.check stableMacroTable = true := by
  norm_num [scalarCert491, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece35, macroPiece36]
lemma scalarCert492_check : scalarCert492.check stableMacroTable = true := by
  norm_num [scalarCert492, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece35, macroPiece36]
lemma scalarCert493_check : scalarCert493.check stableMacroTable = true := by
  norm_num [scalarCert493, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece42, macroPiece43]
lemma scalarCert494_check : scalarCert494.check stableMacroTable = true := by
  norm_num [scalarCert494, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece42, macroPiece43]
lemma scalarCert495_check : scalarCert495.check stableMacroTable = true := by
  norm_num [scalarCert495, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece36, macroPiece37]
lemma scalarCert496_check : scalarCert496.check stableMacroTable = true := by
  norm_num [scalarCert496, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece36, macroPiece37]
lemma scalarCert497_check : scalarCert497.check stableMacroTable = true := by
  norm_num [scalarCert497, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece36, macroPiece37]
lemma scalarCert498_check : scalarCert498.check stableMacroTable = true := by
  norm_num [scalarCert498, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece36, macroPiece37]
lemma scalarCert499_check : scalarCert499.check stableMacroTable = true := by
  norm_num [scalarCert499, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece47, macroPiece48, macroPiece49]
lemma scalarCert500_check : scalarCert500.check stableMacroTable = true := by
  norm_num [scalarCert500, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece47, macroPiece48, macroPiece49]
lemma scalarCert501_check : scalarCert501.check stableMacroTable = true := by
  norm_num [scalarCert501, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece47, macroPiece48, macroPiece49]
lemma scalarCert502_check : scalarCert502.check stableMacroTable = true := by
  norm_num [scalarCert502, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece47, macroPiece48, macroPiece49]
lemma scalarCert503_check : scalarCert503.check stableMacroTable = true := by
  norm_num [scalarCert503, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece47, macroPiece48, macroPiece49]
lemma scalarCert504_check : scalarCert504.check stableMacroTable = true := by
  norm_num [scalarCert504, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece47, macroPiece48, macroPiece49]
lemma scalarCert505_check : scalarCert505.check stableMacroTable = true := by
  norm_num [scalarCert505, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece47, macroPiece48, macroPiece49]
lemma scalarCert506_check : scalarCert506.check stableMacroTable = true := by
  norm_num [scalarCert506, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece48, macroPiece49]
lemma scalarCert507_check : scalarCert507.check stableMacroTable = true := by
  norm_num [scalarCert507, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece47, macroPiece48]
lemma scalarCert508_check : scalarCert508.check stableMacroTable = true := by
  norm_num [scalarCert508, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece47, macroPiece48]
lemma scalarCert509_check : scalarCert509.check stableMacroTable = true := by
  norm_num [scalarCert509, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece47, macroPiece48]
lemma scalarCert510_check : scalarCert510.check stableMacroTable = true := by
  norm_num [scalarCert510, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece47, macroPiece48]
lemma scalarCert511_check : scalarCert511.check stableMacroTable = true := by
  norm_num [scalarCert511, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece47, macroPiece48, macroPiece49]
lemma scalarCert512_check : scalarCert512.check stableMacroTable = true := by
  norm_num [scalarCert512, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece47, macroPiece48, macroPiece49]
lemma scalarCert513_check : scalarCert513.check stableMacroTable = true := by
  norm_num [scalarCert513, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece47, macroPiece48, macroPiece49]
lemma scalarCert514_check : scalarCert514.check stableMacroTable = true := by
  norm_num [scalarCert514, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece47, macroPiece48]
lemma scalarCert515_check : scalarCert515.check stableMacroTable = true := by
  norm_num [scalarCert515, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece47, macroPiece48]
lemma scalarCert516_check : scalarCert516.check stableMacroTable = true := by
  norm_num [scalarCert516, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece47, macroPiece48]
lemma scalarCert517_check : scalarCert517.check stableMacroTable = true := by
  norm_num [scalarCert517, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece29, macroPiece30]
lemma scalarCert518_check : scalarCert518.check stableMacroTable = true := by
  norm_num [scalarCert518, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece47, macroPiece48, macroPiece49]
lemma scalarCert519_check : scalarCert519.check stableMacroTable = true := by
  norm_num [scalarCert519, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece47, macroPiece48, macroPiece49]
lemma scalarCert520_check : scalarCert520.check stableMacroTable = true := by
  norm_num [scalarCert520, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece47, macroPiece48, macroPiece49]
lemma scalarCert521_check : scalarCert521.check stableMacroTable = true := by
  norm_num [scalarCert521, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece48, macroPiece49]
lemma scalarCert522_check : scalarCert522.check stableMacroTable = true := by
  norm_num [scalarCert522, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece47, macroPiece48, macroPiece49]
lemma scalarCert523_check : scalarCert523.check stableMacroTable = true := by
  norm_num [scalarCert523, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece48, macroPiece49]
lemma scalarCert524_check : scalarCert524.check stableMacroTable = true := by
  norm_num [scalarCert524, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece48, macroPiece49]
lemma scalarCert525_check : scalarCert525.check stableMacroTable = true := by
  norm_num [scalarCert525, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece48, macroPiece49]
lemma scalarCert526_check : scalarCert526.check stableMacroTable = true := by
  norm_num [scalarCert526, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece48, macroPiece49]
lemma scalarCert527_check : scalarCert527.check stableMacroTable = true := by
  norm_num [scalarCert527, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece48, macroPiece49]
lemma scalarCert528_check : scalarCert528.check stableMacroTable = true := by
  norm_num [scalarCert528, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece48, macroPiece49]
lemma scalarCert529_check : scalarCert529.check stableMacroTable = true := by
  norm_num [scalarCert529, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece47, macroPiece48, macroPiece49]
lemma scalarCert530_check : scalarCert530.check stableMacroTable = true := by
  norm_num [scalarCert530, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece48, macroPiece49]
lemma scalarCert531_check : scalarCert531.check stableMacroTable = true := by
  norm_num [scalarCert531, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece48, macroPiece49]
lemma scalarCert532_check : scalarCert532.check stableMacroTable = true := by
  norm_num [scalarCert532, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece47, macroPiece48, macroPiece49]
lemma scalarCert533_check : scalarCert533.check stableMacroTable = true := by
  norm_num [scalarCert533, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece47, macroPiece48, macroPiece49]
lemma scalarCert534_check : scalarCert534.check stableMacroTable = true := by
  norm_num [scalarCert534, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece48, macroPiece49]
lemma scalarCert535_check : scalarCert535.check stableMacroTable = true := by
  norm_num [scalarCert535, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece48, macroPiece49]
lemma scalarCert536_check : scalarCert536.check stableMacroTable = true := by
  norm_num [scalarCert536, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece48, macroPiece49]
lemma scalarCert537_check : scalarCert537.check stableMacroTable = true := by
  norm_num [scalarCert537, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece48, macroPiece49]
lemma scalarCert538_check : scalarCert538.check stableMacroTable = true := by
  norm_num [scalarCert538, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece48, macroPiece49]
lemma scalarCert539_check : scalarCert539.check stableMacroTable = true := by
  norm_num [scalarCert539, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece48, macroPiece49]
lemma scalarCert540_check : scalarCert540.check stableMacroTable = true := by
  norm_num [scalarCert540, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece48, macroPiece49]
lemma scalarCert541_check : scalarCert541.check stableMacroTable = true := by
  norm_num [scalarCert541, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece48, macroPiece49]
lemma scalarCert542_check : scalarCert542.check stableMacroTable = true := by
  norm_num [scalarCert542, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece48, macroPiece49]
lemma scalarCert543_check : scalarCert543.check stableMacroTable = true := by
  norm_num [scalarCert543, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece48, macroPiece49]
lemma scalarCert544_check : scalarCert544.check stableMacroTable = true := by
  norm_num [scalarCert544, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece48, macroPiece49, macroPiece50, macroPiece51]
lemma scalarCert545_check : scalarCert545.check stableMacroTable = true := by
  norm_num [scalarCert545, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece25, macroPiece26, macroPiece27]
lemma scalarCert546_check : scalarCert546.check stableMacroTable = true := by
  norm_num [scalarCert546, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece29, macroPiece30]
lemma scalarCert547_check : scalarCert547.check stableMacroTable = true := by
  norm_num [scalarCert547, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece36, macroPiece37]
lemma scalarCert548_check : scalarCert548.check stableMacroTable = true := by
  norm_num [scalarCert548, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece36, macroPiece37]
lemma scalarCert549_check : scalarCert549.check stableMacroTable = true := by
  norm_num [scalarCert549, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece36, macroPiece37]
lemma scalarCert550_check : scalarCert550.check stableMacroTable = true := by
  norm_num [scalarCert550, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece23, macroPiece24]
lemma scalarCert551_check : scalarCert551.check stableMacroTable = true := by
  norm_num [scalarCert551, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece24, macroPiece25]
lemma scalarCert552_check : scalarCert552.check stableMacroTable = true := by
  norm_num [scalarCert552, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece41, macroPiece42]
lemma scalarCert553_check : scalarCert553.check stableMacroTable = true := by
  norm_num [scalarCert553, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece30, macroPiece31]
lemma scalarCert554_check : scalarCert554.check stableMacroTable = true := by
  norm_num [scalarCert554, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece30, macroPiece31]
lemma scalarCert555_check : scalarCert555.check stableMacroTable = true := by
  norm_num [scalarCert555, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece42, macroPiece43]
lemma scalarCert556_check : scalarCert556.check stableMacroTable = true := by
  norm_num [scalarCert556, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece42, macroPiece43]
lemma scalarCert557_check : scalarCert557.check stableMacroTable = true := by
  norm_num [scalarCert557, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece26, macroPiece27]
lemma scalarCert558_check : scalarCert558.check stableMacroTable = true := by
  norm_num [scalarCert558, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece20, macroPiece21]
lemma scalarCert559_check : scalarCert559.check stableMacroTable = true := by
  norm_num [scalarCert559, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece20, macroPiece21]
lemma scalarCert560_check : scalarCert560.check stableMacroTable = true := by
  norm_num [scalarCert560, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece26, macroPiece27]
lemma scalarCert561_check : scalarCert561.check stableMacroTable = true := by
  norm_num [scalarCert561, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece48, macroPiece49]
lemma scalarCert562_check : scalarCert562.check stableMacroTable = true := by
  norm_num [scalarCert562, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece48, macroPiece49]
lemma scalarCert563_check : scalarCert563.check stableMacroTable = true := by
  norm_num [scalarCert563, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece25, macroPiece26]
lemma scalarCert564_check : scalarCert564.check stableMacroTable = true := by
  norm_num [scalarCert564, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece25, macroPiece26, macroPiece27]
lemma scalarCert565_check : scalarCert565.check stableMacroTable = true := by
  norm_num [scalarCert565, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece25, macroPiece26]
lemma scalarCert566_check : scalarCert566.check stableMacroTable = true := by
  norm_num [scalarCert566, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece25, macroPiece26]
lemma scalarCert567_check : scalarCert567.check stableMacroTable = true := by
  norm_num [scalarCert567, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece25, macroPiece26, macroPiece27]
lemma scalarCert568_check : scalarCert568.check stableMacroTable = true := by
  norm_num [scalarCert568, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece26, macroPiece27]
lemma scalarCert569_check : scalarCert569.check stableMacroTable = true := by
  norm_num [scalarCert569, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece26, macroPiece27]
lemma scalarCert570_check : scalarCert570.check stableMacroTable = true := by
  norm_num [scalarCert570, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece26, macroPiece27]
lemma scalarCert571_check : scalarCert571.check stableMacroTable = true := by
  norm_num [scalarCert571, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece42, macroPiece43]
lemma scalarCert572_check : scalarCert572.check stableMacroTable = true := by
  norm_num [scalarCert572, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece42, macroPiece43]
lemma scalarCert573_check : scalarCert573.check stableMacroTable = true := by
  norm_num [scalarCert573, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece23, macroPiece24]
lemma scalarCert574_check : scalarCert574.check stableMacroTable = true := by
  norm_num [scalarCert574, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece35, macroPiece36]
lemma scalarCert575_check : scalarCert575.check stableMacroTable = true := by
  norm_num [scalarCert575, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece42, macroPiece43]
lemma scalarCert576_check : scalarCert576.check stableMacroTable = true := by
  norm_num [scalarCert576, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece23, macroPiece24]
lemma scalarCert577_check : scalarCert577.check stableMacroTable = true := by
  norm_num [scalarCert577, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece35, macroPiece36]
lemma scalarCert578_check : scalarCert578.check stableMacroTable = true := by
  norm_num [scalarCert578, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece42, macroPiece43]
lemma scalarCert579_check : scalarCert579.check stableMacroTable = true := by
  norm_num [scalarCert579, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece42, macroPiece43]
lemma scalarCert580_check : scalarCert580.check stableMacroTable = true := by
  norm_num [scalarCert580, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece42, macroPiece43]
lemma scalarCert581_check : scalarCert581.check stableMacroTable = true := by
  norm_num [scalarCert581, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece41, macroPiece42]
lemma scalarCert582_check : scalarCert582.check stableMacroTable = true := by
  norm_num [scalarCert582, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece35, macroPiece36]
lemma scalarCert583_check : scalarCert583.check stableMacroTable = true := by
  norm_num [scalarCert583, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece35, macroPiece36]
lemma scalarCert584_check : scalarCert584.check stableMacroTable = true := by
  norm_num [scalarCert584, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece35, macroPiece36]
lemma scalarCert585_check : scalarCert585.check stableMacroTable = true := by
  norm_num [scalarCert585, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece42, macroPiece43]
lemma scalarCert586_check : scalarCert586.check stableMacroTable = true := by
  norm_num [scalarCert586, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece17, macroPiece18]
lemma scalarCert587_check : scalarCert587.check stableMacroTable = true := by
  norm_num [scalarCert587, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece42, macroPiece43]
lemma scalarCert588_check : scalarCert588.check stableMacroTable = true := by
  norm_num [scalarCert588, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece42, macroPiece43]
lemma scalarCert589_check : scalarCert589.check stableMacroTable = true := by
  norm_num [scalarCert589, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece42, macroPiece43]
lemma scalarCert590_check : scalarCert590.check stableMacroTable = true := by
  norm_num [scalarCert590, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece29, macroPiece30]
lemma scalarCert591_check : scalarCert591.check stableMacroTable = true := by
  norm_num [scalarCert591, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece36, macroPiece37]
lemma scalarCert592_check : scalarCert592.check stableMacroTable = true := by
  norm_num [scalarCert592, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece36, macroPiece37]
lemma scalarCert593_check : scalarCert593.check stableMacroTable = true := by
  norm_num [scalarCert593, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece29, macroPiece30]
lemma scalarCert594_check : scalarCert594.check stableMacroTable = true := by
  norm_num [scalarCert594, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece41, macroPiece42]
lemma scalarCert595_check : scalarCert595.check stableMacroTable = true := by
  norm_num [scalarCert595, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece26, macroPiece27]
lemma scalarCert596_check : scalarCert596.check stableMacroTable = true := by
  norm_num [scalarCert596, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece26, macroPiece27]
lemma scalarCert597_check : scalarCert597.check stableMacroTable = true := by
  norm_num [scalarCert597, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece41, macroPiece42]
lemma scalarCert598_check : scalarCert598.check stableMacroTable = true := by
  norm_num [scalarCert598, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece41, macroPiece42]
lemma scalarCert599_check : scalarCert599.check stableMacroTable = true := by
  norm_num [scalarCert599, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece41, macroPiece42]
lemma scalarCert600_check : scalarCert600.check stableMacroTable = true := by
  norm_num [scalarCert600, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece41, macroPiece42]
lemma scalarCert601_check : scalarCert601.check stableMacroTable = true := by
  norm_num [scalarCert601, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece26, macroPiece27]
lemma scalarCert602_check : scalarCert602.check stableMacroTable = true := by
  norm_num [scalarCert602, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece41, macroPiece42]
lemma scalarCert603_check : scalarCert603.check stableMacroTable = true := by
  norm_num [scalarCert603, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece41, macroPiece42]
lemma scalarCert604_check : scalarCert604.check stableMacroTable = true := by
  norm_num [scalarCert604, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece41, macroPiece42]
lemma scalarCert605_check : scalarCert605.check stableMacroTable = true := by
  norm_num [scalarCert605, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece41, macroPiece42]
lemma scalarCert606_check : scalarCert606.check stableMacroTable = true := by
  norm_num [scalarCert606, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece41, macroPiece42]
lemma scalarCert607_check : scalarCert607.check stableMacroTable = true := by
  norm_num [scalarCert607, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece41, macroPiece42]
lemma scalarCert608_check : scalarCert608.check stableMacroTable = true := by
  norm_num [scalarCert608, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece41, macroPiece42]
lemma scalarCert609_check : scalarCert609.check stableMacroTable = true := by
  norm_num [scalarCert609, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece41, macroPiece42]
lemma scalarCert610_check : scalarCert610.check stableMacroTable = true := by
  norm_num [scalarCert610, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece23, macroPiece24]
lemma scalarCert611_check : scalarCert611.check stableMacroTable = true := by
  norm_num [scalarCert611, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece41, macroPiece42]
lemma scalarCert612_check : scalarCert612.check stableMacroTable = true := by
  norm_num [scalarCert612, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece41, macroPiece42]
lemma scalarCert613_check : scalarCert613.check stableMacroTable = true := by
  norm_num [scalarCert613, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece23, macroPiece24]
lemma scalarCert614_check : scalarCert614.check stableMacroTable = true := by
  norm_num [scalarCert614, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece8, macroPiece9]
lemma scalarCert615_check : scalarCert615.check stableMacroTable = true := by
  norm_num [scalarCert615, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece23, macroPiece24]
lemma scalarCert616_check : scalarCert616.check stableMacroTable = true := by
  norm_num [scalarCert616, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece23, macroPiece24]
lemma scalarCert617_check : scalarCert617.check stableMacroTable = true := by
  norm_num [scalarCert617, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece23, macroPiece24]
lemma scalarCert618_check : scalarCert618.check stableMacroTable = true := by
  norm_num [scalarCert618, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece35, macroPiece36]
lemma scalarCert619_check : scalarCert619.check stableMacroTable = true := by
  norm_num [scalarCert619, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece23, macroPiece24]
lemma scalarCert620_check : scalarCert620.check stableMacroTable = true := by
  norm_num [scalarCert620, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece35, macroPiece36]
lemma scalarCert621_check : scalarCert621.check stableMacroTable = true := by
  norm_num [scalarCert621, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece23, macroPiece24]
lemma scalarCert622_check : scalarCert622.check stableMacroTable = true := by
  norm_num [scalarCert622, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece35, macroPiece36]
lemma scalarCert623_check : scalarCert623.check stableMacroTable = true := by
  norm_num [scalarCert623, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece23, macroPiece24]
lemma scalarCert624_check : scalarCert624.check stableMacroTable = true := by
  norm_num [scalarCert624, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece42, macroPiece43]
lemma scalarCert625_check : scalarCert625.check stableMacroTable = true := by
  norm_num [scalarCert625, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece42, macroPiece43]
lemma scalarCert626_check : scalarCert626.check stableMacroTable = true := by
  norm_num [scalarCert626, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece42, macroPiece43]
lemma scalarCert627_check : scalarCert627.check stableMacroTable = true := by
  norm_num [scalarCert627, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece42, macroPiece43]
lemma scalarCert628_check : scalarCert628.check stableMacroTable = true := by
  norm_num [scalarCert628, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece23, macroPiece24]
lemma scalarCert629_check : scalarCert629.check stableMacroTable = true := by
  norm_num [scalarCert629, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece42, macroPiece43]
lemma scalarCert630_check : scalarCert630.check stableMacroTable = true := by
  norm_num [scalarCert630, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece35, macroPiece36]
lemma scalarCert631_check : scalarCert631.check stableMacroTable = true := by
  norm_num [scalarCert631, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece42, macroPiece43]
lemma scalarCert632_check : scalarCert632.check stableMacroTable = true := by
  norm_num [scalarCert632, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece23, macroPiece24]
lemma scalarCert633_check : scalarCert633.check stableMacroTable = true := by
  norm_num [scalarCert633, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece35, macroPiece36]
lemma scalarCert634_check : scalarCert634.check stableMacroTable = true := by
  norm_num [scalarCert634, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece35, macroPiece36]
lemma scalarCert635_check : scalarCert635.check stableMacroTable = true := by
  norm_num [scalarCert635, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece35, macroPiece36]
lemma scalarCert636_check : scalarCert636.check stableMacroTable = true := by
  norm_num [scalarCert636, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece35, macroPiece36]
lemma scalarCert637_check : scalarCert637.check stableMacroTable = true := by
  norm_num [scalarCert637, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece42, macroPiece43]
lemma scalarCert638_check : scalarCert638.check stableMacroTable = true := by
  norm_num [scalarCert638, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece42, macroPiece43]
lemma scalarCert639_check : scalarCert639.check stableMacroTable = true := by
  norm_num [scalarCert639, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece42, macroPiece43]
lemma scalarCert640_check : scalarCert640.check stableMacroTable = true := by
  norm_num [scalarCert640, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece41, macroPiece42]
lemma scalarCert641_check : scalarCert641.check stableMacroTable = true := by
  norm_num [scalarCert641, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece41, macroPiece42]
lemma scalarCert642_check : scalarCert642.check stableMacroTable = true := by
  norm_num [scalarCert642, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece23, macroPiece24]
lemma scalarCert643_check : scalarCert643.check stableMacroTable = true := by
  norm_num [scalarCert643, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece23, macroPiece24]
lemma scalarCert644_check : scalarCert644.check stableMacroTable = true := by
  norm_num [scalarCert644, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece23, macroPiece24]
lemma scalarCert645_check : scalarCert645.check stableMacroTable = true := by
  norm_num [scalarCert645, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece35, macroPiece36]
lemma scalarCert646_check : scalarCert646.check stableMacroTable = true := by
  norm_num [scalarCert646, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece35, macroPiece36]
lemma scalarCert647_check : scalarCert647.check stableMacroTable = true := by
  norm_num [scalarCert647, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece35, macroPiece36]
lemma scalarCert648_check : scalarCert648.check stableMacroTable = true := by
  norm_num [scalarCert648, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece23, macroPiece24]
lemma scalarCert649_check : scalarCert649.check stableMacroTable = true := by
  norm_num [scalarCert649, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece23, macroPiece24]
lemma scalarCert650_check : scalarCert650.check stableMacroTable = true := by
  norm_num [scalarCert650, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece35, macroPiece36]
lemma scalarCert651_check : scalarCert651.check stableMacroTable = true := by
  norm_num [scalarCert651, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece35, macroPiece36]
lemma scalarCert652_check : scalarCert652.check stableMacroTable = true := by
  norm_num [scalarCert652, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece35, macroPiece36]
lemma scalarCert653_check : scalarCert653.check stableMacroTable = true := by
  norm_num [scalarCert653, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece35, macroPiece36]
lemma scalarCert654_check : scalarCert654.check stableMacroTable = true := by
  norm_num [scalarCert654, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece35, macroPiece36]
lemma scalarCert655_check : scalarCert655.check stableMacroTable = true := by
  norm_num [scalarCert655, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece35, macroPiece36]
lemma scalarCert656_check : scalarCert656.check stableMacroTable = true := by
  norm_num [scalarCert656, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece35, macroPiece36]
lemma scalarCert657_check : scalarCert657.check stableMacroTable = true := by
  norm_num [scalarCert657, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece42, macroPiece43]
lemma scalarCert658_check : scalarCert658.check stableMacroTable = true := by
  norm_num [scalarCert658, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece42, macroPiece43]
lemma scalarCert659_check : scalarCert659.check stableMacroTable = true := by
  norm_num [scalarCert659, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece42, macroPiece43]
lemma scalarCert660_check : scalarCert660.check stableMacroTable = true := by
  norm_num [scalarCert660, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece42, macroPiece43]
lemma scalarCert661_check : scalarCert661.check stableMacroTable = true := by
  norm_num [scalarCert661, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece42, macroPiece43]
lemma scalarCert662_check : scalarCert662.check stableMacroTable = true := by
  norm_num [scalarCert662, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece42, macroPiece43]
lemma scalarCert663_check : scalarCert663.check stableMacroTable = true := by
  norm_num [scalarCert663, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece42, macroPiece43]
lemma scalarCert664_check : scalarCert664.check stableMacroTable = true := by
  norm_num [scalarCert664, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece42, macroPiece43]
lemma scalarCert665_check : scalarCert665.check stableMacroTable = true := by
  norm_num [scalarCert665, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece35, macroPiece36]
lemma scalarCert666_check : scalarCert666.check stableMacroTable = true := by
  norm_num [scalarCert666, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece35, macroPiece36]
lemma scalarCert667_check : scalarCert667.check stableMacroTable = true := by
  norm_num [scalarCert667, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece35, macroPiece36]
lemma scalarCert668_check : scalarCert668.check stableMacroTable = true := by
  norm_num [scalarCert668, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece42, macroPiece43]
lemma scalarCert669_check : scalarCert669.check stableMacroTable = true := by
  norm_num [scalarCert669, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece42, macroPiece43]
lemma scalarCert670_check : scalarCert670.check stableMacroTable = true := by
  norm_num [scalarCert670, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece42, macroPiece43]
lemma scalarCert671_check : scalarCert671.check stableMacroTable = true := by
  norm_num [scalarCert671, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece24, macroPiece25]
lemma scalarCert672_check : scalarCert672.check stableMacroTable = true := by
  norm_num [scalarCert672, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece24, macroPiece25]
lemma scalarCert673_check : scalarCert673.check stableMacroTable = true := by
  norm_num [scalarCert673, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece24, macroPiece25]
lemma scalarCert674_check : scalarCert674.check stableMacroTable = true := by
  norm_num [scalarCert674, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece42, macroPiece43]
lemma scalarCert675_check : scalarCert675.check stableMacroTable = true := by
  norm_num [scalarCert675, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece17, macroPiece18]
lemma scalarCert676_check : scalarCert676.check stableMacroTable = true := by
  norm_num [scalarCert676, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece17, macroPiece18]
lemma scalarCert677_check : scalarCert677.check stableMacroTable = true := by
  norm_num [scalarCert677, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece17, macroPiece18]
lemma scalarCert678_check : scalarCert678.check stableMacroTable = true := by
  norm_num [scalarCert678, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece36, macroPiece37]
lemma scalarCert679_check : scalarCert679.check stableMacroTable = true := by
  norm_num [scalarCert679, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece36, macroPiece37]
lemma scalarCert680_check : scalarCert680.check stableMacroTable = true := by
  norm_num [scalarCert680, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece42, macroPiece43]
lemma scalarCert681_check : scalarCert681.check stableMacroTable = true := by
  norm_num [scalarCert681, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece24, macroPiece25]
lemma scalarCert682_check : scalarCert682.check stableMacroTable = true := by
  norm_num [scalarCert682, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece42, macroPiece43]
lemma scalarCert683_check : scalarCert683.check stableMacroTable = true := by
  norm_num [scalarCert683, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece24, macroPiece25]
lemma scalarCert684_check : scalarCert684.check stableMacroTable = true := by
  norm_num [scalarCert684, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece24, macroPiece25]
lemma scalarCert685_check : scalarCert685.check stableMacroTable = true := by
  norm_num [scalarCert685, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece23, macroPiece24]
lemma scalarCert686_check : scalarCert686.check stableMacroTable = true := by
  norm_num [scalarCert686, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece23, macroPiece24]
lemma scalarCert687_check : scalarCert687.check stableMacroTable = true := by
  norm_num [scalarCert687, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece35, macroPiece36]
lemma scalarCert688_check : scalarCert688.check stableMacroTable = true := by
  norm_num [scalarCert688, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece35, macroPiece36]
lemma scalarCert689_check : scalarCert689.check stableMacroTable = true := by
  norm_num [scalarCert689, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece23, macroPiece24]
lemma scalarCert690_check : scalarCert690.check stableMacroTable = true := by
  norm_num [scalarCert690, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece23, macroPiece24]
lemma scalarCert691_check : scalarCert691.check stableMacroTable = true := by
  norm_num [scalarCert691, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece35, macroPiece36]
lemma scalarCert692_check : scalarCert692.check stableMacroTable = true := by
  norm_num [scalarCert692, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece23, macroPiece24]
lemma scalarCert693_check : scalarCert693.check stableMacroTable = true := by
  norm_num [scalarCert693, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece23, macroPiece24]
lemma scalarCert694_check : scalarCert694.check stableMacroTable = true := by
  norm_num [scalarCert694, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece35, macroPiece36]
lemma scalarCert695_check : scalarCert695.check stableMacroTable = true := by
  norm_num [scalarCert695, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece35, macroPiece36]
lemma scalarCert696_check : scalarCert696.check stableMacroTable = true := by
  norm_num [scalarCert696, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece35, macroPiece36]
lemma scalarCert697_check : scalarCert697.check stableMacroTable = true := by
  norm_num [scalarCert697, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece35, macroPiece36]
lemma scalarCert698_check : scalarCert698.check stableMacroTable = true := by
  norm_num [scalarCert698, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece35, macroPiece36]
lemma scalarCert699_check : scalarCert699.check stableMacroTable = true := by
  norm_num [scalarCert699, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece35, macroPiece36]
lemma scalarCert700_check : scalarCert700.check stableMacroTable = true := by
  norm_num [scalarCert700, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece35, macroPiece36]
lemma scalarCert701_check : scalarCert701.check stableMacroTable = true := by
  norm_num [scalarCert701, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece35, macroPiece36]
lemma scalarCert702_check : scalarCert702.check stableMacroTable = true := by
  norm_num [scalarCert702, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece42, macroPiece43]
lemma scalarCert703_check : scalarCert703.check stableMacroTable = true := by
  norm_num [scalarCert703, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece35, macroPiece36]
lemma scalarCert704_check : scalarCert704.check stableMacroTable = true := by
  norm_num [scalarCert704, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece42, macroPiece43]
lemma scalarCert705_check : scalarCert705.check stableMacroTable = true := by
  norm_num [scalarCert705, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece35, macroPiece36]
lemma scalarCert706_check : scalarCert706.check stableMacroTable = true := by
  norm_num [scalarCert706, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece35, macroPiece36]
lemma scalarCert707_check : scalarCert707.check stableMacroTable = true := by
  norm_num [scalarCert707, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece35, macroPiece36]
lemma scalarCert708_check : scalarCert708.check stableMacroTable = true := by
  norm_num [scalarCert708, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece35, macroPiece36]
lemma scalarCert709_check : scalarCert709.check stableMacroTable = true := by
  norm_num [scalarCert709, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece35, macroPiece36]
lemma scalarCert710_check : scalarCert710.check stableMacroTable = true := by
  norm_num [scalarCert710, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece42, macroPiece43]
lemma scalarCert711_check : scalarCert711.check stableMacroTable = true := by
  norm_num [scalarCert711, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece42, macroPiece43]
lemma scalarCert712_check : scalarCert712.check stableMacroTable = true := by
  norm_num [scalarCert712, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece42, macroPiece43]
lemma scalarCert713_check : scalarCert713.check stableMacroTable = true := by
  norm_num [scalarCert713, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece42, macroPiece43]
lemma scalarCert714_check : scalarCert714.check stableMacroTable = true := by
  norm_num [scalarCert714, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece42, macroPiece43]
lemma scalarCert715_check : scalarCert715.check stableMacroTable = true := by
  norm_num [scalarCert715, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece35, macroPiece36]
lemma scalarCert716_check : scalarCert716.check stableMacroTable = true := by
  norm_num [scalarCert716, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece42, macroPiece43]
lemma scalarCert717_check : scalarCert717.check stableMacroTable = true := by
  norm_num [scalarCert717, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece42, macroPiece43]
lemma scalarCert718_check : scalarCert718.check stableMacroTable = true := by
  norm_num [scalarCert718, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece42, macroPiece43]
lemma scalarCert719_check : scalarCert719.check stableMacroTable = true := by
  norm_num [scalarCert719, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece42, macroPiece43]
lemma scalarCert720_check : scalarCert720.check stableMacroTable = true := by
  norm_num [scalarCert720, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece42, macroPiece43]
lemma scalarCert721_check : scalarCert721.check stableMacroTable = true := by
  norm_num [scalarCert721, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece23, macroPiece24]
lemma scalarCert722_check : scalarCert722.check stableMacroTable = true := by
  norm_num [scalarCert722, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece42, macroPiece43]
lemma scalarCert723_check : scalarCert723.check stableMacroTable = true := by
  norm_num [scalarCert723, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece42, macroPiece43]
lemma scalarCert724_check : scalarCert724.check stableMacroTable = true := by
  norm_num [scalarCert724, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece42, macroPiece43]
lemma scalarCert725_check : scalarCert725.check stableMacroTable = true := by
  norm_num [scalarCert725, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece42, macroPiece43]
lemma scalarCert726_check : scalarCert726.check stableMacroTable = true := by
  norm_num [scalarCert726, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece42, macroPiece43]
lemma scalarCert727_check : scalarCert727.check stableMacroTable = true := by
  norm_num [scalarCert727, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece29, macroPiece30]
lemma scalarCert728_check : scalarCert728.check stableMacroTable = true := by
  norm_num [scalarCert728, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece36, macroPiece37]
lemma scalarCert729_check : scalarCert729.check stableMacroTable = true := by
  norm_num [scalarCert729, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece29, macroPiece30]
lemma scalarCert730_check : scalarCert730.check stableMacroTable = true := by
  norm_num [scalarCert730, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece36, macroPiece37]
lemma scalarCert731_check : scalarCert731.check stableMacroTable = true := by
  norm_num [scalarCert731, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece29, macroPiece30]
lemma scalarCert732_check : scalarCert732.check stableMacroTable = true := by
  norm_num [scalarCert732, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece36, macroPiece37]
lemma scalarCert733_check : scalarCert733.check stableMacroTable = true := by
  norm_num [scalarCert733, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece29, macroPiece30]
lemma scalarCert734_check : scalarCert734.check stableMacroTable = true := by
  norm_num [scalarCert734, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece41, macroPiece42]
lemma scalarCert735_check : scalarCert735.check stableMacroTable = true := by
  norm_num [scalarCert735, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece47, macroPiece48, macroPiece49]
lemma scalarCert736_check : scalarCert736.check stableMacroTable = true := by
  norm_num [scalarCert736, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece47, macroPiece48, macroPiece49]
lemma scalarCert737_check : scalarCert737.check stableMacroTable = true := by
  norm_num [scalarCert737, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece48, macroPiece49]
lemma scalarCert738_check : scalarCert738.check stableMacroTable = true := by
  norm_num [scalarCert738, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece48, macroPiece49]
lemma scalarCert739_check : scalarCert739.check stableMacroTable = true := by
  norm_num [scalarCert739, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece48, macroPiece49]
lemma scalarCert740_check : scalarCert740.check stableMacroTable = true := by
  norm_num [scalarCert740, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece47, macroPiece48]
lemma scalarCert741_check : scalarCert741.check stableMacroTable = true := by
  norm_num [scalarCert741, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece47, macroPiece48]
lemma scalarCert742_check : scalarCert742.check stableMacroTable = true := by
  norm_num [scalarCert742, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece47, macroPiece48]
lemma scalarCert743_check : scalarCert743.check stableMacroTable = true := by
  norm_num [scalarCert743, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece47, macroPiece48]
lemma scalarCert744_check : scalarCert744.check stableMacroTable = true := by
  norm_num [scalarCert744, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece41, macroPiece42]
lemma scalarCert745_check : scalarCert745.check stableMacroTable = true := by
  norm_num [scalarCert745, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece41, macroPiece42]
lemma scalarCert746_check : scalarCert746.check stableMacroTable = true := by
  norm_num [scalarCert746, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece47, macroPiece48]
lemma scalarCert747_check : scalarCert747.check stableMacroTable = true := by
  norm_num [scalarCert747, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece47, macroPiece48]
lemma scalarCert748_check : scalarCert748.check stableMacroTable = true := by
  norm_num [scalarCert748, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece41, macroPiece42]
lemma scalarCert749_check : scalarCert749.check stableMacroTable = true := by
  norm_num [scalarCert749, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece47, macroPiece48]
lemma scalarCert750_check : scalarCert750.check stableMacroTable = true := by
  norm_num [scalarCert750, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece41, macroPiece42]
lemma scalarCert751_check : scalarCert751.check stableMacroTable = true := by
  norm_num [scalarCert751, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece47, macroPiece48, macroPiece49]
lemma scalarCert752_check : scalarCert752.check stableMacroTable = true := by
  norm_num [scalarCert752, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece48, macroPiece49]
lemma scalarCert753_check : scalarCert753.check stableMacroTable = true := by
  norm_num [scalarCert753, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece48, macroPiece49]
lemma scalarCert754_check : scalarCert754.check stableMacroTable = true := by
  norm_num [scalarCert754, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece48, macroPiece49]
lemma scalarCert755_check : scalarCert755.check stableMacroTable = true := by
  norm_num [scalarCert755, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece48, macroPiece49]
lemma scalarCert756_check : scalarCert756.check stableMacroTable = true := by
  norm_num [scalarCert756, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece48, macroPiece49]
lemma scalarCert757_check : scalarCert757.check stableMacroTable = true := by
  norm_num [scalarCert757, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece48, macroPiece49]
lemma scalarCert758_check : scalarCert758.check stableMacroTable = true := by
  norm_num [scalarCert758, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece48, macroPiece49]
lemma scalarCert759_check : scalarCert759.check stableMacroTable = true := by
  norm_num [scalarCert759, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece48, macroPiece49]
lemma scalarCert760_check : scalarCert760.check stableMacroTable = true := by
  norm_num [scalarCert760, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece48, macroPiece49]
lemma scalarCert761_check : scalarCert761.check stableMacroTable = true := by
  norm_num [scalarCert761, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece48, macroPiece49]
lemma scalarCert762_check : scalarCert762.check stableMacroTable = true := by
  norm_num [scalarCert762, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece48, macroPiece49]
lemma scalarCert763_check : scalarCert763.check stableMacroTable = true := by
  norm_num [scalarCert763, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece53, macroPiece54]
lemma scalarCert764_check : scalarCert764.check stableMacroTable = true := by
  norm_num [scalarCert764, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece35, macroPiece36]
lemma scalarCert765_check : scalarCert765.check stableMacroTable = true := by
  norm_num [scalarCert765, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece35, macroPiece36]
lemma scalarCert766_check : scalarCert766.check stableMacroTable = true := by
  norm_num [scalarCert766, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece14, macroPiece15]
lemma scalarCert767_check : scalarCert767.check stableMacroTable = true := by
  norm_num [scalarCert767, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece29, macroPiece30]
lemma scalarCert768_check : scalarCert768.check stableMacroTable = true := by
  norm_num [scalarCert768, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece36, macroPiece37]
lemma scalarCert769_check : scalarCert769.check stableMacroTable = true := by
  norm_num [scalarCert769, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece36, macroPiece37]
lemma scalarCert770_check : scalarCert770.check stableMacroTable = true := by
  norm_num [scalarCert770, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece30, macroPiece31]
lemma scalarCert771_check : scalarCert771.check stableMacroTable = true := by
  norm_num [scalarCert771, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece36, macroPiece37]
lemma scalarCert772_check : scalarCert772.check stableMacroTable = true := by
  norm_num [scalarCert772, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece29, macroPiece30]
lemma scalarCert773_check : scalarCert773.check stableMacroTable = true := by
  norm_num [scalarCert773, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece36, macroPiece37]
lemma scalarCert774_check : scalarCert774.check stableMacroTable = true := by
  norm_num [scalarCert774, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece36, macroPiece37]
lemma scalarCert775_check : scalarCert775.check stableMacroTable = true := by
  norm_num [scalarCert775, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece36, macroPiece37]
lemma scalarCert776_check : scalarCert776.check stableMacroTable = true := by
  norm_num [scalarCert776, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece12, macroPiece13]
lemma scalarCert777_check : scalarCert777.check stableMacroTable = true := by
  norm_num [scalarCert777, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece36, macroPiece37]
lemma scalarCert778_check : scalarCert778.check stableMacroTable = true := by
  norm_num [scalarCert778, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece30, macroPiece31]
lemma scalarCert779_check : scalarCert779.check stableMacroTable = true := by
  norm_num [scalarCert779, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece11, macroPiece12]
lemma scalarCert780_check : scalarCert780.check stableMacroTable = true := by
  norm_num [scalarCert780, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece30, macroPiece31]
lemma scalarCert781_check : scalarCert781.check stableMacroTable = true := by
  norm_num [scalarCert781, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece30, macroPiece31]
lemma scalarCert782_check : scalarCert782.check stableMacroTable = true := by
  norm_num [scalarCert782, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece30, macroPiece31]
lemma scalarCert783_check : scalarCert783.check stableMacroTable = true := by
  norm_num [scalarCert783, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece30, macroPiece31]
lemma scalarCert784_check : scalarCert784.check stableMacroTable = true := by
  norm_num [scalarCert784, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece30, macroPiece31]
lemma scalarCert785_check : scalarCert785.check stableMacroTable = true := by
  norm_num [scalarCert785, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece30, macroPiece31]
lemma scalarCert786_check : scalarCert786.check stableMacroTable = true := by
  norm_num [scalarCert786, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece48, macroPiece49]
lemma scalarCert787_check : scalarCert787.check stableMacroTable = true := by
  norm_num [scalarCert787, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece48, macroPiece49]
lemma scalarCert788_check : scalarCert788.check stableMacroTable = true := by
  norm_num [scalarCert788, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece48, macroPiece49]
lemma scalarCert789_check : scalarCert789.check stableMacroTable = true := by
  norm_num [scalarCert789, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece20, macroPiece21]
lemma scalarCert790_check : scalarCert790.check stableMacroTable = true := by
  norm_num [scalarCert790, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece20, macroPiece21]
lemma scalarCert791_check : scalarCert791.check stableMacroTable = true := by
  norm_num [scalarCert791, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece19, macroPiece20]
lemma scalarCert792_check : scalarCert792.check stableMacroTable = true := by
  norm_num [scalarCert792, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece20, macroPiece21]
lemma scalarCert793_check : scalarCert793.check stableMacroTable = true := by
  norm_num [scalarCert793, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece20, macroPiece21]
lemma scalarCert794_check : scalarCert794.check stableMacroTable = true := by
  norm_num [scalarCert794, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece20, macroPiece21]
lemma scalarCert795_check : scalarCert795.check stableMacroTable = true := by
  norm_num [scalarCert795, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece20, macroPiece21]
lemma scalarCert796_check : scalarCert796.check stableMacroTable = true := by
  norm_num [scalarCert796, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece29, macroPiece30]
lemma scalarCert797_check : scalarCert797.check stableMacroTable = true := by
  norm_num [scalarCert797, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece32, macroPiece33]
lemma scalarCert798_check : scalarCert798.check stableMacroTable = true := by
  norm_num [scalarCert798, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece32, macroPiece33]
lemma scalarCert799_check : scalarCert799.check stableMacroTable = true := by
  norm_num [scalarCert799, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece31, macroPiece32, macroPiece33]
lemma scalarCert800_check : scalarCert800.check stableMacroTable = true := by
  norm_num [scalarCert800, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece32, macroPiece33]
lemma scalarCert801_check : scalarCert801.check stableMacroTable = true := by
  norm_num [scalarCert801, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece48, macroPiece49]
lemma scalarCert802_check : scalarCert802.check stableMacroTable = true := by
  norm_num [scalarCert802, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece48, macroPiece49]
lemma scalarCert803_check : scalarCert803.check stableMacroTable = true := by
  norm_num [scalarCert803, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece49, macroPiece50, macroPiece51]
lemma scalarCert804_check : scalarCert804.check stableMacroTable = true := by
  norm_num [scalarCert804, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece48, macroPiece49]
lemma scalarCert805_check : scalarCert805.check stableMacroTable = true := by
  norm_num [scalarCert805, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece48, macroPiece49]
lemma scalarCert806_check : scalarCert806.check stableMacroTable = true := by
  norm_num [scalarCert806, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece47, macroPiece48]
lemma scalarCert807_check : scalarCert807.check stableMacroTable = true := by
  norm_num [scalarCert807, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece48, macroPiece49]
lemma scalarCert808_check : scalarCert808.check stableMacroTable = true := by
  norm_num [scalarCert808, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece48, macroPiece49]
lemma scalarCert809_check : scalarCert809.check stableMacroTable = true := by
  norm_num [scalarCert809, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece48, macroPiece49]
lemma scalarCert810_check : scalarCert810.check stableMacroTable = true := by
  norm_num [scalarCert810, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece48, macroPiece49]
lemma scalarCert811_check : scalarCert811.check stableMacroTable = true := by
  norm_num [scalarCert811, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece48, macroPiece49]
lemma scalarCert812_check : scalarCert812.check stableMacroTable = true := by
  norm_num [scalarCert812, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece48, macroPiece49]
lemma scalarCert813_check : scalarCert813.check stableMacroTable = true := by
  norm_num [scalarCert813, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece25, macroPiece26]
lemma scalarCert814_check : scalarCert814.check stableMacroTable = true := by
  norm_num [scalarCert814, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece36, macroPiece37]
lemma scalarCert815_check : scalarCert815.check stableMacroTable = true := by
  norm_num [scalarCert815, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece36, macroPiece37]
lemma scalarCert816_check : scalarCert816.check stableMacroTable = true := by
  norm_num [scalarCert816, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece48, macroPiece49]
lemma scalarCert817_check : scalarCert817.check stableMacroTable = true := by
  norm_num [scalarCert817, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece48, macroPiece49]
lemma scalarCert818_check : scalarCert818.check stableMacroTable = true := by
  norm_num [scalarCert818, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece32, macroPiece33]
lemma scalarCert819_check : scalarCert819.check stableMacroTable = true := by
  norm_num [scalarCert819, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece32, macroPiece33]
lemma scalarCert820_check : scalarCert820.check stableMacroTable = true := by
  norm_num [scalarCert820, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece31, macroPiece32, macroPiece33]
lemma scalarCert821_check : scalarCert821.check stableMacroTable = true := by
  norm_num [scalarCert821, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece31, macroPiece32, macroPiece33]
lemma scalarCert822_check : scalarCert822.check stableMacroTable = true := by
  norm_num [scalarCert822, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece32, macroPiece33]
lemma scalarCert823_check : scalarCert823.check stableMacroTable = true := by
  norm_num [scalarCert823, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece47, macroPiece48]
lemma scalarCert824_check : scalarCert824.check stableMacroTable = true := by
  norm_num [scalarCert824, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece47, macroPiece48]
lemma scalarCert825_check : scalarCert825.check stableMacroTable = true := by
  norm_num [scalarCert825, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece47, macroPiece48]
lemma scalarCert826_check : scalarCert826.check stableMacroTable = true := by
  norm_num [scalarCert826, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece41, macroPiece42]
lemma scalarCert827_check : scalarCert827.check stableMacroTable = true := by
  norm_num [scalarCert827, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece48, macroPiece49]
lemma scalarCert828_check : scalarCert828.check stableMacroTable = true := by
  norm_num [scalarCert828, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece48, macroPiece49]
lemma scalarCert829_check : scalarCert829.check stableMacroTable = true := by
  norm_num [scalarCert829, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece41, macroPiece42]
lemma scalarCert830_check : scalarCert830.check stableMacroTable = true := by
  norm_num [scalarCert830, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece48, macroPiece49]
lemma scalarCert831_check : scalarCert831.check stableMacroTable = true := by
  norm_num [scalarCert831, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece48, macroPiece49]
lemma scalarCert832_check : scalarCert832.check stableMacroTable = true := by
  norm_num [scalarCert832, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece41, macroPiece42]
lemma scalarCert833_check : scalarCert833.check stableMacroTable = true := by
  norm_num [scalarCert833, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece48, macroPiece49]
lemma scalarCert834_check : scalarCert834.check stableMacroTable = true := by
  norm_num [scalarCert834, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece48, macroPiece49]
lemma scalarCert835_check : scalarCert835.check stableMacroTable = true := by
  norm_num [scalarCert835, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece48, macroPiece49]
lemma scalarCert836_check : scalarCert836.check stableMacroTable = true := by
  norm_num [scalarCert836, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece48, macroPiece49]
lemma scalarCert837_check : scalarCert837.check stableMacroTable = true := by
  norm_num [scalarCert837, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece47, macroPiece48]
lemma scalarCert838_check : scalarCert838.check stableMacroTable = true := by
  norm_num [scalarCert838, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece48, macroPiece49]
lemma scalarCert839_check : scalarCert839.check stableMacroTable = true := by
  norm_num [scalarCert839, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece48, macroPiece49]
lemma scalarCert840_check : scalarCert840.check stableMacroTable = true := by
  norm_num [scalarCert840, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece29, macroPiece30]
lemma scalarCert841_check : scalarCert841.check stableMacroTable = true := by
  norm_num [scalarCert841, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece41, macroPiece42]
lemma scalarCert842_check : scalarCert842.check stableMacroTable = true := by
  norm_num [scalarCert842, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece48, macroPiece49]
lemma scalarCert843_check : scalarCert843.check stableMacroTable = true := by
  norm_num [scalarCert843, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece29, macroPiece30]
lemma scalarCert844_check : scalarCert844.check stableMacroTable = true := by
  norm_num [scalarCert844, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece41, macroPiece42]
lemma scalarCert845_check : scalarCert845.check stableMacroTable = true := by
  norm_num [scalarCert845, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece48, macroPiece49]
lemma scalarCert846_check : scalarCert846.check stableMacroTable = true := by
  norm_num [scalarCert846, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece48, macroPiece49]
lemma scalarCert847_check : scalarCert847.check stableMacroTable = true := by
  norm_num [scalarCert847, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece48, macroPiece49]
lemma scalarCert848_check : scalarCert848.check stableMacroTable = true := by
  norm_num [scalarCert848, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece48, macroPiece49]
lemma scalarCert849_check : scalarCert849.check stableMacroTable = true := by
  norm_num [scalarCert849, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece48, macroPiece49]
lemma scalarCert850_check : scalarCert850.check stableMacroTable = true := by
  norm_num [scalarCert850, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece53, macroPiece54]
lemma scalarCert851_check : scalarCert851.check stableMacroTable = true := by
  norm_num [scalarCert851, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece25, macroPiece26]
lemma scalarCert852_check : scalarCert852.check stableMacroTable = true := by
  norm_num [scalarCert852, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece25, macroPiece26]
lemma scalarCert853_check : scalarCert853.check stableMacroTable = true := by
  norm_num [scalarCert853, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece13, macroPiece14]
lemma scalarCert854_check : scalarCert854.check stableMacroTable = true := by
  norm_num [scalarCert854, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece13, macroPiece14]
lemma scalarCert855_check : scalarCert855.check stableMacroTable = true := by
  norm_num [scalarCert855, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece37, macroPiece38]
lemma scalarCert856_check : scalarCert856.check stableMacroTable = true := by
  norm_num [scalarCert856, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece14, macroPiece15]
lemma scalarCert857_check : scalarCert857.check stableMacroTable = true := by
  norm_num [scalarCert857, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece37, macroPiece38]
lemma scalarCert858_check : scalarCert858.check stableMacroTable = true := by
  norm_num [scalarCert858, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece13, macroPiece14]
lemma scalarCert859_check : scalarCert859.check stableMacroTable = true := by
  norm_num [scalarCert859, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece25, macroPiece26]
lemma scalarCert860_check : scalarCert860.check stableMacroTable = true := by
  norm_num [scalarCert860, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece19, macroPiece20]
lemma scalarCert861_check : scalarCert861.check stableMacroTable = true := by
  norm_num [scalarCert861, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece14, macroPiece15]
lemma scalarCert862_check : scalarCert862.check stableMacroTable = true := by
  norm_num [scalarCert862, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece25, macroPiece26]
lemma scalarCert863_check : scalarCert863.check stableMacroTable = true := by
  norm_num [scalarCert863, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece25, macroPiece26]
lemma scalarCert864_check : scalarCert864.check stableMacroTable = true := by
  norm_num [scalarCert864, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece26, macroPiece27]
lemma scalarCert865_check : scalarCert865.check stableMacroTable = true := by
  norm_num [scalarCert865, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece26, macroPiece27]
lemma scalarCert866_check : scalarCert866.check stableMacroTable = true := by
  norm_num [scalarCert866, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece26, macroPiece27]
lemma scalarCert867_check : scalarCert867.check stableMacroTable = true := by
  norm_num [scalarCert867, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece26, macroPiece27]
lemma scalarCert868_check : scalarCert868.check stableMacroTable = true := by
  norm_num [scalarCert868, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece25, macroPiece26]
lemma scalarCert869_check : scalarCert869.check stableMacroTable = true := by
  norm_num [scalarCert869, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece26, macroPiece27]
lemma scalarCert870_check : scalarCert870.check stableMacroTable = true := by
  norm_num [scalarCert870, MacroScalarCert.check, MacroScalarSegment.check,
    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,
    RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box,
    wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece19, macroPiece20]

/-- Deduplicated positive seam bounds, addressed by the serialized UInt16 term stream. -/
def scalarCertTable (i : Fin 871) : MacroScalarCert 56 :=
  match i.val with
  | 0 => scalarCert0
  | 1 => scalarCert1
  | 2 => scalarCert2
  | 3 => scalarCert3
  | 4 => scalarCert4
  | 5 => scalarCert5
  | 6 => scalarCert6
  | 7 => scalarCert7
  | 8 => scalarCert8
  | 9 => scalarCert9
  | 10 => scalarCert10
  | 11 => scalarCert11
  | 12 => scalarCert12
  | 13 => scalarCert13
  | 14 => scalarCert14
  | 15 => scalarCert15
  | 16 => scalarCert16
  | 17 => scalarCert17
  | 18 => scalarCert18
  | 19 => scalarCert19
  | 20 => scalarCert20
  | 21 => scalarCert21
  | 22 => scalarCert22
  | 23 => scalarCert23
  | 24 => scalarCert24
  | 25 => scalarCert25
  | 26 => scalarCert26
  | 27 => scalarCert27
  | 28 => scalarCert28
  | 29 => scalarCert29
  | 30 => scalarCert30
  | 31 => scalarCert31
  | 32 => scalarCert32
  | 33 => scalarCert33
  | 34 => scalarCert34
  | 35 => scalarCert35
  | 36 => scalarCert36
  | 37 => scalarCert37
  | 38 => scalarCert38
  | 39 => scalarCert39
  | 40 => scalarCert40
  | 41 => scalarCert41
  | 42 => scalarCert42
  | 43 => scalarCert43
  | 44 => scalarCert44
  | 45 => scalarCert45
  | 46 => scalarCert46
  | 47 => scalarCert47
  | 48 => scalarCert48
  | 49 => scalarCert49
  | 50 => scalarCert50
  | 51 => scalarCert51
  | 52 => scalarCert52
  | 53 => scalarCert53
  | 54 => scalarCert54
  | 55 => scalarCert55
  | 56 => scalarCert56
  | 57 => scalarCert57
  | 58 => scalarCert58
  | 59 => scalarCert59
  | 60 => scalarCert60
  | 61 => scalarCert61
  | 62 => scalarCert62
  | 63 => scalarCert63
  | 64 => scalarCert64
  | 65 => scalarCert65
  | 66 => scalarCert66
  | 67 => scalarCert67
  | 68 => scalarCert68
  | 69 => scalarCert69
  | 70 => scalarCert70
  | 71 => scalarCert71
  | 72 => scalarCert72
  | 73 => scalarCert73
  | 74 => scalarCert74
  | 75 => scalarCert75
  | 76 => scalarCert76
  | 77 => scalarCert77
  | 78 => scalarCert78
  | 79 => scalarCert79
  | 80 => scalarCert80
  | 81 => scalarCert81
  | 82 => scalarCert82
  | 83 => scalarCert83
  | 84 => scalarCert84
  | 85 => scalarCert85
  | 86 => scalarCert86
  | 87 => scalarCert87
  | 88 => scalarCert88
  | 89 => scalarCert89
  | 90 => scalarCert90
  | 91 => scalarCert91
  | 92 => scalarCert92
  | 93 => scalarCert93
  | 94 => scalarCert94
  | 95 => scalarCert95
  | 96 => scalarCert96
  | 97 => scalarCert97
  | 98 => scalarCert98
  | 99 => scalarCert99
  | 100 => scalarCert100
  | 101 => scalarCert101
  | 102 => scalarCert102
  | 103 => scalarCert103
  | 104 => scalarCert104
  | 105 => scalarCert105
  | 106 => scalarCert106
  | 107 => scalarCert107
  | 108 => scalarCert108
  | 109 => scalarCert109
  | 110 => scalarCert110
  | 111 => scalarCert111
  | 112 => scalarCert112
  | 113 => scalarCert113
  | 114 => scalarCert114
  | 115 => scalarCert115
  | 116 => scalarCert116
  | 117 => scalarCert117
  | 118 => scalarCert118
  | 119 => scalarCert119
  | 120 => scalarCert120
  | 121 => scalarCert121
  | 122 => scalarCert122
  | 123 => scalarCert123
  | 124 => scalarCert124
  | 125 => scalarCert125
  | 126 => scalarCert126
  | 127 => scalarCert127
  | 128 => scalarCert128
  | 129 => scalarCert129
  | 130 => scalarCert130
  | 131 => scalarCert131
  | 132 => scalarCert132
  | 133 => scalarCert133
  | 134 => scalarCert134
  | 135 => scalarCert135
  | 136 => scalarCert136
  | 137 => scalarCert137
  | 138 => scalarCert138
  | 139 => scalarCert139
  | 140 => scalarCert140
  | 141 => scalarCert141
  | 142 => scalarCert142
  | 143 => scalarCert143
  | 144 => scalarCert144
  | 145 => scalarCert145
  | 146 => scalarCert146
  | 147 => scalarCert147
  | 148 => scalarCert148
  | 149 => scalarCert149
  | 150 => scalarCert150
  | 151 => scalarCert151
  | 152 => scalarCert152
  | 153 => scalarCert153
  | 154 => scalarCert154
  | 155 => scalarCert155
  | 156 => scalarCert156
  | 157 => scalarCert157
  | 158 => scalarCert158
  | 159 => scalarCert159
  | 160 => scalarCert160
  | 161 => scalarCert161
  | 162 => scalarCert162
  | 163 => scalarCert163
  | 164 => scalarCert164
  | 165 => scalarCert165
  | 166 => scalarCert166
  | 167 => scalarCert167
  | 168 => scalarCert168
  | 169 => scalarCert169
  | 170 => scalarCert170
  | 171 => scalarCert171
  | 172 => scalarCert172
  | 173 => scalarCert173
  | 174 => scalarCert174
  | 175 => scalarCert175
  | 176 => scalarCert176
  | 177 => scalarCert177
  | 178 => scalarCert178
  | 179 => scalarCert179
  | 180 => scalarCert180
  | 181 => scalarCert181
  | 182 => scalarCert182
  | 183 => scalarCert183
  | 184 => scalarCert184
  | 185 => scalarCert185
  | 186 => scalarCert186
  | 187 => scalarCert187
  | 188 => scalarCert188
  | 189 => scalarCert189
  | 190 => scalarCert190
  | 191 => scalarCert191
  | 192 => scalarCert192
  | 193 => scalarCert193
  | 194 => scalarCert194
  | 195 => scalarCert195
  | 196 => scalarCert196
  | 197 => scalarCert197
  | 198 => scalarCert198
  | 199 => scalarCert199
  | 200 => scalarCert200
  | 201 => scalarCert201
  | 202 => scalarCert202
  | 203 => scalarCert203
  | 204 => scalarCert204
  | 205 => scalarCert205
  | 206 => scalarCert206
  | 207 => scalarCert207
  | 208 => scalarCert208
  | 209 => scalarCert209
  | 210 => scalarCert210
  | 211 => scalarCert211
  | 212 => scalarCert212
  | 213 => scalarCert213
  | 214 => scalarCert214
  | 215 => scalarCert215
  | 216 => scalarCert216
  | 217 => scalarCert217
  | 218 => scalarCert218
  | 219 => scalarCert219
  | 220 => scalarCert220
  | 221 => scalarCert221
  | 222 => scalarCert222
  | 223 => scalarCert223
  | 224 => scalarCert224
  | 225 => scalarCert225
  | 226 => scalarCert226
  | 227 => scalarCert227
  | 228 => scalarCert228
  | 229 => scalarCert229
  | 230 => scalarCert230
  | 231 => scalarCert231
  | 232 => scalarCert232
  | 233 => scalarCert233
  | 234 => scalarCert234
  | 235 => scalarCert235
  | 236 => scalarCert236
  | 237 => scalarCert237
  | 238 => scalarCert238
  | 239 => scalarCert239
  | 240 => scalarCert240
  | 241 => scalarCert241
  | 242 => scalarCert242
  | 243 => scalarCert243
  | 244 => scalarCert244
  | 245 => scalarCert245
  | 246 => scalarCert246
  | 247 => scalarCert247
  | 248 => scalarCert248
  | 249 => scalarCert249
  | 250 => scalarCert250
  | 251 => scalarCert251
  | 252 => scalarCert252
  | 253 => scalarCert253
  | 254 => scalarCert254
  | 255 => scalarCert255
  | 256 => scalarCert256
  | 257 => scalarCert257
  | 258 => scalarCert258
  | 259 => scalarCert259
  | 260 => scalarCert260
  | 261 => scalarCert261
  | 262 => scalarCert262
  | 263 => scalarCert263
  | 264 => scalarCert264
  | 265 => scalarCert265
  | 266 => scalarCert266
  | 267 => scalarCert267
  | 268 => scalarCert268
  | 269 => scalarCert269
  | 270 => scalarCert270
  | 271 => scalarCert271
  | 272 => scalarCert272
  | 273 => scalarCert273
  | 274 => scalarCert274
  | 275 => scalarCert275
  | 276 => scalarCert276
  | 277 => scalarCert277
  | 278 => scalarCert278
  | 279 => scalarCert279
  | 280 => scalarCert280
  | 281 => scalarCert281
  | 282 => scalarCert282
  | 283 => scalarCert283
  | 284 => scalarCert284
  | 285 => scalarCert285
  | 286 => scalarCert286
  | 287 => scalarCert287
  | 288 => scalarCert288
  | 289 => scalarCert289
  | 290 => scalarCert290
  | 291 => scalarCert291
  | 292 => scalarCert292
  | 293 => scalarCert293
  | 294 => scalarCert294
  | 295 => scalarCert295
  | 296 => scalarCert296
  | 297 => scalarCert297
  | 298 => scalarCert298
  | 299 => scalarCert299
  | 300 => scalarCert300
  | 301 => scalarCert301
  | 302 => scalarCert302
  | 303 => scalarCert303
  | 304 => scalarCert304
  | 305 => scalarCert305
  | 306 => scalarCert306
  | 307 => scalarCert307
  | 308 => scalarCert308
  | 309 => scalarCert309
  | 310 => scalarCert310
  | 311 => scalarCert311
  | 312 => scalarCert312
  | 313 => scalarCert313
  | 314 => scalarCert314
  | 315 => scalarCert315
  | 316 => scalarCert316
  | 317 => scalarCert317
  | 318 => scalarCert318
  | 319 => scalarCert319
  | 320 => scalarCert320
  | 321 => scalarCert321
  | 322 => scalarCert322
  | 323 => scalarCert323
  | 324 => scalarCert324
  | 325 => scalarCert325
  | 326 => scalarCert326
  | 327 => scalarCert327
  | 328 => scalarCert328
  | 329 => scalarCert329
  | 330 => scalarCert330
  | 331 => scalarCert331
  | 332 => scalarCert332
  | 333 => scalarCert333
  | 334 => scalarCert334
  | 335 => scalarCert335
  | 336 => scalarCert336
  | 337 => scalarCert337
  | 338 => scalarCert338
  | 339 => scalarCert339
  | 340 => scalarCert340
  | 341 => scalarCert341
  | 342 => scalarCert342
  | 343 => scalarCert343
  | 344 => scalarCert344
  | 345 => scalarCert345
  | 346 => scalarCert346
  | 347 => scalarCert347
  | 348 => scalarCert348
  | 349 => scalarCert349
  | 350 => scalarCert350
  | 351 => scalarCert351
  | 352 => scalarCert352
  | 353 => scalarCert353
  | 354 => scalarCert354
  | 355 => scalarCert355
  | 356 => scalarCert356
  | 357 => scalarCert357
  | 358 => scalarCert358
  | 359 => scalarCert359
  | 360 => scalarCert360
  | 361 => scalarCert361
  | 362 => scalarCert362
  | 363 => scalarCert363
  | 364 => scalarCert364
  | 365 => scalarCert365
  | 366 => scalarCert366
  | 367 => scalarCert367
  | 368 => scalarCert368
  | 369 => scalarCert369
  | 370 => scalarCert370
  | 371 => scalarCert371
  | 372 => scalarCert372
  | 373 => scalarCert373
  | 374 => scalarCert374
  | 375 => scalarCert375
  | 376 => scalarCert376
  | 377 => scalarCert377
  | 378 => scalarCert378
  | 379 => scalarCert379
  | 380 => scalarCert380
  | 381 => scalarCert381
  | 382 => scalarCert382
  | 383 => scalarCert383
  | 384 => scalarCert384
  | 385 => scalarCert385
  | 386 => scalarCert386
  | 387 => scalarCert387
  | 388 => scalarCert388
  | 389 => scalarCert389
  | 390 => scalarCert390
  | 391 => scalarCert391
  | 392 => scalarCert392
  | 393 => scalarCert393
  | 394 => scalarCert394
  | 395 => scalarCert395
  | 396 => scalarCert396
  | 397 => scalarCert397
  | 398 => scalarCert398
  | 399 => scalarCert399
  | 400 => scalarCert400
  | 401 => scalarCert401
  | 402 => scalarCert402
  | 403 => scalarCert403
  | 404 => scalarCert404
  | 405 => scalarCert405
  | 406 => scalarCert406
  | 407 => scalarCert407
  | 408 => scalarCert408
  | 409 => scalarCert409
  | 410 => scalarCert410
  | 411 => scalarCert411
  | 412 => scalarCert412
  | 413 => scalarCert413
  | 414 => scalarCert414
  | 415 => scalarCert415
  | 416 => scalarCert416
  | 417 => scalarCert417
  | 418 => scalarCert418
  | 419 => scalarCert419
  | 420 => scalarCert420
  | 421 => scalarCert421
  | 422 => scalarCert422
  | 423 => scalarCert423
  | 424 => scalarCert424
  | 425 => scalarCert425
  | 426 => scalarCert426
  | 427 => scalarCert427
  | 428 => scalarCert428
  | 429 => scalarCert429
  | 430 => scalarCert430
  | 431 => scalarCert431
  | 432 => scalarCert432
  | 433 => scalarCert433
  | 434 => scalarCert434
  | 435 => scalarCert435
  | 436 => scalarCert436
  | 437 => scalarCert437
  | 438 => scalarCert438
  | 439 => scalarCert439
  | 440 => scalarCert440
  | 441 => scalarCert441
  | 442 => scalarCert442
  | 443 => scalarCert443
  | 444 => scalarCert444
  | 445 => scalarCert445
  | 446 => scalarCert446
  | 447 => scalarCert447
  | 448 => scalarCert448
  | 449 => scalarCert449
  | 450 => scalarCert450
  | 451 => scalarCert451
  | 452 => scalarCert452
  | 453 => scalarCert453
  | 454 => scalarCert454
  | 455 => scalarCert455
  | 456 => scalarCert456
  | 457 => scalarCert457
  | 458 => scalarCert458
  | 459 => scalarCert459
  | 460 => scalarCert460
  | 461 => scalarCert461
  | 462 => scalarCert462
  | 463 => scalarCert463
  | 464 => scalarCert464
  | 465 => scalarCert465
  | 466 => scalarCert466
  | 467 => scalarCert467
  | 468 => scalarCert468
  | 469 => scalarCert469
  | 470 => scalarCert470
  | 471 => scalarCert471
  | 472 => scalarCert472
  | 473 => scalarCert473
  | 474 => scalarCert474
  | 475 => scalarCert475
  | 476 => scalarCert476
  | 477 => scalarCert477
  | 478 => scalarCert478
  | 479 => scalarCert479
  | 480 => scalarCert480
  | 481 => scalarCert481
  | 482 => scalarCert482
  | 483 => scalarCert483
  | 484 => scalarCert484
  | 485 => scalarCert485
  | 486 => scalarCert486
  | 487 => scalarCert487
  | 488 => scalarCert488
  | 489 => scalarCert489
  | 490 => scalarCert490
  | 491 => scalarCert491
  | 492 => scalarCert492
  | 493 => scalarCert493
  | 494 => scalarCert494
  | 495 => scalarCert495
  | 496 => scalarCert496
  | 497 => scalarCert497
  | 498 => scalarCert498
  | 499 => scalarCert499
  | 500 => scalarCert500
  | 501 => scalarCert501
  | 502 => scalarCert502
  | 503 => scalarCert503
  | 504 => scalarCert504
  | 505 => scalarCert505
  | 506 => scalarCert506
  | 507 => scalarCert507
  | 508 => scalarCert508
  | 509 => scalarCert509
  | 510 => scalarCert510
  | 511 => scalarCert511
  | 512 => scalarCert512
  | 513 => scalarCert513
  | 514 => scalarCert514
  | 515 => scalarCert515
  | 516 => scalarCert516
  | 517 => scalarCert517
  | 518 => scalarCert518
  | 519 => scalarCert519
  | 520 => scalarCert520
  | 521 => scalarCert521
  | 522 => scalarCert522
  | 523 => scalarCert523
  | 524 => scalarCert524
  | 525 => scalarCert525
  | 526 => scalarCert526
  | 527 => scalarCert527
  | 528 => scalarCert528
  | 529 => scalarCert529
  | 530 => scalarCert530
  | 531 => scalarCert531
  | 532 => scalarCert532
  | 533 => scalarCert533
  | 534 => scalarCert534
  | 535 => scalarCert535
  | 536 => scalarCert536
  | 537 => scalarCert537
  | 538 => scalarCert538
  | 539 => scalarCert539
  | 540 => scalarCert540
  | 541 => scalarCert541
  | 542 => scalarCert542
  | 543 => scalarCert543
  | 544 => scalarCert544
  | 545 => scalarCert545
  | 546 => scalarCert546
  | 547 => scalarCert547
  | 548 => scalarCert548
  | 549 => scalarCert549
  | 550 => scalarCert550
  | 551 => scalarCert551
  | 552 => scalarCert552
  | 553 => scalarCert553
  | 554 => scalarCert554
  | 555 => scalarCert555
  | 556 => scalarCert556
  | 557 => scalarCert557
  | 558 => scalarCert558
  | 559 => scalarCert559
  | 560 => scalarCert560
  | 561 => scalarCert561
  | 562 => scalarCert562
  | 563 => scalarCert563
  | 564 => scalarCert564
  | 565 => scalarCert565
  | 566 => scalarCert566
  | 567 => scalarCert567
  | 568 => scalarCert568
  | 569 => scalarCert569
  | 570 => scalarCert570
  | 571 => scalarCert571
  | 572 => scalarCert572
  | 573 => scalarCert573
  | 574 => scalarCert574
  | 575 => scalarCert575
  | 576 => scalarCert576
  | 577 => scalarCert577
  | 578 => scalarCert578
  | 579 => scalarCert579
  | 580 => scalarCert580
  | 581 => scalarCert581
  | 582 => scalarCert582
  | 583 => scalarCert583
  | 584 => scalarCert584
  | 585 => scalarCert585
  | 586 => scalarCert586
  | 587 => scalarCert587
  | 588 => scalarCert588
  | 589 => scalarCert589
  | 590 => scalarCert590
  | 591 => scalarCert591
  | 592 => scalarCert592
  | 593 => scalarCert593
  | 594 => scalarCert594
  | 595 => scalarCert595
  | 596 => scalarCert596
  | 597 => scalarCert597
  | 598 => scalarCert598
  | 599 => scalarCert599
  | 600 => scalarCert600
  | 601 => scalarCert601
  | 602 => scalarCert602
  | 603 => scalarCert603
  | 604 => scalarCert604
  | 605 => scalarCert605
  | 606 => scalarCert606
  | 607 => scalarCert607
  | 608 => scalarCert608
  | 609 => scalarCert609
  | 610 => scalarCert610
  | 611 => scalarCert611
  | 612 => scalarCert612
  | 613 => scalarCert613
  | 614 => scalarCert614
  | 615 => scalarCert615
  | 616 => scalarCert616
  | 617 => scalarCert617
  | 618 => scalarCert618
  | 619 => scalarCert619
  | 620 => scalarCert620
  | 621 => scalarCert621
  | 622 => scalarCert622
  | 623 => scalarCert623
  | 624 => scalarCert624
  | 625 => scalarCert625
  | 626 => scalarCert626
  | 627 => scalarCert627
  | 628 => scalarCert628
  | 629 => scalarCert629
  | 630 => scalarCert630
  | 631 => scalarCert631
  | 632 => scalarCert632
  | 633 => scalarCert633
  | 634 => scalarCert634
  | 635 => scalarCert635
  | 636 => scalarCert636
  | 637 => scalarCert637
  | 638 => scalarCert638
  | 639 => scalarCert639
  | 640 => scalarCert640
  | 641 => scalarCert641
  | 642 => scalarCert642
  | 643 => scalarCert643
  | 644 => scalarCert644
  | 645 => scalarCert645
  | 646 => scalarCert646
  | 647 => scalarCert647
  | 648 => scalarCert648
  | 649 => scalarCert649
  | 650 => scalarCert650
  | 651 => scalarCert651
  | 652 => scalarCert652
  | 653 => scalarCert653
  | 654 => scalarCert654
  | 655 => scalarCert655
  | 656 => scalarCert656
  | 657 => scalarCert657
  | 658 => scalarCert658
  | 659 => scalarCert659
  | 660 => scalarCert660
  | 661 => scalarCert661
  | 662 => scalarCert662
  | 663 => scalarCert663
  | 664 => scalarCert664
  | 665 => scalarCert665
  | 666 => scalarCert666
  | 667 => scalarCert667
  | 668 => scalarCert668
  | 669 => scalarCert669
  | 670 => scalarCert670
  | 671 => scalarCert671
  | 672 => scalarCert672
  | 673 => scalarCert673
  | 674 => scalarCert674
  | 675 => scalarCert675
  | 676 => scalarCert676
  | 677 => scalarCert677
  | 678 => scalarCert678
  | 679 => scalarCert679
  | 680 => scalarCert680
  | 681 => scalarCert681
  | 682 => scalarCert682
  | 683 => scalarCert683
  | 684 => scalarCert684
  | 685 => scalarCert685
  | 686 => scalarCert686
  | 687 => scalarCert687
  | 688 => scalarCert688
  | 689 => scalarCert689
  | 690 => scalarCert690
  | 691 => scalarCert691
  | 692 => scalarCert692
  | 693 => scalarCert693
  | 694 => scalarCert694
  | 695 => scalarCert695
  | 696 => scalarCert696
  | 697 => scalarCert697
  | 698 => scalarCert698
  | 699 => scalarCert699
  | 700 => scalarCert700
  | 701 => scalarCert701
  | 702 => scalarCert702
  | 703 => scalarCert703
  | 704 => scalarCert704
  | 705 => scalarCert705
  | 706 => scalarCert706
  | 707 => scalarCert707
  | 708 => scalarCert708
  | 709 => scalarCert709
  | 710 => scalarCert710
  | 711 => scalarCert711
  | 712 => scalarCert712
  | 713 => scalarCert713
  | 714 => scalarCert714
  | 715 => scalarCert715
  | 716 => scalarCert716
  | 717 => scalarCert717
  | 718 => scalarCert718
  | 719 => scalarCert719
  | 720 => scalarCert720
  | 721 => scalarCert721
  | 722 => scalarCert722
  | 723 => scalarCert723
  | 724 => scalarCert724
  | 725 => scalarCert725
  | 726 => scalarCert726
  | 727 => scalarCert727
  | 728 => scalarCert728
  | 729 => scalarCert729
  | 730 => scalarCert730
  | 731 => scalarCert731
  | 732 => scalarCert732
  | 733 => scalarCert733
  | 734 => scalarCert734
  | 735 => scalarCert735
  | 736 => scalarCert736
  | 737 => scalarCert737
  | 738 => scalarCert738
  | 739 => scalarCert739
  | 740 => scalarCert740
  | 741 => scalarCert741
  | 742 => scalarCert742
  | 743 => scalarCert743
  | 744 => scalarCert744
  | 745 => scalarCert745
  | 746 => scalarCert746
  | 747 => scalarCert747
  | 748 => scalarCert748
  | 749 => scalarCert749
  | 750 => scalarCert750
  | 751 => scalarCert751
  | 752 => scalarCert752
  | 753 => scalarCert753
  | 754 => scalarCert754
  | 755 => scalarCert755
  | 756 => scalarCert756
  | 757 => scalarCert757
  | 758 => scalarCert758
  | 759 => scalarCert759
  | 760 => scalarCert760
  | 761 => scalarCert761
  | 762 => scalarCert762
  | 763 => scalarCert763
  | 764 => scalarCert764
  | 765 => scalarCert765
  | 766 => scalarCert766
  | 767 => scalarCert767
  | 768 => scalarCert768
  | 769 => scalarCert769
  | 770 => scalarCert770
  | 771 => scalarCert771
  | 772 => scalarCert772
  | 773 => scalarCert773
  | 774 => scalarCert774
  | 775 => scalarCert775
  | 776 => scalarCert776
  | 777 => scalarCert777
  | 778 => scalarCert778
  | 779 => scalarCert779
  | 780 => scalarCert780
  | 781 => scalarCert781
  | 782 => scalarCert782
  | 783 => scalarCert783
  | 784 => scalarCert784
  | 785 => scalarCert785
  | 786 => scalarCert786
  | 787 => scalarCert787
  | 788 => scalarCert788
  | 789 => scalarCert789
  | 790 => scalarCert790
  | 791 => scalarCert791
  | 792 => scalarCert792
  | 793 => scalarCert793
  | 794 => scalarCert794
  | 795 => scalarCert795
  | 796 => scalarCert796
  | 797 => scalarCert797
  | 798 => scalarCert798
  | 799 => scalarCert799
  | 800 => scalarCert800
  | 801 => scalarCert801
  | 802 => scalarCert802
  | 803 => scalarCert803
  | 804 => scalarCert804
  | 805 => scalarCert805
  | 806 => scalarCert806
  | 807 => scalarCert807
  | 808 => scalarCert808
  | 809 => scalarCert809
  | 810 => scalarCert810
  | 811 => scalarCert811
  | 812 => scalarCert812
  | 813 => scalarCert813
  | 814 => scalarCert814
  | 815 => scalarCert815
  | 816 => scalarCert816
  | 817 => scalarCert817
  | 818 => scalarCert818
  | 819 => scalarCert819
  | 820 => scalarCert820
  | 821 => scalarCert821
  | 822 => scalarCert822
  | 823 => scalarCert823
  | 824 => scalarCert824
  | 825 => scalarCert825
  | 826 => scalarCert826
  | 827 => scalarCert827
  | 828 => scalarCert828
  | 829 => scalarCert829
  | 830 => scalarCert830
  | 831 => scalarCert831
  | 832 => scalarCert832
  | 833 => scalarCert833
  | 834 => scalarCert834
  | 835 => scalarCert835
  | 836 => scalarCert836
  | 837 => scalarCert837
  | 838 => scalarCert838
  | 839 => scalarCert839
  | 840 => scalarCert840
  | 841 => scalarCert841
  | 842 => scalarCert842
  | 843 => scalarCert843
  | 844 => scalarCert844
  | 845 => scalarCert845
  | 846 => scalarCert846
  | 847 => scalarCert847
  | 848 => scalarCert848
  | 849 => scalarCert849
  | 850 => scalarCert850
  | 851 => scalarCert851
  | 852 => scalarCert852
  | 853 => scalarCert853
  | 854 => scalarCert854
  | 855 => scalarCert855
  | 856 => scalarCert856
  | 857 => scalarCert857
  | 858 => scalarCert858
  | 859 => scalarCert859
  | 860 => scalarCert860
  | 861 => scalarCert861
  | 862 => scalarCert862
  | 863 => scalarCert863
  | 864 => scalarCert864
  | 865 => scalarCert865
  | 866 => scalarCert866
  | 867 => scalarCert867
  | 868 => scalarCert868
  | 869 => scalarCert869
  | _ => scalarCert870

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem scalarCertTable_check (i : Fin 871) :
    (scalarCertTable i).check stableMacroTable = true := by
  fin_cases i
  · exact scalarCert0_check
  · exact scalarCert1_check
  · exact scalarCert2_check
  · exact scalarCert3_check
  · exact scalarCert4_check
  · exact scalarCert5_check
  · exact scalarCert6_check
  · exact scalarCert7_check
  · exact scalarCert8_check
  · exact scalarCert9_check
  · exact scalarCert10_check
  · exact scalarCert11_check
  · exact scalarCert12_check
  · exact scalarCert13_check
  · exact scalarCert14_check
  · exact scalarCert15_check
  · exact scalarCert16_check
  · exact scalarCert17_check
  · exact scalarCert18_check
  · exact scalarCert19_check
  · exact scalarCert20_check
  · exact scalarCert21_check
  · exact scalarCert22_check
  · exact scalarCert23_check
  · exact scalarCert24_check
  · exact scalarCert25_check
  · exact scalarCert26_check
  · exact scalarCert27_check
  · exact scalarCert28_check
  · exact scalarCert29_check
  · exact scalarCert30_check
  · exact scalarCert31_check
  · exact scalarCert32_check
  · exact scalarCert33_check
  · exact scalarCert34_check
  · exact scalarCert35_check
  · exact scalarCert36_check
  · exact scalarCert37_check
  · exact scalarCert38_check
  · exact scalarCert39_check
  · exact scalarCert40_check
  · exact scalarCert41_check
  · exact scalarCert42_check
  · exact scalarCert43_check
  · exact scalarCert44_check
  · exact scalarCert45_check
  · exact scalarCert46_check
  · exact scalarCert47_check
  · exact scalarCert48_check
  · exact scalarCert49_check
  · exact scalarCert50_check
  · exact scalarCert51_check
  · exact scalarCert52_check
  · exact scalarCert53_check
  · exact scalarCert54_check
  · exact scalarCert55_check
  · exact scalarCert56_check
  · exact scalarCert57_check
  · exact scalarCert58_check
  · exact scalarCert59_check
  · exact scalarCert60_check
  · exact scalarCert61_check
  · exact scalarCert62_check
  · exact scalarCert63_check
  · exact scalarCert64_check
  · exact scalarCert65_check
  · exact scalarCert66_check
  · exact scalarCert67_check
  · exact scalarCert68_check
  · exact scalarCert69_check
  · exact scalarCert70_check
  · exact scalarCert71_check
  · exact scalarCert72_check
  · exact scalarCert73_check
  · exact scalarCert74_check
  · exact scalarCert75_check
  · exact scalarCert76_check
  · exact scalarCert77_check
  · exact scalarCert78_check
  · exact scalarCert79_check
  · exact scalarCert80_check
  · exact scalarCert81_check
  · exact scalarCert82_check
  · exact scalarCert83_check
  · exact scalarCert84_check
  · exact scalarCert85_check
  · exact scalarCert86_check
  · exact scalarCert87_check
  · exact scalarCert88_check
  · exact scalarCert89_check
  · exact scalarCert90_check
  · exact scalarCert91_check
  · exact scalarCert92_check
  · exact scalarCert93_check
  · exact scalarCert94_check
  · exact scalarCert95_check
  · exact scalarCert96_check
  · exact scalarCert97_check
  · exact scalarCert98_check
  · exact scalarCert99_check
  · exact scalarCert100_check
  · exact scalarCert101_check
  · exact scalarCert102_check
  · exact scalarCert103_check
  · exact scalarCert104_check
  · exact scalarCert105_check
  · exact scalarCert106_check
  · exact scalarCert107_check
  · exact scalarCert108_check
  · exact scalarCert109_check
  · exact scalarCert110_check
  · exact scalarCert111_check
  · exact scalarCert112_check
  · exact scalarCert113_check
  · exact scalarCert114_check
  · exact scalarCert115_check
  · exact scalarCert116_check
  · exact scalarCert117_check
  · exact scalarCert118_check
  · exact scalarCert119_check
  · exact scalarCert120_check
  · exact scalarCert121_check
  · exact scalarCert122_check
  · exact scalarCert123_check
  · exact scalarCert124_check
  · exact scalarCert125_check
  · exact scalarCert126_check
  · exact scalarCert127_check
  · exact scalarCert128_check
  · exact scalarCert129_check
  · exact scalarCert130_check
  · exact scalarCert131_check
  · exact scalarCert132_check
  · exact scalarCert133_check
  · exact scalarCert134_check
  · exact scalarCert135_check
  · exact scalarCert136_check
  · exact scalarCert137_check
  · exact scalarCert138_check
  · exact scalarCert139_check
  · exact scalarCert140_check
  · exact scalarCert141_check
  · exact scalarCert142_check
  · exact scalarCert143_check
  · exact scalarCert144_check
  · exact scalarCert145_check
  · exact scalarCert146_check
  · exact scalarCert147_check
  · exact scalarCert148_check
  · exact scalarCert149_check
  · exact scalarCert150_check
  · exact scalarCert151_check
  · exact scalarCert152_check
  · exact scalarCert153_check
  · exact scalarCert154_check
  · exact scalarCert155_check
  · exact scalarCert156_check
  · exact scalarCert157_check
  · exact scalarCert158_check
  · exact scalarCert159_check
  · exact scalarCert160_check
  · exact scalarCert161_check
  · exact scalarCert162_check
  · exact scalarCert163_check
  · exact scalarCert164_check
  · exact scalarCert165_check
  · exact scalarCert166_check
  · exact scalarCert167_check
  · exact scalarCert168_check
  · exact scalarCert169_check
  · exact scalarCert170_check
  · exact scalarCert171_check
  · exact scalarCert172_check
  · exact scalarCert173_check
  · exact scalarCert174_check
  · exact scalarCert175_check
  · exact scalarCert176_check
  · exact scalarCert177_check
  · exact scalarCert178_check
  · exact scalarCert179_check
  · exact scalarCert180_check
  · exact scalarCert181_check
  · exact scalarCert182_check
  · exact scalarCert183_check
  · exact scalarCert184_check
  · exact scalarCert185_check
  · exact scalarCert186_check
  · exact scalarCert187_check
  · exact scalarCert188_check
  · exact scalarCert189_check
  · exact scalarCert190_check
  · exact scalarCert191_check
  · exact scalarCert192_check
  · exact scalarCert193_check
  · exact scalarCert194_check
  · exact scalarCert195_check
  · exact scalarCert196_check
  · exact scalarCert197_check
  · exact scalarCert198_check
  · exact scalarCert199_check
  · exact scalarCert200_check
  · exact scalarCert201_check
  · exact scalarCert202_check
  · exact scalarCert203_check
  · exact scalarCert204_check
  · exact scalarCert205_check
  · exact scalarCert206_check
  · exact scalarCert207_check
  · exact scalarCert208_check
  · exact scalarCert209_check
  · exact scalarCert210_check
  · exact scalarCert211_check
  · exact scalarCert212_check
  · exact scalarCert213_check
  · exact scalarCert214_check
  · exact scalarCert215_check
  · exact scalarCert216_check
  · exact scalarCert217_check
  · exact scalarCert218_check
  · exact scalarCert219_check
  · exact scalarCert220_check
  · exact scalarCert221_check
  · exact scalarCert222_check
  · exact scalarCert223_check
  · exact scalarCert224_check
  · exact scalarCert225_check
  · exact scalarCert226_check
  · exact scalarCert227_check
  · exact scalarCert228_check
  · exact scalarCert229_check
  · exact scalarCert230_check
  · exact scalarCert231_check
  · exact scalarCert232_check
  · exact scalarCert233_check
  · exact scalarCert234_check
  · exact scalarCert235_check
  · exact scalarCert236_check
  · exact scalarCert237_check
  · exact scalarCert238_check
  · exact scalarCert239_check
  · exact scalarCert240_check
  · exact scalarCert241_check
  · exact scalarCert242_check
  · exact scalarCert243_check
  · exact scalarCert244_check
  · exact scalarCert245_check
  · exact scalarCert246_check
  · exact scalarCert247_check
  · exact scalarCert248_check
  · exact scalarCert249_check
  · exact scalarCert250_check
  · exact scalarCert251_check
  · exact scalarCert252_check
  · exact scalarCert253_check
  · exact scalarCert254_check
  · exact scalarCert255_check
  · exact scalarCert256_check
  · exact scalarCert257_check
  · exact scalarCert258_check
  · exact scalarCert259_check
  · exact scalarCert260_check
  · exact scalarCert261_check
  · exact scalarCert262_check
  · exact scalarCert263_check
  · exact scalarCert264_check
  · exact scalarCert265_check
  · exact scalarCert266_check
  · exact scalarCert267_check
  · exact scalarCert268_check
  · exact scalarCert269_check
  · exact scalarCert270_check
  · exact scalarCert271_check
  · exact scalarCert272_check
  · exact scalarCert273_check
  · exact scalarCert274_check
  · exact scalarCert275_check
  · exact scalarCert276_check
  · exact scalarCert277_check
  · exact scalarCert278_check
  · exact scalarCert279_check
  · exact scalarCert280_check
  · exact scalarCert281_check
  · exact scalarCert282_check
  · exact scalarCert283_check
  · exact scalarCert284_check
  · exact scalarCert285_check
  · exact scalarCert286_check
  · exact scalarCert287_check
  · exact scalarCert288_check
  · exact scalarCert289_check
  · exact scalarCert290_check
  · exact scalarCert291_check
  · exact scalarCert292_check
  · exact scalarCert293_check
  · exact scalarCert294_check
  · exact scalarCert295_check
  · exact scalarCert296_check
  · exact scalarCert297_check
  · exact scalarCert298_check
  · exact scalarCert299_check
  · exact scalarCert300_check
  · exact scalarCert301_check
  · exact scalarCert302_check
  · exact scalarCert303_check
  · exact scalarCert304_check
  · exact scalarCert305_check
  · exact scalarCert306_check
  · exact scalarCert307_check
  · exact scalarCert308_check
  · exact scalarCert309_check
  · exact scalarCert310_check
  · exact scalarCert311_check
  · exact scalarCert312_check
  · exact scalarCert313_check
  · exact scalarCert314_check
  · exact scalarCert315_check
  · exact scalarCert316_check
  · exact scalarCert317_check
  · exact scalarCert318_check
  · exact scalarCert319_check
  · exact scalarCert320_check
  · exact scalarCert321_check
  · exact scalarCert322_check
  · exact scalarCert323_check
  · exact scalarCert324_check
  · exact scalarCert325_check
  · exact scalarCert326_check
  · exact scalarCert327_check
  · exact scalarCert328_check
  · exact scalarCert329_check
  · exact scalarCert330_check
  · exact scalarCert331_check
  · exact scalarCert332_check
  · exact scalarCert333_check
  · exact scalarCert334_check
  · exact scalarCert335_check
  · exact scalarCert336_check
  · exact scalarCert337_check
  · exact scalarCert338_check
  · exact scalarCert339_check
  · exact scalarCert340_check
  · exact scalarCert341_check
  · exact scalarCert342_check
  · exact scalarCert343_check
  · exact scalarCert344_check
  · exact scalarCert345_check
  · exact scalarCert346_check
  · exact scalarCert347_check
  · exact scalarCert348_check
  · exact scalarCert349_check
  · exact scalarCert350_check
  · exact scalarCert351_check
  · exact scalarCert352_check
  · exact scalarCert353_check
  · exact scalarCert354_check
  · exact scalarCert355_check
  · exact scalarCert356_check
  · exact scalarCert357_check
  · exact scalarCert358_check
  · exact scalarCert359_check
  · exact scalarCert360_check
  · exact scalarCert361_check
  · exact scalarCert362_check
  · exact scalarCert363_check
  · exact scalarCert364_check
  · exact scalarCert365_check
  · exact scalarCert366_check
  · exact scalarCert367_check
  · exact scalarCert368_check
  · exact scalarCert369_check
  · exact scalarCert370_check
  · exact scalarCert371_check
  · exact scalarCert372_check
  · exact scalarCert373_check
  · exact scalarCert374_check
  · exact scalarCert375_check
  · exact scalarCert376_check
  · exact scalarCert377_check
  · exact scalarCert378_check
  · exact scalarCert379_check
  · exact scalarCert380_check
  · exact scalarCert381_check
  · exact scalarCert382_check
  · exact scalarCert383_check
  · exact scalarCert384_check
  · exact scalarCert385_check
  · exact scalarCert386_check
  · exact scalarCert387_check
  · exact scalarCert388_check
  · exact scalarCert389_check
  · exact scalarCert390_check
  · exact scalarCert391_check
  · exact scalarCert392_check
  · exact scalarCert393_check
  · exact scalarCert394_check
  · exact scalarCert395_check
  · exact scalarCert396_check
  · exact scalarCert397_check
  · exact scalarCert398_check
  · exact scalarCert399_check
  · exact scalarCert400_check
  · exact scalarCert401_check
  · exact scalarCert402_check
  · exact scalarCert403_check
  · exact scalarCert404_check
  · exact scalarCert405_check
  · exact scalarCert406_check
  · exact scalarCert407_check
  · exact scalarCert408_check
  · exact scalarCert409_check
  · exact scalarCert410_check
  · exact scalarCert411_check
  · exact scalarCert412_check
  · exact scalarCert413_check
  · exact scalarCert414_check
  · exact scalarCert415_check
  · exact scalarCert416_check
  · exact scalarCert417_check
  · exact scalarCert418_check
  · exact scalarCert419_check
  · exact scalarCert420_check
  · exact scalarCert421_check
  · exact scalarCert422_check
  · exact scalarCert423_check
  · exact scalarCert424_check
  · exact scalarCert425_check
  · exact scalarCert426_check
  · exact scalarCert427_check
  · exact scalarCert428_check
  · exact scalarCert429_check
  · exact scalarCert430_check
  · exact scalarCert431_check
  · exact scalarCert432_check
  · exact scalarCert433_check
  · exact scalarCert434_check
  · exact scalarCert435_check
  · exact scalarCert436_check
  · exact scalarCert437_check
  · exact scalarCert438_check
  · exact scalarCert439_check
  · exact scalarCert440_check
  · exact scalarCert441_check
  · exact scalarCert442_check
  · exact scalarCert443_check
  · exact scalarCert444_check
  · exact scalarCert445_check
  · exact scalarCert446_check
  · exact scalarCert447_check
  · exact scalarCert448_check
  · exact scalarCert449_check
  · exact scalarCert450_check
  · exact scalarCert451_check
  · exact scalarCert452_check
  · exact scalarCert453_check
  · exact scalarCert454_check
  · exact scalarCert455_check
  · exact scalarCert456_check
  · exact scalarCert457_check
  · exact scalarCert458_check
  · exact scalarCert459_check
  · exact scalarCert460_check
  · exact scalarCert461_check
  · exact scalarCert462_check
  · exact scalarCert463_check
  · exact scalarCert464_check
  · exact scalarCert465_check
  · exact scalarCert466_check
  · exact scalarCert467_check
  · exact scalarCert468_check
  · exact scalarCert469_check
  · exact scalarCert470_check
  · exact scalarCert471_check
  · exact scalarCert472_check
  · exact scalarCert473_check
  · exact scalarCert474_check
  · exact scalarCert475_check
  · exact scalarCert476_check
  · exact scalarCert477_check
  · exact scalarCert478_check
  · exact scalarCert479_check
  · exact scalarCert480_check
  · exact scalarCert481_check
  · exact scalarCert482_check
  · exact scalarCert483_check
  · exact scalarCert484_check
  · exact scalarCert485_check
  · exact scalarCert486_check
  · exact scalarCert487_check
  · exact scalarCert488_check
  · exact scalarCert489_check
  · exact scalarCert490_check
  · exact scalarCert491_check
  · exact scalarCert492_check
  · exact scalarCert493_check
  · exact scalarCert494_check
  · exact scalarCert495_check
  · exact scalarCert496_check
  · exact scalarCert497_check
  · exact scalarCert498_check
  · exact scalarCert499_check
  · exact scalarCert500_check
  · exact scalarCert501_check
  · exact scalarCert502_check
  · exact scalarCert503_check
  · exact scalarCert504_check
  · exact scalarCert505_check
  · exact scalarCert506_check
  · exact scalarCert507_check
  · exact scalarCert508_check
  · exact scalarCert509_check
  · exact scalarCert510_check
  · exact scalarCert511_check
  · exact scalarCert512_check
  · exact scalarCert513_check
  · exact scalarCert514_check
  · exact scalarCert515_check
  · exact scalarCert516_check
  · exact scalarCert517_check
  · exact scalarCert518_check
  · exact scalarCert519_check
  · exact scalarCert520_check
  · exact scalarCert521_check
  · exact scalarCert522_check
  · exact scalarCert523_check
  · exact scalarCert524_check
  · exact scalarCert525_check
  · exact scalarCert526_check
  · exact scalarCert527_check
  · exact scalarCert528_check
  · exact scalarCert529_check
  · exact scalarCert530_check
  · exact scalarCert531_check
  · exact scalarCert532_check
  · exact scalarCert533_check
  · exact scalarCert534_check
  · exact scalarCert535_check
  · exact scalarCert536_check
  · exact scalarCert537_check
  · exact scalarCert538_check
  · exact scalarCert539_check
  · exact scalarCert540_check
  · exact scalarCert541_check
  · exact scalarCert542_check
  · exact scalarCert543_check
  · exact scalarCert544_check
  · exact scalarCert545_check
  · exact scalarCert546_check
  · exact scalarCert547_check
  · exact scalarCert548_check
  · exact scalarCert549_check
  · exact scalarCert550_check
  · exact scalarCert551_check
  · exact scalarCert552_check
  · exact scalarCert553_check
  · exact scalarCert554_check
  · exact scalarCert555_check
  · exact scalarCert556_check
  · exact scalarCert557_check
  · exact scalarCert558_check
  · exact scalarCert559_check
  · exact scalarCert560_check
  · exact scalarCert561_check
  · exact scalarCert562_check
  · exact scalarCert563_check
  · exact scalarCert564_check
  · exact scalarCert565_check
  · exact scalarCert566_check
  · exact scalarCert567_check
  · exact scalarCert568_check
  · exact scalarCert569_check
  · exact scalarCert570_check
  · exact scalarCert571_check
  · exact scalarCert572_check
  · exact scalarCert573_check
  · exact scalarCert574_check
  · exact scalarCert575_check
  · exact scalarCert576_check
  · exact scalarCert577_check
  · exact scalarCert578_check
  · exact scalarCert579_check
  · exact scalarCert580_check
  · exact scalarCert581_check
  · exact scalarCert582_check
  · exact scalarCert583_check
  · exact scalarCert584_check
  · exact scalarCert585_check
  · exact scalarCert586_check
  · exact scalarCert587_check
  · exact scalarCert588_check
  · exact scalarCert589_check
  · exact scalarCert590_check
  · exact scalarCert591_check
  · exact scalarCert592_check
  · exact scalarCert593_check
  · exact scalarCert594_check
  · exact scalarCert595_check
  · exact scalarCert596_check
  · exact scalarCert597_check
  · exact scalarCert598_check
  · exact scalarCert599_check
  · exact scalarCert600_check
  · exact scalarCert601_check
  · exact scalarCert602_check
  · exact scalarCert603_check
  · exact scalarCert604_check
  · exact scalarCert605_check
  · exact scalarCert606_check
  · exact scalarCert607_check
  · exact scalarCert608_check
  · exact scalarCert609_check
  · exact scalarCert610_check
  · exact scalarCert611_check
  · exact scalarCert612_check
  · exact scalarCert613_check
  · exact scalarCert614_check
  · exact scalarCert615_check
  · exact scalarCert616_check
  · exact scalarCert617_check
  · exact scalarCert618_check
  · exact scalarCert619_check
  · exact scalarCert620_check
  · exact scalarCert621_check
  · exact scalarCert622_check
  · exact scalarCert623_check
  · exact scalarCert624_check
  · exact scalarCert625_check
  · exact scalarCert626_check
  · exact scalarCert627_check
  · exact scalarCert628_check
  · exact scalarCert629_check
  · exact scalarCert630_check
  · exact scalarCert631_check
  · exact scalarCert632_check
  · exact scalarCert633_check
  · exact scalarCert634_check
  · exact scalarCert635_check
  · exact scalarCert636_check
  · exact scalarCert637_check
  · exact scalarCert638_check
  · exact scalarCert639_check
  · exact scalarCert640_check
  · exact scalarCert641_check
  · exact scalarCert642_check
  · exact scalarCert643_check
  · exact scalarCert644_check
  · exact scalarCert645_check
  · exact scalarCert646_check
  · exact scalarCert647_check
  · exact scalarCert648_check
  · exact scalarCert649_check
  · exact scalarCert650_check
  · exact scalarCert651_check
  · exact scalarCert652_check
  · exact scalarCert653_check
  · exact scalarCert654_check
  · exact scalarCert655_check
  · exact scalarCert656_check
  · exact scalarCert657_check
  · exact scalarCert658_check
  · exact scalarCert659_check
  · exact scalarCert660_check
  · exact scalarCert661_check
  · exact scalarCert662_check
  · exact scalarCert663_check
  · exact scalarCert664_check
  · exact scalarCert665_check
  · exact scalarCert666_check
  · exact scalarCert667_check
  · exact scalarCert668_check
  · exact scalarCert669_check
  · exact scalarCert670_check
  · exact scalarCert671_check
  · exact scalarCert672_check
  · exact scalarCert673_check
  · exact scalarCert674_check
  · exact scalarCert675_check
  · exact scalarCert676_check
  · exact scalarCert677_check
  · exact scalarCert678_check
  · exact scalarCert679_check
  · exact scalarCert680_check
  · exact scalarCert681_check
  · exact scalarCert682_check
  · exact scalarCert683_check
  · exact scalarCert684_check
  · exact scalarCert685_check
  · exact scalarCert686_check
  · exact scalarCert687_check
  · exact scalarCert688_check
  · exact scalarCert689_check
  · exact scalarCert690_check
  · exact scalarCert691_check
  · exact scalarCert692_check
  · exact scalarCert693_check
  · exact scalarCert694_check
  · exact scalarCert695_check
  · exact scalarCert696_check
  · exact scalarCert697_check
  · exact scalarCert698_check
  · exact scalarCert699_check
  · exact scalarCert700_check
  · exact scalarCert701_check
  · exact scalarCert702_check
  · exact scalarCert703_check
  · exact scalarCert704_check
  · exact scalarCert705_check
  · exact scalarCert706_check
  · exact scalarCert707_check
  · exact scalarCert708_check
  · exact scalarCert709_check
  · exact scalarCert710_check
  · exact scalarCert711_check
  · exact scalarCert712_check
  · exact scalarCert713_check
  · exact scalarCert714_check
  · exact scalarCert715_check
  · exact scalarCert716_check
  · exact scalarCert717_check
  · exact scalarCert718_check
  · exact scalarCert719_check
  · exact scalarCert720_check
  · exact scalarCert721_check
  · exact scalarCert722_check
  · exact scalarCert723_check
  · exact scalarCert724_check
  · exact scalarCert725_check
  · exact scalarCert726_check
  · exact scalarCert727_check
  · exact scalarCert728_check
  · exact scalarCert729_check
  · exact scalarCert730_check
  · exact scalarCert731_check
  · exact scalarCert732_check
  · exact scalarCert733_check
  · exact scalarCert734_check
  · exact scalarCert735_check
  · exact scalarCert736_check
  · exact scalarCert737_check
  · exact scalarCert738_check
  · exact scalarCert739_check
  · exact scalarCert740_check
  · exact scalarCert741_check
  · exact scalarCert742_check
  · exact scalarCert743_check
  · exact scalarCert744_check
  · exact scalarCert745_check
  · exact scalarCert746_check
  · exact scalarCert747_check
  · exact scalarCert748_check
  · exact scalarCert749_check
  · exact scalarCert750_check
  · exact scalarCert751_check
  · exact scalarCert752_check
  · exact scalarCert753_check
  · exact scalarCert754_check
  · exact scalarCert755_check
  · exact scalarCert756_check
  · exact scalarCert757_check
  · exact scalarCert758_check
  · exact scalarCert759_check
  · exact scalarCert760_check
  · exact scalarCert761_check
  · exact scalarCert762_check
  · exact scalarCert763_check
  · exact scalarCert764_check
  · exact scalarCert765_check
  · exact scalarCert766_check
  · exact scalarCert767_check
  · exact scalarCert768_check
  · exact scalarCert769_check
  · exact scalarCert770_check
  · exact scalarCert771_check
  · exact scalarCert772_check
  · exact scalarCert773_check
  · exact scalarCert774_check
  · exact scalarCert775_check
  · exact scalarCert776_check
  · exact scalarCert777_check
  · exact scalarCert778_check
  · exact scalarCert779_check
  · exact scalarCert780_check
  · exact scalarCert781_check
  · exact scalarCert782_check
  · exact scalarCert783_check
  · exact scalarCert784_check
  · exact scalarCert785_check
  · exact scalarCert786_check
  · exact scalarCert787_check
  · exact scalarCert788_check
  · exact scalarCert789_check
  · exact scalarCert790_check
  · exact scalarCert791_check
  · exact scalarCert792_check
  · exact scalarCert793_check
  · exact scalarCert794_check
  · exact scalarCert795_check
  · exact scalarCert796_check
  · exact scalarCert797_check
  · exact scalarCert798_check
  · exact scalarCert799_check
  · exact scalarCert800_check
  · exact scalarCert801_check
  · exact scalarCert802_check
  · exact scalarCert803_check
  · exact scalarCert804_check
  · exact scalarCert805_check
  · exact scalarCert806_check
  · exact scalarCert807_check
  · exact scalarCert808_check
  · exact scalarCert809_check
  · exact scalarCert810_check
  · exact scalarCert811_check
  · exact scalarCert812_check
  · exact scalarCert813_check
  · exact scalarCert814_check
  · exact scalarCert815_check
  · exact scalarCert816_check
  · exact scalarCert817_check
  · exact scalarCert818_check
  · exact scalarCert819_check
  · exact scalarCert820_check
  · exact scalarCert821_check
  · exact scalarCert822_check
  · exact scalarCert823_check
  · exact scalarCert824_check
  · exact scalarCert825_check
  · exact scalarCert826_check
  · exact scalarCert827_check
  · exact scalarCert828_check
  · exact scalarCert829_check
  · exact scalarCert830_check
  · exact scalarCert831_check
  · exact scalarCert832_check
  · exact scalarCert833_check
  · exact scalarCert834_check
  · exact scalarCert835_check
  · exact scalarCert836_check
  · exact scalarCert837_check
  · exact scalarCert838_check
  · exact scalarCert839_check
  · exact scalarCert840_check
  · exact scalarCert841_check
  · exact scalarCert842_check
  · exact scalarCert843_check
  · exact scalarCert844_check
  · exact scalarCert845_check
  · exact scalarCert846_check
  · exact scalarCert847_check
  · exact scalarCert848_check
  · exact scalarCert849_check
  · exact scalarCert850_check
  · exact scalarCert851_check
  · exact scalarCert852_check
  · exact scalarCert853_check
  · exact scalarCert854_check
  · exact scalarCert855_check
  · exact scalarCert856_check
  · exact scalarCert857_check
  · exact scalarCert858_check
  · exact scalarCert859_check
  · exact scalarCert860_check
  · exact scalarCert861_check
  · exact scalarCert862_check
  · exact scalarCert863_check
  · exact scalarCert864_check
  · exact scalarCert865_check
  · exact scalarCert866_check
  · exact scalarCert867_check
  · exact scalarCert868_check
  · exact scalarCert869_check
  · exact scalarCert870_check

#print axioms stableMacroTable_check
#print axioms scalarCertTable_check

end Zeta23.ThmD.Sextuple.MacroPrototype
