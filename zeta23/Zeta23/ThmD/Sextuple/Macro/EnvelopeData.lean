import Zeta23.ThmD.Sextuple.Macro.Analytic

namespace Zeta23.ThmD.Sextuple.MacroPrototype

open RatInterval

def macroPiece0 : MacroPiece := .base { box := ⟨0, 2⟩, q := 0, a := (1/4), c := 0, kind := .low }
def macroPiece1 : MacroPiece := .base { box := ⟨2, (235723/40000)⟩, q := 0, a := (14630385677/1000000000000), c := 0, kind := .numeric [
      { box := ⟨2, (475723/160000)⟩, turn := 1 },
      { box := ⟨(475723/160000), (315723/80000)⟩, turn := 1 },
      { box := ⟨(315723/80000), (787169/160000)⟩, turn := 1 },
      { box := ⟨(787169/160000), (235723/40000)⟩, turn := 2 }
    ] }
def macroPiece2 : MacroPiece := .well { box := ⟨(235723/40000), (250723/40000)⟩, side := .left, positive := true, q := (250723/40000), v := (27867868213/500000000000), m := (143964883497/1000000000000), turn := 2 }
def macroPiece3 : MacroPiece := .well { box := ⟨(250723/40000), (265723/40000)⟩, side := .left, positive := true, q := (265723/40000), v := (11833/200000000000), m := (129043175877/1000000000000), turn := 2 }
def macroPiece4 : MacroPiece := .base { box := ⟨(265723/40000), (1660769/250000)⟩, q := 0, a := 0, c := 0, kind := .zero }
def macroPiece5 : MacroPiece := .well { box := ⟨(1660769/250000), (1754519/250000)⟩, side := .right, positive := false, q := (1660769/250000), v := (16097/200000000000), m := (27917259037/250000000000), turn := 2 }
def macroPiece6 : MacroPiece := .well { box := ⟨(1754519/250000), (1848269/250000)⟩, side := .right, positive := false, q := (1754519/250000), v := (24399891953/500000000000), m := (92227986803/1000000000000), turn := 2 }
def macroPiece7 : MacroPiece := .base { box := ⟨(1848269/250000), (1200529/100000)⟩, q := 0, a := (3595147923/1000000000000), c := 0, kind := .numeric [
      { box := ⟨(1848269/250000), (20788797/2500000)⟩, turn := 3 },
      { box := ⟨(20788797/2500000), (2886863/312500)⟩, turn := 3 },
      { box := ⟨(2886863/312500), (25401011/2500000)⟩, turn := 3 },
      { box := ⟨(25401011/2500000), (13853559/1250000)⟩, turn := 3 },
      { box := ⟨(13853559/1250000), (1200529/100000)⟩, turn := 4 }
    ] }
def macroPiece8 : MacroPiece := .well { box := ⟨(1200529/100000), (1238029/100000)⟩, side := .left, positive := false, q := (1238029/100000), v := (643699421/25000000000), m := (34061638159/500000000000), turn := 4 }
def macroPiece9 : MacroPiece := .well { box := ⟨(1238029/100000), (1275529/100000)⟩, side := .left, positive := false, q := (1275529/100000), v := (31993/1000000000000), m := (65221387031/1000000000000), turn := 4 }
def macroPiece10 : MacroPiece := .base { box := ⟨(1275529/100000), (12755291/1000000)⟩, q := 0, a := 0, c := 0, kind := .zero }
def macroPiece11 : MacroPiece := .well { box := ⟨(12755291/1000000), (13130291/1000000)⟩, side := .right, positive := true, q := (12755291/1000000), v := (17477/500000000000), m := (30123389409/500000000000), turn := 4 }
def macroPiece12 : MacroPiece := .well { box := ⟨(13130291/1000000), (13505291/1000000)⟩, side := .right, positive := true, q := (13130291/1000000), v := (1210437121/50000000000), m := (53414399479/1000000000000), turn := 4 }
def macroPiece13 : MacroPiece := .base { box := ⟨(13505291/1000000), (9113373/500000)⟩, q := 0, a := (1610977803/1000000000000), c := 0, kind := .numeric [
      { box := ⟨(13505291/1000000), (7224791/500000)⟩, turn := 4 },
      { box := ⟨(7224791/500000), (15393873/1000000)⟩, turn := 5 },
      { box := ⟨(15393873/1000000), (4084541/250000)⟩, turn := 5 },
      { box := ⟨(4084541/250000), (3456491/200000)⟩, turn := 5 },
      { box := ⟨(3456491/200000), (9113373/500000)⟩, turn := 6 }
    ] }
def macroPiece14 : MacroPiece := .well { box := ⟨(9113373/500000), (9300873/500000)⟩, side := .left, positive := true, q := (9300873/500000), v := (4207133411/250000000000), m := (2200479609/50000000000), turn := 6 }
def macroPiece15 : MacroPiece := .well { box := ⟨(9300873/500000), (9488373/500000)⟩, side := .left, positive := true, q := (9488373/500000), v := (8681/500000000000), m := (43533863507/1000000000000), turn := 6 }
def macroPiece16 : MacroPiece := .base { box := ⟨(9488373/500000), (18976747/1000000)⟩, q := 0, a := 0, c := 0, kind := .zero }
def macroPiece17 : MacroPiece := .well { box := ⟨(18976747/1000000), (19351747/1000000)⟩, side := .right, positive := false, q := (18976747/1000000), v := (26869/1000000000000), m := (8212254167/200000000000), turn := 6 }
def macroPiece18 : MacroPiece := .well { box := ⟨(19351747/1000000), (19726747/1000000)⟩, side := .right, positive := false, q := (19351747/1000000), v := (16162428093/1000000000000), m := (7444483427/200000000000), turn := 6 }
def macroPiece19 : MacroPiece := .base { box := ⟨(19726747/1000000), (24478469/1000000)⟩, q := 0, a := (459565243/500000000000), c := 0, kind := .numeric [
      { box := ⟨(19726747/1000000), (103385457/5000000)⟩, turn := 6 },
      { box := ⟨(103385457/5000000), (108137179/5000000)⟩, turn := 7 },
      { box := ⟨(108137179/5000000), (112888901/5000000)⟩, turn := 7 },
      { box := ⟨(112888901/5000000), (117640623/5000000)⟩, turn := 7 },
      { box := ⟨(117640623/5000000), (24478469/1000000)⟩, turn := 8 }
    ] }
def macroPiece20 : MacroPiece := .well { box := ⟨(24478469/1000000), (24853469/1000000)⟩, side := .left, positive := false, q := (24853469/1000000), v := (3128766681/250000000000), m := (16161423221/500000000000), turn := 8 }
def macroPiece21 : MacroPiece := .well { box := ⟨(24853469/1000000), (25228469/1000000)⟩, side := .left, positive := false, q := (25228469/1000000), v := (12267/1000000000000), m := (2042028109/62500000000), turn := 8 }
def macroPiece22 : MacroPiece := .base { box := ⟨(25228469/1000000), (2522847/100000)⟩, q := 0, a := 0, c := 0, kind := .zero }
def macroPiece23 : MacroPiece := .well { box := ⟨(2522847/100000), (2560347/100000)⟩, side := .right, positive := true, q := (2522847/100000), v := (10399/500000000000), m := (7782844861/250000000000), turn := 8 }
def macroPiece24 : MacroPiece := .well { box := ⟨(2560347/100000), (2597847/100000)⟩, side := .right, positive := true, q := (2560347/100000), v := (12144023451/1000000000000), m := (1426679091/50000000000), turn := 8 }
def macroPiece25 : MacroPiece := .base { box := ⟨(2597847/100000), (15371317/500000)⟩, q := 0, a := (148698801/250000000000), c := 0, kind := .numeric [
      { box := ⟨(2597847/100000), (67328257/2500000)⟩, turn := 8 },
      { box := ⟨(67328257/2500000), (69710339/2500000)⟩, turn := 9 },
      { box := ⟨(69710339/2500000), (72092421/2500000)⟩, turn := 9 },
      { box := ⟨(72092421/2500000), (74474503/2500000)⟩, turn := 9 },
      { box := ⟨(74474503/2500000), (15371317/500000)⟩, turn := 10 }
    ] }
def macroPiece26 : MacroPiece := .well { box := ⟨(15371317/500000), (15558817/500000)⟩, side := .left, positive := true, q := (15558817/500000), v := (622882353/62500000000), m := (25545035051/1000000000000), turn := 10 }
def macroPiece27 : MacroPiece := .well { box := ⟨(15558817/500000), (15746317/500000)⟩, side := .left, positive := true, q := (15746317/500000), v := (12681/1000000000000), m := (5230095841/200000000000), turn := 10 }
def macroPiece28 : MacroPiece := .base { box := ⟨(15746317/500000), (6298527/200000)⟩, q := 0, a := 0, c := 0, kind := .zero }
def macroPiece29 : MacroPiece := .well { box := ⟨(6298527/200000), (6373527/200000)⟩, side := .right, positive := false, q := (6298527/200000), v := (13731/1000000000000), m := (6267293181/250000000000), turn := 10 }
def macroPiece30 : MacroPiece := .well { box := ⟨(6373527/200000), (6448527/200000)⟩, side := .right, positive := false, q := (6373527/200000), v := (389189381/40000000000), m := (5781973269/250000000000), turn := 10 }
def macroPiece31 : MacroPiece := .base { box := ⟨(6448527/200000), (9253273/250000)⟩, q := 0, a := (104124691/250000000000), c := 0, kind := .numeric [
      { box := ⟨(6448527/200000), (10373977/312500)⟩, turn := 10 },
      { box := ⟨(10373977/312500), (170754089/5000000)⟩, turn := 11 },
      { box := ⟨(170754089/5000000), (87762273/2500000)⟩, turn := 11 },
      { box := ⟨(87762273/2500000), (180295003/5000000)⟩, turn := 11 },
      { box := ⟨(180295003/5000000), (9253273/250000)⟩, turn := 12 }
    ] }
def macroPiece32 : MacroPiece := .well { box := ⟨(9253273/250000), (9347023/250000)⟩, side := .left, positive := false, q := (9347023/250000), v := (8281328177/1000000000000), m := (10559189049/500000000000), turn := 12 }
def macroPiece33 : MacroPiece := .well { box := ⟨(9347023/250000), (9440773/250000)⟩, side := .left, positive := false, q := (9440773/250000), v := (2153/500000000000), m := (21799921507/1000000000000), turn := 12 }
def macroPiece34 : MacroPiece := .base { box := ⟨(9440773/250000), (37763093/1000000)⟩, q := 0, a := 0, c := 0, kind := .zero }
def macroPiece35 : MacroPiece := .well { box := ⟨(37763093/1000000), (38138093/1000000)⟩, side := .right, positive := true, q := (37763093/1000000), v := (3537/200000000000), m := (20983503123/1000000000000), turn := 12 }
def macroPiece36 : MacroPiece := .well { box := ⟨(38138093/1000000), (38513093/1000000)⟩, side := .right, positive := true, q := (38138093/1000000), v := (4058799267/500000000000), m := (3888525077/200000000000), turn := 12 }
def macroPiece37 : MacroPiece := .base { box := ⟨(38513093/1000000), (43287167/1000000)⟩, q := 0, a := (76986939/250000000000), c := 0, kind := .numeric [
      { box := ⟨(38513093/1000000), (197339539/5000000)⟩, turn := 12 },
      { box := ⟨(197339539/5000000), (202113613/5000000)⟩, turn := 13 },
      { box := ⟨(202113613/5000000), (206887687/5000000)⟩, turn := 13 },
      { box := ⟨(206887687/5000000), (211661761/5000000)⟩, turn := 13 },
      { box := ⟨(211661761/5000000), (43287167/1000000)⟩, turn := 14 }
    ] }
def macroPiece38 : MacroPiece := .well { box := ⟨(43287167/1000000), (43662167/1000000)⟩, side := .left, positive := true, q := (43662167/1000000), v := (708446159/100000000000), m := (17999836703/1000000000000), turn := 14 }
def macroPiece39 : MacroPiece := .well { box := ⟨(43662167/1000000), (44037167/1000000)⟩, side := .left, positive := true, q := (44037167/1000000), v := (71/125000000000), m := (4670171149/250000000000), turn := 14 }
def macroPiece40 : MacroPiece := .base { box := ⟨(44037167/1000000), (2752323/62500)⟩, q := 0, a := 0, c := 0, kind := .zero }
def macroPiece41 : MacroPiece := .well { box := ⟨(2752323/62500), (5551521/125000)⟩, side := .right, positive := false, q := (2752323/62500), v := (18271/1000000000000), m := (4510792599/250000000000), turn := 14 }
def macroPiece42 : MacroPiece := .well { box := ⟨(5551521/125000), (1399599/31250)⟩, side := .right, positive := false, q := (5551521/125000), v := (696436159/100000000000), m := (4192457661/250000000000), turn := 14 }
def macroPiece43 : MacroPiece := .base { box := ⟨(1399599/31250), (4956351/100000)⟩, q := 0, a := (236947891/1000000000000), c := 0, kind := .numeric [
      { box := ⟨(1399599/31250), (114356091/2500000)⟩, turn := 14 },
      { box := ⟨(114356091/2500000), (58372131/1250000)⟩, turn := 15 },
      { box := ⟨(58372131/1250000), (119132433/2500000)⟩, turn := 15 },
      { box := ⟨(119132433/2500000), (30380151/625000)⟩, turn := 15 },
      { box := ⟨(30380151/625000), (4956351/100000)⟩, turn := 16 }
    ] }
def macroPiece44 : MacroPiece := .well { box := ⟨(4956351/100000), (4993851/100000)⟩, side := .left, positive := false, q := (4993851/100000), v := (1547547903/250000000000), m := (7842023811/500000000000), turn := 16 }
def macroPiece45 : MacroPiece := .well { box := ⟨(4993851/100000), (5031351/100000)⟩, side := .left, positive := false, q := (5031351/100000), v := (7079/1000000000000), m := (101959387/6250000000), turn := 16 }
def macroPiece46 : MacroPiece := .base { box := ⟨(5031351/100000), (50313511/1000000)⟩, q := 0, a := 0, c := 0, kind := .zero }
def macroPiece47 : MacroPiece := .well { box := ⟨(50313511/1000000), (50688511/1000000)⟩, side := .right, positive := true, q := (50313511/1000000), v := (47/5000000000), m := (791286487/50000000000), turn := 16 }
def macroPiece48 : MacroPiece := .well { box := ⟨(50688511/1000000), (51063511/1000000)⟩, side := .right, positive := true, q := (50688511/1000000), v := (3049160163/500000000000), m := (14742857977/1000000000000), turn := 16 }
def macroPiece49 : MacroPiece := .base { box := ⟨(51063511/1000000), (55841369/1000000)⟩, q := 0, a := (587393/3125000000), c := 0, kind := .numeric [
      { box := ⟨(51063511/1000000), (260095413/5000000)⟩, turn := 16 },
      { box := ⟨(260095413/5000000), (264873271/5000000)⟩, turn := 17 },
      { box := ⟨(264873271/5000000), (269651129/5000000)⟩, turn := 17 },
      { box := ⟨(269651129/5000000), (274428987/5000000)⟩, turn := 17 },
      { box := ⟨(274428987/5000000), (55841369/1000000)⟩, turn := 18 }
    ] }
def macroPiece50 : MacroPiece := .well { box := ⟨(55841369/1000000), (56216369/1000000)⟩, side := .left, positive := true, q := (56216369/1000000), v := (5496549093/1000000000000), m := (6948165239/500000000000), turn := 18 }
def macroPiece51 : MacroPiece := .well { box := ⟨(56216369/1000000), (56591369/1000000)⟩, side := .left, positive := true, q := (56591369/1000000), v := (1647/200000000000), m := (14478984049/1000000000000), turn := 18 }
def macroPiece52 : MacroPiece := .base { box := ⟨(56591369/1000000), (5659137/100000)⟩, q := 0, a := 0, c := 0, kind := .zero }
def macroPiece53 : MacroPiece := .well { box := ⟨(5659137/100000), (5696637/100000)⟩, side := .right, positive := false, q := (5659137/100000), v := (641/100000000000), m := (880859249/62500000000), turn := 18 }
def macroPiece54 : MacroPiece := .well { box := ⟨(5696637/100000), (5734137/100000)⟩, side := .right, positive := false, q := (5696637/100000), v := (1084801073/200000000000), m := (13152938453/1000000000000), turn := 18 }
def macroPiece55 : MacroPiece := .base { box := ⟨(5734137/100000), 59⟩, q := 0, a := (180593923/1000000000000), c := 0, kind := .numeric [
      { box := ⟨(5734137/100000), (11634137/200000)⟩, turn := 18 },
      { box := ⟨(11634137/200000), 59⟩, turn := 19 }
    ] }

def macroPieces : List MacroPiece := [macroPiece0, macroPiece1, macroPiece2, macroPiece3, macroPiece4, macroPiece5, macroPiece6, macroPiece7, macroPiece8, macroPiece9, macroPiece10, macroPiece11, macroPiece12, macroPiece13, macroPiece14, macroPiece15, macroPiece16, macroPiece17, macroPiece18, macroPiece19, macroPiece20, macroPiece21, macroPiece22, macroPiece23, macroPiece24, macroPiece25, macroPiece26, macroPiece27, macroPiece28, macroPiece29, macroPiece30, macroPiece31, macroPiece32, macroPiece33, macroPiece34, macroPiece35, macroPiece36, macroPiece37, macroPiece38, macroPiece39, macroPiece40, macroPiece41, macroPiece42, macroPiece43, macroPiece44, macroPiece45, macroPiece46, macroPiece47, macroPiece48, macroPiece49, macroPiece50, macroPiece51, macroPiece52, macroPiece53, macroPiece54, macroPiece55]

lemma macroPiece0_check : macroPiece0.check = true := by
  norm_num [macroPiece0, MacroPiece.check, LowerPiece.check]
lemma macroPiece1_check : macroPiece1.check = true := by
  norm_num [macroPiece1, MacroPiece.check, LowerPiece.check, LowerPiece.coverFrom, LowerPiece.cellCheck,
    LowerPiece.cellModelUpper, LowerPiece.absLower, kernelRange, kernelDenRange, rootTwoInterval, thetaTrig, thetaInterval,
    trigRange, trigPoint, reducedMid, reducedRadius, quarterTurn, piInterval,
    widen, sinPoint, cosPoint, sinPoly, cosPoly, trigError,
    RatInterval.divPos, RatInterval.invPos, RatInterval.sq, RatInterval.mul,
    RatInterval.scale, RatInterval.sub, RatInterval.neg, RatInterval.add, List.cons_ne_nil]
lemma macroPiece2_check : macroPiece2.check = true := by
  norm_num [macroPiece2, MacroPiece.check, WellCert.check, WellCert.analyticPrereq, WellCert.midpoint, WellCert.radius,
    WellCert.point, WellCert.derivativePositive, orientedLower, absUpper,
    mtClosedDerivRange, mtClosedSecondRange, mtNumRange, mtNumDerivRange,
    mtNumSecondRange, mtDenDerivRange, mtDenSecondRange, kernelRange, kernelDenRange, rootTwoInterval, thetaTrig, thetaInterval,
    trigRange, trigPoint, reducedMid, reducedRadius, quarterTurn, piInterval,
    widen, sinPoint, cosPoint, sinPoly, cosPoly, trigError,
    RatInterval.divPos, RatInterval.invPos, RatInterval.sq, RatInterval.mul,
    RatInterval.scale, RatInterval.sub, RatInterval.neg, RatInterval.add, List.cons_ne_nil]
lemma macroPiece3_check : macroPiece3.check = true := by
  norm_num [macroPiece3, MacroPiece.check, WellCert.check, WellCert.analyticPrereq, WellCert.midpoint, WellCert.radius,
    WellCert.point, WellCert.derivativePositive, orientedLower, absUpper,
    mtClosedDerivRange, mtClosedSecondRange, mtNumRange, mtNumDerivRange,
    mtNumSecondRange, mtDenDerivRange, mtDenSecondRange, kernelRange, kernelDenRange, rootTwoInterval, thetaTrig, thetaInterval,
    trigRange, trigPoint, reducedMid, reducedRadius, quarterTurn, piInterval,
    widen, sinPoint, cosPoint, sinPoly, cosPoly, trigError,
    RatInterval.divPos, RatInterval.invPos, RatInterval.sq, RatInterval.mul,
    RatInterval.scale, RatInterval.sub, RatInterval.neg, RatInterval.add, List.cons_ne_nil]
lemma macroPiece4_check : macroPiece4.check = true := by
  norm_num [macroPiece4, MacroPiece.check, LowerPiece.check]
lemma macroPiece5_check : macroPiece5.check = true := by
  norm_num [macroPiece5, MacroPiece.check, WellCert.check, WellCert.analyticPrereq, WellCert.midpoint, WellCert.radius,
    WellCert.point, WellCert.derivativePositive, orientedLower, absUpper,
    mtClosedDerivRange, mtClosedSecondRange, mtNumRange, mtNumDerivRange,
    mtNumSecondRange, mtDenDerivRange, mtDenSecondRange, kernelRange, kernelDenRange, rootTwoInterval, thetaTrig, thetaInterval,
    trigRange, trigPoint, reducedMid, reducedRadius, quarterTurn, piInterval,
    widen, sinPoint, cosPoint, sinPoly, cosPoly, trigError,
    RatInterval.divPos, RatInterval.invPos, RatInterval.sq, RatInterval.mul,
    RatInterval.scale, RatInterval.sub, RatInterval.neg, RatInterval.add, List.cons_ne_nil]
lemma macroPiece6_check : macroPiece6.check = true := by
  norm_num [macroPiece6, MacroPiece.check, WellCert.check, WellCert.analyticPrereq, WellCert.midpoint, WellCert.radius,
    WellCert.point, WellCert.derivativePositive, orientedLower, absUpper,
    mtClosedDerivRange, mtClosedSecondRange, mtNumRange, mtNumDerivRange,
    mtNumSecondRange, mtDenDerivRange, mtDenSecondRange, kernelRange, kernelDenRange, rootTwoInterval, thetaTrig, thetaInterval,
    trigRange, trigPoint, reducedMid, reducedRadius, quarterTurn, piInterval,
    widen, sinPoint, cosPoint, sinPoly, cosPoly, trigError,
    RatInterval.divPos, RatInterval.invPos, RatInterval.sq, RatInterval.mul,
    RatInterval.scale, RatInterval.sub, RatInterval.neg, RatInterval.add, List.cons_ne_nil]
lemma macroPiece7_check : macroPiece7.check = true := by
  norm_num [macroPiece7, MacroPiece.check, LowerPiece.check, LowerPiece.coverFrom, LowerPiece.cellCheck,
    LowerPiece.cellModelUpper, LowerPiece.absLower, kernelRange, kernelDenRange, rootTwoInterval, thetaTrig, thetaInterval,
    trigRange, trigPoint, reducedMid, reducedRadius, quarterTurn, piInterval,
    widen, sinPoint, cosPoint, sinPoly, cosPoly, trigError,
    RatInterval.divPos, RatInterval.invPos, RatInterval.sq, RatInterval.mul,
    RatInterval.scale, RatInterval.sub, RatInterval.neg, RatInterval.add, List.cons_ne_nil]
lemma macroPiece8_check : macroPiece8.check = true := by
  norm_num [macroPiece8, MacroPiece.check, WellCert.check, WellCert.analyticPrereq, WellCert.midpoint, WellCert.radius,
    WellCert.point, WellCert.derivativePositive, orientedLower, absUpper,
    mtClosedDerivRange, mtClosedSecondRange, mtNumRange, mtNumDerivRange,
    mtNumSecondRange, mtDenDerivRange, mtDenSecondRange, kernelRange, kernelDenRange, rootTwoInterval, thetaTrig, thetaInterval,
    trigRange, trigPoint, reducedMid, reducedRadius, quarterTurn, piInterval,
    widen, sinPoint, cosPoint, sinPoly, cosPoly, trigError,
    RatInterval.divPos, RatInterval.invPos, RatInterval.sq, RatInterval.mul,
    RatInterval.scale, RatInterval.sub, RatInterval.neg, RatInterval.add, List.cons_ne_nil]
lemma macroPiece9_check : macroPiece9.check = true := by
  norm_num [macroPiece9, MacroPiece.check, WellCert.check, WellCert.analyticPrereq, WellCert.midpoint, WellCert.radius,
    WellCert.point, WellCert.derivativePositive, orientedLower, absUpper,
    mtClosedDerivRange, mtClosedSecondRange, mtNumRange, mtNumDerivRange,
    mtNumSecondRange, mtDenDerivRange, mtDenSecondRange, kernelRange, kernelDenRange, rootTwoInterval, thetaTrig, thetaInterval,
    trigRange, trigPoint, reducedMid, reducedRadius, quarterTurn, piInterval,
    widen, sinPoint, cosPoint, sinPoly, cosPoly, trigError,
    RatInterval.divPos, RatInterval.invPos, RatInterval.sq, RatInterval.mul,
    RatInterval.scale, RatInterval.sub, RatInterval.neg, RatInterval.add, List.cons_ne_nil]
lemma macroPiece10_check : macroPiece10.check = true := by
  norm_num [macroPiece10, MacroPiece.check, LowerPiece.check]
lemma macroPiece11_check : macroPiece11.check = true := by
  norm_num [macroPiece11, MacroPiece.check, WellCert.check, WellCert.analyticPrereq, WellCert.midpoint, WellCert.radius,
    WellCert.point, WellCert.derivativePositive, orientedLower, absUpper,
    mtClosedDerivRange, mtClosedSecondRange, mtNumRange, mtNumDerivRange,
    mtNumSecondRange, mtDenDerivRange, mtDenSecondRange, kernelRange, kernelDenRange, rootTwoInterval, thetaTrig, thetaInterval,
    trigRange, trigPoint, reducedMid, reducedRadius, quarterTurn, piInterval,
    widen, sinPoint, cosPoint, sinPoly, cosPoly, trigError,
    RatInterval.divPos, RatInterval.invPos, RatInterval.sq, RatInterval.mul,
    RatInterval.scale, RatInterval.sub, RatInterval.neg, RatInterval.add, List.cons_ne_nil]
lemma macroPiece12_check : macroPiece12.check = true := by
  norm_num [macroPiece12, MacroPiece.check, WellCert.check, WellCert.analyticPrereq, WellCert.midpoint, WellCert.radius,
    WellCert.point, WellCert.derivativePositive, orientedLower, absUpper,
    mtClosedDerivRange, mtClosedSecondRange, mtNumRange, mtNumDerivRange,
    mtNumSecondRange, mtDenDerivRange, mtDenSecondRange, kernelRange, kernelDenRange, rootTwoInterval, thetaTrig, thetaInterval,
    trigRange, trigPoint, reducedMid, reducedRadius, quarterTurn, piInterval,
    widen, sinPoint, cosPoint, sinPoly, cosPoly, trigError,
    RatInterval.divPos, RatInterval.invPos, RatInterval.sq, RatInterval.mul,
    RatInterval.scale, RatInterval.sub, RatInterval.neg, RatInterval.add, List.cons_ne_nil]
lemma macroPiece13_check : macroPiece13.check = true := by
  norm_num [macroPiece13, MacroPiece.check, LowerPiece.check, LowerPiece.coverFrom, LowerPiece.cellCheck,
    LowerPiece.cellModelUpper, LowerPiece.absLower, kernelRange, kernelDenRange, rootTwoInterval, thetaTrig, thetaInterval,
    trigRange, trigPoint, reducedMid, reducedRadius, quarterTurn, piInterval,
    widen, sinPoint, cosPoint, sinPoly, cosPoly, trigError,
    RatInterval.divPos, RatInterval.invPos, RatInterval.sq, RatInterval.mul,
    RatInterval.scale, RatInterval.sub, RatInterval.neg, RatInterval.add, List.cons_ne_nil]
lemma macroPiece14_check : macroPiece14.check = true := by
  norm_num [macroPiece14, MacroPiece.check, WellCert.check, WellCert.analyticPrereq, WellCert.midpoint, WellCert.radius,
    WellCert.point, WellCert.derivativePositive, orientedLower, absUpper,
    mtClosedDerivRange, mtClosedSecondRange, mtNumRange, mtNumDerivRange,
    mtNumSecondRange, mtDenDerivRange, mtDenSecondRange, kernelRange, kernelDenRange, rootTwoInterval, thetaTrig, thetaInterval,
    trigRange, trigPoint, reducedMid, reducedRadius, quarterTurn, piInterval,
    widen, sinPoint, cosPoint, sinPoly, cosPoly, trigError,
    RatInterval.divPos, RatInterval.invPos, RatInterval.sq, RatInterval.mul,
    RatInterval.scale, RatInterval.sub, RatInterval.neg, RatInterval.add, List.cons_ne_nil]
lemma macroPiece15_check : macroPiece15.check = true := by
  norm_num [macroPiece15, MacroPiece.check, WellCert.check, WellCert.analyticPrereq, WellCert.midpoint, WellCert.radius,
    WellCert.point, WellCert.derivativePositive, orientedLower, absUpper,
    mtClosedDerivRange, mtClosedSecondRange, mtNumRange, mtNumDerivRange,
    mtNumSecondRange, mtDenDerivRange, mtDenSecondRange, kernelRange, kernelDenRange, rootTwoInterval, thetaTrig, thetaInterval,
    trigRange, trigPoint, reducedMid, reducedRadius, quarterTurn, piInterval,
    widen, sinPoint, cosPoint, sinPoly, cosPoly, trigError,
    RatInterval.divPos, RatInterval.invPos, RatInterval.sq, RatInterval.mul,
    RatInterval.scale, RatInterval.sub, RatInterval.neg, RatInterval.add, List.cons_ne_nil]
lemma macroPiece16_check : macroPiece16.check = true := by
  norm_num [macroPiece16, MacroPiece.check, LowerPiece.check]
lemma macroPiece17_check : macroPiece17.check = true := by
  norm_num [macroPiece17, MacroPiece.check, WellCert.check, WellCert.analyticPrereq, WellCert.midpoint, WellCert.radius,
    WellCert.point, WellCert.derivativePositive, orientedLower, absUpper,
    mtClosedDerivRange, mtClosedSecondRange, mtNumRange, mtNumDerivRange,
    mtNumSecondRange, mtDenDerivRange, mtDenSecondRange, kernelRange, kernelDenRange, rootTwoInterval, thetaTrig, thetaInterval,
    trigRange, trigPoint, reducedMid, reducedRadius, quarterTurn, piInterval,
    widen, sinPoint, cosPoint, sinPoly, cosPoly, trigError,
    RatInterval.divPos, RatInterval.invPos, RatInterval.sq, RatInterval.mul,
    RatInterval.scale, RatInterval.sub, RatInterval.neg, RatInterval.add, List.cons_ne_nil]
lemma macroPiece18_check : macroPiece18.check = true := by
  norm_num [macroPiece18, MacroPiece.check, WellCert.check, WellCert.analyticPrereq, WellCert.midpoint, WellCert.radius,
    WellCert.point, WellCert.derivativePositive, orientedLower, absUpper,
    mtClosedDerivRange, mtClosedSecondRange, mtNumRange, mtNumDerivRange,
    mtNumSecondRange, mtDenDerivRange, mtDenSecondRange, kernelRange, kernelDenRange, rootTwoInterval, thetaTrig, thetaInterval,
    trigRange, trigPoint, reducedMid, reducedRadius, quarterTurn, piInterval,
    widen, sinPoint, cosPoint, sinPoly, cosPoly, trigError,
    RatInterval.divPos, RatInterval.invPos, RatInterval.sq, RatInterval.mul,
    RatInterval.scale, RatInterval.sub, RatInterval.neg, RatInterval.add, List.cons_ne_nil]
lemma macroPiece19_check : macroPiece19.check = true := by
  norm_num [macroPiece19, MacroPiece.check, LowerPiece.check, LowerPiece.coverFrom, LowerPiece.cellCheck,
    LowerPiece.cellModelUpper, LowerPiece.absLower, kernelRange, kernelDenRange, rootTwoInterval, thetaTrig, thetaInterval,
    trigRange, trigPoint, reducedMid, reducedRadius, quarterTurn, piInterval,
    widen, sinPoint, cosPoint, sinPoly, cosPoly, trigError,
    RatInterval.divPos, RatInterval.invPos, RatInterval.sq, RatInterval.mul,
    RatInterval.scale, RatInterval.sub, RatInterval.neg, RatInterval.add, List.cons_ne_nil]
lemma macroPiece20_check : macroPiece20.check = true := by
  norm_num [macroPiece20, MacroPiece.check, WellCert.check, WellCert.analyticPrereq, WellCert.midpoint, WellCert.radius,
    WellCert.point, WellCert.derivativePositive, orientedLower, absUpper,
    mtClosedDerivRange, mtClosedSecondRange, mtNumRange, mtNumDerivRange,
    mtNumSecondRange, mtDenDerivRange, mtDenSecondRange, kernelRange, kernelDenRange, rootTwoInterval, thetaTrig, thetaInterval,
    trigRange, trigPoint, reducedMid, reducedRadius, quarterTurn, piInterval,
    widen, sinPoint, cosPoint, sinPoly, cosPoly, trigError,
    RatInterval.divPos, RatInterval.invPos, RatInterval.sq, RatInterval.mul,
    RatInterval.scale, RatInterval.sub, RatInterval.neg, RatInterval.add, List.cons_ne_nil]
lemma macroPiece21_check : macroPiece21.check = true := by
  norm_num [macroPiece21, MacroPiece.check, WellCert.check, WellCert.analyticPrereq, WellCert.midpoint, WellCert.radius,
    WellCert.point, WellCert.derivativePositive, orientedLower, absUpper,
    mtClosedDerivRange, mtClosedSecondRange, mtNumRange, mtNumDerivRange,
    mtNumSecondRange, mtDenDerivRange, mtDenSecondRange, kernelRange, kernelDenRange, rootTwoInterval, thetaTrig, thetaInterval,
    trigRange, trigPoint, reducedMid, reducedRadius, quarterTurn, piInterval,
    widen, sinPoint, cosPoint, sinPoly, cosPoly, trigError,
    RatInterval.divPos, RatInterval.invPos, RatInterval.sq, RatInterval.mul,
    RatInterval.scale, RatInterval.sub, RatInterval.neg, RatInterval.add, List.cons_ne_nil]
lemma macroPiece22_check : macroPiece22.check = true := by
  norm_num [macroPiece22, MacroPiece.check, LowerPiece.check]
lemma macroPiece23_check : macroPiece23.check = true := by
  norm_num [macroPiece23, MacroPiece.check, WellCert.check, WellCert.analyticPrereq, WellCert.midpoint, WellCert.radius,
    WellCert.point, WellCert.derivativePositive, orientedLower, absUpper,
    mtClosedDerivRange, mtClosedSecondRange, mtNumRange, mtNumDerivRange,
    mtNumSecondRange, mtDenDerivRange, mtDenSecondRange, kernelRange, kernelDenRange, rootTwoInterval, thetaTrig, thetaInterval,
    trigRange, trigPoint, reducedMid, reducedRadius, quarterTurn, piInterval,
    widen, sinPoint, cosPoint, sinPoly, cosPoly, trigError,
    RatInterval.divPos, RatInterval.invPos, RatInterval.sq, RatInterval.mul,
    RatInterval.scale, RatInterval.sub, RatInterval.neg, RatInterval.add, List.cons_ne_nil]
lemma macroPiece24_check : macroPiece24.check = true := by
  norm_num [macroPiece24, MacroPiece.check, WellCert.check, WellCert.analyticPrereq, WellCert.midpoint, WellCert.radius,
    WellCert.point, WellCert.derivativePositive, orientedLower, absUpper,
    mtClosedDerivRange, mtClosedSecondRange, mtNumRange, mtNumDerivRange,
    mtNumSecondRange, mtDenDerivRange, mtDenSecondRange, kernelRange, kernelDenRange, rootTwoInterval, thetaTrig, thetaInterval,
    trigRange, trigPoint, reducedMid, reducedRadius, quarterTurn, piInterval,
    widen, sinPoint, cosPoint, sinPoly, cosPoly, trigError,
    RatInterval.divPos, RatInterval.invPos, RatInterval.sq, RatInterval.mul,
    RatInterval.scale, RatInterval.sub, RatInterval.neg, RatInterval.add, List.cons_ne_nil]
lemma macroPiece25_check : macroPiece25.check = true := by
  norm_num [macroPiece25, MacroPiece.check, LowerPiece.check, LowerPiece.coverFrom, LowerPiece.cellCheck,
    LowerPiece.cellModelUpper, LowerPiece.absLower, kernelRange, kernelDenRange, rootTwoInterval, thetaTrig, thetaInterval,
    trigRange, trigPoint, reducedMid, reducedRadius, quarterTurn, piInterval,
    widen, sinPoint, cosPoint, sinPoly, cosPoly, trigError,
    RatInterval.divPos, RatInterval.invPos, RatInterval.sq, RatInterval.mul,
    RatInterval.scale, RatInterval.sub, RatInterval.neg, RatInterval.add, List.cons_ne_nil]
lemma macroPiece26_check : macroPiece26.check = true := by
  norm_num [macroPiece26, MacroPiece.check, WellCert.check, WellCert.analyticPrereq, WellCert.midpoint, WellCert.radius,
    WellCert.point, WellCert.derivativePositive, orientedLower, absUpper,
    mtClosedDerivRange, mtClosedSecondRange, mtNumRange, mtNumDerivRange,
    mtNumSecondRange, mtDenDerivRange, mtDenSecondRange, kernelRange, kernelDenRange, rootTwoInterval, thetaTrig, thetaInterval,
    trigRange, trigPoint, reducedMid, reducedRadius, quarterTurn, piInterval,
    widen, sinPoint, cosPoint, sinPoly, cosPoly, trigError,
    RatInterval.divPos, RatInterval.invPos, RatInterval.sq, RatInterval.mul,
    RatInterval.scale, RatInterval.sub, RatInterval.neg, RatInterval.add, List.cons_ne_nil]
lemma macroPiece27_check : macroPiece27.check = true := by
  norm_num [macroPiece27, MacroPiece.check, WellCert.check, WellCert.analyticPrereq, WellCert.midpoint, WellCert.radius,
    WellCert.point, WellCert.derivativePositive, orientedLower, absUpper,
    mtClosedDerivRange, mtClosedSecondRange, mtNumRange, mtNumDerivRange,
    mtNumSecondRange, mtDenDerivRange, mtDenSecondRange, kernelRange, kernelDenRange, rootTwoInterval, thetaTrig, thetaInterval,
    trigRange, trigPoint, reducedMid, reducedRadius, quarterTurn, piInterval,
    widen, sinPoint, cosPoint, sinPoly, cosPoly, trigError,
    RatInterval.divPos, RatInterval.invPos, RatInterval.sq, RatInterval.mul,
    RatInterval.scale, RatInterval.sub, RatInterval.neg, RatInterval.add, List.cons_ne_nil]
lemma macroPiece28_check : macroPiece28.check = true := by
  norm_num [macroPiece28, MacroPiece.check, LowerPiece.check]
lemma macroPiece29_check : macroPiece29.check = true := by
  norm_num [macroPiece29, MacroPiece.check, WellCert.check, WellCert.analyticPrereq, WellCert.midpoint, WellCert.radius,
    WellCert.point, WellCert.derivativePositive, orientedLower, absUpper,
    mtClosedDerivRange, mtClosedSecondRange, mtNumRange, mtNumDerivRange,
    mtNumSecondRange, mtDenDerivRange, mtDenSecondRange, kernelRange, kernelDenRange, rootTwoInterval, thetaTrig, thetaInterval,
    trigRange, trigPoint, reducedMid, reducedRadius, quarterTurn, piInterval,
    widen, sinPoint, cosPoint, sinPoly, cosPoly, trigError,
    RatInterval.divPos, RatInterval.invPos, RatInterval.sq, RatInterval.mul,
    RatInterval.scale, RatInterval.sub, RatInterval.neg, RatInterval.add, List.cons_ne_nil]
lemma macroPiece30_check : macroPiece30.check = true := by
  norm_num [macroPiece30, MacroPiece.check, WellCert.check, WellCert.analyticPrereq, WellCert.midpoint, WellCert.radius,
    WellCert.point, WellCert.derivativePositive, orientedLower, absUpper,
    mtClosedDerivRange, mtClosedSecondRange, mtNumRange, mtNumDerivRange,
    mtNumSecondRange, mtDenDerivRange, mtDenSecondRange, kernelRange, kernelDenRange, rootTwoInterval, thetaTrig, thetaInterval,
    trigRange, trigPoint, reducedMid, reducedRadius, quarterTurn, piInterval,
    widen, sinPoint, cosPoint, sinPoly, cosPoly, trigError,
    RatInterval.divPos, RatInterval.invPos, RatInterval.sq, RatInterval.mul,
    RatInterval.scale, RatInterval.sub, RatInterval.neg, RatInterval.add, List.cons_ne_nil]
lemma macroPiece31_check : macroPiece31.check = true := by
  norm_num [macroPiece31, MacroPiece.check, LowerPiece.check, LowerPiece.coverFrom, LowerPiece.cellCheck,
    LowerPiece.cellModelUpper, LowerPiece.absLower, kernelRange, kernelDenRange, rootTwoInterval, thetaTrig, thetaInterval,
    trigRange, trigPoint, reducedMid, reducedRadius, quarterTurn, piInterval,
    widen, sinPoint, cosPoint, sinPoly, cosPoly, trigError,
    RatInterval.divPos, RatInterval.invPos, RatInterval.sq, RatInterval.mul,
    RatInterval.scale, RatInterval.sub, RatInterval.neg, RatInterval.add, List.cons_ne_nil]
lemma macroPiece32_check : macroPiece32.check = true := by
  norm_num [macroPiece32, MacroPiece.check, WellCert.check, WellCert.analyticPrereq, WellCert.midpoint, WellCert.radius,
    WellCert.point, WellCert.derivativePositive, orientedLower, absUpper,
    mtClosedDerivRange, mtClosedSecondRange, mtNumRange, mtNumDerivRange,
    mtNumSecondRange, mtDenDerivRange, mtDenSecondRange, kernelRange, kernelDenRange, rootTwoInterval, thetaTrig, thetaInterval,
    trigRange, trigPoint, reducedMid, reducedRadius, quarterTurn, piInterval,
    widen, sinPoint, cosPoint, sinPoly, cosPoly, trigError,
    RatInterval.divPos, RatInterval.invPos, RatInterval.sq, RatInterval.mul,
    RatInterval.scale, RatInterval.sub, RatInterval.neg, RatInterval.add, List.cons_ne_nil]
lemma macroPiece33_check : macroPiece33.check = true := by
  norm_num [macroPiece33, MacroPiece.check, WellCert.check, WellCert.analyticPrereq, WellCert.midpoint, WellCert.radius,
    WellCert.point, WellCert.derivativePositive, orientedLower, absUpper,
    mtClosedDerivRange, mtClosedSecondRange, mtNumRange, mtNumDerivRange,
    mtNumSecondRange, mtDenDerivRange, mtDenSecondRange, kernelRange, kernelDenRange, rootTwoInterval, thetaTrig, thetaInterval,
    trigRange, trigPoint, reducedMid, reducedRadius, quarterTurn, piInterval,
    widen, sinPoint, cosPoint, sinPoly, cosPoly, trigError,
    RatInterval.divPos, RatInterval.invPos, RatInterval.sq, RatInterval.mul,
    RatInterval.scale, RatInterval.sub, RatInterval.neg, RatInterval.add, List.cons_ne_nil]
lemma macroPiece34_check : macroPiece34.check = true := by
  norm_num [macroPiece34, MacroPiece.check, LowerPiece.check]
lemma macroPiece35_check : macroPiece35.check = true := by
  norm_num [macroPiece35, MacroPiece.check, WellCert.check, WellCert.analyticPrereq, WellCert.midpoint, WellCert.radius,
    WellCert.point, WellCert.derivativePositive, orientedLower, absUpper,
    mtClosedDerivRange, mtClosedSecondRange, mtNumRange, mtNumDerivRange,
    mtNumSecondRange, mtDenDerivRange, mtDenSecondRange, kernelRange, kernelDenRange, rootTwoInterval, thetaTrig, thetaInterval,
    trigRange, trigPoint, reducedMid, reducedRadius, quarterTurn, piInterval,
    widen, sinPoint, cosPoint, sinPoly, cosPoly, trigError,
    RatInterval.divPos, RatInterval.invPos, RatInterval.sq, RatInterval.mul,
    RatInterval.scale, RatInterval.sub, RatInterval.neg, RatInterval.add, List.cons_ne_nil]
lemma macroPiece36_check : macroPiece36.check = true := by
  norm_num [macroPiece36, MacroPiece.check, WellCert.check, WellCert.analyticPrereq, WellCert.midpoint, WellCert.radius,
    WellCert.point, WellCert.derivativePositive, orientedLower, absUpper,
    mtClosedDerivRange, mtClosedSecondRange, mtNumRange, mtNumDerivRange,
    mtNumSecondRange, mtDenDerivRange, mtDenSecondRange, kernelRange, kernelDenRange, rootTwoInterval, thetaTrig, thetaInterval,
    trigRange, trigPoint, reducedMid, reducedRadius, quarterTurn, piInterval,
    widen, sinPoint, cosPoint, sinPoly, cosPoly, trigError,
    RatInterval.divPos, RatInterval.invPos, RatInterval.sq, RatInterval.mul,
    RatInterval.scale, RatInterval.sub, RatInterval.neg, RatInterval.add, List.cons_ne_nil]
lemma macroPiece37_check : macroPiece37.check = true := by
  norm_num [macroPiece37, MacroPiece.check, LowerPiece.check, LowerPiece.coverFrom, LowerPiece.cellCheck,
    LowerPiece.cellModelUpper, LowerPiece.absLower, kernelRange, kernelDenRange, rootTwoInterval, thetaTrig, thetaInterval,
    trigRange, trigPoint, reducedMid, reducedRadius, quarterTurn, piInterval,
    widen, sinPoint, cosPoint, sinPoly, cosPoly, trigError,
    RatInterval.divPos, RatInterval.invPos, RatInterval.sq, RatInterval.mul,
    RatInterval.scale, RatInterval.sub, RatInterval.neg, RatInterval.add, List.cons_ne_nil]
lemma macroPiece38_check : macroPiece38.check = true := by
  norm_num [macroPiece38, MacroPiece.check, WellCert.check, WellCert.analyticPrereq, WellCert.midpoint, WellCert.radius,
    WellCert.point, WellCert.derivativePositive, orientedLower, absUpper,
    mtClosedDerivRange, mtClosedSecondRange, mtNumRange, mtNumDerivRange,
    mtNumSecondRange, mtDenDerivRange, mtDenSecondRange, kernelRange, kernelDenRange, rootTwoInterval, thetaTrig, thetaInterval,
    trigRange, trigPoint, reducedMid, reducedRadius, quarterTurn, piInterval,
    widen, sinPoint, cosPoint, sinPoly, cosPoly, trigError,
    RatInterval.divPos, RatInterval.invPos, RatInterval.sq, RatInterval.mul,
    RatInterval.scale, RatInterval.sub, RatInterval.neg, RatInterval.add, List.cons_ne_nil]
lemma macroPiece39_check : macroPiece39.check = true := by
  norm_num [macroPiece39, MacroPiece.check, WellCert.check, WellCert.analyticPrereq, WellCert.midpoint, WellCert.radius,
    WellCert.point, WellCert.derivativePositive, orientedLower, absUpper,
    mtClosedDerivRange, mtClosedSecondRange, mtNumRange, mtNumDerivRange,
    mtNumSecondRange, mtDenDerivRange, mtDenSecondRange, kernelRange, kernelDenRange, rootTwoInterval, thetaTrig, thetaInterval,
    trigRange, trigPoint, reducedMid, reducedRadius, quarterTurn, piInterval,
    widen, sinPoint, cosPoint, sinPoly, cosPoly, trigError,
    RatInterval.divPos, RatInterval.invPos, RatInterval.sq, RatInterval.mul,
    RatInterval.scale, RatInterval.sub, RatInterval.neg, RatInterval.add, List.cons_ne_nil]
lemma macroPiece40_check : macroPiece40.check = true := by
  norm_num [macroPiece40, MacroPiece.check, LowerPiece.check]
lemma macroPiece41_check : macroPiece41.check = true := by
  norm_num [macroPiece41, MacroPiece.check, WellCert.check, WellCert.analyticPrereq, WellCert.midpoint, WellCert.radius,
    WellCert.point, WellCert.derivativePositive, orientedLower, absUpper,
    mtClosedDerivRange, mtClosedSecondRange, mtNumRange, mtNumDerivRange,
    mtNumSecondRange, mtDenDerivRange, mtDenSecondRange, kernelRange, kernelDenRange, rootTwoInterval, thetaTrig, thetaInterval,
    trigRange, trigPoint, reducedMid, reducedRadius, quarterTurn, piInterval,
    widen, sinPoint, cosPoint, sinPoly, cosPoly, trigError,
    RatInterval.divPos, RatInterval.invPos, RatInterval.sq, RatInterval.mul,
    RatInterval.scale, RatInterval.sub, RatInterval.neg, RatInterval.add, List.cons_ne_nil]
lemma macroPiece42_check : macroPiece42.check = true := by
  norm_num [macroPiece42, MacroPiece.check, WellCert.check, WellCert.analyticPrereq, WellCert.midpoint, WellCert.radius,
    WellCert.point, WellCert.derivativePositive, orientedLower, absUpper,
    mtClosedDerivRange, mtClosedSecondRange, mtNumRange, mtNumDerivRange,
    mtNumSecondRange, mtDenDerivRange, mtDenSecondRange, kernelRange, kernelDenRange, rootTwoInterval, thetaTrig, thetaInterval,
    trigRange, trigPoint, reducedMid, reducedRadius, quarterTurn, piInterval,
    widen, sinPoint, cosPoint, sinPoly, cosPoly, trigError,
    RatInterval.divPos, RatInterval.invPos, RatInterval.sq, RatInterval.mul,
    RatInterval.scale, RatInterval.sub, RatInterval.neg, RatInterval.add, List.cons_ne_nil]
lemma macroPiece43_check : macroPiece43.check = true := by
  norm_num [macroPiece43, MacroPiece.check, LowerPiece.check, LowerPiece.coverFrom, LowerPiece.cellCheck,
    LowerPiece.cellModelUpper, LowerPiece.absLower, kernelRange, kernelDenRange, rootTwoInterval, thetaTrig, thetaInterval,
    trigRange, trigPoint, reducedMid, reducedRadius, quarterTurn, piInterval,
    widen, sinPoint, cosPoint, sinPoly, cosPoly, trigError,
    RatInterval.divPos, RatInterval.invPos, RatInterval.sq, RatInterval.mul,
    RatInterval.scale, RatInterval.sub, RatInterval.neg, RatInterval.add, List.cons_ne_nil]
lemma macroPiece44_check : macroPiece44.check = true := by
  norm_num [macroPiece44, MacroPiece.check, WellCert.check, WellCert.analyticPrereq, WellCert.midpoint, WellCert.radius,
    WellCert.point, WellCert.derivativePositive, orientedLower, absUpper,
    mtClosedDerivRange, mtClosedSecondRange, mtNumRange, mtNumDerivRange,
    mtNumSecondRange, mtDenDerivRange, mtDenSecondRange, kernelRange, kernelDenRange, rootTwoInterval, thetaTrig, thetaInterval,
    trigRange, trigPoint, reducedMid, reducedRadius, quarterTurn, piInterval,
    widen, sinPoint, cosPoint, sinPoly, cosPoly, trigError,
    RatInterval.divPos, RatInterval.invPos, RatInterval.sq, RatInterval.mul,
    RatInterval.scale, RatInterval.sub, RatInterval.neg, RatInterval.add, List.cons_ne_nil]
lemma macroPiece45_check : macroPiece45.check = true := by
  norm_num [macroPiece45, MacroPiece.check, WellCert.check, WellCert.analyticPrereq, WellCert.midpoint, WellCert.radius,
    WellCert.point, WellCert.derivativePositive, orientedLower, absUpper,
    mtClosedDerivRange, mtClosedSecondRange, mtNumRange, mtNumDerivRange,
    mtNumSecondRange, mtDenDerivRange, mtDenSecondRange, kernelRange, kernelDenRange, rootTwoInterval, thetaTrig, thetaInterval,
    trigRange, trigPoint, reducedMid, reducedRadius, quarterTurn, piInterval,
    widen, sinPoint, cosPoint, sinPoly, cosPoly, trigError,
    RatInterval.divPos, RatInterval.invPos, RatInterval.sq, RatInterval.mul,
    RatInterval.scale, RatInterval.sub, RatInterval.neg, RatInterval.add, List.cons_ne_nil]
lemma macroPiece46_check : macroPiece46.check = true := by
  norm_num [macroPiece46, MacroPiece.check, LowerPiece.check]
lemma macroPiece47_check : macroPiece47.check = true := by
  norm_num [macroPiece47, MacroPiece.check, WellCert.check, WellCert.analyticPrereq, WellCert.midpoint, WellCert.radius,
    WellCert.point, WellCert.derivativePositive, orientedLower, absUpper,
    mtClosedDerivRange, mtClosedSecondRange, mtNumRange, mtNumDerivRange,
    mtNumSecondRange, mtDenDerivRange, mtDenSecondRange, kernelRange, kernelDenRange, rootTwoInterval, thetaTrig, thetaInterval,
    trigRange, trigPoint, reducedMid, reducedRadius, quarterTurn, piInterval,
    widen, sinPoint, cosPoint, sinPoly, cosPoly, trigError,
    RatInterval.divPos, RatInterval.invPos, RatInterval.sq, RatInterval.mul,
    RatInterval.scale, RatInterval.sub, RatInterval.neg, RatInterval.add, List.cons_ne_nil]
lemma macroPiece48_check : macroPiece48.check = true := by
  norm_num [macroPiece48, MacroPiece.check, WellCert.check, WellCert.analyticPrereq, WellCert.midpoint, WellCert.radius,
    WellCert.point, WellCert.derivativePositive, orientedLower, absUpper,
    mtClosedDerivRange, mtClosedSecondRange, mtNumRange, mtNumDerivRange,
    mtNumSecondRange, mtDenDerivRange, mtDenSecondRange, kernelRange, kernelDenRange, rootTwoInterval, thetaTrig, thetaInterval,
    trigRange, trigPoint, reducedMid, reducedRadius, quarterTurn, piInterval,
    widen, sinPoint, cosPoint, sinPoly, cosPoly, trigError,
    RatInterval.divPos, RatInterval.invPos, RatInterval.sq, RatInterval.mul,
    RatInterval.scale, RatInterval.sub, RatInterval.neg, RatInterval.add, List.cons_ne_nil]
lemma macroPiece49_check : macroPiece49.check = true := by
  norm_num [macroPiece49, MacroPiece.check, LowerPiece.check, LowerPiece.coverFrom, LowerPiece.cellCheck,
    LowerPiece.cellModelUpper, LowerPiece.absLower, kernelRange, kernelDenRange, rootTwoInterval, thetaTrig, thetaInterval,
    trigRange, trigPoint, reducedMid, reducedRadius, quarterTurn, piInterval,
    widen, sinPoint, cosPoint, sinPoly, cosPoly, trigError,
    RatInterval.divPos, RatInterval.invPos, RatInterval.sq, RatInterval.mul,
    RatInterval.scale, RatInterval.sub, RatInterval.neg, RatInterval.add, List.cons_ne_nil]
lemma macroPiece50_check : macroPiece50.check = true := by
  norm_num [macroPiece50, MacroPiece.check, WellCert.check, WellCert.analyticPrereq, WellCert.midpoint, WellCert.radius,
    WellCert.point, WellCert.derivativePositive, orientedLower, absUpper,
    mtClosedDerivRange, mtClosedSecondRange, mtNumRange, mtNumDerivRange,
    mtNumSecondRange, mtDenDerivRange, mtDenSecondRange, kernelRange, kernelDenRange, rootTwoInterval, thetaTrig, thetaInterval,
    trigRange, trigPoint, reducedMid, reducedRadius, quarterTurn, piInterval,
    widen, sinPoint, cosPoint, sinPoly, cosPoly, trigError,
    RatInterval.divPos, RatInterval.invPos, RatInterval.sq, RatInterval.mul,
    RatInterval.scale, RatInterval.sub, RatInterval.neg, RatInterval.add, List.cons_ne_nil]
lemma macroPiece51_check : macroPiece51.check = true := by
  norm_num [macroPiece51, MacroPiece.check, WellCert.check, WellCert.analyticPrereq, WellCert.midpoint, WellCert.radius,
    WellCert.point, WellCert.derivativePositive, orientedLower, absUpper,
    mtClosedDerivRange, mtClosedSecondRange, mtNumRange, mtNumDerivRange,
    mtNumSecondRange, mtDenDerivRange, mtDenSecondRange, kernelRange, kernelDenRange, rootTwoInterval, thetaTrig, thetaInterval,
    trigRange, trigPoint, reducedMid, reducedRadius, quarterTurn, piInterval,
    widen, sinPoint, cosPoint, sinPoly, cosPoly, trigError,
    RatInterval.divPos, RatInterval.invPos, RatInterval.sq, RatInterval.mul,
    RatInterval.scale, RatInterval.sub, RatInterval.neg, RatInterval.add, List.cons_ne_nil]
lemma macroPiece52_check : macroPiece52.check = true := by
  norm_num [macroPiece52, MacroPiece.check, LowerPiece.check]
lemma macroPiece53_check : macroPiece53.check = true := by
  norm_num [macroPiece53, MacroPiece.check, WellCert.check, WellCert.analyticPrereq, WellCert.midpoint, WellCert.radius,
    WellCert.point, WellCert.derivativePositive, orientedLower, absUpper,
    mtClosedDerivRange, mtClosedSecondRange, mtNumRange, mtNumDerivRange,
    mtNumSecondRange, mtDenDerivRange, mtDenSecondRange, kernelRange, kernelDenRange, rootTwoInterval, thetaTrig, thetaInterval,
    trigRange, trigPoint, reducedMid, reducedRadius, quarterTurn, piInterval,
    widen, sinPoint, cosPoint, sinPoly, cosPoly, trigError,
    RatInterval.divPos, RatInterval.invPos, RatInterval.sq, RatInterval.mul,
    RatInterval.scale, RatInterval.sub, RatInterval.neg, RatInterval.add, List.cons_ne_nil]
lemma macroPiece54_check : macroPiece54.check = true := by
  norm_num [macroPiece54, MacroPiece.check, WellCert.check, WellCert.analyticPrereq, WellCert.midpoint, WellCert.radius,
    WellCert.point, WellCert.derivativePositive, orientedLower, absUpper,
    mtClosedDerivRange, mtClosedSecondRange, mtNumRange, mtNumDerivRange,
    mtNumSecondRange, mtDenDerivRange, mtDenSecondRange, kernelRange, kernelDenRange, rootTwoInterval, thetaTrig, thetaInterval,
    trigRange, trigPoint, reducedMid, reducedRadius, quarterTurn, piInterval,
    widen, sinPoint, cosPoint, sinPoly, cosPoly, trigError,
    RatInterval.divPos, RatInterval.invPos, RatInterval.sq, RatInterval.mul,
    RatInterval.scale, RatInterval.sub, RatInterval.neg, RatInterval.add, List.cons_ne_nil]
lemma macroPiece55_check : macroPiece55.check = true := by
  norm_num [macroPiece55, MacroPiece.check, LowerPiece.check, LowerPiece.coverFrom, LowerPiece.cellCheck,
    LowerPiece.cellModelUpper, LowerPiece.absLower, kernelRange, kernelDenRange, rootTwoInterval, thetaTrig, thetaInterval,
    trigRange, trigPoint, reducedMid, reducedRadius, quarterTurn, piInterval,
    widen, sinPoint, cosPoint, sinPoly, cosPoly, trigError,
    RatInterval.divPos, RatInterval.invPos, RatInterval.sq, RatInterval.mul,
    RatInterval.scale, RatInterval.sub, RatInterval.neg, RatInterval.add, List.cons_ne_nil]

lemma macroPieces_cover : macroCoverFrom 0 59 macroPieces = true := by
  norm_num [macroPieces, macroCoverFrom, MacroPiece.box, macroPiece0, macroPiece1, macroPiece2, macroPiece3, macroPiece4, macroPiece5, macroPiece6, macroPiece7, macroPiece8, macroPiece9, macroPiece10, macroPiece11, macroPiece12, macroPiece13, macroPiece14, macroPiece15, macroPiece16, macroPiece17, macroPiece18, macroPiece19, macroPiece20, macroPiece21, macroPiece22, macroPiece23, macroPiece24, macroPiece25, macroPiece26, macroPiece27, macroPiece28, macroPiece29, macroPiece30, macroPiece31, macroPiece32, macroPiece33, macroPiece34, macroPiece35, macroPiece36, macroPiece37, macroPiece38, macroPiece39, macroPiece40, macroPiece41, macroPiece42, macroPiece43, macroPiece44, macroPiece45, macroPiece46, macroPiece47, macroPiece48, macroPiece49, macroPiece50, macroPiece51, macroPiece52, macroPiece53, macroPiece54, macroPiece55]

lemma macroPieces_all : macroPieces.all MacroPiece.check = true := by
  simp [macroPieces, macroPiece0_check, macroPiece1_check, macroPiece2_check, macroPiece3_check, macroPiece4_check, macroPiece5_check, macroPiece6_check, macroPiece7_check, macroPiece8_check, macroPiece9_check, macroPiece10_check, macroPiece11_check, macroPiece12_check, macroPiece13_check, macroPiece14_check, macroPiece15_check, macroPiece16_check, macroPiece17_check, macroPiece18_check, macroPiece19_check, macroPiece20_check, macroPiece21_check, macroPiece22_check, macroPiece23_check, macroPiece24_check, macroPiece25_check, macroPiece26_check, macroPiece27_check, macroPiece28_check, macroPiece29_check, macroPiece30_check, macroPiece31_check, macroPiece32_check, macroPiece33_check, macroPiece34_check, macroPiece35_check, macroPiece36_check, macroPiece37_check, macroPiece38_check, macroPiece39_check, macroPiece40_check, macroPiece41_check, macroPiece42_check, macroPiece43_check, macroPiece44_check, macroPiece45_check, macroPiece46_check, macroPiece47_check, macroPiece48_check, macroPiece49_check, macroPiece50_check, macroPiece51_check, macroPiece52_check, macroPiece53_check, macroPiece54_check, macroPiece55_check]

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem macroPieces_check : checkMacroPieces 0 59 macroPieces = true := by
  unfold checkMacroPieces
  rw [macroPieces_cover, macroPieces_all]
  have hne : macroPieces ≠ [] := by
    unfold macroPieces
    exact List.cons_ne_nil _ _
  have hdec : decide (macroPieces ≠ []) = true := decide_eq_true hne
  simp [hdec]

theorem macroEnvelope_sound {x : ℝ} (hx0 : 0 ≤ x) (hx59 : x ≤ 59) :
    ∃ p ∈ macroPieces, Holds p.box x ∧ p.model x ≤ 2 * mtKernel x ^ 2 := by
  apply checkMacroPieces_sound macroPieces_check
  · simpa using hx0
  · norm_num
    exact hx59

#print axioms macroEnvelope_sound

#print axioms macroPiece0_check
#print axioms macroPiece3_check
#print axioms macroPieces_check

end Zeta23.ThmD.Sextuple.MacroPrototype
