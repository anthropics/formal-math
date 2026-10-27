/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import VariableBound.Net.Defs
import VariableBound.Net.Rank
import VariableBound.Net.CertRank
import VariableBound.Net.Val
import VariableBound.Net.Prof
import VariableBound.Net.Tuples
import VariableBound.Net.Total
import VariableBound.Net.SizeU
import VariableBound.Net.SizeB
import VariableBound.Net.SizeP
import VariableBound.Net.SizeSmall
import VariableBound.Net.Fit
import VariableBound.Net.Ev
import VariableBound.Net.CertNet
import VariableBound.Net.CertEv
import VariableBound.StepParity
import VariableBound.Params.Ineq
import ClauseBound.Alg.TopNet
import ClauseBound.Alg.CertTopNet
import PaddedDescent.Col.CertG

/-! # Step 3 of Appendix D: statements of proof/variables/VariableBound/Net/Defs.lean, with nothing assumed

Every file of proof/variables/VariableBound/Net proves its statements from the statements of the
other files, taken as hypotheses. Here these hypotheses are discharged for the statements below.
From outside Step 3 come: the inequalities of «Setting and parameters»
(proof/variables/VariableBound/Params/Ineq.lean), and the certificate of the generic plug of a
network on 3K⁸ nodes into a clique solver (proof/rates/ClauseBound/Alg/CertTopNet.lean, with the
certificate of the grouping
`certRebalG` of proof/rates/PaddedDescent/Col/CertG.lean). -/

public section

namespace VariableBound.Net.Main

/-- Step 3, «The total»: Ψ_(a,b) factors through c_(a,b) bits: labels have c_(a,b) bits, and two
settings whose strings have the numbers of ones of the profile have the same label iff they give the
same marks (`StLab`). -/
theorem lab : StLab := stLab

/-- The functions `netD` present the network `netDN`. -/
theorem presents : StPresents := Val.stPresents

/-- Step 3: «Hence the nonzero terms are the tuples (ξ, Π₀, …, Π_r), each once, with the values in
(65)», for the network of one profile, for g > 0 and well-formed data (`StVal`). -/
theorem val : StVal := Val.stVal lab

/-- Step 3, «Profiles»: «Every nonzero term belongs to exactly one profile», which is admissible iff
the term is within the limits of (65); for g > 0, well-formed data and a set of places of objects
(`StProf`). -/
theorem prof : StProf := Prof.stProf

/-- Step 3, «Profiles»: if every check has at most s clauses, there are at most r·s + m objects and
at most (I + m + 1)^(2(g² + g)) numbers tried as profiles (`StNPr`). -/
theorem nPr : StNPr := Prof.stNPr

/-- For well-formed data, the list of checks as sets has the numbers r, |Λ_j|, load(E) of the list
of lists (`StChks`). -/
theorem chks : StChks := Tuples.stChks

/-- For well-formed data, the sum over ξ and the sets of objects with violated clauses within the
limits is the right side of display (65) (`StTuples`). -/
theorem tuples : StTuples := Tuples.stTuples

/-- Step 3, «Profiles»: «Each right side of (65) is the sum of the values of the networks of the
admissible profiles», for g > 0 and well-formed data (`StTotal`). -/
theorem total : StTotal := Total.stTotal val prof tuples

/-- Binomial coefficients of numbers in unary, ⌈log C(t, μ)⌉ and positions of strings in polynomial
time (`StCertRank`). -/
theorem certRank : StCertRank := stCertRank

/-- Display (68) before display (61) is used, for g > 0, the setting of Step 3 for m > n̄
(`Setting`) and an admissible profile (`StU`). -/
theorem u : StU := SizeU.stU VariableBound.paramIneq

/-- Display (68) as printed, for g > 0, the setting of Step 3 for m > n̄, M ≤ 14n and an admissible
profile (`StUPrinted`). -/
theorem uPrinted : StUPrinted := SizeU.stUPrinted u

/-- Step 3, «The parameters»: conditions (i) and (ii) of the definition of a network hold with P =
⌈2P₀⌉ and B = (k + 1)M + 1, under the hypotheses of `StSized` (g > 0, s̄ ≥ 0, well-formed data,
every variable in at most Δ clauses, r ≤ r̄, |Λ_j| ≤ s̄, load(E) ≤ t̄ + 2, an admissible profile). -/
theorem sized : StSized := SizeP.stSized

/-- Display (69), for g > 0, s̄ ≥ 0 and r̄ ≤ 10n (`StP`). -/
theorem p : StP := SizeB.stP

/-- Step 3, «The parameters», last sentence: the case m ≤ n̄, for g > 0, well-formed data with the
empty list, every variable in at most Δ clauses and an admissible profile (`StSmall`). -/
theorem small : StSmall := SizeSmall.stSmall

/-- t̄ ≤ log m + 33·log(2Δ) + 1 gives t̄ ≤ `tbMax`, for 1 ≤ m ≤ Δn (`StTbMax`). -/
theorem tbMax : StTbMax := FitL.stTbMax

/-- A list with display (67), under display (61), is fit for an evaluation; so is the empty list if
m ≤ n̄; for the hypotheses on ψ, Δ, n̄ and M of `StFit`. -/
theorem fit : StFit := FitL.stFit

/-- For a list that is fit for an evaluation, the number of profiles is below a bound that does not
depend on the formula (`StNPrMax`). -/
theorem nPrMax : StNPrMax := FitL.stNPrMax nPr

/-- For n ≥ 1 and Δ ≥ 2: `UbD` ≤ 140kn·⌈log(2Δ)⌉ + 2g², and gP ≤ 2(n + g)(1 + Δ(`tbMax` + 3)) +
2(10n + g)·`sbMax` + g on g = 3K⁸ nodes (`StBounds`). -/
theorem bounds : StBounds := FitL.stBounds p

/-- «The total» and «The parameters» with bounds that do not depend on the formula, for K > 0, a
list that is fit for an evaluation and an admissible profile (`StSize`). -/
theorem size : StSize := FitL.stSize VariableBound.paramIneq uPrinted sized small

/-- Condition (iii) of the definition of a network: the lengths of the network of one profile are
given in unary and its functions are polynomial-time (`StCertNet`). -/
theorem certNet : StCertNet := stCertNet certRank

/-- The test «admissible» is polynomial-time, for g given in unary and the other arguments
polynomial-time (`StCertAdm`). -/
theorem certAdm : StCertAdm := stCertAdm

/-- One evaluation is polynomial-time jointly in all its arguments, the width k included, for a
polynomial-time solver, with k, n and Δ given in unary (`StCertEvD`). -/
theorem certEvD : StCertEvD := CertEv.stCertEvD (ClauseBound.Alg.CertTopNet.stCertValS PaddedDescent.F.certRebalG) certNet certAdm

end VariableBound.Net.Main
