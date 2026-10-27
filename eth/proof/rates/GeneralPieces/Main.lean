/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import AppRunningTimeStatement
public import GeneralPieces.Ring.Basic
public import ClauseBound.Part.Bounds
public import GeneralPieces.Ring.OpFacts
public import GeneralPieces.Ring.Op
public import GeneralPieces.Series.Deriv
public import GeneralPieces.GenF.Main
public import GeneralPieces.Ring.LemmaQ
public import GeneralPieces.Series.LemmaQ
public import GeneralPieces.Ring.Bridge
public import GeneralPieces.Ring.Dual
public import GeneralPieces.Ring.Lex
public import GeneralPieces.Ring.Pieces
public import GeneralPieces.Ring.ThmHalfPieces
public import GeneralPieces.DefGenPieces.ToPure
public import GeneralPieces.DefGenPieces.MayAssume
public import GeneralPieces.Group.Lemma
public import GeneralPieces.Group.Calls
public import GeneralPieces.ThmRunningTime
public import GeneralPieces.Half.Main
public import GeneralPieces.Tied.Bound

/-! # Appendices A and B: theorems for statements of the two statement files

Theorems for statements of `AppHalfPiecesStatement.lean` and `AppRunningTimeStatement.lean`, under
the name of the statement with a small first letter, in the order of the two files;
before the lemma on the operators Q_s stands the expansion of f₊ and f₋ on which its proof rests
(`stExpansion`, which proves `GeneralPieces.Series.StExpansion`).
The proofs are in the other files of this folder; here they are only put together: a proof that
takes other statements as hypotheses is given them. -/

public section

namespace AppHalfPieces

/-- Display (47) defines a[r]: finitely many nonzero terms on every f, no dependence on the order of
the parts, linear in f and in a. -/
theorem opFacts : OpFacts :=
  GeneralPieces.opFacts

/-- (O1): a[r] maps V_E to V_{E+r}, keeps integer polynomials if a is one, and 1[r] = [r = 0]·Id. -/
theorem o1 : O1 :=
  GeneralPieces.o1

/-- The lemma on the operators Q_s, «comparing the coefficients of x^μx'^ν» in the display on the
two orders: f₊ and f₋ are the same combination of powers of ε₊, or ε₋, times elements of 𝓛. -/
theorem stExpansion : GeneralPieces.Series.StExpansion :=
  GeneralPieces.GenF.stExpansion

/-- The lemma on the operators Q_s: (a) the two factors may be exchanged, (b) Q_s = 0 on V_E for |s| >
E + h, (c) the Q_s add up to (a[−h]b)·Id. -/
theorem lemmaQ : LemmaQ :=
  GeneralPieces.lemmaQ GeneralPieces.stBridge opFacts o1
    (fun _ _ hA hb _ s _ _ hπ hσ => GeneralPieces.Series.Qk_eq_Qk'_of stExpansion hA hb s hπ hσ)
    (fun _ _ hA hb _ _ _ _ hπ hσ hs => GeneralPieces.Series.Qk_eq_zero_of stExpansion hA hb hπ hσ hs)
    (fun _ _ hA hb _ _ _ hπ hσ => GeneralPieces.Series.sum_Qk_of stExpansion hA hb hπ hσ)

/-- The lemma on the dual families: a^μ[−h]·b^ν = h!·[μ = ν]. -/
theorem lemmaDual : LemmaDual :=
  GeneralPieces.Dual.lemmaDual

/-- Appendix B: h!/z_μ is an integer. -/
theorem zDvd : ZDvd :=
  GeneralPieces.Dual.zDvd

/-- The steps of the proof of the theorem on the pieces with ρ = 1/√2 that are statements about the
ring: Σ_s A_s = h!·[x = v][y = u], displays (54) and (55), all factors are integers. -/
theorem pieceFacts : PieceFacts :=
  GeneralPieces.pieceFacts lemmaQ lemmaDual opFacts o1 zDvd

end AppHalfPieces

namespace AppRunningTime

/-- The lemma on groupings with explicit cost, first step of the proof: some grouping has at most
2g/K nodes in every group and Y ≤ L for any two groups, in case (i) and in case (ii). -/
theorem someGrouping : SomeGrouping :=
  GeneralPieces.someGrouping

/-- The lemma on groupings with explicit cost, end of the proof: K ≤ g in both cases, and L ≤ gP + 1. -/
theorem groupingSizes : GroupingSizes :=
  GeneralPieces.groupingSizes

/-- The theorem on the general recursion, parts (a) to (d). Parts (b), (c), (d) say that SOME
algorithm exists: they do not name the recursion through case (ii). The form of the first sentence
of (c) that names the programs is `GeneralPieces.thmRunningTimeCm_tied`. -/
theorem thmRunningTime : ThmRunningTime :=
  GeneralPieces.thmRunningTime

/-- The theorem on the pieces with ρ = 1/√2, for the functions A_s of its proof, with the running
time. -/
theorem thmHalfPieces : ThmHalfPieces :=
  GeneralPieces.thmHalfPieces AppHalfPieces.pieceFacts

end AppRunningTime
