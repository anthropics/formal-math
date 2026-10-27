/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import MainRoute.Defs

/-! # The chain for every solver: definitions and statements

**Why.** proof/maintheorem/MainRoute/Defs.lean states the seven items of the route for ONE algorithm
for cliques, the recursion of Appendix A on the pieces of Appendix B
(`RecursionWithPieces.solverAB P₀ val c`), and for ONE function for the bound in m
(`ClauseBound.Alg.AM` on it). The proof uses little of the two. Of the algorithm for cliques: that
it is polynomial-time, has a sequence of levels, that a
number in [e_ℓ, 2e_ℓ] is computed, and that e_ℓ = O((log K_ℓ)^(−1/2)). Of the function for the bound
in m: that some machine computes it, and that every machine that computes it meets the bound in m.
Here items (3), (4), (6) and (7) are stated for every solver and every function with these
properties. So the Main Theorem's bound follows from ANY algorithm for cliques as in the hypothesis
of Theorem D (a) with
e_ℓ = O((log K_ℓ)^(−1/2)) and ANY function with the bound in m; the chain on the recursion of
Appendix A is an instance, and so is a chain on any other form of Theorem A (b) that gives such a
solver.

**What is stated here.**
* `RouteOn S Q num fm em n₁`: items (3), (4), (6) and (7) of the route of
  proof/maintheorem/MainRoute/Defs.lean, with `RecursionToBound.count S n₁ Q.pick num` and
  `RecursionToBound.expo S n₁ Q.pick num` as the function of Steps 1 to 5 and its exponent, fm and
  em for the bound in m, and K₀ = `S.K (Q.idx 0)`. Each bound is stated for EVERY machine that is
  made in the printed way, and existence is stated apart.
* `RouteOnEverySolver`: `RouteOn` holds, for all n₁ ≥ n₀, where n₀ depends only on S, Q and `num`,
  for every polynomial-time solver S with a sequence Q of levels, every `num` that computes a number
  in [e_ℓ, 2e_ℓ], if e_ℓ ≤ a/√(log K_ℓ) for all ℓ, and for all fm and em such that some machine with
  finite alphabets computes fm with the exponent em and every machine that does meets the bound in
  m.
* `BoundInMOnEverySolver`: item (5) for every such solver: some machine computes the function for
  the bound in m (`ClauseBound.Alg.AM`) on S, and every machine that does meets the bound in m.
* `BothBoundsOnEverySolver`: the chain with this function in the place of fm: both bounds from ONE
  algorithm for cliques, as in the paper, with nothing assumed of a function for the bound in m.

**What is not here.** Items (1) and (2), which are about the pieces and the recursion: they are the
hypotheses on S and Q. What differs from the text is what proof/maintheorem/MainRoute/Defs.lean
lists. The items (1) to (7) of the route are numbered as in that file; all numbers of theorems,
corollaries, appendices and of the Steps of Appendix D are those of the paper. -/

@[expose] public section

namespace MainRoute

open Turing Groundwork PaddedDescent.F ClauseBound.Alg Wrap TwoMachines MainTheoremForms MinOfBounds PairsToBound
open Sat3 (CNF)

/-- Items (3), (4), (6) and (7) of the route for the solver S with the sequence Q of levels, the
function `num` for the number in [e_ℓ, 2e_ℓ], the function fm with the exponent em for the bound in
m, and the bound n₁ below which the function of Steps 1 to 5 tries all assignments. K₀ is K at the
level 0. -/
structure RouteOn {Idx : Type} [Enc Idx] (S : Solver Idx) {e : ℕ → ℝ} {C₀ : ℕ} (Q : S.Seq e C₀) (num : U × U → ℕ × ℕ) (fm : List Bool × U → List Bool) (em : List Bool → ℕ) (n₁ : ℕ) : Prop where
  /-- (3) Theorem D (a): EVERY machine that computes the function of Steps 1 to 5 on S has the
      conclusion of Theorem D (a) for this sequence -/
  da : ∀ (Ma : TM2ComputableAux Bool Bool) (qa : ℕ), Computes Ma (RecursionToBound.count S n₁ Q.pick num) (RecursionToBound.expo S n₁ Q.pick num) qa → ∃ Ca : ℕ, ThmVariablesAFor S Q Ma Ca
  /-- (4) Step 6, from the BODY of Theorem D (a): for EVERY machine Ma with the conclusion of
      Theorem D (a) for this sequence and EVERY machine Mb that tries all assignments, EVERY machine
      that chooses between them as Step 6 says meets the bound of Theorem D (b) -/
  variablesBFromTheBody : ∀ (Ma : TM2ComputableAux Bool Bool) (Ca : ℕ), ThmVariablesAFor S Q Ma Ca → ∀ (Mb : TM2ComputableAux Bool Bool) (cb : ℕ), TriesAllWithin Mb cb →
    ∀ (pre : List Bool → List Bool) (test : List Bool → Bool), RewritesAtWidthOr3 pre → TestsTheMainRegime (S.K (Q.idx 0)) test →
      ∀ (M₂ : TM2ComputableAux Bool Bool) (q₂ : ℕ), Chooses Ma Mb test pre id id id M₂ q₂ → ∃ C₂ : ℕ, ThmVariablesBFor M₂ C₂
  /-- EVERY machine that computes exhaustive counting tries all assignments within 2^{cb·n}·n^{cb·k}
  steps, for some cb that depends on the machine -/
  tries : ∀ (Mb : TM2ComputableAux Bool Bool) (qb : ℕ), Computes Mb exhaust (fun x => (fmlOf x).1.length) qb → ∃ cb : ℕ, TriesAllWithin Mb cb
  /-- (4) Step 6, for the named function: EVERY machine made as Step 6 says meets the bound of
      Theorem D (b) -/
  db : ∀ M₂ : TM2ComputableAux Bool Bool, ChosenAsPrinted (RecursionToBound.count S n₁ Q.pick num) (RecursionToBound.expo S n₁ Q.pick num) (S.K (Q.idx 0)) M₂ → ∃ C₂ : ℕ, ThmVariablesBFor M₂ C₂
  /-- (6) Corollary 11, from the BODIES of Theorem A (c) and Theorem D (b): for EVERY machine M₁
      that meets the bound in m and EVERY machine M₂ that meets the bound of Theorem D (b), EVERY
      machine that runs them in alternation behind a renaming meets the bound of Corollary 11 -/
  cor : ∀ ren : List Bool → List Bool, RenamesTheVariablesThatOccur ren → ∀ (M₁ : TM2ComputableAux Bool Bool) (C₁ : ℕ), MeetsBoundInM M₁ C₁ → ∀ (M₂ : TM2ComputableAux Bool Bool) (C₂ : ℕ), ThmVariablesBFor M₂ C₂ →
    ∀ (N : TM2ComputableAux Bool Bool) (q : ℕ), Alternates M₁ M₂ ren ren id id N q → ∃ C : ℕ, MeetsMinBound N C
  /-- (6), (7) Corollary 11, which is the Main Theorem, for the named function and fm: EVERY machine
  assembled as printed meets the bound of Corollary 11 and that of Theorem 1 on the compact code -/
  main : ∀ N : TM2ComputableAux Bool Bool, AssembledAsPrinted (RecursionToBound.count S n₁ Q.pick num) (RecursionToBound.expo S n₁ Q.pick num) fm em (S.K (Q.idx 0)) id N →
    ∃ C : ℕ, MeetsMinBound N C ∧ CountsCompactKCNFWithinMinBound N C
  /-- the same for deciding, with `someBit` (“some bit is 1”) after either machine -/
  decides : ∀ N : TM2ComputableAux Bool Bool, AssembledAsPrinted (RecursionToBound.count S n₁ Q.pick num) (RecursionToBound.expo S n₁ Q.pick num) fm em (S.K (Q.idx 0)) someBit N →
    ∃ C : ℕ, DecidesWithinMinBound N C
  /-- there IS a machine built as printed, for counting and for deciding: finite alphabets,
  polynomial-time front ends and test, and the named computations `choose` and `alt` carried out -/
  exist : (∃ N : TM2ComputableAux Bool Bool, BuiltAsPrinted (RecursionToBound.count S n₁ Q.pick num) (RecursionToBound.expo S n₁ Q.pick num) fm em (S.K (Q.idx 0)) id N) ∧
    ∃ N : TM2ComputableAux Bool Bool, BuiltAsPrinted (RecursionToBound.count S n₁ Q.pick num) (RecursionToBound.expo S n₁ Q.pick num) fm em (S.K (Q.idx 0)) someBit N

/-- **The chain for every solver.** Let S be a polynomial-time solver for cliques with a sequence Q
of levels, let `num` compute a number in [e_ℓ, 2e_ℓ] (the hypothesis of Theorem D (a)), and let e_ℓ
≤ a/√(log K_ℓ) for all ℓ, for a natural number a. Let fm, with the exponent em, be a function of
(input, padding string) such that some machine with finite alphabets computes it and EVERY machine
that computes it meets the bound in m (`MinOfBounds.MeetsBoundInM`). All of these are arbitrary.
Then `RouteOn S Q num fm em n₁` holds for every n₁ ≥ n₀, where n₀ is chosen after S, Q and `num` and
before a, fm and em: every machine assembled in the printed way from machines that compute the
function of Steps 1 to 5 on S, exhaustive counting and fm has the bound of the Main Theorem, and
such a machine exists. -/
def RouteOnEverySolver : Prop :=
  ∀ (Idx : Type) [Enc Idx] (S : Solver Idx) (e : ℕ → ℝ) (C₀ : ℕ) (Q : S.Seq e C₀), S.Poly → ∀ num : U × U → ℕ × ℕ, NumberBetween S Q num →
    ∃ n₀ : ℕ, ∀ a : ℕ, (∀ l : ℕ, e l ≤ a / Real.sqrt (lg (S.K (Q.idx l)))) →
      ∀ (fm : List Bool × U → List Bool) (em : List Bool → ℕ), (∃ (M : TM2ComputableAux Bool Bool) (q : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧ Computes M fm em q) →
        (∀ (M : TM2ComputableAux Bool Bool) (q : ℕ), Computes M fm em q → ∃ C : ℕ, MeetsBoundInM M C) →
          ∀ n₁ : ℕ, n₀ ≤ n₁ → RouteOn S Q num fm em n₁

/-! ### Item (5) on every solver, and both bounds from one algorithm -/

/-- Item (5) of the route for EVERY solver. The paper has the first sentence of Theorem A (c) for
the recursion of Theorem A only; this is its printed proof, at α′ = 1/2 and for formulas in which
every variable occurs, carried out for any solver with levels: K_ℓ > m^(1/(9C₀)) stands for the
printed K ≥ m^(1/90). Let S be a polynomial-time solver for cliques with a sequence Q of levels and
e_ℓ ≤ a/√(log K_ℓ) for all ℓ, for a natural number a. Then (i) some machine with finite alphabets
computes `ClauseBound.Alg.AM` (the network of the formula, rebalanced and handed to the solver) on S
with the exponent
`ClauseBound.Alg.eM`, the level picked by `Q.pick` for ⌊m^(1/9)⌋; (ii) EVERY machine that computes
this function with this exponent meets the bound in m (`MinOfBounds.MeetsBoundInM`) with some
constant. -/
def BoundInMOnEverySolver : Prop :=
  ∀ (Idx : Type) [Enc Idx] (S : Solver Idx) (e : ℕ → ℝ) (C₀ : ℕ) (Q : S.Seq e C₀), S.Poly → ∀ a : ℕ, (∀ l : ℕ, e l ≤ a / Real.sqrt (lg (S.K (Q.idx l)))) →
    (∃ (M : TM2ComputableAux Bool Bool) (q : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧ Computes M (AM S Q.pick) (eM S Q.pick) q) ∧
    ∀ (M : TM2ComputableAux Bool Bool) (q : ℕ), Computes M (AM S Q.pick) (eM S Q.pick) q → ∃ C : ℕ, MeetsBoundInM M C

/-- **Both bounds from ONE algorithm for cliques.** Let S be a polynomial-time solver for cliques
with a sequence Q of levels, let `num` compute a number in [e_ℓ, 2e_ℓ], and let e_ℓ ≤ a/√(log K_ℓ)
for all ℓ. Then (5) EVERY machine that computes the function for the bound in m on S meets the bound
in m; and for every n₁ ≥ n₀, where n₀ is chosen after S, Q and `num` and before a, the chain
`RouteOn` holds with this function: every machine
assembled in the printed way from machines that compute the function of Steps 1 to 5 and the
function for the bound in m, both on S, and exhaustive counting has the bound of the Main Theorem,
and such a machine exists. Nothing is assumed of a function for the bound in m. -/
def BothBoundsOnEverySolver : Prop :=
  ∀ (Idx : Type) [Enc Idx] (S : Solver Idx) (e : ℕ → ℝ) (C₀ : ℕ) (Q : S.Seq e C₀), S.Poly → ∀ num : U × U → ℕ × ℕ, NumberBetween S Q num →
    ∃ n₀ : ℕ, ∀ a : ℕ, (∀ l : ℕ, e l ≤ a / Real.sqrt (lg (S.K (Q.idx l)))) →
      (∀ (M₁ : TM2ComputableAux Bool Bool) (q₁ : ℕ), Computes M₁ (AM S Q.pick) (eM S Q.pick) q₁ → ∃ C₁ : ℕ, MeetsBoundInM M₁ C₁) ∧
      ∀ n₁ : ℕ, n₀ ≤ n₁ → RouteOn S Q num (AM S Q.pick) (eM S Q.pick) n₁

end MainRoute
