/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSatRateStatement
public import PaddedDescent.RateLemmas
import PaddedDescent.Reduce
import PaddedDescent.F.Table
import PaddedDescent.F.RebalF
import PaddedDescent.F.Expand
import PaddedDescent.F.Descend
import PaddedDescent.F.MarkSums
import PaddedDescent.F.MarkLayers
import PaddedDescent.F.MarkCode
import PaddedDescent.F.MarkVal
import PaddedDescent.F.MarkProf
import PaddedDescent.F.MarkPi
import PaddedDescent.F.MarkSum
import PaddedDescent.F.MarkSize
import PaddedDescent.F.MarkDeg
import PaddedDescent.F.Eval
import PaddedDescent.F.Top
import PaddedDescent.F.ArithSched
import PaddedDescent.F.ArithA
import PaddedDescent.F.CertNet
import PaddedDescent.Col.CertG
import PaddedDescent.F.CertSide
import PaddedDescent.F.CertGrid
import PaddedDescent.F.CertMark
import PaddedDescent.F.CertA

/-! # The end theorem: ONE Turing machine decides 3-SAT within C·2^{C·n/(log₂(n+2))^{3/19}} steps

**What is proved.** `Sat3.inRateTM`: there are one multi-stack Turing machine of Mathlib
(`Turing.FinTM2`, all alphabets finite) and one constant C
such that, for every n and every instance of 3-SAT on n variables, the machine, started on the code
of the instance, halts within
C·2^{C·n/(log₂(n+2))^{3/19}} steps with the bit «satisfiable». The machine and C do not depend on n.
Theorem 2 of the paper has a separate algorithm
for every δ > 0 and no rate.

**What a reader has to read.** Two files: `ThreeSatStatement.lean` (3-SAT, the code of an instance,
time on Mathlib's machines) and
`ThreeSatRateStatement.lean` (the bound and the order of the quantifiers). Everything else is proof.

**What it does not say.** The constants are chosen for ease of proof, and C is not explicit. The
bound is asymptotic: the machine leaves plain
exhaustive search only when sOf n ≥ s0K 3 = 2^7 = 128. Since
sOf n = 3·(⌊log₂⌊log₂ n⌋⌋ − 911)/19, rounded down (Params.lean), that means ⌊log₂⌊log₂ n⌋⌋ ≥ 1722,
that is n ≥ 2^(2^1722). For smaller n the
theorem says nothing that exhaustive search does not give. (The parameters are the same for clauses
of every width k,
and the width enters only through the number s0K k = 2^(k+4).)
Even for larger n the bound need not be below 2^n: the pad alone has 2^(2^131·(n/2^s + 1)) units, s =
sOf n, which is more than 2^n until s ≥ 132, that is
until n ≥ 2^(2^1747), and the running time is a polynomial of unknown degree in that length. So no
explicit n is known from which the bound beats
exhaustive search; the content of the theorem is the growth rate, with one machine for all n. In
general, whatever the constant C ≥ 1 is: the bound
C·2^{C·n/(log₂(n+2))^{3/19}} can be below 2^n only if C·n/(log₂(n+2))^{3/19} < n, that is only if
log₂(n+2) > C^(19/3).

**How it is proved.** `PaddedDescent.inRateTM_of_algorithm` (Reduce.lean) reduces the statement to
one pure function
`PaddedDescent.F.A : List Bool × List Unit → Bool` of the input and a pad of 2^{C₀(n/2^{s(n)}+1)}
units, C₀ = `C0K 3` = 2^131, which the machine first writes by doubling. The function must be
(1) polynomial-time in the length of (input, pad), in the sense of the class `PolyT`, and (2)
    correct when the pad has that length.
A (F/Prog.lean) is the recursive algorithm of grids and groupings, with the number of levels, K, g
and τ as data computed from n, with explicit tables for the
tensors, a breadth-first list of instances in place of the recursion, and every loop cut off by the
pad. (1) is `StCertA`; (2) is
`StCorrect (C0K 3) (s0K 3)`, from the value theorems for one level and from the arithmetic of bit
counts (`StA`, `StAW`). The interface statements
`St…` are in F/Interfaces.lean.

**Where the exponent comes from.** Roughly: one level shrinks the number of label bits by the factor
ρ = (log₂ 12)/4 and takes K nodes to about K^(2^a)
nodes, and the network at the top has about ε^(−d)·n label bits, where 2^(εn) bounds the number of
sparse formulas. Then t levels need ρ^t·ε^(−d) ≤ ε and
2^(a·t) ≤ log₂ n up to constants, which allows ε = (log₂ n)^(−c) for c below log₂(1/ρ)/(a·(1 + d)).
The recursion with grids of side 3K⁸ at every level has a = 4 and d = 3. A departs from it in
three places, which bring a to 1 and d to 0, up to a factor polynomial in log₂(1/ε) that does not
matter for c; the limit is then log₂(1/ρ) = 0.15804…. The
arithmetic here uses 8963/10000 in place of ρ = 0.89624…, which allows every c below
log₂(10000/8963) = 0.15794…, and 3/19 = 0.15789….
First, below the top level the grid has side g = K·L with a small factor L, in place of 3K⁸. This
rests on a second colouring lemma
(Col/Colouring.lean): it bounds the tails of three linear statistics of a random colouring by
exponential moments, and it needs a bound on the number of label
bits that two nodes share, which the networks below the top level have (`Grid.sideCap_le`). The
network at the top has none and uses the grouping lemma for g = 3K⁸.
Second, the sparsification tree is that of proof/sparsification/SparsifyWidthK, in whose leaves, for
width k, every variable occurs in at most leafC τ k clauses, a power of τ (2 + 8τ + 96τ² for
k = 3).
Third, the construction at the top. The clauses of a leaf are divided into layers such that every
assignment that satisfies the later
layers violates at most n + 2 clauses of a layer (F/MarkMath.lean, F/MarkLayers.lean). Then the
product over the layers of the inclusion-exclusion sums, cut off
at n + 2, is 1 at the satisfying assignments and 0 elsewhere (F/MarkSums.lean). The sum of these
products over all assignments is a sum of values of networks in
which the nodes share only marks of clauses (F/MarkNet.lean, F/MarkVal.lean, F/MarkSum.lean). There
is one network for each profile, which fixes how many marks
are set where, and inside a profile the shared marks have a short code, so that a network has only
about k·n·β² label
bits, where 2^β bounds the number of clauses per variable (F/MarkSize.lean). The layers are chosen
clause by clause by a greedy rule: a clause is offered to the layers in turn,
and a layer takes it if a sum over assignments grows by less than a threshold; every such test takes
two more evaluations of the same kind.
Everything from the evaluation of one sparse formula upwards is written for clauses of width k; this
file uses it at k = 3, and proof/consequences/CountKSatRate/ for every k. -/

namespace Sat3

open PaddedDescent PaddedDescent.F

/-- ONE Turing machine decides 3-SAT on n variables within C·2^{C·n/(log₂(n+2))^{3/19}} steps. -/
public theorem inRateTM : InRateTM (3 / 19) :=
  inRateTM_of_algorithm (C0K 3) (s0K 3) (two_pow_s0K_le 3)
    (CertTop.certA certRebal (certDescend (CertGrid.certExpand certRebalG stCertSide)) CertGrid.certBrute certMark certAdm)
    (Top.correct
      (Eval.stCountM
        (Eval.stEval (Eval.stValF RebalF.stR (stD Table.stT3b Expand.stE)) Mark.Val.stMarkPresents
          (Mark.Sum.stMarkSum (Mark.Val.stMarkVal stEncLen stEncInj) Mark.Prof.stProfSum Mark.Pi.stPiSum) stMarkSized)
        stLayersE)
      stLeaf stSched stA stAW)

end Sat3
