/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import VariableBound.Printed.ThmVariablesADefs
public import VariableBound.Count.Defs
public import VariableBound.Top.Defs
public import StepSparsify.Defs
public import SparsificationLemma.StepSparsifyDefs
public import SparsificationLemma.Cal.Defs
public import PairsToBound.Defs

/-! # Theorem D (a) along the printed Step 5: definitions and statements

**The text.** Theorem D (a), hypothesis: «Suppose that K_ℓ and a number in [e_ℓ, 2e_ℓ] can be
computed from ℓ in time polynomial in K_ℓ». Step 5: «The algorithm takes for k the largest number of
literals in a clause of its input, or 3 if that is larger; the bound increases with k. Take ε ≤ 1
between e and 2e, for the e of Step 4.
An output without clauses counts 2^n. Every other output is a formula Φ as above, with Δ the larger
of 2 and the largest number of its clauses in which one variable occurs; so log Δ ≤ 3k·log(8k/e) + 2 =
O(k·log(k/e)). As e ≥ (log n)^(−C₀) and k ≤ (log n)^(1/4), this is at most 3k(3 + (C₀ + 1/4)·log log
n) + 2, which is at most 4kC₀·log log n for
large n, because C₀ ≥ 1. Run Steps 2 to 4 on each of the at most 2^(2en) outputs and add the
results. The time is 2^(2en)·n^{O(k)}·2^{O(ekn·log Δ)} = 2^{O(k²·e·n·log(k/e))}, because k·log n ≤
en for large n. Here n is large if it exceeds a bound that depends only on the constants of the
hypothesis. For the finitely many smaller n ≥ K₀^17, and the
k ≤ (log n)^(1/4) that go with them, trying all assignments is within the bound.»

**Another form in this development.** `MainTheoremForms.ThmVariablesA` has a precision 2^(−s) ≤ e_ℓ
in place of the number in [e_ℓ, 2e_ℓ].

**What is defined here**, in the order of the text. S is a solver for cliques, `pick` picks the
level for n, `num` computes the number in [e_ℓ, 2e_ℓ], n₁ is the bound from which on n is «large».
* `PairsToBound.NumberBetween S Q num` (proof/variables/PairsToBound/Defs.lean): the printed clause
  of the hypothesis; `num` gets ℓ and K_ℓ in unary, so its time is polynomial in K_ℓ.
* `epsOf r`: ε = min(r, 1) for the number r = a/b. `widthOr3F ψ`: this k. `thresholds k r`: the
  thresholds of the sparsification for k and ε. This Δ is
  `SparsificationLemma.StepSparsify.DeltaOf n Φ`
  (proof/sparsification/SparsificationLemma/StepSparsifyDefs.lean).
* `countOutput`: «An output without clauses counts 2^n»; every other output ψ ∪ 𝒩
  (`SparsificationLemma.out x`, every clause written once) is counted by Steps 2 to 4
  (`VariableBound.countD`) with its own Δ. `countAll`: the walk through the tree of the
  sparsification (`StepSparsify.walkSG`) that adds these counts.
* `needOutputs`, `needWalk`: the exponent of a padding string that suffices. As the exponent must be
  computed from the input before any output is known, and nothing says that the exponent of the
  solver grows with the label length, `needOutputs` is the MAXIMUM over all Δ from 2 to the bound on
  the occurrences, cut off at n + 1.
* `planAt`, `plan`, `expo`, `count`: the algorithm. If n < n₁ it tries all assignments. Else it
  sparsifies and counts.

**The statements.** `ThmVariablesAWithNumberBetween`: Theorem D (a) with the printed clause.
`ThmVariablesAForEveryMachine`: for all large n₁ some machine computes the named function
`count S n₁ Q.pick num`, and EVERY machine that computes it has the bound of Theorem D (a).
`WalkTreeIsSparsify`: the outputs at the leaves of the tree that the function walks are the outputs
`SparsificationLemma.Cal.sparsify`, of which
proof/sparsification/SparsificationLemma/StepSparsify.lean proves the sentences of Step 5 one by
one. `OutputsAreFew`, `OwnDeltaIsBounded`, `OutputsAreWithinTheSetting`, `OneOutputCost` (Step 4's
conclusion), `WalkCost`, `ExponentIsWithinTheBound`, `PlanFailsOnlyAboveN`, `CutOffIsIdle`,
`WidthOnTheCode`, `CountIsRight`, `CountIsPolynomialTime`: the sentences of Steps 4 and 5 for this
function. «For the finitely many smaller n …» is `MainTheoremForms.StepSparsifySmallStmt`, which the
proof of `ThmVariablesAForEveryMachine` uses (End.lean).

**What differs from the text.** (1) Cost is the length of a padding string. (2) A guard that the
text does not have: if the exponent computed exceeds n, the function tries all assignments (which is
then no slower). It cannot be dropped: a solver's exponent is computable only under a bound given in
unary. `PlanFailsOnlyAboveN` says that for n ≥ n₁ this is the only case in which the
function does not sparsify. (3) k is cut off at ⌊log₂(n+1)⌋ in the call, so that 2^k is polynomial
on ALL inputs; `CutOffIsIdle`: in the range of Theorem D (a) the cut-off does nothing. (4) The label
length in the call of the solver is ⌊(U + gP/K)/K²⌋ + 1, at bounds on U and P that do not depend on
the formula (`ClauseBound.Alg.valS`). B′ is not handed to the solver; it stands only in the
exponent, as `ClauseBound.Alg.bitsS`, which is at most the printed B′ for K ≥ 5. (5) Outside the
range
n ≥ K₀^17, 3 ≤ k ≤ (log n)^(1/4), of which Theorem D (a) says nothing, nothing is claimed of the
number that the function returns nor of its exponent: for n ≥ n₁ outside this range it may sparsify
with a padding string that is too short and return a wrong number. Polynomial time
(`CountIsPolynomialTime`) and the guard (`PlanFailsOnlyAboveN`) hold on all inputs. (6) n₁ and the
constant of the bound are chosen after the solver, the sequence of levels and `num`; the text says
that they depend only on the constants of the hypothesis. (7) One padding string serves all outputs,
so its exponent is a maximum over Δ where the text adds up
times. (8) Lean's formulas are lists: a formula with an empty clause counts 0, clauses that contain
a variable together with its negation are deleted first, and the side list of the walk starts with
the n clauses xᵢ ∨ ¬xᵢ, which `SparsificationLemma.out` drops. (9) The exponent of the walk has,
besides εn and O(k·log n), a term O(k·log(k/ε)): the stack is bounded through the length (β₁ + … +
β_(k−1))·n of a path, not through the number of nodes. `WalkCost` states it; it is absorbed because
k·log(k/e) ≤ k²·e·n·log(k/e). (10) α and ⌈log₂ x⌉ in the thresholds are rounded up to natural
numbers (`SparsificationLemma.Cal.alphaC`). -/

@[expose] public section

namespace RecursionToBound

open Finset Turing Groundwork Groundwork.Prog PaddedDescent PaddedDescent.F CountKSat CountKSatRate ClauseBound.Alg ClauseBound.TopN ClauseBound.ParityChecks UniformInK VariableBound VariableBound.Net SparsificationLemma MainTheoremForms PairsToBound
open PaddedDescent.F.Mark (occ)
open Sat3 (CNF)

/-! ### The numbers of Step 5 -/

/-- «Take ε ≤ 1 between e and 2e»: ε = min(a/b, 1) for the number a/b in [e, 2e]; as e ≤ 1 it is
again in [e, 2e]. -/
def epsOf (r : ℕ × ℕ) : ℚ := min ((r.1 : ℚ) / (r.2 : ℚ)) 1

/-- «the largest number of literals in a clause of its input, or 3 if that is larger». -/
def widthOr3F (ψ : Fml) : ℕ := max 3 (StepSparsify.widthOf ψ)

/-- The thresholds of the sparsification for k and ε = `epsOf r`: θ₀ = 2, θ_c = α·β_c with α =
⌈2(k−1)²·ε⁻¹·⌈log₂(32(k−1)²/ε)⌉⌉, where the numbers β_c (for clauses of size c; not the β of the
paper) are those of the definition of `Cal.thetaC`. -/
def thresholds (k : ℕ) (r : ℕ × ℕ) : ℕ → ℕ := Cal.thetaC (Cal.alphaC k (epsOf r))

/-- The bound on the number of clauses of an output in which one variable occurs: 2·(θ₀ + … +
θ_(k−1)) + 2; for k ≥ 3 and 0 < ε ≤ 1 it is at most 2·(8k/ε)^(3k) + 2. -/
def occBound (k : ℕ) (r : ℕ × ℕ) : ℕ := 2 * (∑ j ∈ range k, thresholds k r j) + 2

section
variable {Idx : Type} [Enc Idx] (S : Solver Idx)

/-! ### The count -/

/-- The count of the output at the node x: «An output without clauses counts 2^n. Every other output
is a formula Φ as above, with Δ the larger of 2 and the largest number of its clauses in which one
variable occurs»: Steps 2 to 4 (`VariableBound.countD`) with this Δ
(`SparsificationLemma.StepSparsify.DeltaOf`). The output is `SparsificationLemma.out x`: the side
clauses of one literal and the clauses of the formula at x,
every clause written once. -/
def countOutput (k : ℕ) (pad : U) (i : Idx) (n : ℕ) (x : CNode) : ℕ :=
  bif (out x).isEmpty then 2 ^ n else countD S k pad i n (StepSparsify.DeltaOf n (out x)) (out x)

/-- «Run Steps 2 to 4 on each of the … outputs and add the results»: the walk, with the thresholds
for k and ε, through the tree of the sparsification of the decoded formula d = (n in unary, clauses)
without the clauses that contain a variable together with its negation; 0 if d has an empty clause. -/
def countAll (k : ℕ) (r : ℕ × ℕ) (i : Idx) (d : U × Fml) (pad : U) : ℕ :=
  bif hasNil d.2 then 0 else _root_.StepSparsify.walkSG (thresholds k r) k pad (countOutput S k pad i d.1.length) (rootC (d.1, noTaut d.2))

/-! ### The exponent of the padding string -/

/-- What the count of one output with this Δ needs: the networks, the list of profiles, the list of
checks (the three fields of `VariableBound.FitsD`). -/
def needAt (k : ℕ) (i : Idx) (n Δ : ℕ) : ℕ :=
  needNet S i (UbD k (S.K i) n Δ) (PbD (S.K i) n Δ) (BbD k n) + Nat.size (nPrMax (S.K i) n Δ) + Nat.size (8 * (10 * n + 1) * (sbMax Δ + 1) * (Nat.size (Δ * n) + 2) + 8)

/-- The same, computed under the bound b in unary: `none` if the exponent of the solver is larger
than the bound. -/
def needAtC (b : U) (k : ℕ) (i : Idx) (n Δ : ℕ) : Option ℕ :=
  (needNetC S b i (UbD k (S.K i) n Δ) (PbD (S.K i) n Δ) (BbD k n)).map fun v =>
    v + Nat.size (nPrMax (S.K i) n Δ) + Nat.size (8 * (10 * n + 1) * (sbMax Δ + 1) * (Nat.size (Δ * n) + 2) + 8)

/-- The numbers Δ that an output can have: 2, …, the bound on the occurrences, cut off at n + 1. -/
def deltas (k : ℕ) (r : ℕ × ℕ) (n : ℕ) : List ℕ := (List.range (min (occBound k r) (n + 1) - 1)).map (· + 2)

/-- The maximum of `needAt` over these Δ. -/
def needOutputs (k : ℕ) (r : ℕ × ℕ) (i : Idx) (n : ℕ) : ℕ := ((deltas k r n).map (needAt S k i n)).foldr max 0

/-- The same, computed under the bound b: `none` if one of them is. -/
def needOutputsC (b : U) (k : ℕ) (r : ℕ × ℕ) (i : Idx) (n : ℕ) : Option ℕ :=
  (deltas k r n).foldr (fun Δ o => o.bind fun v => (needAtC S b k i n Δ).map (max v)) (some 0)

end

/-- What the walk needs: its rounds (at most 2^(εn) outputs, so fewer than 2^(⌈εn⌉+1) nodes) and its
stack. -/
def needWalk (k : ℕ) (r : ℕ × ℕ) (n : ℕ) : ℕ :=
  (⌈epsOf r * n⌉₊ + 2) + Nat.size (stackLenCU k (32 * Cal.alphaC k (epsOf r)) n (inLen k n))

section
variable {Idx : Type} [Enc Idx] (S : Solver Idx)

/-! ### The algorithm -/

/-- The exponent for width k, n variables, the index i and the number r, if n ≥ n₁ and the exponent
is at most n. -/
def planAt (n₁ k n : ℕ) (i : Idx) (r : ℕ × ℕ) : Option ℕ :=
  if n₁ ≤ n then (needOutputsC S (List.replicate n ()) k r i n).bind fun v => if v + needWalk k r n ≤ n then some (v + needWalk k r n) else none
  else none

/-- This k, read from the input. -/
def widthU (x : List Bool) : ℕ := widthOr3F (fmlOf x).2

/-- The number in [e, 2e] for the level ℓ picked for n, «the largest ℓ with K_ℓ ≤ n^(1/17)». -/
def numU (pick : U → U × Idx) (num : U × U → ℕ × ℕ) (x : List Bool) : ℕ × ℕ :=
  num ((pick (root17 (nU x))).1, List.replicate (S.K (idxU pick x)) ())

/-- The plan for the input x, with this k cut off at ⌊log₂(n+1)⌋, as in the call. -/
def plan (n₁ : ℕ) (pick : U → U × Idx) (num : U × U → ℕ × ℕ) (x : List Bool) : Option ℕ :=
  planAt S n₁ (kcU (widthU x) (nU x)) (nU x) (idxU pick x) (numU S pick num x)

/-- The exponent of the padding string: that of the plan, or n. -/
def expo (n₁ : ℕ) (pick : U → U × Idx) (num : U × U → ℕ × ℕ) (x : List Bool) : ℕ := (plan S n₁ pick num x).getD (nU x)

/-- **The algorithm of Theorem D (a)**, as a function of (input, padding string): the number of
satisfying assignments of the formula written in p.1, in n + 1 bits. Without a plan (n < n₁, or the
exponent exceeds n) it tries all assignments; else it sparsifies and counts each output. -/
def count (n₁ : ℕ) (pick : U → U × Idx) (num : U × U → ℕ × ℕ) (p : List Bool × U) : List Bool :=
  outW (fmlOf p.1, bif (plan S n₁ pick num p.1).isNone then bruteU p
    else countAll S (kcU (widthU p.1) (nU p.1)) (numU S pick num p.1) (idxU pick p.1) (fmlOf p.1) p.2)

end

/-! ### The statements -/

/-- **Theorem D (a), with the printed clause on the number in [e_ℓ, 2e_ℓ].** For every
polynomial-time solver S for cliques with a sequence Q of levels and every `num` as in
`NumberBetween` there are one machine with finite alphabets and one constant C′ with the bound
`MainTheoremForms.ThmVariablesAFor`. -/
def ThmVariablesAWithNumberBetween : Prop :=
  ∀ (Idx : Type) [Enc Idx] (S : Solver Idx) (e : ℕ → ℝ) (C₀ : ℕ) (Q : S.Seq e C₀), S.Poly → ∀ num : U × U → ℕ × ℕ, NumberBetween S Q num →
    ∃ (M : TM2ComputableAux Bool Bool) (C' : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧ ThmVariablesAFor S Q M C'

/-- The same for every machine that computes the named function: there is a number n₀ such that for
every n₁ ≥ n₀ (i) there are a machine with finite alphabets and a q such that the machine computes
`count S n₁ Q.pick num` with the exponent `expo S n₁ Q.pick num`, and (ii) EVERY machine M that
computes this function with this exponent, for whatever q, has the bound of Theorem D (a) with some
constant C′. -/
def ThmVariablesAForEveryMachine : Prop :=
  ∀ (Idx : Type) [Enc Idx] (S : Solver Idx) (e : ℕ → ℝ) (C₀ : ℕ) (Q : S.Seq e C₀), S.Poly → ∀ num : U × U → ℕ × ℕ, NumberBetween S Q num →
    ∃ n₀ : ℕ, ∀ n₁ : ℕ, n₀ ≤ n₁ → (∃ (M : TM2ComputableAux Bool Bool) (q : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧ Computes M (count S n₁ Q.pick num) (expo S n₁ Q.pick num) q) ∧
      ∀ (M : TM2ComputableAux Bool Bool) (q : ℕ), Computes M (count S n₁ Q.pick num) (expo S n₁ Q.pick num) q → ∃ C' : ℕ, ThmVariablesAFor S Q M C'

/-- The outputs at the leaves of the tree that `countAll` walks are the outputs of the
sparsification as proof/sparsification/SparsificationLemma states it: for k ≥ 3, 0 < r, a k-CNF ψ on
n variables and every D ≥ (β₁ + … + β_(k−1))·n = `Cal.depthC`, a bound on the length of a path, the
leaves of the tree from `rootC`, mapped by `SparsificationLemma.out`, are the list
`SparsificationLemma.Cal.sparsify k n ε ψ`, ε = `epsOf r`. So the theorems
`SparsificationLemma.StepSparsify.outputs_le`,
`exactly_one`, `count_eq_sum`, which are sentences of Step 5 on the sparsification, speak of what
the function counts. -/
def WalkTreeIsSparsify : Prop :=
  ∀ (k n D : ℕ) (r : ℕ × ℕ) (ψ : Sparsify.PFml), 3 ≤ k → 0 < r.1 → 0 < r.2 → IsKCNF k n ψ → Cal.depthC (Cal.alphaC k (epsOf r)) k n ≤ D →
    (Sparsify.leaves (stepC (thresholds k r) k) D (rootC (List.replicate n (), noTaut ψ))).map out = Cal.sparsify k n (epsOf r) ψ

/-- «… each of the at most 2^(2en) outputs». For k ≥ 3, a number r with e ≤ r ≤ 2e, 0 < e ≤ 1, and a
k-CNF ψ on n variables there are at most 2^(εn) ≤ 2^(2en) outputs, ε = `epsOf r`; and e ≤ ε ≤ 2e, ε
≤ 1. -/
def OutputsAreFew : Prop :=
  ∀ (k n : ℕ) (r : ℕ × ℕ) (e : ℝ) (ψ : Sparsify.PFml), 3 ≤ k → 0 < e → e ≤ 1 → e ≤ (r.1 : ℝ) / r.2 → (r.1 : ℝ) / r.2 ≤ 2 * e → IsKCNF k n ψ →
    e ≤ ((epsOf r : ℚ) : ℝ) ∧ ((epsOf r : ℚ) : ℝ) ≤ 2 * e ∧ ((epsOf r : ℚ) : ℝ) ≤ 1 ∧
    ((Cal.sparsify k n (epsOf r) ψ).length : ℝ) ≤ (2 : ℝ) ^ (((epsOf r : ℚ) : ℝ) * n) ∧ (2 : ℝ) ^ (((epsOf r : ℚ) : ℝ) * n) ≤ (2 : ℝ) ^ (2 * e * n)

/-- «Every other output is a formula Φ as above, with Δ …; so log Δ ≤ 3k·log(8k/e) + 2 … which is at
most 4kC₀·log log n for large n». For every C₀ ≥ 1 there is an n₁ such that for all n ≥ n₁, all k
with 3 ≤ k ≤ (log n)^(1/4), all real e with (log n)^(−C₀) ≤ e ≤ 1 and all r with e ≤ r ≤ 2e: every Δ
with 2 ≤ Δ ≤ `occBound k r` has
log Δ ≤ 3k·log(8k/e) + 2 and Δ ≤ (log n)^(4kC₀) (so it is within «Setting and parameters»), Δ ≤ n +
1, and n ≥ 29·⌈log₂(2Δ)⌉ + 19 (what `VariableBound.StCountD` asks). That the Δ of an output is at
most `occBound k r` is `OwnDeltaIsBounded`. The middle step of the text, 3k·log(8k/e) + 2 ≤ 3k(3 +
(C₀ + 1/4)·log log n) + 2 ≤ 4kC₀·log log n, is the third conjunct. -/
def OutputsAreWithinTheSetting : Prop :=
  ∀ C₀ : ℕ, 1 ≤ C₀ → ∃ n₁ : ℕ, ∀ (k n Δ : ℕ) (r : ℕ × ℕ) (e : ℝ), n₁ ≤ n → 3 ≤ k → (k : ℝ) ^ 4 ≤ MainTheoremForms.lg n → 1 / MainTheoremForms.lg n ^ C₀ ≤ e → e ≤ 1 → e ≤ (r.1 : ℝ) / r.2 → (r.1 : ℝ) / r.2 ≤ 2 * e →
    2 ≤ Δ → Δ ≤ occBound k r →
      MainTheoremForms.lg Δ ≤ 3 * k * MainTheoremForms.lg (8 * k / e) + 2 ∧ (Δ : ℝ) ≤ MainTheoremForms.lg n ^ (4 * k * C₀) ∧
      (3 * k * MainTheoremForms.lg (8 * k / e) + 2 ≤ 3 * k * (3 + (C₀ + 1 / 4) * MainTheoremForms.lg (MainTheoremForms.lg n)) + 2 ∧ 3 * (k : ℝ) * (3 + (C₀ + 1 / 4) * MainTheoremForms.lg (MainTheoremForms.lg n)) + 2 ≤ 4 * k * C₀ * MainTheoremForms.lg (MainTheoremForms.lg n)) ∧
      Δ ≤ n + 1 ∧ 29 * LD Δ + 19 ≤ n

/-- In every output a variable occurs in at most `occBound k r` clauses: for k ≥ 3, 0 < r and a
k-CNF ψ on n variables, every output Φ has `DeltaOf n Φ ≤ occBound k r`. -/
def OwnDeltaIsBounded : Prop :=
  ∀ (k n : ℕ) (r : ℕ × ℕ) (ψ : Sparsify.PFml), 3 ≤ k → 0 < r.1 → 0 < r.2 → IsKCNF k n ψ → ∀ Φ ∈ Cal.sparsify k n (epsOf r) ψ, StepSparsify.DeltaOf n Φ ≤ occBound k r

/-- «So every variable occurs in at most 2(8k/ε)^(3k) + 2 clauses of each output»: for k ≥ 3 and 0 <
r the bound `occBound k r` is at most 2·(8k/ε)^(3k) + 2, ε = `epsOf r`. -/
def OccBoundIsThePrinted : Prop :=
  ∀ (k : ℕ) (r : ℕ × ℕ), 3 ≤ k → 0 < r.1 → 0 < r.2 → (occBound k r : ℝ) ≤ 2 * (8 * (k : ℝ) / ((epsOf r : ℚ) : ℝ)) ^ (3 * k) + 2

/-- The bounds on the total, on P, on the number of profiles and on the lists grow with Δ. (So the
arithmetic of proof/variables/VariableBound/Top, which is stated for Δ a power of two, bounds every
Δ below that power.) -/
def BoundsGrowWithDelta : Prop :=
  ∀ k K n Δ Δ' : ℕ, Δ ≤ Δ' → UbD k K n Δ ≤ UbD k K n Δ' ∧ PbD K n Δ ≤ PbD K n Δ' ∧ nPrMax K n Δ ≤ nPrMax K n Δ' ∧ sbMax Δ ≤ sbMax Δ'

/-- Step 4, its conclusion: «Hence the number of satisfying assignments of Φ is computed in time
2^{O(ekn·log Δ)}.» For every polynomial-time solver with a sequence of levels there are A and n₁
such that for all n ≥ n₁, the level ℓ of n, all k with 3 ≤ k ≤ (log n)^(1/4) and all Δ with 2 ≤ Δ ≤
(log n)^(4kC₀) the exponent for one output with this Δ is at most A·e_ℓ·k·n·log Δ. -/
def OneOutputCost : Prop :=
  ∀ (Idx : Type) [Enc Idx] (S : Solver Idx) (e : ℕ → ℝ) (C₀ : ℕ) (Q : S.Seq e C₀), S.Poly →
    ∃ A n₁ : ℕ, ∀ k n l Δ : ℕ, n₁ ≤ n → IsLevel S Q n l → 3 ≤ k → (k : ℝ) ^ 4 ≤ MainTheoremForms.lg n → 2 ≤ Δ → (Δ : ℝ) ≤ MainTheoremForms.lg n ^ (4 * k * C₀) →
      (needAt S k (Q.idx l) n Δ : ℝ) ≤ A * e l * k * n * MainTheoremForms.lg Δ

/-- Step 5: the sparsification «produces at most 2^(εn) outputs in time 2^(εn)·n^{O(k)}»; here with
an extra factor (8k/ε)^{O(k)} (item (9) of the module comment). There is a c such that for k ≥ 3, n
≥ 2 and 0 < r the exponent for the walk is at most εn + c·k·(log n + log(8k/ε)). -/
def WalkCost : Prop :=
  ∃ c : ℕ, ∀ (k n : ℕ) (r : ℕ × ℕ), 3 ≤ k → 2 ≤ n → 0 < r.1 → 0 < r.2 →
    (needWalk k r n : ℝ) ≤ ((epsOf r : ℚ) : ℝ) * n + c * k * (MainTheoremForms.lg n + MainTheoremForms.lg (8 * k / ((epsOf r : ℚ) : ℝ)))

/-- «The time is 2^(2en)·n^{O(k)}·2^{O(ekn·log Δ)} = 2^{O(k²·e·n·log(k/e))}, because k·log n ≤ en
for large n.» For every polynomial-time solver with a sequence of levels and every `num` as in the
hypothesis there are A and n₁ such that for all n ≥ n₁, the level ℓ of n and all k with 3 ≤ k ≤ (log
n)^(1/4) the sum `needOutputs` + `needWalk`, which is the exponent of the padding string where there
is a plan, is at most
A·k²·e_ℓ·n·log(k/e_ℓ). It follows from `OneOutputCost`, `WalkCost`, `OutputsAreWithinTheSetting` and
`MainTheoremForms.StepSparsifyLargeStmt` (k·log n ≤ en). -/
def ExponentIsWithinTheBound : Prop :=
  ∀ (Idx : Type) [Enc Idx] (S : Solver Idx) (e : ℕ → ℝ) (C₀ : ℕ) (Q : S.Seq e C₀), S.Poly → ∀ num : U × U → ℕ × ℕ, NumberBetween S Q num →
    ∃ A n₁ : ℕ, ∀ k n l : ℕ, n₁ ≤ n → IsLevel S Q n l → 3 ≤ k → (k : ℝ) ^ 4 ≤ MainTheoremForms.lg n →
      ((needOutputs S k (num (List.replicate l (), List.replicate (S.K (Q.idx l)) ())) (Q.idx l) n + needWalk k (num (List.replicate l (), List.replicate (S.K (Q.idx l)) ())) n : ℕ) : ℝ) ≤ A * expVariablesA k n (e l)

/-- For n ≥ n₁ the function sparsifies unless the exponent exceeds n: if `planAt S n₁ k n i r` is
`none` and n₁ ≤ n, then n < `needOutputs S k r i n` + `needWalk k r n`; and if it is `some v`, then
v is that sum. For polynomial-time solvers. -/
def PlanFailsOnlyAboveN : Prop :=
  ∀ (Idx : Type) [Enc Idx] (S : Solver Idx), S.Poly → ∀ (n₁ k n : ℕ) (i : Idx) (r : ℕ × ℕ),
    (∀ v, planAt S n₁ k n i r = some v → n₁ ≤ n ∧ v = needOutputs S k r i n + needWalk k r n ∧ v ≤ n) ∧
    (planAt S n₁ k n i r = none → n₁ ≤ n → n < needOutputs S k r i n + needWalk k r n)

/-- In the range of Theorem D (a) the cut-off of k does nothing: if k ≤ (log n)^(1/4) and n ≥ 1,
then min(k, ⌊log₂(n+1)⌋) = k. -/
def CutOffIsIdle : Prop := ∀ k n : ℕ, 1 ≤ n → (k : ℝ) ^ 4 ≤ MainTheoremForms.lg n → kcU k n = k

/-- On the code of (k, φ) the function reads «the largest number of literals in a clause, or 3»:
`widthU (SatM.enc k φ)` is `PairsToBound.widthOr3 φ`, for k ≥ 1 and a k-CNF φ; and for the level ℓ
of n, the index that it picks is that of ℓ and the number that it takes is `num` at (ℓ, K_ℓ). -/
def WidthOnTheCode : Prop :=
  (∀ (k n : ℕ) (φ : CNF n), 1 ≤ k → SatK.IsKCNF k φ → widthU (SatM.enc k φ) = PairsToBound.widthOr3 φ) ∧
  ∀ (Idx : Type) [Enc Idx] (S : Solver Idx) (e : ℕ → ℝ) (C₀ : ℕ) (Q : S.Seq e C₀) (num : U × U → ℕ × ℕ) (k n l : ℕ) (φ : CNF n), 1 ≤ k → SatK.IsKCNF k φ → IsLevel S Q n l →
    numU S Q.pick num (SatM.enc k φ) = num (List.replicate l (), List.replicate (S.K (Q.idx l)) ()) ∧ idxU Q.pick (SatM.enc k φ) = Q.idx l

/-- The function is right in the range of Theorem D (a): for every polynomial-time solver with a
sequence of levels and `num` as in the hypothesis there is an n₀ such that for every n₁ ≥ n₀, all n
≥ K₀^17, all k with 3 ≤ k ≤ (log n)^(1/4), every k-CNF φ on n variables and every padding string of
at least 2^(`expo`) units, `count` on the code of (k, φ) is the number of
satisfying assignments in n + 1 bits. k is the width declared in the input; the function itself
takes `widthOr3F`. -/
def CountIsRight : Prop :=
  ∀ (Idx : Type) [Enc Idx] (S : Solver Idx) (e : ℕ → ℝ) (C₀ : ℕ) (Q : S.Seq e C₀), S.Poly → ∀ num : U × U → ℕ × ℕ, NumberBetween S Q num →
    ∃ n₀ : ℕ, ∀ n₁ : ℕ, n₀ ≤ n₁ → ∀ (k n : ℕ) (φ : CNF n), S.K (Q.idx 0) ^ 17 ≤ n → 3 ≤ k → (k : ℝ) ^ 4 ≤ MainTheoremForms.lg n → SatK.IsKCNF k φ →
      ∀ pad : U, 2 ^ expo S n₁ Q.pick num (SatM.enc k φ) ≤ pad.length → count S n₁ Q.pick num (SatM.enc k φ, pad) = SatK.binary n (SatK.numSat φ)

/-- The function and its exponent are polynomial-time in (input, padding string), on ALL inputs, for
every n₁, if the solver, `pick` and `num` are. -/
def CountIsPolynomialTime : Prop :=
  ∀ (Idx : Type) [Enc Idx] (S : Solver Idx), S.Poly → ∀ (n₁ : ℕ) (pick : U → U × Idx) (num : U × U → ℕ × ℕ), PolyT pick → PolyT num →
    PolyT (count S n₁ pick num) ∧ PolyT (expo S n₁ pick num)

end RecursionToBound
