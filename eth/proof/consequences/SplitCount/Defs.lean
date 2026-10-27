/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import PaperSentencesStatement
public import Occ.Defs
public import Eight.Cor.WidthProg
public import Eight.ViaGrouping.CorDefs2
public import CountKSat.Interfaces

/-! # Section 7, Corollary 6 (#k-SAT in time O(2^{δn})) along its printed proof: the machine and the statements (no proofs)

The proof has four steps.
1. For every δ' > 0, the proof of Theorem 2, with K and g chosen from δ' as there (we may assume δ'
   ≤ 1), computes Z, and hence the number Z·2^{n'} of satisfying assignments of a 3-CNF with m ≥ 1
   clauses in which n' of the n variables do not occur, in time O(2^{δ'm}) plus a polynomial in n;
   with no clauses the number is 2^n. (The paper says only «For k = 3 this is Theorem 2».) Here:
   `timesFreeAfter Cnt`, `StStepOneFor` (for EVERY machine Cnt that computes Z as Section 6 says),
   `StComputesZ` (Section 6's machine, for every K and every algorithm for cliques with the exponent
   δ'/12), `countThree ℓ`, `StCountIsNetworkMachine` and `StStepOne` (for COUNT of Algorithm 1). «By
   the work of Dell et al. … this case suffices»: `StSuffices`, for EVERY procedure that does what
   step 1 says.
2. «their form of the Sparsification Lemma turns a k-CNF on n variables, for any ε > 0, into at most
   2^{εn} k-CNFs on the same variables, each with O(n) clauses, no two of which share a satisfying
   assignment, so that their numbers of satisfying assignments add up.» Here: `SparsifiesPlain`,
   `StStepTwo`, and for «no two of which share …» `StDisjoint`, `StDisjointLeaves`.
3. «each of these is turned into a 3-CNF with O(n) clauses and O(n) variables and the same number of
   satisfying assignments, by the standard width reduction …» Here: `Eight.Width.widthP` and
   `StStepThree`.
4. «The constants in O(n) depend on k and ε, so choosing ε = δ/3 first and then applying Theorem 2
   with a small enough value in place of δ gives time O(2^{δn}).» Here: `deltaPrime` and
   `StCountsAt`.

The machine `COUNTsplit k ℓ τ` does just this: read the input; write 0 if some clause is empty;
otherwise walk the tree of the sparsification for counting (the tree of
proof/consequences/CountKSat/, after Dell, Husfeldt, Marx, Taslaman and Wahlén: the child that gets
the petals also gets «every literal of the heart is false», kept on a side list that the branching
rule never reads, as Appendix C does, where Dell et al. add these clauses to the formula itself,
which can change the tree; the branching rule and the thresholds `WidthK.theta τ` are those of
proof/consequences/WidthK/, Lean's own, not those of their Lemma A.1, and not the thresholds
`UniformInK.thetaU` of the tree that the deciding route in proof/consequences/SplitSat/ walks); at
each leaf apply the width reduction,
run COUNT of Algorithm 1 at level ℓ on the 3-CNF (`Eight.ViaGrouping.COUNTp ℓ`: the network has 3
places per clause), multiply by 2^{n'}; write the sum.
So no network for a width above 3 is ever made; the side list of the tree does not begin with the
clauses xᵢ ∨ ¬xᵢ; the constants for K_ℓ and e_ℓ are those of Section 6 (72/δ' and δ'/12).

Different from the paper: Step 1 is instantiated with COUNT of Algorithm 1 (Section 8) at a level ℓ
with K_ℓ ≥ 72/δ', e_ℓ ≤ δ'/12 and g_ℓ = 3K_ℓ⁸, where the proof of Theorem 2 (Section 6) takes some K
≥ 72/δ' for which (K, δ'/12) is achievable, from e* = 0, without naming the algorithm for cliques:
the constants are Section 6's, the algorithm for cliques is Section 8's CLIQUE(ℓ) (`StStepOneFor`
and `StSuffices` hold for every machine with the contract, so also for Section 6's);
«O(2^{δ'm}) plus a polynomial in n» becomes «A·2^{δ'm} steps on states of size polynomial in n and
the size of Φ», so that on the Turing machine the polynomial multiplies 2^{δ'm} and is not added to
it; a node of the tree carries n in unary (the width reduction needs a name for its first fresh
variable, and the factor needs n); a leaf has clauses of at most max(k, 2) literals in the bound
taken over from proof/consequences/CountKSat/ (for k ≥ 3 that is k);
time is counted in steps of a machine cut into polynomial-time steps, and then in steps of Mathlib's
Turing machine.
This file has no theorem. -/

@[expose] public section

namespace SplitCount

open Groundwork Groundwork.Prog Groundwork.Sparsify WidthK.Prog Paper CountKSat GraphProblems Eight Eight.ViaGrouping Eight.Width Occ

/-! ### The machine -/

/-- A node of the tree with n in unary beside it. -/
abbrev NNode : Type := List Unit × CNode

/-- The root: the formula as the rule looks at it, and an EMPTY side list. -/
def rootPlain (p : List Unit × Fml) : NNode := (p.1, (rootP p.2, []))

/-- The step of the tree; n is handed down unchanged. -/
def stepPlain (step : CNode → Option (CNode × CNode)) (x : NNode) : Option (NNode × NNode) := (step x.2).map fun lh => ((x.1, lh.1), (x.1, lh.2))

/-- What is counted at a node: (n in unary, side list and formula). -/
def leafPlain (x : NNode) : List Unit × Fml := (x.1, leafF x.2)

/-- Step 1 of the proof, with the machine that computes Z as a parameter: on (n in unary, Φ) run Cnt
on Φ, which gives Z, and return Z·2^{n'}. -/
def timesFreeAfter (Cnt : StepMachine Fml ℤ) : StepMachine (List Unit × Fml) ℕ := Stepped.bind (Stepped.mapIn Prod.snd Cnt) (Stepped.ofFun timesFree)

/-- Step 1 with COUNT of Algorithm 1 at level ℓ. -/
def countThree (ℓ : ℕ) : StepMachine (List Unit × Fml) ℕ := timesFreeAfter (COUNTp ℓ)

/-- The whole procedure without the reader of the input, with the procedure D for 3-CNFs as a
parameter: on (n in unary, formula), 0 if there is an empty clause; otherwise walk the tree, at each
leaf apply the width reduction and then D, and add up; the sum in n + 1 bits. -/
def engineBy (step : CNode → Option (CNode × CNode)) (D : StepMachine (List Unit × Fml) ℕ) : StepMachine (List Unit × Fml) (List Bool) :=
  Stepped.bind
    (Stepped.ite (fun p => hasNil p.2) (Stepped.const 0) (walkSum (stepPlain step) rootPlain (Stepped.mapIn leafPlain (Stepped.mapIn widthP D))))
    (Stepped.ofFun outW)

/-- The procedure with COUNT of Algorithm 1 at level ℓ. -/
def engineSplit (step : CNode → Option (CNode × CNode)) (ℓ : ℕ) : StepMachine (List Unit × Fml) (List Bool) := engineBy step (countThree ℓ)

/-- The procedure at width k, level ℓ, threshold parameter τ of the sparsification. -/
def ENGINEsplit (k ℓ τ : ℕ) : StepMachine (List Unit × Fml) (List Bool) := engineSplit (stepC (WidthK.theta τ) k) ℓ

/-- The machine for #k-SAT: the reader of the input, then the procedure. -/
def COUNTsplit (k ℓ τ : ℕ) : StepMachine (List Bool) (List Bool) := Stepped.mapIn (decU k) (ENGINEsplit k ℓ τ)

/-! ### Step 1 -/

/-- What Section 6 says of the machine that computes Z («Cost»): on a 3-CNF Φ with m clauses, Cnt
returns Z, the number of assignments of the variables occurring in Φ that satisfy Φ, within
A·2^{δ'm} steps, on states of size at most A·(size Φ)^A. It is the conclusion of
`Eight.ViaGrouping.COUNTp_cost`. -/
def ComputesZ (Cnt : StepMachine Fml ℤ) (δ' : ℝ) (A : ℕ) : Prop := ∀ Φ : Fml, (∀ C ∈ Φ, C.length ≤ 3) →
  ∃ T : ℕ, Cnt.Runs Φ T (A * size Φ ^ A) ((Eight.numSat Φ : ℕ) : ℤ) ∧ (T : ℝ) ≤ A * (2 : ℝ) ^ (δ' * Φ.length)

/-- What step 1 says of a procedure D: on (n in unary, Φ), for a list Φ of m clauses of at most 3
literals each on x₀ … xₙ₋₁ (m = 0, empty clauses and repeated clauses included), D returns the
number of satisfying assignments of Φ on n variables within A·2^{δ'm} steps, on states of size
polynomial in n and the size of Φ. -/
def CountsThree (D : StepMachine (List Unit × Fml) ℕ) (δ' : ℝ) (A : ℕ) : Prop := ∀ (n : ℕ) (Φ : Fml), (∀ C ∈ Φ, C.length ≤ 3) → Below n Φ →
  ∃ T : ℕ, D.Runs (List.replicate n (), Φ) T (A * (n + size Φ + 1) ^ A) (cntN n Φ) ∧ (T : ℝ) ≤ A * (2 : ℝ) ^ (δ' * Φ.length)

/-- **Step 1, computes Z, and hence the number Z·2^{n'}, for EVERY machine that computes Z.** -/
def StStepOneFor : Prop := ∀ (Cnt : StepMachine Fml ℤ) (δ' : ℝ) (A : ℕ), 0 ≤ δ' → ComputesZ Cnt δ' A → ∃ A' : ℕ, CountsThree (timesFreeAfter Cnt) δ' A'

/-- **The proof of Theorem 2, with K and g chosen from δ' as there, computes Z, in the form of
Section 6.** Let 0 < δ' ≤ 1, let K ≥ 2 with K ≥ 72/δ', let E be ANY algorithm for cliques on K nodes
with the exponent δ'/12 (`E.Within K (δ'/12)`; «(K, δ'/12) is achievable» asks besides that the
steps of E are polynomial time, which this statement does not need), and g = 3K⁸. The algorithm of
the printed proof of Lemma 1 with E, run on the network of Φ on g clusters, computes Z as Section 6
says.
It is proved (`SplitCount.stComputesZ`) from `Eight.ViaGrouping.stLemGrouping` and
`Eight.ViaGrouping.count_cost_of`. -/
def StComputesZ : Prop := ∀ (δ' : ℝ), 0 < δ' → δ' ≤ 1 → ∀ (K : ℕ) (E : Paper.CliqueAlgorithm), 2 ≤ K → 72 / δ' ≤ K → E.Within K (δ' / 12) →
  ∃ A : ℕ, ComputesZ ((netAlg K (3 * K ^ 8) E).app (satProcs (3 * K ^ 8) 3)) δ' A

/-- COUNT of Algorithm 1 at level ℓ is the machine of `StComputesZ` at K = K_ℓ and E = CLIQUE(ℓ).
(By unfolding definitions.) -/
def StCountIsNetworkMachine : Prop := ∀ ℓ : ℕ, COUNTp ℓ = (netAlg (levelK ℓ) (3 * levelK ℓ ^ 8) (CLIQUEp ℓ)).app (satProcs (3 * levelK ℓ ^ 8) 3)

/-- **Step 1 for COUNT of Algorithm 1.** Let 0 < δ' ≤ 1. At every level ℓ with K_ℓ ≥ 72/δ' and e_ℓ ≤
δ'/12 (Section 6's constants; the level ℓ stands for Section 6's achievable K), `countThree ℓ` does
what step 1 says. Proved from `StComputesZ` at K = K_ℓ and E = CLIQUE(ℓ) (`StCountIsNetworkMachine`;
CLIQUE(ℓ) has the exponent e_ℓ ≤ δ'/12: `Eight.ViaGrouping.CLIQUEp_within`) and `StStepOneFor`, so
that Section 6's form is on the path. -/
def StStepOne : Prop := ∀ (δ' : ℝ), 0 < δ' → δ' ≤ 1 → ∀ ℓ : ℕ, 72 / δ' ≤ levelK ℓ → Eight.Level.levelE ℓ ≤ δ' / 12 → ∃ A : ℕ, CountsThree (countThree ℓ) δ' A

/-! ### Step 2 -/

/-- `step` (with `rootPlain`) sparsifies width k for counting. ψ has variables below n and nonempty
clauses of at most k literals. The tree of depth Dd·n has at most 2^{εn} leaves. The formula of a
leaf has at most Bl·n clauses of at most max k 2 literals, on the same variables.
The numbers of satisfying assignments of the leaves add up to that of ψ. The stack of the walk never
holds more than Dd·n + 1 nodes, each with at most (|ψ| + n)·Sk clauses.
It is `CountKSat.SparsifiesC` without the clauses xᵢ ∨ ¬xᵢ at the root and without «every variable
occurs in every leaf». -/
def SparsifiesPlain (k : ℕ) (ε : ℝ) (step : CNode → Option (CNode × CNode)) (Dd Bl Sk : ℕ) : Prop :=
  ∀ (n : ℕ) (ψ : Fml), (∀ C ∈ ψ, C ≠ [] ∧ C.length ≤ k ∧ ∀ l ∈ C, l.1 < n) →
    ((leaves (stepPlain step) (Dd * n) (rootPlain (List.replicate n (), ψ))).length : ℝ) ≤ (2 : ℝ) ^ (ε * n) ∧
    (∀ x ∈ leaves (stepPlain step) (Dd * n) (rootPlain (List.replicate n (), ψ)), stepPlain step x = none ∧ x.1 = List.replicate n () ∧ (leafF x.2).length ≤ Bl * n ∧
      ∀ C ∈ leafF x.2, C.length ≤ max k 2 ∧ ∀ l ∈ C, l.1 < n) ∧
    cntN n ψ = ((leaves (stepPlain step) (Dd * n) (rootPlain (List.replicate n (), ψ))).map fun x => cntN n (leafF x.2)).sum ∧
    ∀ i, ((round (stepPlain step))^[i] ([rootPlain (List.replicate n (), ψ)], [])).1.length ≤ Dd * n + 1 ∧
      ∀ x ∈ ((round (stepPlain step))^[i] ([rootPlain (List.replicate n (), ψ)], [])).1, x.1 = List.replicate n () ∧ (leafF x.2).length ≤ (ψ.length + n) * Sk ∧
        ∀ C ∈ leafF x.2, C.length ≤ max k 2 ∧ ∀ l ∈ C, l.1 < n

/-- «no two of which share a satisfying assignment»: at every node the two children have no common
satisfying assignment, and an assignment satisfies the node exactly if it satisfies one of them.
(With «the root has the count of the formula» and the sum over the leaves, `CountKSat.StRootCount`
and `CountKSat.StSumLeaves`, this gives the sum in `SparsifiesPlain`. The proof of `StStepTwo` may
take the sum from `CountKSat.SparsifiesC`, where it comes from `CountKSat.StStepCount`, which says
the same for the numbers on n variables; so this is a statement beside the path, there for the
paper's words.) -/
def StDisjoint : Prop := ∀ (θ : ℕ → ℕ) (k : ℕ) (x l h : CNode), stepC θ k x = some (l, h) → ∀ a : ℕ → Bool,
  ((∀ C ∈ leafF x, ∃ t ∈ C, a t.1 = t.2) ↔ ((∀ C ∈ leafF l, ∃ t ∈ C, a t.1 = t.2) ∨ (∀ C ∈ leafF h, ∃ t ∈ C, a t.1 = t.2))) ∧
  ¬((∀ C ∈ leafF l, ∃ t ∈ C, a t.1 = t.2) ∧ (∀ C ∈ leafF h, ∃ t ∈ C, a t.1 = t.2))

/-- «no two of which share a satisfying assignment», for the outputs: no assignment satisfies the
formulas of two different leaves of the tree below any node, cut at any depth. -/
def StDisjointLeaves : Prop := ∀ (θ : ℕ → ℕ) (k d : ℕ) (x : CNode),
  (leaves (stepC θ k) d x).Pairwise fun y z => ∀ a : ℕ → Bool, ¬((∀ C ∈ leafF y, ∃ t ∈ C, a t.1 = t.2) ∧ (∀ C ∈ leafF z, ∃ t ∈ C, a t.1 = t.2))

/-- **Step 2.** For every k and ε > 0 some threshold parameter τ works. -/
def StStepTwo : Prop := ∀ (k : ℕ) (ε : ℝ), 0 < ε → ∃ τ Dd Bl Sk : ℕ, SparsifiesPlain k ε (stepC (WidthK.theta τ) k) Dd Bl Sk

/-! ### Step 3 -/

/-- **Step 3**, for the program. Let Ψ be a formula on x₀ … xₙ₋₁ with m clauses of at most w
literals. `widthP` returns (n₃ in unary, Ψ₃) with: Ψ₃ has at most 3 literals per clause, variables
below n₃, no clause twice; n₃ ≤ n + (w−3)·m; at most m + 3(w−3)·m clauses;
and Ψ₃ has on n₃ variables as many satisfying assignments as Ψ on n. -/
def StStepThree : Prop := ∀ (w n : ℕ) (Ψ : Fml), (∀ C ∈ Ψ, C.length ≤ w) → Below n Ψ →
  (∀ C ∈ (widthP (List.replicate n (), Ψ)).2, C.length ≤ 3) ∧ Below (widthP (List.replicate n (), Ψ)).1.length (widthP (List.replicate n (), Ψ)).2 ∧ (widthP (List.replicate n (), Ψ)).2.Nodup ∧
  (widthP (List.replicate n (), Ψ)).1.length ≤ n + (w - 3) * Ψ.length ∧ (widthP (List.replicate n (), Ψ)).2.length ≤ Ψ.length + 3 * ((w - 3) * Ψ.length) ∧
  cntN (widthP (List.replicate n (), Ψ)).1.length (widthP (List.replicate n (), Ψ)).2 = cntN n Ψ

/-! ### Step 4 and the end -/

/-- «then applying Theorem 2 with a small enough value in place of δ»: a leaf has at most Bl·n
clauses of at most w literals, its 3-CNF at most (1 + 3(w−3))·Bl·n clauses; δ' = min(δ/(3·(1 +
3(w−3))·(Bl+1)), 1). -/
/- (Used with w ≥ 3 only; every caller passes max k 3.) -/
noncomputable def deltaPrime (δ : ℝ) (w Bl : ℕ) : ℝ := min (δ / (3 * ((1 + 3 * ((w : ℝ) - 3)) * ((Bl : ℝ) + 1)))) 1

/-- **«By the work of Dell et al. … this case suffices», for EVERY procedure D that does what step 1
says.** Let k ≥ 1 and δ > 0, let `step` sparsify width k for counting with ε = δ/3 and leaves of at
most Bl·n clauses, and let D do what step 1 says with an exponent δ' ≥ 0 such that δ'·(1 +
3(max(k,3) − 3))·(Bl + 1) ≤ δ/3.
Then `engineBy step D` serves as the procedure for #k-SAT with the exponent δ (`Eight.Serves`: on (N
in unary, ψ) it returns the number of satisfying assignments in N + 1 bits within c·2^{δN} steps, on
states of polynomial size). -/
def StSuffices : Prop := ∀ (k : ℕ), 1 ≤ k → ∀ δ : ℝ, 0 < δ → ∀ (step : CNode → Option (CNode × CNode)) (Dd Bl Sk : ℕ), SparsifiesPlain k (δ / 3) step Dd Bl Sk →
  ∀ (D : StepMachine (List Unit × Fml) ℕ) (δ' : ℝ) (A : ℕ), 0 ≤ δ' → δ' * ((1 + 3 * (((max k 3 : ℕ) : ℝ) - 3)) * ((Bl : ℝ) + 1)) ≤ δ / 3 → CountsThree D δ' A →
  ∃ c : ℕ, Serves (engineBy step D) k δ c

/-- **Step 4, with the machine named.** Let k ≥ 1 and δ > 0, let `step` sparsify width k for
counting with ε = δ/3 and leaves of at most Bl·n clauses, and δ' = `deltaPrime δ (max k 3) Bl` (for
the paper's k ≥ 3, max(k, 3) = k). At every level ℓ with K_ℓ ≥ 72/δ' and e_ℓ ≤ δ'/12,
`engineSplit step ℓ` serves as the procedure for #k-SAT with the exponent δ. Proved from `StStepOne`
and `StSuffices`. -/
def StCountsAt : Prop := ∀ (k : ℕ), 1 ≤ k → ∀ δ : ℝ, 0 < δ → ∀ (step : CNode → Option (CNode × CNode)) (Dd Bl Sk : ℕ), SparsifiesPlain k (δ / 3) step Dd Bl Sk →
  ∀ ℓ : ℕ, 72 / deltaPrime δ (max k 3) Bl ≤ levelK ℓ → Eight.Level.levelE ℓ ≤ deltaPrime δ (max k 3) Bl / 12 → ∃ c : ℕ, Serves (engineSplit step ℓ) k δ c

/-- The steps of the procedure are polynomial time, if the step of the tree and the steps of the
parameter are. -/
def StCert : Prop := (∀ Cnt : StepMachine Fml ℤ, PolyTimeSteps Cnt → PolyTimeSteps (timesFreeAfter Cnt)) ∧
  ∀ (step : CNode → Option (CNode × CNode)) (D : StepMachine (List Unit × Fml) ℕ), PolyT step → PolyTimeSteps D → PolyTimeSteps (engineBy step D)

/-- **Corollary 6 for machines cut into steps, with the machine named**, in the form in which
Corollary 7 and the circuit lower bound for E^NP (Section 7) take it
(`Eight.ViaGrouping.EngineCounts`; there for every k ≥ 1: below 3 the width reduction changes
nothing). -/
def StEngineCounts : Prop := EngineCounts ENGINEsplit

/-- **#k-SAT with the machine named.** For every k ≥ 1 and δ > 0 there are a level ℓ and a threshold
parameter τ such that `COUNTsplit k ℓ τ` has polynomial-time steps and writes the number of
satisfying assignments of a k-CNF on n variables, in n + 1 bits, within c·2^{δn} steps, on states of
size polynomial in the length of the input. -/
def StCOUNTsplitCounts : Prop := ∀ (k : ℕ), 1 ≤ k → ∀ δ : ℝ, 0 < δ → ∃ ℓ τ : ℕ, PolyTimeSteps (COUNTsplit k ℓ τ) ∧
  ∃ c : ℕ, ∀ (n : ℕ) (φ : Sat3.CNF n), SatK.IsKCNF k φ →
    ∃ T : ℕ, (COUNTsplit k ℓ τ).Runs (SatK.enc k φ) T (c * ((SatK.enc k φ).length + 1) ^ c) (SatK.binary n (SatK.numSat φ)) ∧ (T : ℝ) ≤ c * (2 : ℝ) ^ (δ * n)

/-- **Tied to the machine, on Mathlib's Turing machines.** For every k ≥ 1 and δ > 0 there are ℓ, τ
such that (1) `COUNTsplit k ℓ τ` ITSELF has polynomial-time steps and writes the number of
satisfying assignments of a k-CNF on n variables within c·2^{δn} steps, on states of size polynomial
in the length of the input; (2) a Turing machine M with finite alphabets simulates it with
polynomial overhead
(whenever that machine ends on a word x with a word w within T steps on states of size at most S, M
started on x halts with w within q·(T+1)·(|x|+S+1)^q steps); (3) M counts the satisfying assignments
of k-CNFs within ⌊c·2^{δn}⌋ steps. (Without (1), a machine that runs the named machine and another
one side by side would meet (2) and (3).) -/
def StTiedTM : Prop := ∀ (k : ℕ), 1 ≤ k → ∀ δ : ℝ, 0 < δ → ∃ (ℓ τ : ℕ) (M : Turing.TM2ComputableAux Bool Bool) (c q : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧
  PolyTimeSteps (COUNTsplit k ℓ τ) ∧
  (∀ (n : ℕ) (φ : Sat3.CNF n), SatK.IsKCNF k φ →
    ∃ T : ℕ, (COUNTsplit k ℓ τ).Runs (SatK.enc k φ) T (c * ((SatK.enc k φ).length + 1) ^ c) (SatK.binary n (SatK.numSat φ)) ∧ (T : ℝ) ≤ c * (2 : ℝ) ^ (δ * n)) ∧
  (∀ (x w : List Bool) (T S : ℕ), (COUNTsplit k ℓ τ).Runs x T S w →
    Nonempty (Turing.TM2OutputsInTime M.tm (x.map M.inputAlphabet.invFun) (some (w.map M.outputAlphabet.invFun)) (q * (T + 1) * (x.length + S + 1) ^ q))) ∧
  SatK.CountsTM k M fun n => ⌊(c : ℝ) * (2 : ℝ) ^ (δ * n)⌋₊

/-- The end theorem has the statement `ThreeSatStatement` (below), the statement of Corollary 6 in
PaperSentencesStatement.lean. Both of its halves are proved from `StTiedTM`: the second, «#ETH is
false», from `StTiedTM` at k = 3 by the generic `not_CountETH_TM_of` of
proof/consequences/CountKSat/EndLemmas.lean.
The end theorem is proved through `SplitCount.endFrom : StTiedTM → ThreeSatStatement`, which has the
tied statement as HYPOTHESES. Of the theorems of this development, the proof of `SplitCount.endFrom`
uses only lemmas that say nothing about a particular machine (such as `not_CountETH_TM_of`); so what
it says about machines can only come from the hypotheses.
The proof of `StStepTwo` takes the bound on the tree from `CountKSat.StProgC` (the tree does not
depend on the side list), and the count of a leaf never uses the clauses xᵢ ∨ ¬xᵢ. -/
abbrev ThreeSatStatement : Prop := PaperSentences.CorCounting

end SplitCount
