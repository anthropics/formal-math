/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Printed.Programs
public import SplitSat.Defs
public import FreeCode.Defs
public import Sat3Graph.Defs
public import Consequences.Defs

/-! # Section 7 on the machines of proof/threesat/Printed/, the deciding half (definitions and statements only)

The files of proof/consequences/SplitSat/, proof/consequences/FreeCode/,
proof/consequences/Sat3Graph/ and proof/consequences/Consequences/ draw Corollary 5, the sentence on
NSETH and Corollary 7 for deciding (Section 7) from Theorem 2 along the routes of the printed
proofs, with the procedure D for 3-SAT as a PARAMETER (`SplitSat.Decides3 D δ c`). Only a few of
their definitions and statements name a machine: `SplitSat.core3 ℓ τ`, which is another machine for
the main text (`ThreeSatPrinted.SATCp ℓ τ`, over `Eight.ViaGrouping.COUNTp ℓ`) without its reader.
This file states such definitions and statements for `Printed.SAT ℓ τ` (over `Printed.COUNT ℓ`,
`Printed.NETWORK ℓ`, `Printed.CLIQUE ℓ`; proof/threesat/Printed/) in the namespaces `FromPrinted.X`:
where those folders have a statement of the same short name, `SplitSat.core3` is replaced by the
machine of `Printed.SAT`, and nothing else is changed. `Printed.SAT ℓ τ` is Algorithm 1 on
Definition 4 in the paper's unit of cost (a table query costs one operation), with a bound on memory
(`Printed.Achievable`); ℓ is the level, and τ is the threshold parameter of the sparsification
behind Lean's enumeration for Lemma 4 (`Enumerate.rule τ`), not the price of a query in Definition 2
(iii). What is said there for every D is used as it stands.

Two things differ because the machines differ. (1) `Printed.SAT ℓ τ` is
`Suffices.satLoop τ (Printed.COUNT ℓ)`: lines 1 to 4 of Algorithm 1 with the early return
(`Exits.walkUntil`), over the outputs ψ ∪ 𝒩 of the enumeration of Lemma 4 (`Enumerate.rule τ`,
`SparsificationLemma.out`); so the body of `core3` is that loop, not the walk of `SplitSat.core3`,
and it looks at N (the root of the tree carries it). (2) Its reader is `decU 3`, so `StCore3Eq` is
written with `decU 3`.
What is different from the paper is listed at the heads of proof/consequences/SplitSat/Defs.lean,
proof/consequences/FreeCode/Defs.lean, proof/consequences/Sat3Graph/Defs.lean,
proof/consequences/Consequences/Defs.lean and proof/threesat/Printed/Programs.lean.
This file has no theorem. -/

@[expose] public section

section

open Groundwork Groundwork.Prog Groundwork.Prog.SatTopK Groundwork.Sparsify WidthK.Prog UniformInK Paper CountKSat Eight Eight.ViaGrouping Eight.Width SplitSat

namespace FromPrinted.SplitSat

/-! ### Theorem 2 in its decision form as the procedure -/

/-- Procedure SAT of Algorithm 1 (lines 1 to 4, with the early return, over the formulas that the
enumeration of Lemma 4 produces; at level ℓ, with threshold parameter τ) without its reader of the
input. -/
def core3 (ℓ τ : ℕ) : StepMachine (List Unit × Fml) Bool :=
  Stepped.ite (fun p => hasNil p.2) (Stepped.const false) (Exits.walkUntil (Enumerate.rule τ) rootC (Stepped.mapIn SparsificationLemma.out (Stepped.mapOut (Printed.COUNT ℓ) posZ)))

/-- The machine of Theorem 2 is the reader of the input followed by `core3`. -/
def StCore3Eq : Prop := ∀ ℓ τ : ℕ, Printed.SAT ℓ τ = Stepped.mapIn (decU 3) (core3 ℓ τ)

/-- **«Theorem 2 gives s_3 = 0»**, for the machine of Theorem 2 in its decision form without its
reader: for every δ > 0 there are ℓ and τ such that `core3 ℓ τ` has polynomial-time steps and
decides 3-SAT with the exponent δ. Derived from the tied form of Theorem 2, `Printed.stDecides`. -/
def StCore3 : Prop := ∀ δ : ℝ, 0 < δ → ∃ ℓ τ : ℕ, PolyTimeSteps (core3 ℓ τ) ∧ ∃ c : ℕ, Decides3 (core3 ℓ τ) δ c

/-- k-SAT by the reduction to the algorithm of Theorem 2: τ is the threshold parameter of the tree
at width k; ℓ₃ and τ₃ are the level and the threshold parameter of the algorithm for 3-SAT. -/
def SATsplit (k τ ℓ₃ τ₃ : ℕ) : StepMachine (List Bool) Bool := REDUCE k τ (core3 ℓ₃ τ₃)

/-- **k-SAT with the machine named.** For every k ≥ 3 and δ > 0 there are τ, ℓ₃, τ₃ such that
`SATsplit k τ ℓ₃ τ₃` has polynomial-time steps and decides k-SAT with the exponent δ. (It holds at k =
3 too, where the reduction puts a further sparsification in front of the algorithm of Theorem 2; the
end theorem takes s_3 = 0 from Theorem 2 directly, as the paper does, and uses this statement for k > 3.) -/
def StSATsplit : Prop := ∀ (k : ℕ), 3 ≤ k → ∀ δ : ℝ, 0 < δ → ∃ τ ℓ₃ τ₃ : ℕ, PolyTimeSteps (SATsplit k τ ℓ₃ τ₃) ∧ ∃ c : ℕ, Decides (SATsplit k τ ℓ₃ τ₃) k δ c

/-- **Tied to the machine, on Mathlib's Turing machines.** For every k ≥ 3 and δ > 0 there are τ,
ℓ₃, τ₃ such that (1) `SATsplit k τ ℓ₃ τ₃` ITSELF has polynomial-time steps and decides k-SAT with
the exponent δ; (2) a Turing machine M with finite alphabets simulates it with polynomial overhead
(`Simulates`);
(3) M decides k-SAT within ⌊c·2^{δn}⌋ steps. (Without (1), a machine that runs the named machine and
    another one side by side would meet (2) and (3).) -/
def StTiedTM : Prop := ∀ (k : ℕ), 3 ≤ k → ∀ δ : ℝ, 0 < δ → ∃ (τ ℓ₃ τ₃ : ℕ) (M : Turing.TM2ComputableAux Bool Bool) (c q : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧
  PolyTimeSteps (SATsplit k τ ℓ₃ τ₃) ∧ Decides (SATsplit k τ ℓ₃ τ₃) k δ c ∧
  Simulates M (SATsplit k τ ℓ₃ τ₃) q ∧
  SatK.DecidesTM k M fun n => ⌊(c : ℝ) * (2 : ℝ) ^ (δ * n)⌋₊

/-- **«Theorem 2 gives s_3 = 0», tied to the machine of Theorem 2 in its decision form.** For every
δ > 0 there are ℓ, τ such that (1) `Printed.SAT ℓ τ` (lines 1 to 4 of Algorithm 1 in their deciding
form, with its own reader) ITSELF has polynomial-time steps and decides 3-SAT with the exponent δ; (2)
a Turing machine M with finite alphabets simulates it with polynomial overhead; (3) M decides 3-SAT
within ⌊c·2^{δn}⌋ steps. (`SatK.enc 3 φ` is `Sat3.enc φ` by definition.) Proved from
`Printed.stDecides`. -/
def StTiedThreeTM : Prop := ∀ δ : ℝ, 0 < δ → ∃ (ℓ τ : ℕ) (M : Turing.TM2ComputableAux Bool Bool) (c q : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧
  PolyTimeSteps (Printed.SAT ℓ τ) ∧ Decides (Printed.SAT ℓ τ) 3 δ c ∧ Simulates M (Printed.SAT ℓ τ) q ∧ SatK.DecidesTM 3 M fun n => ⌊(c : ℝ) * (2 : ℝ) ^ (δ * n)⌋₊

/-- The end theorem has the statement `PaperSentences.CorEth` of
proof/statements/PaperSentencesStatement.lean. For k > 3 the proof uses `StTiedTM`; at k = 3 it uses
`StTiedThreeTM`, as the paper does («Theorem 2 gives s_3 = 0»); then the generic
`SatK.sTM_eq_zero_of`.
The end theorem is proved in two pieces:
`FromPrinted.SplitSat.endFrom : StTiedTM → StTiedThreeTM → ThreeSatStatement`, which has the two
tied statements as HYPOTHESES, and the one-line instance
`FromPrinted.SplitSat.eth_and_seth_false := endFrom stTiedTM stTiedThreeTM`. The theorems of this
development (everything outside Lean's core, Std, Batteries and Mathlib) that the proof of
`FromPrinted.SplitSat.endFrom` reaches say nothing about a particular machine (such as
`SatK.sTM_eq_zero_of`); so what the end theorem says about machines can only come from the
hypotheses.
The instance rests on the proofs of `StReduceCore`, `StCore3`, `StSATsplit`, `StTiedTM` and
`StTiedThreeTM` (named `SplitSat.stReduceCore` and `FromPrinted.SplitSat.stCore3`, `stSATsplit`,
`stTiedTM`, `stTiedThreeTM`), `Printed.stDecides` and
`SparsificationLemma.TreeWalk.lemSparsification_walk_k`, and not on the other machines for the main
text (`SplitSat.core3`, `ThreeSatPrinted.SATCp`, `ThreeSatPrinted.algPseudocode_decides_viaC`,
`Eight.ViaGrouping.COUNTp`, `Eight.ViaGrouping.CLIQUEp`, `Eight.ViaGrouping.stLemGrouping`). -/
abbrev ThreeSatStatement : Prop := PaperSentences.CorEth

end FromPrinted.SplitSat

end

section

open Groundwork Groundwork.Prog WidthK.Prog UniformInK Paper FreeCode
open SplitSat hiding core3 StCore3Eq StCore3 SATsplit StSATsplit StTiedTM StTiedThreeTM ThreeSatStatement
open FromPrinted.SplitSat

namespace FromPrinted.FreeCode

/-- **«Theorem 2 gives s_3 = 0».** For every δ > 0 there are a polynomial-time reader, ℓ, τ such
that (1) the machine of Theorem 2 in its decision form (`core3 ℓ τ`) behind the reader ITSELF has
polynomial-time steps and decides 3-SAT with the exponent δ; (2) a Turing machine with finite
alphabets simulates it with polynomial overhead; (3) that Turing machine decides 3-SAT within
⌊c·2^{δn}⌋ steps. -/
def StTiedThree : Prop := ∀ δ : ℝ, 0 < δ → ∃ (dec : List Bool → List Unit × Fml) (ℓ τ : ℕ) (M : Turing.TM2ComputableAux Bool Bool) (c q : ℕ), PolyT dec ∧ Reads dec ∧ (∀ i, Finite (M.tm.Γ i)) ∧
  PolyTimeSteps (Stepped.mapIn dec (core3 ℓ τ)) ∧ DecidesFree (Stepped.mapIn dec (core3 ℓ τ)) 3 δ c ∧
  Simulates M (Stepped.mapIn dec (core3 ℓ τ)) q ∧ SatFree.DecidesTM 3 M fun n => ⌊(c : ℝ) * (2 : ℝ) ^ (δ * n)⌋₊

/-- **Corollary 5, tied to the reduction.** For every k ≥ 3 and δ > 0 there are a polynomial-time
reader, τ, ℓ₃, τ₃ such that (1) the reduction (sparsify at width k with the parameter τ, split every
long clause, ask the machine of Theorem 2 in its decision form) behind the reader ITSELF has
polynomial-time steps and decides k-SAT with the exponent δ; (2) a Turing machine with finite
alphabets simulates it with polynomial overhead;
(3) that Turing machine decides k-SAT within ⌊c·2^{δn}⌋ steps. (Without (1), a machine that runs the
    reduction and another machine side by side would meet (2) and (3), and only the correctness of
    the reduction would be needed, not its running time.) -/
def StTied : Prop := ∀ (k : ℕ), 3 ≤ k → ∀ δ : ℝ, 0 < δ → ∃ (dec : List Bool → List Unit × Fml) (τ ℓ₃ τ₃ : ℕ) (M : Turing.TM2ComputableAux Bool Bool) (c q : ℕ), PolyT dec ∧ Reads dec ∧ (∀ i, Finite (M.tm.Γ i)) ∧
  PolyTimeSteps (Stepped.mapIn dec (reduceCore (stepK (thetaU τ) k) (core3 ℓ₃ τ₃))) ∧ DecidesFree (Stepped.mapIn dec (reduceCore (stepK (thetaU τ) k) (core3 ℓ₃ τ₃))) k δ c ∧
  Simulates M (Stepped.mapIn dec (reduceCore (stepK (thetaU τ) k) (core3 ℓ₃ τ₃))) q ∧ SatFree.DecidesTM k M fun n => ⌊(c : ℝ) * (2 : ℝ) ^ (δ * n)⌋₊

end FromPrinted.FreeCode

end

section

open Groundwork Groundwork.Prog CountKSat GraphProblems Paper Eight.Width SizeCircuit Complement Sat3Graph
open SplitSat hiding core3 StCore3Eq StCore3 SATsplit StSATsplit StTiedTM StTiedThreeTM ThreeSatStatement
open FromPrinted.SplitSat

namespace FromPrinted.Sat3Graph

/-- **«Theorem 2 suffices»**: for every family of circuits that tests the size and is computed in
polynomial time, every δ > 0 and k ≥ 3 there are ℓ, τ, w such that the five deciders with D = the
machine of Theorem 2 in its decision form without its reader have polynomial-time steps and decide
the five problems within c·2^{δn} steps. -/
def StWithThreeSatMachine : Prop := ∀ (gates : ℕ → ℕ → List CircuitLowerBound.GateD) (a : ℕ), TestsSize gates a → CertGates gates → ∀ (δ : ℝ), 0 < δ → ∀ k : ℕ, 3 ≤ k → ∃ ℓ τ w c : ℕ,
  (PolyTimeSteps (INDEP gates (core3 ℓ τ)) ∧ PolyTimeSteps (CLIQUE gates (core3 ℓ τ)) ∧ PolyTimeSteps (COVER gates (core3 ℓ τ)) ∧
    PolyTimeSteps (DOM w gates (core3 ℓ τ)) ∧ PolyTimeSteps (COLOR k (core3 ℓ τ))) ∧
  DecidesGraph (INDEP gates (core3 ℓ τ)) (fun n G s => ∃ S : Finset (Fin n), G.IsIndepSet (S : Set (Fin n)) ∧ s ≤ S.card) δ c ∧
  DecidesGraph (CLIQUE gates (core3 ℓ τ)) (fun n G s => ∃ S : Finset (Fin n), G.IsClique (S : Set (Fin n)) ∧ s ≤ S.card) δ c ∧
  DecidesGraph (COVER gates (core3 ℓ τ)) (fun n G s => ∃ S : Finset (Fin n), G.IsVertexCover (S : Set (Fin n)) ∧ S.card ≤ s) δ c ∧
  DecidesGraph (DOM w gates (core3 ℓ τ)) (fun n G s => ∃ S : Finset (Fin n), IsDominating G S ∧ S.card ≤ s) δ c ∧
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)), ∃ (T : ℕ) (b : Bool), (COLOR k (core3 ℓ τ)).Runs (code G) T (c * (n + 2) ^ c) b ∧ (b = true ↔ G.Colorable k) ∧ (T : ℝ) ≤ c * (2 : ℝ) ^ (δ * n)

/-- **Tied to the machines, on Mathlib's Turing machines.** For every δ > 0 and k ≥ 3 there are a
family of circuits that tests the size and is computed in polynomial time, and ℓ, τ, w, c such that
each of the five deciders with D = the machine of Theorem 2 in its decision form without its reader (1)
ITSELF has polynomial-time steps and decides its problem within c·2^{δn} steps, and (2) is simulated
with polynomial overhead by a Turing machine with finite alphabets that decides the problem within
O(2^{δn}) steps. -/
def StTiedTM : Prop := ∀ δ : ℝ, 0 < δ → ∀ k : ℕ, 3 ≤ k → ∃ (gates : ℕ → ℕ → List CircuitLowerBound.GateD) (a ℓ τ w c : ℕ), TestsSize gates a ∧ CertGates gates ∧
  (PolyTimeSteps (INDEP gates (core3 ℓ τ)) ∧ DecidesGraph (INDEP gates (core3 ℓ τ)) (fun n G s => ∃ S : Finset (Fin n), G.IsIndepSet (S : Set (Fin n)) ∧ s ≤ S.card) δ c ∧
    HostedFor (INDEP gates (core3 ℓ τ)) (fun n G s => ∃ S : Finset (Fin n), G.IsIndepSet (S : Set (Fin n)) ∧ s ≤ S.card) δ) ∧
  (PolyTimeSteps (CLIQUE gates (core3 ℓ τ)) ∧ DecidesGraph (CLIQUE gates (core3 ℓ τ)) (fun n G s => ∃ S : Finset (Fin n), G.IsClique (S : Set (Fin n)) ∧ s ≤ S.card) δ c ∧
    HostedFor (CLIQUE gates (core3 ℓ τ)) (fun n G s => ∃ S : Finset (Fin n), G.IsClique (S : Set (Fin n)) ∧ s ≤ S.card) δ) ∧
  (PolyTimeSteps (COVER gates (core3 ℓ τ)) ∧ DecidesGraph (COVER gates (core3 ℓ τ)) (fun n G s => ∃ S : Finset (Fin n), G.IsVertexCover (S : Set (Fin n)) ∧ S.card ≤ s) δ c ∧
    HostedFor (COVER gates (core3 ℓ τ)) (fun n G s => ∃ S : Finset (Fin n), G.IsVertexCover (S : Set (Fin n)) ∧ S.card ≤ s) δ) ∧
  (PolyTimeSteps (DOM w gates (core3 ℓ τ)) ∧ DecidesGraph (DOM w gates (core3 ℓ τ)) (fun n G s => ∃ S : Finset (Fin n), IsDominating G S ∧ S.card ≤ s) δ c ∧
    HostedFor (DOM w gates (core3 ℓ τ)) (fun n G s => ∃ S : Finset (Fin n), IsDominating G S ∧ S.card ≤ s) δ) ∧
  (PolyTimeSteps (COLOR k (core3 ℓ τ)) ∧
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)), ∃ (T : ℕ) (b : Bool), (COLOR k (core3 ℓ τ)).Runs (code G) T (c * (n + 2) ^ c) b ∧ (b = true ↔ G.Colorable k) ∧ (T : ℝ) ≤ c * (2 : ℝ) ^ (δ * n)) ∧
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (C q : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧ Simulates M (COLOR k (core3 ℓ τ)) q ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)), ∃ b : Bool, (b = true ↔ G.Colorable k) ∧ Outputs M (code G) [b] ⌊(C : ℝ) * (2 : ℝ) ^ (δ * n)⌋₊)

/-- The end theorem has the statement `GraphProblems.CorGraphsDecide`. It is proved from `StTiedTM`,
in two pieces: `FromPrinted.Sat3Graph.endFrom : StTiedTM → ThreeSatStatement`, which has the tied
statement as HYPOTHESES, and the one-line instance
`FromPrinted.Sat3Graph.decideFromThreeSat := endFrom stTiedTM`. The theorems of this development
(everything outside Lean's core, Std, Batteries and Mathlib) that the proof of
`FromPrinted.Sat3Graph.endFrom` reaches say nothing about a particular machine (only
`Sat3Graph.decidesInTime_of_hosted`, which takes a tuple apart); so what the end theorem says about
machines can only come from the hypotheses.
The instance rests on the proofs of `StAskSized`, `StSets`, `StDominating`, `StColoring` (named
`Sat3Graph.stAskSized`, …) and `StTiedTM` (`FromPrinted.Sat3Graph.stTiedTM`), on
`Sat3Graph.askSized`, `SizeCircuit.gamma`, `Eight.Width.widthP`, `FromPrinted.SplitSat.core3`,
`Complement.readClique`, `Complement.readCover` and `GraphProblems.stepD`,
and not on the other machines for the main text (`SplitSat.core3`, `ThreeSatPrinted.SATCp`,
`ThreeSatPrinted.algPseudocode_decides_viaC`, `Eight.ViaGrouping.COUNTp`,
`Eight.ViaGrouping.CLIQUEp`, `Eight.ViaGrouping.stLemGrouping`), `GraphProblems.blockF`,
`GraphProblems.cliqueF`, `GraphProblems.coverF`, nor on any machine for #k-SAT or for counting with
a prescribed number of true variables (`CountKSat.walkSum`, `SplitCount.engineBy`,
`SizeCircuit.sizedBy`). -/
abbrev ThreeSatStatement : Prop := GraphProblems.CorGraphsDecide

end FromPrinted.Sat3Graph

end

section

open Groundwork Groundwork.Prog CountKSat GraphProblems Paper Eight Eight.ViaGrouping SizeCircuit Complement
open SplitSat hiding core3 StCore3Eq StCore3 SATsplit StSATsplit StTiedTM StTiedThreeTM ThreeSatStatement
open FromPrinted.SplitSat

namespace FromPrinted.Consequences

/-- **The verifier for tautologies, with the machine named**: for every k ≥ 3 and δ > 0 there are τ,
ℓ₃, τ₃ and c such that `SATsplit k τ ℓ₃ τ₃` has polynomial-time steps and decides k-SAT with the
exponent δ and the constant c, and the verifier made from it (take the witness off and ignore it,
run the machine, answer with the opposite bit) has polynomial-time steps and, on every witness w and
the code of a k-DNF ψ on n variables, ends within c·2^{δn} steps,
on states of size at most c·(length of the code of ψ + 1)^c, with the bit «ψ is a tautology». Taking
the witness off happens when the input is handed over and is not counted among the steps. The
machine runs on the code of ψ as it stands: read as a k-CNF, that code is the negation of ψ with
every variable complemented, so it is satisfiable exactly when ψ is not a tautology.
Proved from `FromPrinted.SplitSat.stSATsplit`, `Eight.ViaGrouping.verifier_polyTimeSteps` and
`Eight.ViaGrouping.verifier_recognizes`. `nsethFrom` uses only its first two conjuncts. -/
def StVerifier : Prop := ∀ (k : ℕ), 3 ≤ k → ∀ δ : ℝ, 0 < δ → ∃ τ ℓ₃ τ₃ c : ℕ,
  PolyTimeSteps (SATsplit k τ ℓ₃ τ₃) ∧ Decides (SATsplit k τ ℓ₃ τ₃) k δ c ∧ PolyTimeSteps (verifier (SATsplit k τ ℓ₃ τ₃)) ∧
  ∀ (n : ℕ) (ψ : Eight.DNF n), Eight.IsKDNF k ψ → ∀ w : List Bool,
    ∃ (T : ℕ) (b : Bool), (verifier (SATsplit k τ ℓ₃ τ₃)).Runs (Eight.withWitness w (SatK.enc k ψ)) T (c * ((SatK.enc k ψ).length + 1) ^ c) [b] ∧
      (b = true ↔ Eight.Tautology ψ) ∧ (T : ℝ) ≤ c * (2 : ℝ) ^ (δ * n)

/-- A k-CNF with k ≤ 3 is a 3-CNF, but its code has k slots per clause, not 3. So for k ≤ 3 the
machine for k-SAT is the reader for width k followed by the machine of Theorem 2 in its decision
form without its reader. (At k = 3 it is `Printed.SAT ℓ τ`; see `FromPrinted.SplitSat.StCore3Eq`.) -/
def SATsmall (k ℓ τ : ℕ) : StepMachine (List Bool) Bool := Stepped.mapIn (decU k) (core3 ℓ τ)

/-- For 1 ≤ k ≤ 3 and δ > 0 some `SATsmall k ℓ τ` has polynomial-time steps and decides k-SAT with
the exponent δ. -/
def StSmallWidths : Prop := ∀ (k : ℕ), 1 ≤ k → k ≤ 3 → ∀ δ : ℝ, 0 < δ → ∃ ℓ τ c : ℕ, PolyTimeSteps (SATsmall k ℓ τ) ∧ Decides (SATsmall k ℓ τ) k δ c

/-- «NSETH … is false as well».
`FromPrinted.Consequences.nsethFrom : StVerifier → StSmallWidths → NsethFalse`, by
`Eight.ViaGrouping.not_NSETH_TM_of`, whose hypothesis is met for k > 3 by the machines of
`StVerifier` (its first two conjuncts) and for k ≤ 3 by those of `StSmallWidths`; inside
`not_NSETH_TM_of` the Turing machine simulates `verifier M` for exactly these M. It rests on
`FromPrinted.Consequences.stVerifier`, `FromPrinted.Consequences.stSmallWidths`,
`FromPrinted.SplitSat.stSATsplit`, `FromPrinted.SplitSat.stCore3`, `Printed.stDecides`.
It does not rest on the other machines for the main text (`SplitSat.core3`, `ThreeSatPrinted.SATCp`,
`ThreeSatPrinted.algPseudocode_decides_viaC`, `Eight.ViaGrouping.COUNTp`,
`Eight.ViaGrouping.CLIQUEp`, `Eight.ViaGrouping.stLemGrouping`). -/
abbrev NsethFalse : Prop := ¬ Eight.NSETH_TM

end FromPrinted.Consequences

end
