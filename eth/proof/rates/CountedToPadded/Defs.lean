/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import CliqueLevelsStatement
public import QueryMachines.Poly
public import ClauseBound.Alg.Interfaces
public import PaddedDescent.F.Fuel
public import PaddedDescent.F.Data
public import VariableBound.Printed.ThmVariablesADefs

/-! # From counted operations to the padding string

Definitions and statements only; nothing is proved here.

**Why.** Appendix D, the joining theorem and the Main Theorem of this development stand on
`ClauseBound.Alg.Solver` with `Solver.Seq` (proof/rates/ClauseBound/Alg/Interfaces.lean): an
algorithm for cliques is a polynomial-time function of (padding string, index, instance with its
tables written out) that is right once the padding string has 2^need units. Theorem A (b) and the
hypothesis of Theorem D (a) speak of ONE algorithm with query access and of its number of operations
(`CliqueLevels.Solves`). This file is the step from the second form to the first, for EVERY machine
M: `solverOfMachine M num C₀` is a definition, a function of M and of its certificate of
polynomial-time steps (the cut reads the coding of the states, which comes with the certificate; on
the inputs of which `Solver.Correct` speaks the result does not
depend on it). So a statement about `solverOfMachine M` has a binder `[IsPolyQ M]`.

**What is here.**
* `runFor N fuel room a`: the step machine N on the input a, run for as many steps as `fuel` has
  units; a state whose word has more than `room` symbols ends the run without a result.
  `RunForIsRight`: it returns the result of N if N halts within that many steps on states that are
  small enough. `RunForPoly`: it is
  polynomial-time in (fuel, room in unary, a) if N has polynomial-time steps, whether or not N
  halts.
* `EveryWordIsCompared`: whether the word of a value is at most as long as a given padding string is
  decided in polynomial time, for EVERY coding. This development can compute the length of the word
  for the codings of numbers, pairs and lists (`PaddedDescent.F.Meas`); the coding of the states of
  M comes with the certificate of M and is arbitrary, so
  `RunForPoly` needs this in general.
* `entry`, `lookup`, `onTables M`: the queries of M answered from tables that are written out
  (`QueryMachine.plug`). `bitsOfTables`: the number B that M is given; an instance here does not
  hold it.
* `needOf`, `solverOfMachine`, `pickOf`; `SolverOfMachineLevels`, the main statement.

**Where the solver differs from the machine.**
* The sequence of levels is for e′_ℓ = `CliqueLevels.cutNumber K num ℓ`, the number in [e_ℓ, 2e_ℓ]
  that can be computed, cut at 1, and not for e_ℓ: the exponent `need` must be computed, e_ℓ is a
  real number, and `Solves` says only that some number of operations below the bound exists.
* The constant is 2C₀ + 1 in place of C₀. It does not depend on the certificate of M: the padding
  string has to be as long as the run (three times the number of operations) and as the states of M,
  not as the run of a Turing machine.
* The tables do not have to fit into the padding string: a state of `onTables M` holds them twice,
  and the room that `solverOfMachine` allows is 7 times the padding string and 14 times the word of
  the tables. (For small e_ℓ and large λ the tables, of 2^{(K−1)λ} entries each, are longer than
  2^need.)
* M is given B′ = the largest number of bits of an entry, at least 1. If all entries are at most 2^B
  in absolute value, as `ClauseBound.Alg.WFe` says, then B′ ≤ B + 1 and all entries are below
  2^{B′}, as `Solves` asks. So `need` is the bound at B + 1. -/

@[expose] public section

namespace QueryMachines.Bridge

open Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg Eight.SecNetworks Printed CliqueLevels

/-! ### A step machine run on a padding string -/

section runFor

variable {α β : Type}

/-- One step of N; a state that has halted stays as it is. -/
def stay (N : Stepped α β) (s : N.σ) : N.σ := if (N.out s).isSome then s else N.step s

/-- x if its word has at most `room` symbols, else nothing. (This is `PaddedDescent.F.cap` with a
padding string of `room` units and `none` as the value to fall back on.) -/
def cutAt {γ : Type} [Enc γ] (room : ℕ) (x : Option γ) : Option γ := if len x ≤ room then x else none

/-- N on the input a, run for as many steps as `fuel` has units. A state whose word (as an optional
value) has more than `room` symbols ends the run. The result, if N has halted. -/
def runFor (N : Stepped α β) [Enc N.σ] (fuel : U) (room : ℕ) (a : α) : Option β :=
  (fuel.foldl (fun (s : Option N.σ) _ => cutAt room (s.map (stay N))) (cutAt room (some (N.init a)))).bind N.out

end runFor

/-- If N halts on a with the result b within T steps on states of size at most S, then `runFor`
returns b once the fuel has at least T units and the room is at least 7S + 2. (`Carried`: the word
of a state has at most 7 times its size minus 2 symbols; as an optional value it has 4 more.) -/
def RunForIsRight : Prop := ∀ (α β : Type) (N : Stepped α β) [Enc N.σ] [Carried N.σ] (a : α) (T S : ℕ) (b : β) (fuel : U) (room : ℕ),
  N.Runs a T S b → T ≤ fuel.length → 7 * S + 2 ≤ room → runFor N fuel room a = some b

/-- Whether the word of a value has at most as many symbols as a padding string has units is decided
in polynomial time, for every type and every coding. (A machine sees the word and not the type. The
proof visits the nodes of the tree that the word writes, one in each round, for as many rounds as
the padding string has units, and counts their symbols.) -/
def EveryWordIsCompared : Prop := ∀ (α : Type) [Enc α], PolyT fun p : U × α => decide (len p.2 ≤ p.1.length)

/-- `runFor N` is polynomial-time in the fuel, the room in unary and the input, for every step
machine N with polynomial-time steps. Nothing is asked of the runs of N. -/
def RunForPoly : Prop := ∀ (α β : Type) [Enc α] [Enc β] (N : Stepped α β) [IsPolyT N], PolyT fun p : (U × U) × α => runFor N p.1.1 p.1.2.length p.2

/-- `RunForPoly` follows from `EveryWordIsCompared`. -/
def RunForPolyFrom : Prop := EveryWordIsCompared → RunForPoly

/-! ### Tables that are written out -/

/-- The entry that the query (w, z) of Definition 3 names in tables that are written out: row w,
place z read as a number, low bit first; 0 if there is no such place. It is
`PaddedDescent.F.look T (w, ls)` for every list ls of strings whose concatenation is z. -/
def entry (T : Tab) (x : TableQuery) : ℤ := (T.getD x.1 []).getD (ofWord x.2) 0

/-- The step machine that answers a query from the tables, in one step. -/
def lookup : Stepped (Tab × TableQuery) ℤ := Stepped.ofFun fun p => entry p.1 p.2

/-- The largest number of bits of an entry, at least 1. -/
def bitsOfTables (T : Tab) : ℕ := (T.flatten.map fun z => z.natAbs.size).foldr max 1

/-- The value of the clique of Definition 3 with the tables read from T is the sum that this
development calls the value of the instance (λ, T). (It is `Printed.StCliqueValue` for these
tables.) -/
def TablesValue : Prop := ∀ (K lam : ℕ) (T : Tab), 2 ≤ K → 1 ≤ lam → (clique K lam fun w z => entry T (w.val, z)).value = zval K (unary lam, T)

/-- B′ = `bitsOfTables T` is at least 1, and all entries are below 2^{B′} in absolute value; if all
entries are at most 2^B in absolute value (`ClauseBound.Alg.WFe`), it is at most B + 1. -/
def BitsOfTablesFacts : Prop := ∀ (T : Tab), 1 ≤ bitsOfTables T ∧ (∀ x : TableQuery, |entry T x| < 2 ^ bitsOfTables T) ∧
  ∀ (K lam B : ℕ) (lu : U), WFe K lam B (lu, T) → bitsOfTables T ≤ B + 1

section solver

variable (M : QueryMachine TableQuery ℤ (U × U × U) ℤ)

/-- M with its queries answered from tables that are written out; the input is (tables, (ℓ, λ, B)). -/
def onTables : Stepped (Tab × (U × U × U)) ℤ := M.plug lookup

/-- The states of `onTables M`. -/
abbrev OnTablesState : Type := Tab × (M.σ ⊕ (M.σ × ((Tab × TableQuery) ⊕ ℤ)))

/-- ⌈min(a/b, 1)·n⌉ in natural numbers, for b > 0. (For b = 0 it is n, while a fraction with the
denominator 0 is 0 in Lean's real numbers. Under `Levels` and `NumberBetween` the denominator is not
0, which is why the statements on `needOf` have these premises.) -/
def ceilMul (a b n : ℕ) : ℕ := if b ≤ a then n else (a * n + b - 1) / b

/-- The exponent of a padding string that suffices, from ((ℓ, K_ℓ), λ, B), all in unary: ⌈e′K²λ⌉ +
C₀K²·(number of bits of K(λ + B + 1)) + 2, where e′ = min(a/b, 1) for the numerator a and the
denominator b that `num` returns. -/
def needOf (num : U × U → ℕ × ℕ) (C₀ : ℕ) (x : (U × U) × U × U) : ℕ :=
  ceilMul (num x.1).1 (num x.1).2 (x.1.2.length ^ 2 * x.2.1.length) + C₀ * x.1.2.length ^ 2 * Nat.size (x.1.2.length * (x.2.1.length + x.2.2.length + 1)) + 2

/-- **The solver that a machine gives.** The index is (ℓ, K_ℓ), both in unary. `run`: M on (ℓ, λ,
B′), its queries answered from the tables of the instance, for as many steps as the padding string
has units, in room for 7 times the padding string and 14 times the word of the tables; 0 if that
gives no result. The coding
of the states of M, which the cut looks at, is that of the certificate of M: the solver is a
function of M AND of its certificate, and whoever speaks of it needs a binder `[IsPolyQ M]`. -/
def solverOfMachine [QueryMachine.IsPolyQ M] (num : U × U → ℕ × ℕ) (C₀ : ℕ) : Solver (U × U) where
  K i := i.2.length
  run x := (@runFor _ _ (onTables M) (inferInstanceAs (Enc (OnTablesState M))) x.1 (7 * x.1.length + 14 * len x.2.2.2 + 2) (x.2.2.2, (x.2.1.1, x.2.2.1, unary (bitsOfTables x.2.2.2)))).getD 0
  need := needOf num C₀
  needC x := if needOf num C₀ x.2 ≤ x.1.length then some (needOf num C₀ x.2) else none

end solver

/-- From a bound b in unary: the largest ℓ with K_ℓ ≤ b, in unary, and its index (ℓ, K_ℓ); for b <
K₀ it is ℓ = 0 with its index. `kf` is the function of `CliqueLevels.ComputesLevels`, K₀ the number
K at the level 0. Since K_ℓ > ℓ, only ℓ ≤ b are tried; ℓ in unary is the list of the first ℓ units
of b. -/
def pickOf (kf : U × U → Option U) (K₀ : ℕ) (b : U) : U × (U × U) :=
  ((List.range (b.length + 1)).filterMap fun l => (kf (b.take l, b)).map fun k => (b.take l, (b.take l, k))).getLast?.getD ([], ([], unary K₀))

/-- The fraction that `num` returns, cut at 1. -/
def cutFraction (num : U × U → ℕ × ℕ) (p : U × U) : ℕ × ℕ := (min (num p).1 (num p).2, (num p).2)

/-! ### The statements on the solver -/

/-- The number e′_ℓ = `cutNumber K num ℓ` lies in [e_ℓ, 2e_ℓ], is positive and at most 1, and is
itself computed from ℓ and K_ℓ in polynomial time, as the fraction `cutFraction num`. So the clause
«a number in [e′_ℓ, 2e′_ℓ] can be computed» holds for the new sequence too. -/
def CutNumberFacts : Prop := ∀ (K : ℕ → ℕ) (e : ℕ → ℝ) (C₀ : ℕ) (num : U × U → ℕ × ℕ), Levels K e C₀ → NumberBetween K e num →
  PolyT (cutFraction num) ∧ ∀ l : ℕ, 0 < cutNumber K num l ∧ e l ≤ cutNumber K num l ∧ cutNumber K num l ≤ 2 * e l ∧ cutNumber K num l ≤ 1 ∧
    ((cutFraction num (unary l, unary (K l))).1 : ℝ) / ((cutFraction num (unary l, unary (K l))).2 : ℝ) = cutNumber K num l

/-- The form of Theorem D (a) in `MainTheoremForms.ThmVariablesA` takes, in place of the number in
[e_ℓ, 2e_ℓ], a precision function for the numbers e of the sequence of levels
(`MainTheoremForms.Precision`). It carries over from e to every e′ with e_ℓ ≤ e′_ℓ ≤ 2e_ℓ and e′_ℓ ≤
1, with twice the constant: 2/e ≤ 4/e′ ≤ (2/e′)². -/
def PrecisionCarriesOver : Prop := ∀ (e e' : ℕ → ℝ) (slU : U → U) (C : ℕ), MainTheoremForms.Precision e slU C → (∀ l : ℕ, e l ≤ e' l ∧ e' l ≤ 2 * e l ∧ e' l ≤ 1) → MainTheoremForms.Precision e' slU (2 * C)

/-- The exponent, from below: 2^need is at least 4 times the printed bound for e′, C₀ and B + 1. -/
def NeedSuffices : Prop := ∀ (K : ℕ → ℕ) (e : ℕ → ℝ) (C₀ : ℕ) (num : U × U → ℕ × ℕ), Levels K e C₀ → NumberBetween K e num → ∀ l lam B : ℕ, 1 ≤ lam →
  4 * bound (cutNumber K num l) (K l) C₀ lam (B + 1) ≤ (2 : ℝ) ^ needOf num C₀ ((unary l, unary (K l)), unary lam, unary B)

/-- The exponent, from above: need ≤ e′K²λ + (2C₀ + 1)·K²·log(K(λ + B)). -/
def NeedIsSmall : Prop := ∀ (K : ℕ → ℕ) (e : ℕ → ℝ) (C₀ : ℕ) (num : U × U → ℕ × ℕ), Levels K e C₀ → NumberBetween K e num → ∀ l lam B : ℕ, 1 ≤ lam → 1 ≤ B →
  (needOf num C₀ ((unary l, unary (K l)), unary lam, unary B) : ℝ) ≤
    cutNumber K num l * (K l : ℝ) ^ 2 * lam + ((2 * C₀ + 1 : ℕ) : ℝ) * (K l : ℝ) ^ 2 * Real.logb 2 (K l * (lam + B))

/-- The solver is polynomial-time, for every machine with polynomial-time steps and every
polynomial-time `num`. Nothing is asked of what M computes. -/
def SolverOfMachinePoly : Prop := ∀ (M : QueryMachine TableQuery ℤ (U × U × U) ℤ) [QueryMachine.IsPolyQ M] (num : U × U → ℕ × ℕ) (C₀ : ℕ), PolyT num → (solverOfMachine M num C₀).Poly

/-- `SolverOfMachinePoly` follows from `RunForPoly`. The certificate of `onTables M` to which
`RunForPoly` is applied has to be `QueryMachine.plug_isPolyT M lookup` with `IsPolyT.ofFun` for
`lookup`: its coding of the states is by definition the one in `solverOfMachine`. (`StPolyPlug` says
only that some certificate exists, and
so does not fix the coding.) -/
def SolverOfMachinePolyFrom : Prop := RunForPoly → SolverOfMachinePoly

/-- The program that picks the level: it is polynomial-time, returns an index of the sequence, the
largest one whose K is within the bound. -/
def PickOfFacts : Prop := ∀ (K : ℕ → ℕ) (e : ℕ → ℝ) (C₀ : ℕ) (kf : U × U → Option U), Levels K e C₀ → ComputesLevels K kf →
  PolyT (pickOf kf (K 0)) ∧ ∀ b : U, (pickOf kf (K 0) b).2 = (unary (pickOf kf (K 0) b).1.length, unary (K (pickOf kf (K 0) b).1.length)) ∧
    (K 0 ≤ b.length → K (pickOf kf (K 0) b).1.length ≤ b.length) ∧ b.length < K ((pickOf kf (K 0) b).1.length + 1)

/-- **The main statement.** Let M be a machine with query access and polynomial-time steps (with any
certificate of that) which, given ℓ, λ, B and query access to tables with |W_w| < 2^B, outputs the
value of the (K_ℓ, λ)-clique within 2^{e_ℓK_ℓ²λ}·(K_ℓ(λ+B))^{C₀K_ℓ²} operations on states of at most
that size; let K and e
be as in the hypothesis of Theorem D (a), K_ℓ computed by `kf` and a number in [e_ℓ, 2e_ℓ] by `num`.
Then the named solver `solverOfMachine M num C₀` is polynomial-time and has a sequence Q of levels
for the numbers e′_ℓ = `cutNumber K num ℓ` with the constant 2C₀ + 1, whose ℓ-th index is (ℓ, K_ℓ),
so that K at this
index is K_ℓ, and whose level is picked by the named program `pickOf kf (K 0)`. (The fields of Q
say: K_ℓ ≥ 2, K_ℓ < K_(ℓ+1) ≤ K_ℓ^(2C₀+1), (log K_ℓ)^(−2C₀−1) ≤ e′_ℓ ≤ 1, the solver is right when
the padding string has 2^need units, and need ≤ e′_ℓK_ℓ²λ + (2C₀+1)K_ℓ²·log(K_ℓ(λ+B)).) -/
def SolverOfMachineLevels : Prop :=
  ∀ (M : QueryMachine TableQuery ℤ (U × U × U) ℤ) [QueryMachine.IsPolyQ M] (K : ℕ → ℕ) (e : ℕ → ℝ) (C₀ : ℕ) (kf : U × U → Option U) (num : U × U → ℕ × ℕ),
    Solves M K e C₀ → Levels K e C₀ → ComputesLevels K kf → NumberBetween K e num →
      (solverOfMachine M num C₀).Poly ∧
      ∃ Q : (solverOfMachine M num C₀).Seq (cutNumber K num) (2 * C₀ + 1),
        (∀ l : ℕ, Q.idx l = (unary l, unary (K l))) ∧ (∀ l : ℕ, (solverOfMachine M num C₀).K (Q.idx l) = K l) ∧ Q.pick = pickOf kf (K 0)

/-- The main statement follows from these: `StPlug` (queries answered by a step machine), and the
statements of this file on the run, the tables, the number e′, the exponent, polynomial time and the
program that picks the level. -/
def SolverOfMachineLevelsFrom : Prop :=
  StPlug → RunForIsRight → TablesValue → BitsOfTablesFacts → CutNumberFacts → NeedSuffices → NeedIsSmall → SolverOfMachinePoly → PickOfFacts → SolverOfMachineLevels

end QueryMachines.Bridge
