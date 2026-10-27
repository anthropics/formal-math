/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib

/-!
# The two main results of the accompanying paper, as Lean statements

This file has definitions only: no theorem, no proof. It imports Mathlib and nothing else, so it
can be read, and compiled, on its own. Two of its definitions are the claims:

* `ETHIsFalse`: the Exponential Time Hypothesis, `ETH`, is false.
* `MainTheorem`: one machine counts the satisfying assignments of every k-CNF (no clause written
  twice) with k ≥ 1 and m ≥ 2 clauses on n ≥ 4 variables x₀ … x_{n−1} (the paper's x₁ … xₙ), each of
  which occurs, within 2^{C·min{km/√(log m), k²·n·log log n/√(log n)}} steps (log is log₂), for one
  constant C that does not depend on k.

A proof is a separate file that imports this one and states theorems whose types are exactly these
two propositions.

**The machine.** An algorithm is a machine of Mathlib's kind `Turing.FinTM2`: a deterministic
machine with finitely many stacks in place of tapes. Its program is a finite set of labelled
blocks; it has finitely many internal states; on a stack it can push a symbol, pop the top symbol,
or read it. `Turing.TM2ComputableAux Bool Bool` adds a bijection from the alphabet of the input
stack to Bool = {false, true}, and one from the alphabet of the output stack; bits are written
through them. Time is the number of steps. One step runs the current block until it jumps to a
block (possibly itself) or halts; for a fixed machine this is a bounded number of stack operations.
`Turing.TM2OutputsInTime M.tm x (some y) t` says that the machine, started with x on its input
stack and all other stacks empty, halts after at most t steps with y on its output stack, all other
stacks empty, and its internal state back at its initial value. Of the stack alphabets, Mathlib
requires only that of the input stack to be finite; the condition `∀ i, Finite (M.tm.Γ i)`, used
below, requires every stack alphabet to be finite, as for a textbook machine.

**Why this machine suffices.** A random-access machine simulates such a machine with a bounded
number of operations per step, and it can rewrite a formula on the paper's variables x₁ … xₙ into
the input words used here (with x₀ … x_{n−1}) in time polynomial in n and the length of the
formula. In the paper a formula is a set of clauses, so no clause is repeated in it. For ETH: a
3-CNF on n variables then has length polynomial in n. So, for δ > 0, a machine here that runs in
time O(2^{δn}) gives an algorithm in the usual sense that runs in time O(2^{δn}). Hence s₃ (defined
below) for algorithms in the usual sense is at most s₃ as defined here, and s₃ = 0 here gives
s₃ = 0 there.
For the Main Theorem: every variable occurs and no clause is repeated, so n ≤ km and m ≤ (2n+1)^k;
then the formula has O(km·log n) bits, and every polynomial in that length is at most
2^{O(min{km/√(log m), k²·n·log log n/√(log n)})}. So a machine as in `MainTheorem` gives an
algorithm in the usual sense within the same bound, with another constant. The simulation and the
rewriting are standard facts; they are not part of the Lean statements or proofs.
-/

namespace MainResults

open Turing
open scoped NNReal ENNReal

/-! ### Formulas -/

/-- A literal on x₀ … x_{n−1} is a pair (i, b): it is xᵢ if b is true and ¬xᵢ if b is false. -/
abbrev Lit (n : ℕ) : Type := Fin n × Bool

/-- A clause is the OR of a list of literals; a formula is the AND of a list of clauses. -/
abbrev CNF (n : ℕ) : Type := List (List (Lit n))

/-- An instance of k-SAT: every clause has at most k literals, and no clause is written twice. A
clause is a list: it may be empty (then it is false), may repeat a literal or hold both x and ¬x,
and the same literals in another order make a different clause. So a k-CNF on n variables has at
most (2n+1)^k clauses. (Without this, no time bound in n alone could hold: before halting, a machine
must pop nearly all of its input, a bounded number of symbols per step.) -/
def IsKCNF (k : ℕ) {n : ℕ} (φ : CNF n) : Prop := (∀ C ∈ φ, C.length ≤ k) ∧ φ.Nodup

/-- The number written for one position of a clause: 0 for an empty position, 2i+1 for ¬xᵢ,
2i+2 for xᵢ. -/
def slot {n : ℕ} : Option (Lit n) → ℕ
  | none => 0
  | some l => 2 * l.1.val + 1 + l.2.toNat

/-! ### The Exponential Time Hypothesis -/

/-- Some assignment makes a literal of every clause true. -/
def Satisfiable {n : ℕ} (φ : CNF n) : Prop := ∃ a : Fin n → Bool, ∀ C ∈ φ, ∃ l ∈ C, a l.1 = l.2

/-- The input word for k-SAT with k fixed, n in unary: 1ⁿ 0, then for each clause k positions of
`Nat.log2 (2 * n) + 1` bits each (⌊log₂ (2n)⌋ + 1 bits; 1 bit when n = 0), each holding a `slot`
number, lowest bit first. A clause with fewer than k literals is padded with empty positions (0). -/
def encClauses (k : ℕ) {n : ℕ} (φ : CNF n) : List Bool :=
  List.replicate n true ++ false :: φ.flatMap fun C => (List.range k).flatMap fun j =>
    (List.range (Nat.log2 (2 * n) + 1)).map (slot C[j]?).testBit

/-- `M` decides k-SAT within t(n) steps: started on `encClauses k φ`, for any n and any k-CNF φ on
x₀ … x_{n−1} with any number of clauses, it halts after at most t(n) steps with one bit as output,
which is 1 if and only if φ is satisfiable. Here k is fixed and is not a part of the input. -/
def DecidesKSat (k : ℕ) (M : TM2ComputableAux Bool Bool) (t : ℕ → ℕ) : Prop :=
  ∀ (n : ℕ) (φ : CNF n), IsKCNF k φ → ∃ b : Bool, (b = true ↔ Satisfiable φ) ∧
    Nonempty (TM2OutputsInTime M.tm ((encClauses k φ).map M.inputAlphabet.invFun)
      (some ([b].map M.outputAlphabet.invFun)) (t n))

/-- “Some deterministic algorithm decides k-SAT on n variables in time O(2^{δn})”: one machine,
finite alphabets, one constant c; the machine decides k-SAT within c·2^{δn} steps, rounded down,
for every n. The machine and c may depend on k and on δ. -/
def InTime (k : ℕ) (δ : ℝ≥0) : Prop :=
  ∃ (M : TM2ComputableAux Bool Bool) (c : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧
    DecidesKSat k M fun n => ⌊(c : ℝ) * (2 : ℝ) ^ ((δ : ℝ) * n)⌋₊

/-- s_k: the infimum of all δ ≥ 0 such that some deterministic algorithm decides k-SAT on n
variables in time O(2^{δn}). It is a number in [0, ∞], and ∞ if there is no such δ. Only s₃ is
used below. -/
noncomputable def s (k : ℕ) : ℝ≥0∞ := ⨅ (δ : ℝ≥0) (_ : InTime k δ), (δ : ℝ≥0∞)

/-- **The Exponential Time Hypothesis** (Impagliazzo and Paturi, “On the complexity of k-SAT”,
J. Comput. Syst. Sci. 62 (2001)), in the form s₃ > 0: for some δ > 0 no deterministic algorithm
decides 3-SAT on n variables in time O(2^{δn}). The paper that this file accompanies defines ETH as
“s_k > 0 for all k ≥ 3” and notes that this is the same as s₃ > 0. The form here follows from that
one: take k = 3, then use that s₃ for algorithms in the usual sense is at most s₃ as defined here
(see the head comment); so its negation refutes both. (A remark outside Lean: a deterministic
algorithm is a randomized algorithm that uses no random bits, so allowing randomness could only make
s₃ smaller, and refuting this deterministic form also refutes the randomized form.) -/
def ETH : Prop := 0 < s 3

/-- **The Exponential Time Hypothesis is false**: not s₃ > 0. As s₃ ≥ 0, this says s₃ = 0. It is
equivalent to: for every δ > 0 some deterministic algorithm decides 3-SAT on n variables in time
O(2^{δn}) (`InTime 3 δ`, which gets weaker as δ grows). -/
def ETHIsFalse : Prop := ¬ ETH

/-! ### The Main Theorem -/

/-- Every one of the variables x₀ … x_{n−1} occurs in φ, positively or negatively. -/
def AllOccur {n : ℕ} (φ : CNF n) : Prop := ∀ i : Fin n, ∃ C ∈ φ, ∃ l ∈ C, l.1 = i

/-- The number of satisfying assignments of φ, among all 2ⁿ assignments to x₀ … x_{n−1}. -/
def numSat {n : ℕ} (φ : CNF n) : ℕ :=
  (Finset.univ.filter fun a : Fin n → Bool => ∀ C ∈ φ, ∃ l ∈ C, a l.1 = l.2).card

/-- The lowest n + 1 bits of the number c, lowest bit first. (A count of assignments of n variables
is at most 2ⁿ, so nothing of it is lost.) -/
def binary (n c : ℕ) : List Bool := (List.range (n + 1)).map c.testBit

/-- The input word of the Main Theorem, with k as a part of it: 1ᵏ 0, then `encClauses k φ`. -/
def encInput (k : ℕ) {n : ℕ} (φ : CNF n) : List Bool :=
  List.replicate k true ++ false :: encClauses k φ

/-- The paper's log: the logarithm to base 2, not rounded, and of x itself, not of x + 1. In the
comments of this file, log always means this. Under the conditions of `MainTheorem` (m ≥ 2, n ≥ 4)
it is applied only to numbers that are at least 2. -/
noncomputable def lg (x : ℝ) : ℝ := Real.logb 2 x

/-- The exponent in the number m of clauses: k·m/√(log m). -/
noncomputable def expM (k m : ℕ) : ℝ := (k : ℝ) * m / Real.sqrt (lg m)

/-- The exponent in the number n of variables: k²·n·log log n/√(log n). -/
noncomputable def expN (k n : ℕ) : ℝ := (k : ℝ) ^ 2 * n * lg (lg n) / Real.sqrt (lg n)

/-- The time of the Main Theorem, rounded down: 2^{C·min{km/√(log m), k²·n·log log n/√(log n)}}. -/
noncomputable def timeMin (C k m n : ℕ) : ℕ :=
  ⌊(2 : ℝ) ^ ((C : ℝ) * min (expM k m) (expN k n))⌋₊

/-- `M`, started on `encInput k φ`, halts after at most t steps with output the number of
satisfying assignments of φ, written in n + 1 bits, lowest bit first (`binary`). -/
def CountsWithin (M : TM2ComputableAux Bool Bool) (k : ℕ) {n : ℕ} (φ : CNF n) (t : ℕ) : Prop :=
  Nonempty (TM2OutputsInTime M.tm ((encInput k φ).map M.inputAlphabet.invFun)
    (some ((binary n (numSat φ)).map M.outputAlphabet.invFun)) t)

/-- **The Main Theorem.** There is one machine with finite alphabets, and one constant C, both
chosen before k and the formula, such that: for every k ≥ 1, every n ≥ 4, and every formula φ on the
variables x₀ … x_{n−1}, each of which occurs in it, with `IsKCNF k φ` (clauses of at most k
literals, none written twice) and m ≥ 2 clauses, the machine, started on `encInput k φ`, outputs
the number of satisfying assignments of φ within
2^{C·min{km/√(log m), k²·n·log log n/√(log n)}} steps (rounded down). Where no thresholds are
stated, an O(·) as in the bound 2^{O(…)} speaks only of all large enough m and n; here one C
serves every m ≥ 2 and n ≥ 4, which implies that reading. These are the least values with
log m ≥ 1 and log log n ≥ 1. At n = 2 the factor log log n is 0, so the bound would be one step.
At m = 1 the divisor √(log m) is 0, so km/√(log m) is undefined (Lean's convention x/0 = 0 would
make the bound one step there too). And k ≥ 1 because the paper defines k-CNFs only for k ≥ 1; with
k = 0 every clause is empty, so there is at most one clause and no variable occurs.
Nothing is said about any other input word, including words for k = 0, for formulas with a
repeated clause or with a variable that does not occur, and for formulas with fewer than two
clauses or fewer than four variables. -/
def MainTheorem : Prop :=
  ∃ (M : TM2ComputableAux Bool Bool) (C : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧
    ∀ (k n : ℕ) (φ : CNF n), 1 ≤ k → IsKCNF k φ → 2 ≤ φ.length → 4 ≤ n → AllOccur φ →
      CountsWithin M k φ (timeMin C k φ.length n)

end MainResults
