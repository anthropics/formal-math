/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import SparsificationLemma.Geo.Defs
public import ClauseBoundStatement

/-! # A machine that prints the outputs of the sparsification: definitions and statements

`SparsABCD` below states sparsification with parts (a) to (d), a form that the paper does not state;
its part (d) is the running time, and `Prints` is that part in the parameters of the machine. Lemma
4 says «one can compute, in time 2^(εn) times a polynomial in n, …».
It is ONE machine for all widths k and all precisions.
On the side of the input, «k-CNF» is `SatK.IsKCNF` (at most k literals in every clause, no clause
written twice) without an empty clause; on the side of the output it is `SparsificationLemma.IsKCNF`
together with `List.Nodup`.
**The input** is 1^s 0 1^k 0 followed by the code of the formula (`encIn`): the precision s and the
width k in unary. The machine runs the sparsification procedure of Appendix C (Calabro's algorithm
as changed there), with the thresholds `thetaU τ` for τ = 2^(4s+17), so 2^(−s) has the role of ε.
**The output** is the list of the formulas, written by the code `code`.
**The time** is at most C·(length of the input + 2^k)^C·2^(C·⌊n/2^s⌋) for one constant C (`Prints`).
In the machine built here, with the tools of this development, every round of the walk through the
tree rewrites the whole state, which holds the formulas found so far. So the
exponent of 2^(n/2^s) is C and not 1. To get time 2^(εn) one gives the machine a precision s with C
≤ ε·2^s. The theorems of this development that turn a function into a machine give C only after the
machine is fixed, and only as «there is a C»; so we do not build a machine that computes such an s
from ε, and the input has s and not ε. This is a limit of the tools used here, not of the
mathematics.
`SparsABCD` is the form with parts (a) to (d), with s = `precE C k ε`; the price is an absolute
constant in part (c): at most (Ck/ε)^(16k) occurrences of a variable.
`LemSparsification` is the case k = 3 in the words of the paper.
This file has definitions only. The statements are propositions; they are proved in other files. -/

@[expose] public section

namespace SparsificationLemma.Mach

open Finset Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat CountKSatRate UniformInK PaddedDescent SparsificationLemma.Geo Turing

/-! ### Input and output as words -/

/-- The input word: 1^s 0, then 1^k 0 and the code of φ as in `SatM.enc`. -/
def encIn (s k : ℕ) {n : ℕ} (φ : Sat3.CNF n) : List Bool := List.replicate s true ++ false :: SatM.enc k φ

/-- A number in unary: 1^v 0. -/
def codeNat (v : ℕ) : List Bool := List.replicate v true ++ [false]

/-- A literal: one bit, true for xᵢ and false for ¬xᵢ, then i in unary. -/
def codeLit (l : PLit) : List Bool := l.2 :: codeNat l.1

/-- A clause: 1 before every literal, 0 at the end. -/
def codeCl (C : PCl) : List Bool := C.flatMap (fun l => true :: codeLit l) ++ [false]

/-- A formula: 1 before every clause, 0 at the end. -/
def codeFml (ψ : PFml) : List Bool := ψ.flatMap (fun C => true :: codeCl C) ++ [false]

/-- A list of formulas: 1 before every formula, 0 at the end. -/
def code (L : List PFml) : List Bool := L.flatMap (fun ψ => true :: codeFml ψ) ++ [false]

/-! ### The machine -/

/-- **Part (d), in the parameters of the machine.** One machine and one constant C: for all k ≥ 1,
all s ≥ `s0U k`, all n and every k-CNF φ on n variables without an empty clause, the machine,
started on 1^s 0 1^k 0 code(φ), halts with
the code of the list of outputs for τ = 2^(4s+17) within C·(length of the input +
2^k)^C·2^(C·⌊n/2^s⌋) steps. -/
def Prints : Prop := ∃ (M : TM2ComputableAux Bool Bool) (C : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧
  ∀ (k n s : ℕ) (φ : Sat3.CNF n), 1 ≤ k → s0U k ≤ s → SatK.IsKCNF k φ → [] ∉ φ →
    Nonempty (TM2OutputsInTime M.tm ((encIn s k φ).map M.inputAlphabet.invFun)
      (some ((code (outTau k n (tauOf s) (Decode.toN φ))).map M.outputAlphabet.invFun))
      (C * ((encIn s k φ).length + 2 ^ k) ^ C * 2 ^ (C * (n / 2 ^ s))))

/-- The precision for width k and ε, given the constant C of the machine: the least s ≥ `s0U k` with
C/ε ≤ 2^s. -/
def precE (C k : ℕ) (ε : ℚ) : ℕ := max (s0U k) (Nat.clog 2 ⌈(C : ℚ) / ε⌉₊)

/-- **Sparsification, parts (a) to (d), on a Turing machine.** One machine and one constant C: for
all k ≥ 1, n, rational ε ∈ (0,1] and k-CNF φ on n variables with no empty clause, let s =
`precE C k ε`.
The machine, started on 1^s 0 1^k 0 code(φ), halts with the code of a list Φ of k-CNFs on the same
variables, none with a clause written twice, such that (a) Φ has at most 2^(εn) members; (b) every
assignment that satisfies φ satisfies
exactly one of them, and every other assignment none; (c) in each of them every variable occurs in
at most (Ck/ε)^(16k) clauses; (d) the number of steps is at most C·(length of the input +
2^k)^C·2^(εn).
This form is not in the paper. The machine gets not ε but the precision s, which depends on C; as
only «a C exists» is stated, it does not say how to run it for a given ε (`Prints` is the form with
s
as a free input). In (c) the bound is (Ck/ε)^(16k), where Step 5 of Appendix D has 2·(8k/ε)^(3k) +
2; in (d) it is the product above, where Step 5 has time 2^(εn)·n^(O(k)). -/
def SparsABCD : Prop := ∃ (M : TM2ComputableAux Bool Bool) (C : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧
  ∀ (k n : ℕ) (ε : ℚ) (φ : Sat3.CNF n), 1 ≤ k → 0 < ε → ε ≤ 1 → SatK.IsKCNF k φ → [] ∉ φ →
    ∃ (Φ : List PFml) (T : ℕ),
      Nonempty (TM2OutputsInTime M.tm ((encIn (precE C k ε) k φ).map M.inputAlphabet.invFun) (some ((code Φ).map M.outputAlphabet.invFun)) T) ∧
      (∀ Ψ ∈ Φ, IsKCNF k n Ψ ∧ Ψ.Nodup) ∧
      (Φ.length : ℝ) ≤ (2 : ℝ) ^ ((ε : ℝ) * (n : ℝ)) ∧
      (∀ b, ExactlyOne b (Decode.toN φ) Φ) ∧
      (∀ Ψ ∈ Φ, ∀ v, (occN Ψ v : ℝ) ≤ ((C : ℝ) * (k : ℝ) / (ε : ℝ)) ^ (16 * k)) ∧
      (T : ℝ) ≤ (C : ℝ) * (((encIn (precE C k ε) k φ).length : ℝ) + 2 ^ k) ^ C * (2 : ℝ) ^ ((ε : ℝ) * (n : ℝ))

/-- **Lemma 4 (Sparsification Lemma, for clauses of at most 3 literals).** For every ε > 0 there is
a constant M(ε) ≥ 1 such that for every 3-CNF φ on n variables one can compute, in time 2^(εn) times
a polynomial in n, at most 2^(εn) 3-CNFs
on the same variables, each with at most M(ε)·n clauses, such that φ is satisfiable if and only if
at least one of them is.
«One can compute»: there is one machine for all ε; for a given ε it is started on the constant word
1^s 0 1^3 0, s = s(ε), followed by the code of φ. A 3-CNF has nonempty clauses of at most 3
literals, and no clause is written twice (in an output, a clause may list a literal twice, and two
clauses may list the same literals in different orders; neither makes the statement weaker). The
polynomial c·(n+1)^c may depend on ε. -/
def LemSparsification : Prop := ∃ M : TM2ComputableAux Bool Bool, (∀ i, Finite (M.tm.Γ i)) ∧
  ∀ ε : ℝ, 0 < ε → ∃ Mε s c : ℕ, 1 ≤ Mε ∧
    ∀ (n : ℕ) (φ : Sat3.CNF n), Sat3.Is3CNF φ → [] ∉ φ →
      ∃ (Φ : List PFml) (T : ℕ),
        Nonempty (TM2OutputsInTime M.tm ((encIn s 3 φ).map M.inputAlphabet.invFun) (some ((code Φ).map M.outputAlphabet.invFun)) T) ∧
        (T : ℝ) ≤ (2 : ℝ) ^ (ε * (n : ℝ)) * ((c : ℝ) * ((n : ℝ) + 1) ^ c) ∧
        (Φ.length : ℝ) ≤ (2 : ℝ) ^ (ε * (n : ℝ)) ∧
        (∀ Ψ ∈ Φ, IsKCNF 3 n Ψ ∧ Ψ.Nodup ∧ Ψ.length ≤ Mε * n) ∧
        (Sat3.Satisfiable φ ↔ ∃ Ψ ∈ Φ, ∃ b, Sat b Ψ)

end SparsificationLemma.Mach
