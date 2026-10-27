/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import CircuitLowerBoundStatement
public import StepMachines.Prog.Chunks

/-! # The circuit lower bound for E^NP (Section 7): the objects of the proof (definitions only)

The proof follows R. Williams's sketch (Improving exhaustive search implies superpolynomial lower
bounds, Theorem 6.1). A run of a machine is written as a formula whose clauses are the shifts of a
finite TABLE of clauses; the
formulas `Phi m` are put together so that a fast nondeterministic algorithm for «is `Phi m`
satisfiable?» contradicts itself; the language `L0` holds the bits of a fixed satisfying assignment
of `Phi m`. -/

@[expose] public section

namespace CircuitLowerBound

open ENP Groundwork

/-! ### Tables: a formula as the shifts of finitely many clauses

A variable of the formula is a triple (kind, t, q): a kind of statement, a time t, a position q. -/

/-- A literal of a table: (kind, how t is formed, how q is formed, a number added to q, sign). -/
abbrev TLit : Type := ℕ × ℕ × ℕ × ℕ × Bool

/-- A clause of a table: three literals (a literal may be repeated). -/
abbrev TCl : Type := TLit × TLit × TLit

/-- A table with its two numbers: (the number of bits for the kind, the number of bits by which
positions are longer than times, the clauses). -/
abbrev MCode : Type := ℕ × ℕ × List TCl

def kb (e : MCode) : ℕ := e.1
def lam (e : MCode) : ℕ := e.2.1
def tab (e : MCode) : List TCl := e.2.2

/-- The number of bits of a time, if a variable is to be written with L bits: times are 0 … 2^bt. -/
def bt (e : MCode) (L : ℕ) : ℕ := (L - kb e - lam e - 2) / 2

/-- The number of bits of a position in the number of a clause. -/
def bq (e : MCode) (L : ℕ) : ℕ := bt e L + lam e

/-- The number of bits for the place of a clause in the table. -/
def rb (e : MCode) : ℕ := Nat.size (tab e).length

/-- The number of bits of the number of a clause. -/
def nb (e : MCode) (L : ℕ) : ℕ := rb e + bt e L + bq e L

/-- The time of a literal in the shift by t: 0, t, t + 1 or the last time 2^b, for the modes 0, 1,
2, 3. -/
def tval (b t mode : ℕ) : ℕ := if mode % 4 = 0 then 0 else if mode % 4 = 1 then t else if mode % 4 = 2 then t + 1 else 2 ^ b

/-- The position of a literal in the shift by q, before the number of the literal is added: 0, q or
the parameter P, for the modes 0, 1 and 2, 3. -/
def qval (P q mode : ℕ) : ℕ := if mode % 4 = 0 then 0 else if mode % 4 = 1 then q else P

/-- The number of the variable (kind, time, position): the position in the lowest bq + 1 bits, then
the time in bt + 1 bits, then the kind in kb bits. -/
def vidx (e : MCode) (L P t q : ℕ) (l : TLit) : ℕ :=
  ((l.1 % 2 ^ kb e) * 2 ^ (bt e L + 1) + tval (bt e L) t l.2.1) * 2 ^ (bq e L + 1) + (qval P q l.2.2.1 + l.2.2.2.1) % 2 ^ (bq e L + 1)

/-- A literal of the formula. -/
def litAt (e : MCode) (L P t q : ℕ) (l : TLit) : ℕ × Bool := (vidx e L P t q l, l.2.2.2.2)

/-- The clause that stands for the places beyond the end of the table: «the variable 0 is false». -/
def zeroCl : TCl := ((0, 0, 0, 0, false), (0, 0, 0, 0, false), (0, 0, 0, 0, false))

/-- Clause number j of the formula: j is (place in the table, t, q), with q in the lowest bq bits
and t in the next bt bits. -/
def clauseAt (e : MCode) (L P j : ℕ) : List (ℕ × Bool) :=
  [litAt e L P (j / 2 ^ bq e L % 2 ^ bt e L) (j % 2 ^ bq e L) ((tab e).getD (j / 2 ^ (bt e L + bq e L)) zeroCl).1,
   litAt e L P (j / 2 ^ bq e L % 2 ^ bt e L) (j % 2 ^ bq e L) ((tab e).getD (j / 2 ^ (bt e L + bq e L)) zeroCl).2.1,
   litAt e L P (j / 2 ^ bq e L % 2 ^ bt e L) (j % 2 ^ bq e L) ((tab e).getD (j / 2 ^ (bt e L + bq e L)) zeroCl).2.2]

/-- The formula of the table e, for variables of L bits and the parameter P. -/
def tabF (e : MCode) (L P : ℕ) : Cnf := (List.range (2 ^ nb e L)).map (clauseAt e L P)

/-- There is room: the variables fit into L bits, there is at least one bit of time, and the
parameter is small against the number of times. -/
def Fits (e : MCode) (L P : ℕ) : Prop := kb e + lam e + 4 ≤ L ∧ P + 2 ≤ 2 ^ bt e L

instance (e : MCode) (L P : ℕ) : Decidable (Fits e L P) := by unfold Fits; infer_instance

/-! ### Tables from numbers -/

/-- The number of ones at the start of a word. -/
def ones (x : List Bool) : ℕ := (x.takeWhile id).length

/-- The word after its first ones and the zero that ends them. -/
def rest (x : List Bool) : List Bool := (x.dropWhile id).tail

/-- The i-th number of W bits in a word. -/
def fld (W : ℕ) (w : List Bool) (i : ℕ) : ℕ := ofWord (block W i w)

/-- Five numbers from place i on, as a literal. -/
def litOf (W : ℕ) (w : List Bool) (i : ℕ) : TLit := (fld W w i, fld W w (i + 1), fld W w (i + 2), fld W w (i + 3), decide (fld W w (i + 4) ≠ 0))

/-- The word 1^W 0, then numbers of W bits: kb, lam, and 15 numbers for each clause. What is left
over at the end is not read. -/
def codeOfWord (u : List Bool) : MCode :=
  (fld (ones u) (rest u) 0, fld (ones u) (rest u) 1,
    (List.range (((rest u).length - 2 * ones u) / (15 * ones u))).map fun r =>
      (litOf (ones u) (rest u) (2 + 15 * r), litOf (ones u) (rest u) (2 + 15 * r + 5), litOf (ones u) (rest u) (2 + 15 * r + 10)))

/-- The table with the number a: the binary digits of a, lowest first, without their first ones and
the zero after these. So every table has infinitely many numbers. -/
def codeOf (a : ℕ) : MCode := codeOfWord (rest (Nat.bits a))

/-! ### The chains: m = 2^a·(2s + 1) is place s of chain a -/

/-- The number of zeros at the low end of m. -/
def nu (m : ℕ) : ℕ := ((Nat.bits m).takeWhile fun b => !b).length

/-- The place of m in its chain. -/
def pos (m : ℕ) : ℕ := m / 2 ^ nu m / 2

/-- The next number of the chain. -/
def next (m : ℕ) : ℕ := m + 2 ^ (nu m + 1)

/-- The last place of chain a. -/
def top (a : ℕ) : ℕ := 2 ^ 2 ^ 2 ^ a

open Classical in
/-- The formulas. Before the last place of chain a: the formula of table a with the parameter
`next m`. At the last place: a formula that is satisfiable if and only if the formula of table a for
the first number 2^a of the chain is not.
Everywhere else, and where there is no room: the empty formula. -/
noncomputable def Phi (m : ℕ) : Cnf :=
  if pos m < top (nu m) then (if Fits (codeOf (nu m)) m (next m) then tabF (codeOf (nu m)) m (next m) else [])
  else if pos m = top (nu m) then (if Fits (codeOf (nu m)) (2 ^ nu m) (2 ^ nu m) ∧ Sat (tabF (codeOf (nu m)) (2 ^ nu m) (2 ^ nu m)) then [[]] else [])
  else []

/-! ### The language -/

/-- «The variables 0, 1, … have the values w.» -/
def units (w : List Bool) : Cnf := (List.range w.length).map fun i => [(i, w.getD i false)]

open Classical in
/-- The values of the first j variables in the search that sets each variable to 0 if that can still
be continued to a satisfying assignment, and to 1 if not. -/
noncomputable def greedy (φ : Cnf) : ℕ → List Bool
  | 0 => []
  | j + 1 => greedy φ j ++ [!decide (Sat (φ ++ units (greedy φ j ++ [false])))]

/-- The language: a word x of length m is the number i of a variable, lowest bit first; x is in the
language if the search for `Phi m` gives the variable i the value 1. -/
def L0 : Lang := fun x => (greedy (Phi x.length) (ofWord x + 1)).getD (ofWord x) false = true

/-! ### Machines -/

/-- The number P in unary: 1^P 0. -/
def unary (P : ℕ) : List Bool := List.replicate P true ++ [false]

/-- `N`, started on the word x, halts within T steps with the word y as output. -/
def Outputs (N : Turing.TM2ComputableAux Bool Bool) (x y : List Bool) (T : ℕ) : Prop :=
  Nonempty (Turing.TM2OutputsInTime N.tm (x.map N.inputAlphabet.invFun) (some (y.map N.outputAlphabet.invFun)) T)

/-- For some word y, `N` started on 1^P 0 y halts within T steps with the output 1. -/
def Acc (N : Turing.TM2ComputableAux Bool Bool) (P T : ℕ) : Prop := ∃ y : List Bool, Outputs N (unary P ++ y) [true] T

end CircuitLowerBound
