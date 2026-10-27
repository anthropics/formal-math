/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import CircuitLowerBound.Interfaces
public import ToTuring.PolyT

/-! # The circuit lower bound for E^NP (Section 7): the interface statements on circuits, formulas and polynomial-time functions

As in `Interfaces.lean`: definitions `St… : Prop` only. `PolyT f`
(proof/machines/ToTuring/PolyT.lean) says that f is computed in polynomial time on a multi-stack
machine. A number that bounds the length of a list comes in unary, as a `List Unit`. -/

@[expose] public section

namespace CircuitLowerBound

open ENP Groundwork Turing

/-! ### Circuits as data -/

/-- A gate as data: its values at 00, 01, 10, 11, and the numbers of the two wires that it reads. -/
abbrev GateD : Type := (Bool × Bool × Bool × Bool) × ℕ × ℕ

def GateD.toGate (g : GateD) : Gate :=
  ⟨fun x y => if x then (if y then g.1.2.2.2 else g.1.2.2.1) else (if y then g.1.2.1 else g.1.1), g.2.1, g.2.2⟩

/-- The circuit of a list of gates given as data. -/
def toC (C : List GateD) : Circuit := C.map GateD.toGate

/-- On n input bits, gate t reads inputs and earlier gates only. -/
def WF (n : ℕ) (C : List GateD) : Prop := ∀ (t : ℕ) (h : t < C.length), C[t].2.1 < n + t ∧ C[t].2.2 < n + t

/-- Every circuit on m ≥ 1 input bits can be written as data in which every gate reads inputs and
earlier gates only, with the same number of gates. -/
def StNorm : Prop := ∀ (m : ℕ) (C : Circuit), 1 ≤ m → ∃ C' : List GateD, WF m C' ∧ C'.length = C.length ∧ ∀ x : List Bool, x.length = m → eval (toC C') x = eval C x

/-- The circuit that computes clause number j of the formula of a table from the bits of j. It has
nb inputs and 3·(L+1) output wires: for each of the three literals the L bits of the variable,
lowest first, and the sign.
Its size is at most a₀·(L+1) + g(e): the number a₀ does NOT depend on the table. -/
def StClauseCirc : Prop := ∃ (a₀ : ℕ) (g : MCode → ℕ) (B : MCode × List Unit × ℕ → List GateD × List ℕ), PolyT B ∧
  ∀ (e : MCode) (L P : ℕ), Fits e L P →
    WF (nb e L) (B (e, List.replicate L (), P)).1 ∧ (B (e, List.replicate L (), P)).1.length ≤ a₀ * (L + 1) + g e ∧
    (B (e, List.replicate L (), P)).2.length = 3 * (L + 1) ∧ (∀ w ∈ (B (e, List.replicate L (), P)).2, w < nb e L + (B (e, List.replicate L (), P)).1.length) ∧
    ∀ j < 2 ^ nb e L, ∀ i < 3,
      (ofWord ((((B (e, List.replicate L (), P)).2.drop (i * (L + 1))).take L).map fun w => (wires (toWord (nb e L) j) (toC (B (e, List.replicate L (), P)).1)).getD w false),
        (wires (toWord (nb e L) j) (toC (B (e, List.replicate L (), P)).1)).getD ((B (e, List.replicate L (), P)).2.getD (i * (L + 1) + L) 0) false)
      = (clauseAt e L P j).getD i (0, false)

/-- Clauses of at most 3 literals, variables below Nv, no clause twice. -/
def Shaped3 (Nv : ℕ) (ψ : Cnf) : Prop := (∀ D ∈ ψ, D.length ≤ 3 ∧ ∀ l ∈ D, l.1 < Nv) ∧ ψ.Nodup

/-- The formula that says «some clause of the formula of the table e is violated by the assignment
that the circuit C computes». It has at most 3·|C| + a₀·(L+1) + g(e) variables: a₀ does NOT depend
on the table. -/
def StForm : Prop := ∃ (a₀ : ℕ) (g : MCode → ℕ) (F : (MCode × List Unit × ℕ) × List GateD → List Unit × Cnf), PolyT F ∧
  ∀ (e : MCode) (L P : ℕ) (C : List GateD), Fits e L P → WF L C →
    Shaped3 (F ((e, List.replicate L (), P), C)).1.length (F ((e, List.replicate L (), P), C)).2 ∧
    (F ((e, List.replicate L (), P), C)).1.length ≤ 3 * C.length + a₀ * (L + 1) + g e ∧
    (Sat (F ((e, List.replicate L (), P), C)).2 ↔ ¬∀ D ∈ tabF e L P, ∃ l ∈ D, eval (toC C) (toWord L l.1) = l.2)

/-! ### The chains and the formulas are computed in polynomial time -/

def StCertSched : Prop :=
  PolyT (fun u : List Unit => codeOf (nu u.length)) ∧ PolyT (fun u : List Unit => next u.length) ∧ PolyT (fun u : List Unit => nu u.length) ∧
  PolyT (fun u : List Unit => decide (pos u.length < top (nu u.length))) ∧ PolyT (fun u : List Unit => decide (pos u.length = top (nu u.length))) ∧
  PolyT (fun p : MCode × List Unit × ℕ => decide (Fits p.1 p.2.1.length p.2.2))

/-- The formula of a table is written out in time polynomial in its length; the last argument is a
list at least as long as the formula has clauses. -/
def StCertTabF : Prop := ∃ G : (MCode × List Unit × ℕ) × List Unit → Cnf, PolyT G ∧
  ∀ (e : MCode) (L P : ℕ) (pad : List Unit), Fits e L P → 2 ^ nb e L ≤ pad.length → G ((e, List.replicate L (), P), pad) = tabF e L P

/-- At the last place of a chain, the question about the first number of the chain is answered by
trying all assignments, in time polynomial in m. -/
def StFlip : Prop := ∃ fb : List Unit → Bool, PolyT fb ∧ ∀ m : ℕ, pos m = top (nu m) →
  (fb (List.replicate m ()) = true ↔ Fits (codeOf (nu m)) (2 ^ nu m) (2 ^ nu m) ∧ Sat (tabF (codeOf (nu m)) (2 ^ nu m) (2 ^ nu m)))

/-! ### The two forms of E^NP -/

/-- A machine that is started again after every answer can be replaced by an oracle machine. -/
def StRestart : Prop := ∀ L : Lang, InENP' L → InENP L

end CircuitLowerBound
