/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import CircuitLowerBound.Interfaces
public import Mathlib.SetTheory.Cardinal.NatCard
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Finset.Lattice.Fold

/-! # The circuit lower bound for E^NP (Section 7): what the table of a machine says (definitions only)

A run of one of Mathlib's multi-stack machines is written as a table of rows, one row for each time
t = 0, …, 2^b. A row holds the label, the state, and for every stack k and every position q the
symbol at depth q below the top of the
stack (or «blank»). One step of the machine sees only the top d symbols of each stack and replaces
them by at most 2d symbols; the rest of the stack is shifted. `Spec` lists the conditions on the
rows; each of them is a clause of at most
three literals that is repeated for all times t and all positions q. -/

@[expose] public section

namespace CircuitLowerBound.Tab

open ENP Turing

/-- The largest number of stack operations on a path through a statement. -/
def ops {K : Type} {Γ : K → Type} {Λ σ : Type} : TM2.Stmt Γ Λ σ → ℕ
  | .push _ _ q => ops q + 1
  | .peek _ _ q => ops q + 1
  | .pop _ _ q => ops q + 1
  | .load _ q => ops q
  | .branch _ q₁ q₂ => max (ops q₁) (ops q₂)
  | .goto _ => 0
  | .halt => 0

/-- The symbols of a list of cells up to the first blank. -/
def pref {α : Type} : List (Option α) → List α
  | [] => []
  | none :: _ => []
  | some a :: L => a :: pref L

instance (tm : FinTM2) : Fintype tm.Λ := tm.ΛFin
instance (tm : FinTM2) : Fintype tm.σ := tm.σFin
instance (tm : FinTM2) : Fintype tm.K := tm.kFin

variable (N : TM2ComputableAux Bool Bool)

/-- The number d of symbols at the top of a stack that one step can see: at least 1. -/
def dep : ℕ := max 1 (Finset.univ.sup fun l : N.tm.Λ => ops (N.tm.m l))

/-- By how many bits positions are longer than times. -/
def lamOf : ℕ := Nat.size (2 * dep N + 2)

/-- The top d cells of every stack. -/
abbrev Win : Type := ∀ k : N.tm.K, Fin (dep N) → Option (N.tm.Γ k)

/-- What one step depends on: label, state, the top d cells of every stack. -/
abbrev Case : Type := Option N.tm.Λ × N.tm.σ × Win N

/-- The number of cases. -/
noncomputable def nc : ℕ := Nat.card (Case N)

/-- The cases in some order. -/
noncomputable def ec [Finite (Case N)] : Case N ≃ Fin (nc N) := Finite.equivFin _

/-- The step of the machine on the tops alone; a halted machine stays as it is. -/
def nxt (γ : Case N) : N.tm.Cfg :=
  match γ.1 with
  | none => ⟨none, γ.2.1, fun k => pref (List.ofFn (γ.2.2 k))⟩
  | some l => TM2.stepAux (N.tm.m l) γ.2.1 fun k => pref (List.ofFn (γ.2.2 k))

/-- The kinds of statements about a row: «the label is l», «the state is v», «the new top of stack k
has n symbols», «the cell of stack k at this position holds x», «the case is γ», «the case is among
the first i», «this position is at most P». -/
inductive Atom
  | lab (l : Option N.tm.Λ)
  | var (v : N.tm.σ)
  | len (k : N.tm.K) (n : Fin (2 * dep N + 1))
  | cell (k : N.tm.K) (x : Option (N.tm.Γ k))
  | cs (γ : Case N)
  | pre (i : Fin (nc N + 1))
  | u

/-- The conditions. α a t q is the truth value of the statement a at time t and position q;
statements about a whole row stand at position 0. -/
structure Spec [Finite (Case N)] (α : Atom N → ℕ → ℕ → Bool) (b Q P : ℕ) : Prop where
  /-- at every time before the last some case holds -/
  preTop : ∀ t < 2 ^ b, α (.pre (Fin.last _)) t 0 = true
  preBot : ∀ t < 2 ^ b, α (.pre 0) t 0 = false
  preStep : ∀ t < 2 ^ b, ∀ i : Fin (nc N), α (.pre i.succ) t 0 = false ∨ α (.pre i.castSucc) t 0 = true ∨ α (.cs ((ec N).symm i)) t 0 = true
  /-- the case that holds is that of the row -/
  csLab : ∀ t < 2 ^ b, ∀ γ : Case N, α (.cs γ) t 0 = true → α (.lab γ.1) t 0 = true
  csVar : ∀ t < 2 ^ b, ∀ γ : Case N, α (.cs γ) t 0 = true → α (.var γ.2.1) t 0 = true
  csCell : ∀ t < 2 ^ b, ∀ (γ : Case N) (k : N.tm.K) (j : Fin (dep N)), α (.cs γ) t 0 = true → α (.cell k (γ.2.2 k j)) t j = true
  /-- the case fixes label, state and the new tops of the next row -/
  nxLab : ∀ t < 2 ^ b, ∀ (γ : Case N) (x : Option N.tm.Λ), α (.cs γ) t 0 = true → (α (.lab x) (t + 1) 0 = true ↔ x = (nxt N γ).l)
  nxVar : ∀ t < 2 ^ b, ∀ (γ : Case N) (x : N.tm.σ), α (.cs γ) t 0 = true → (α (.var x) (t + 1) 0 = true ↔ x = (nxt N γ).var)
  nxLen : ∀ t < 2 ^ b, ∀ (γ : Case N) (k : N.tm.K) (n : Fin (2 * dep N + 1)), α (.cs γ) t 0 = true → (α (.len k n) t 0 = true ↔ (n : ℕ) = ((nxt N γ).stk k).length)
  nxCell : ∀ t < 2 ^ b, ∀ (γ : Case N) (k : N.tm.K) (x : Option (N.tm.Γ k)) (j : ℕ), j < ((nxt N γ).stk k).length → α (.cs γ) t 0 = true →
    (α (.cell k x) (t + 1) j = true ↔ x = ((nxt N γ).stk k)[j]?)
  /-- below the new top the stack is what lay below the old top -/
  copy : ∀ t < 2 ^ b, ∀ q < 2 ^ Q, ∀ (k : N.tm.K) (n : Fin (2 * dep N + 1)) (x : Option (N.tm.Γ k)), α (.len k n) t 0 = true →
    α (.cell k x) (t + 1) (q + n) = α (.cell k x) t (q + dep N)
  /-- the first row: the machine is started on 1^P 0 y -/
  iLab : ∀ x : Option N.tm.Λ, α (.lab x) 0 0 = true ↔ x = some N.tm.main
  iVar : ∀ x : N.tm.σ, α (.var x) 0 0 = true ↔ x = N.tm.initialState
  iCell : ∀ q < 2 ^ Q, ∀ k : N.tm.K, k ≠ N.tm.k₀ → ∀ x : Option (N.tm.Γ k), α (.cell k x) 0 q = true ↔ x = none
  iSome : ∀ q < 2 ^ Q, α (.cell N.tm.k₀ none) 0 q = true ∨ α (.cell N.tm.k₀ (some (N.inputAlphabet.symm false))) 0 q = true ∨ α (.cell N.tm.k₀ (some (N.inputAlphabet.symm true))) 0 q = true
  iMost : ∀ q < 2 ^ Q, ∀ x x' : Option (N.tm.Γ N.tm.k₀), x ≠ x' → α (.cell N.tm.k₀ x) 0 q = false ∨ α (.cell N.tm.k₀ x') 0 q = false
  iBlank : ∀ q < 2 ^ Q, α (.cell N.tm.k₀ none) 0 q = true → α (.cell N.tm.k₀ none) 0 (q + 1) = true
  uStep : ∀ q < 2 ^ Q, α .u 0 (q + 1) = true → α .u 0 q = true
  uP : α .u 0 P = true
  uP1 : α .u 0 (P + 1) = false
  uOne : ∀ q < 2 ^ Q, α .u 0 (q + 1) = true → α (.cell N.tm.k₀ (some (N.inputAlphabet.symm true))) 0 q = true
  cellP : α (.cell N.tm.k₀ (some (N.inputAlphabet.symm false))) 0 P = true
  /-- the last row: halted, with the output 1 -/
  fLab : α (.lab none) (2 ^ b) 0 = true
  fVar : α (.var N.tm.initialState) (2 ^ b) 0 = true
  fOut0 : α (.cell N.tm.k₁ (some (N.outputAlphabet.symm true))) (2 ^ b) 0 = true
  fOut1 : α (.cell N.tm.k₁ none) (2 ^ b) 1 = true
  fOther : ∀ k : N.tm.K, k ≠ N.tm.k₁ → α (.cell k none) (2 ^ b) 0 = true

end CircuitLowerBound.Tab

namespace CircuitLowerBound

open ENP Turing Tab

/-! ### The statements of this group -/

/-- The three literals of a clause of a table. -/
def lits (c : TCl) : List TLit := [c.1, c.2.1, c.2.2]

/-- The kinds are at least 1 and fit into kb bits, and the numbers added to positions are at most
2^lam. -/
def GoodCode (e : MCode) : Prop := ∀ c ∈ tab e, ∀ l ∈ lits c, 1 ≤ l.1 ∧ l.1 < 2 ^ kb e ∧ l.2.2.2.1 ≤ 2 ^ lam e

/-- A literal of a table holds in the shift by (t, q). -/
def holdsT (α : ℕ → ℕ → ℕ → Bool) (b P t q : ℕ) (l : TLit) : Prop := α l.1 (tval b t l.2.1) (qval P q l.2.2.1 + l.2.2.2.1) = l.2.2.2.2

/-- Some truth values of the triples (kind, time, position) satisfy all shifts of the clauses. -/
def SatT (X : List TCl) (b Q P : ℕ) : Prop := ∃ α : ℕ → ℕ → ℕ → Bool, ∀ c ∈ X, ∀ t < 2 ^ b, ∀ q < 2 ^ Q, ∃ l ∈ lits c, holdsT α b P t q l

/-- Triples and numbers of variables: the formula of a table is satisfiable if and only if its
clauses are, read with triples. -/
def StPack : Prop := ∀ (e : MCode) (L P : ℕ), GoodCode e → Fits e L P → (Sat (tabF e L P) ↔ SatT (tab e) (bt e L) (bq e L) P)

/-- The conditions hold for some truth values if and only if the machine accepts. -/
def StSpec : Prop := ∀ (N : TM2ComputableAux Bool Bool) [Finite (Case N)] (b P : ℕ), 1 ≤ b → P + 2 ≤ 2 ^ b →
  ((∃ α, Spec N α b (b + lamOf N) P) ↔ Acc N P (2 ^ b))

/-- The conditions are the shifts of a table. -/
def StSpecTab : Prop := ∀ (N : TM2ComputableAux Bool Bool) [Finite (Case N)], (∀ k, Finite (N.tm.Γ k)) →
  ∃ e : MCode, GoodCode e ∧ lam e = lamOf N ∧ ∀ b Q P : ℕ, SatT (tab e) b Q P ↔ ∃ α, Spec N α b Q P

end CircuitLowerBound
