/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ParityChecksStatement
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Algebra.ZMod
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Nat.Log

/-! # Appendix D, Steps 1 and 2: parity checks, the cut-off lemma, the family of checks, the search for the checks

Definitions and statements only; every statement is a proposition (`…Stmt`, `LemCutoff`,
`LemFamily`) or a structure of propositions (`StepChoice`), proved in proof/variables/VariableBound.
Imports Mathlib and `ParityChecksStatement.lean`, of which only the first
definitions are used: `ParityChecks.ev` ([q even]), `ParityChecks.sig` (σ_i), `ParityChecks.eta` (η)
and `ParityChecks.tuples`.

## How to read it

* Abstract setting, as in `ParityChecksStatement.lean`: X is the finite set of assignments ξ, E the
  finite set of clauses of Φ, V ξ the set of clauses that ξ violates. Nothing else about formulas is
  used in Steps 1 and 2.
* A check is a `Finset E`; a list 𝓛 of checks is a `List (Finset E)`, which may overlap or repeat;
  (𝓛, Γ) is `L ++ [Γ]`. The paper numbers the checks 1, …, r, Lean 0, …, r − 1.
* Fractions are cleared where the paper compares counts: «at most (16/(15v))·|Ω| indices» is
  15·v·(number) ≤ 16·|Ω|.
* The names follow the paper: n̄ `nb`, r̄ `rb`, s̄ `sb`, t̄ `tb`, β `beta`, M `Mb`, p `pp`, Υ `Ups`.

## What is not here

* The inequalities of the paragraph «Setting and parameters» (the bounds on s̄, on 3m/(n̄+1) and on
  β, r̄ ≤ 2.41·β + 1, r̄ ≤ 10n and M ≤ 14n, p·r̄ < 22·log(2Δ), the bound on t̄): stated in
  proof/variables/VariableBound/Params/Defs.lean, proved in
  proof/variables/VariableBound/Params/Ineq.lean.
* The claim of Lemma 13 that the sets can be listed in time polynomial in m: it is a statement about
  a program, in proof/variables/VariableBound/Field. The number of lists that are tried and the size
  of Υ belong to the program too.
* The networks of Step 3, the cost (Step 4), the sparsification (Step 5) and the end (Step 6), which
  speak of formulas, nodes and machines: proof/variables/VariableBound. -/

@[expose] public section

namespace AppVariables

open Finset

/-! ## Step 1: parity checks, and a cut-off modulo a power of 2 -/

section StepParity

variable {X E : Type} [Fintype X] [Fintype E] [DecidableEq E]

/-- ∏_j [ |V_j(ξ)| even ], with V_j(ξ) = Λ_j ∩ V(ξ). -/
def allEven (V : X → Finset E) (L : List (Finset E)) (ξ : X) : ℤ := (L.map fun Λ => ParityChecks.ev #(Λ ∩ V ξ)).prod

/-- F(𝓛) = Σ_ξ η(ξ)·∏_j [ |V_j(ξ)| even ]. -/
def Fsum (V : X → Finset E) (nb : ℕ) (L : List (Finset E)) : ℤ := ∑ ξ, ParityChecks.eta V nb ξ * allEven V L ξ

/-- X(𝓛) = Σ_ξ C(|V(ξ)|, n̄ + 1)·∏_j [ |V_j(ξ)| even ]. -/
def Xsum (V : X → Finset E) (nb : ℕ) (L : List (Finset E)) : ℤ := ∑ ξ, ((#(V ξ)).choose (nb + 1) : ℤ) * allEven V L ξ

/-- The tuples (Π_1, …, Π_r) with Π_j ⊆ V_j(ξ) for all j and Σ_j |Π_j| ≤ M'. -/
def tup (V : X → Finset E) (L : List (Finset E)) (M' : ℕ) (ξ : X) : Finset (Fin L.length → Finset E) :=
  ParityChecks.tuples V L.length (fun j => L.getD j ∅) univ M' ξ

/-- Step 1 of Appendix D: if X(𝓛) = 0, then F(𝓛) is the number of satisfying assignments of Φ. -/
def ProductStmt : Prop := ∀ (X E : Type) [Fintype X] [Fintype E] [DecidableEq E] (V : X → Finset E) (nb : ℕ) (L : List (Finset E)),
  Xsum V nb L = 0 → Fsum V nb L = #{ξ | V ξ = ∅}

/-- If m ≤ n̄, the empty list has X = 0. -/
def EmptyListStmt : Prop := ∀ (X E : Type) [Fintype X] [Fintype E] [DecidableEq E] (V : X → Finset E) (nb : ℕ),
  Fintype.card E ≤ nb → Xsum V nb [] = 0

/-- Lemma 12 (Cut-off): for a list 𝓛 of r checks, a function φ with integer values, ν ≥ 1 and M' ≥ ν
− 1 + r, Σ_ξ φ(ξ)·∏_j [ |V_j(ξ)| even ] is congruent modulo 2^ν to Σ_ξ φ(ξ)·Σ ∏_j σ_{|Π_j|}, the
inner sum over the tuples
with Π_j ⊆ V_j(ξ) for all j and Σ_j |Π_j| ≤ M'. -/
def LemCutoff : Prop := ∀ (X E : Type) [Fintype X] [Fintype E] [DecidableEq E] (V : X → Finset E) (L : List (Finset E)) (φ : X → ℤ) (ν M' : ℕ),
  1 ≤ ν → ν - 1 + L.length ≤ M' →
  ∑ ξ, φ ξ * allEven V L ξ ≡ ∑ ξ, φ ξ * ∑ S ∈ tup V L M' ξ, ∏ j, ParityChecks.sig #(S j) [ZMOD 2 ^ ν]

/-- The congruences after Lemma 12, for r checks, β ≥ 1, M ≥ β − 1 + r, M ≥ n + r (the paper takes r
≤ r̄, M = r̄ + β − 1): X(𝓛) mod 2^β and F(𝓛) mod 2^(n+1) as sums over ξ and tuples (Π_0, …, Π_r). -/
def XFStmt : Prop := ∀ (X E : Type) [Fintype X] [Fintype E] [DecidableEq E] (V : X → Finset E) (nb : ℕ) (L : List (Finset E)) (β n M : ℕ),
  1 ≤ β → β - 1 + L.length ≤ M → n + L.length ≤ M →
  (Xsum V nb L ≡ ∑ ξ, ∑ _S₀ ∈ (V ξ).powerset with #_S₀ = nb + 1, ∑ S ∈ tup V L M ξ, ∏ j, ParityChecks.sig #(S j) [ZMOD 2 ^ β]) ∧
  (Fsum V nb L ≡ ∑ ξ, ∑ S₀ ∈ (V ξ).powerset with #S₀ ≤ nb, (-1) ^ #S₀ * ∑ S ∈ tup V L M ξ, ∏ j, ParityChecks.sig #(S j) [ZMOD 2 ^ (n + 1)])

/-- The residues determine the numbers: 0 ≤ X(𝓛) ≤ 2^n·C(m, n̄+1) ≤ 2^(β−1), and 0 ≤ F(𝓛) ≤ 2^n if
X(𝓛) = 0. Here 2^n is any bound for the number of assignments, and β = n + ⌈log C(m, n̄+1)⌉ + 1. -/
def ResiduesStmt : Prop := ∀ (X E : Type) [Fintype X] [Fintype E] [DecidableEq E] (V : X → Finset E) (nb : ℕ) (L : List (Finset E)) (n : ℕ),
  Fintype.card X ≤ 2 ^ n →
  (0 ≤ Xsum V nb L ∧ Xsum V nb L ≤ 2 ^ n * (Fintype.card E).choose (nb + 1) ∧
    (2 : ℤ) ^ n * (Fintype.card E).choose (nb + 1) ≤ 2 ^ (n + Nat.clog 2 ((Fintype.card E).choose (nb + 1)))) ∧
  (Xsum V nb L = 0 → 0 ≤ Fsum V nb L ∧ Fsum V nb L ≤ 2 ^ n)

end StepParity

/-! ## Step 2: Lemma 13 (Family of checks) -/

/-- What Lemma 13 says of sets Γ_u, u ∈ Ω, of clauses, for the number v: (a) |Γ_u| ≤ 16m/v; (b)
every clause lies in Γ_u for at most (16/(15v))·|Ω| indices u; (c) for every set V of more than v
clauses, |Γ_u ∩ V| is odd for at least |Ω|/4 indices u. -/
structure IsFamily {E ι : Type} [Fintype E] [DecidableEq E] (v : ℕ) (Ω : Finset ι) (Γ : ι → Finset E) : Prop where
  a : ∀ u ∈ Ω, v * #(Γ u) ≤ 16 * Fintype.card E
  b : ∀ e : E, 15 * v * #{u ∈ Ω | e ∈ Γ u} ≤ 16 * #Ω
  c : ∀ V : Finset E, v < #V → #Ω ≤ 4 * #{u ∈ Ω | Odd #(Γ u ∩ V)}

section Family

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]

/-- The inner product modulo 2 of two strings of s bits. -/
def ip {s : ℕ} (x y : Fin s → ZMod 2) : ZMod 2 := ∑ i, x i * y i

/-- Γ_u for u = (u₁, u₂, u₃, u₄) ∈ 𝔽⁴: the clauses E such that the first log v − 1 bits of u₁·ϑ_E +
u₂ are 0 and ⟨u₃^ι(E), u₄⟩ = 1. The clauses are numbered, ι(E) = E; v = 2^a; `bits` writes the
elements of 𝔽
as strings of s bits. In Lean, as in the paper, u₃^0 = 1 also for u₃ = 0. -/
def Gam {m s : ℕ} (bits : F ≃ₗ[ZMod 2] (Fin s → ZMod 2)) (ϑ : Fin m ↪ F) (a : ℕ) (u : F × F × F × F) : Finset (Fin m) :=
  univ.filter fun E => (∀ i : Fin s, i.val < a - 1 → bits (u.1 * ϑ E + u.2.1) i = 0) ∧ ip (bits (u.2.2.1 ^ E.val)) (bits u.2.2.2) = 1

/-- Ω: the u ∈ 𝔽⁴ with |Γ_u| ≤ 16m/v. -/
def Om {m s : ℕ} (bits : F ≃ₗ[ZMod 2] (Fin s → ZMod 2)) (ϑ : Fin m ↪ F) (a : ℕ) : Finset (F × F × F × F) :=
  univ.filter fun u => 2 ^ a * #(Gam bits ϑ a u) ≤ 16 * m

end Family

/-- Lemma 13 (Family of checks), without its claim on the time: for v = 2^a with 2 ≤ v ≤ m and a
field 𝔽 with 2^s elements, 16m ≤ 2^s < 32m, the sets Γ_u, u ∈ Ω, have 0 < |Ω| < (32m)⁴ and (a), (b),
(c). That Ω is not empty is in the printed proof (|Ω| ≥ (15/16)·|𝔽|⁴), not in the printed statement;
Step 2 needs it. -/
def LemFamily : Prop := ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] (m s a : ℕ) (bits : F ≃ₗ[ZMod 2] (Fin s → ZMod 2)) (ϑ : Fin m ↪ F),
  1 ≤ a → 2 ^ a ≤ m → 16 * m ≤ 2 ^ s → 2 ^ s < 32 * m →
  0 < #(Om bits ϑ a) ∧ #(Om bits ϑ a) < (32 * m) ^ 4 ∧ IsFamily (2 ^ a) (Om bits ϑ a) (Gam bits ϑ a)

/-! ## Setting and parameters -/

/-- n̄ is the power of two with n/(2·log(2Δ)) < n̄ ≤ n/log(2Δ), written without the real number
log(2Δ): (2Δ)^n̄ ≤ 2^n < (2Δ)^(2n̄). The paper also has n ≥ 2·log(2Δ), which gives n̄ ≥ 2; this
definition allows n̄ = 1. -/
def IsNb (n Δ nb : ℕ) : Prop := (∃ a, nb = 2 ^ a) ∧ (2 * Δ) ^ nb ≤ 2 ^ n ∧ 2 ^ n < (2 * Δ) ^ (2 * nb)

/-- β = n + ⌈log C(m, n̄+1)⌉ + 1. -/
def beta (n m nb : ℕ) : ℕ := n + Nat.clog 2 (m.choose (nb + 1)) + 1

/-- r̄ is the least j ≥ 0 with 3^j·2^β < 4^j. -/
def IsRb (β rb : ℕ) : Prop := 3 ^ rb * 2 ^ β < 4 ^ rb ∧ ∀ j < rb, ¬ 3 ^ j * 2 ^ β < 4 ^ j

/-- M = r̄ + β − 1. -/
def Mb (β rb : ℕ) : ℕ := rb + β - 1

/-- p = 16/(15·n̄). -/
def pp (nb : ℕ) : ℚ := 16 / (15 * nb)

/-- t̄ is the least c ≥ 0 with 2^c ≥ m·(1+p)^r̄. -/
def IsTb (m nb rb tb : ℕ) : Prop := (m : ℚ) * (1 + pp nb) ^ rb ≤ 2 ^ tb ∧ ∀ c < tb, ¬ (m : ℚ) * (1 + pp nb) ^ rb ≤ 2 ^ c

/-! ## Step 2: finding the checks -/

section StepChoice

variable {X E ι : Type} [Fintype X] [Fintype E] [DecidableEq E]

/-- load(E): the number of checks of the list that contain the clause E. -/
def load (L : List (Finset E)) (e : E) : ℕ := (L.filter fun Λ => e ∈ Λ).length

/-- Υ(𝓛) = (4/3)^r·X(𝓛)/2^(β−1) + (1+p)^(r̄−r)·2^(−t̄)·Σ_E 2^load(E). -/
def Ups (V : X → Finset E) (nb β rb tb : ℕ) (L : List (Finset E)) : ℚ :=
  (4 / 3) ^ L.length * (Xsum V nb L : ℚ) / 2 ^ (β - 1) + (1 + pp nb) ^ (rb - L.length) * (1 / 2 ^ tb) * ∑ e : E, (2 : ℚ) ^ load L e

/-- The lists that the algorithm reaches: the empty list; and, if 𝓛 is reached and X(𝓛) > 0, a list
(𝓛, Γ_u), u ∈ Ω, with the smallest Υ. -/
inductive Reached (V : X → Finset E) (nb β rb tb : ℕ) (Ω : Finset ι) (Γ : ι → Finset E) : List (Finset E) → Prop
  | nil : Reached V nb β rb tb Ω Γ []
  | step (L : List (Finset E)) (u : ι) : Reached V nb β rb tb Ω Γ L → 0 < Xsum V nb L → u ∈ Ω →
      (∀ u' ∈ Ω, Ups V nb β rb tb (L ++ [Γ u]) ≤ Ups V nb β rb tb (L ++ [Γ u'])) → Reached V nb β rb tb Ω Γ (L ++ [Γ u])

/-- Step 2 (finding the checks). Each field names its hypotheses, chosen among: X has at most 2^n
elements; n̄ ≥ 1 (n̄ need not be the n̄ of the paper, and m > n̄ is not assumed); β = n + ⌈log C(m,
n̄+1)⌉ + 1 for m the number of clauses
(`beta`), and r̄, t̄ as in the paper for this β and m (`IsRb`, `IsTb`); Γ_u, u ∈ Ω, a family with
(a), (b), (c) of Lemma 13 for v = n̄ (`IsFamily`). -/
structure StepChoice : Prop where
  /-- for a family as in Lemma 13 with v = n̄: the average of X(𝓛, Γ_u) over u ∈ Ω is at most
  (3/4)·X(𝓛) -/
  avgX : ∀ (X E ι : Type) [Fintype X] [Fintype E] [DecidableEq E] (V : X → Finset E) (nb : ℕ) (Ω : Finset ι) (Γ : ι → Finset E) (L : List (Finset E)),
    IsFamily nb Ω Γ → 4 * ∑ u ∈ Ω, Xsum V nb (L ++ [Γ u]) ≤ 3 * #Ω * Xsum V nb L
  /-- for n̄ ≥ 1 and a family as in Lemma 13 with v = n̄: the average of 2^[E ∈ Γ_u] over u ∈ Ω is
  at most 1 + p -/
  avgCol : ∀ (E ι : Type) [Fintype E] [DecidableEq E] (nb : ℕ) (Ω : Finset ι) (Γ : ι → Finset E) (e : E), 1 ≤ nb →
    IsFamily nb Ω Γ → ∑ u ∈ Ω, (2 : ℚ) ^ (if e ∈ Γ u then 1 else 0) ≤ (1 + pp nb) * #Ω
  /-- for n̄ ≥ 1, a family as in Lemma 13 with v = n̄, any β, r̄, t̄ and a list of r < r̄ checks:
  the average of Υ(𝓛, Γ_u) over u ∈ Ω is at most Υ(𝓛) -/
  avgUps : ∀ (X E ι : Type) [Fintype X] [Fintype E] [DecidableEq E] (V : X → Finset E) (nb β rb tb : ℕ) (Ω : Finset ι) (Γ : ι → Finset E) (L : List (Finset E)),
    1 ≤ nb → IsFamily nb Ω Γ → L.length < rb → ∑ u ∈ Ω, Ups V nb β rb tb (L ++ [Γ u]) ≤ #Ω * Ups V nb β rb tb L
  /-- for at most 2^n assignments, n̄ ≥ 1, β, r̄, t̄ as in the paper and a family as in Lemma 13
  with v = n̄: every list that is reached has at most r̄ checks and Υ ≤ 2 -/
  ups_le : ∀ (X E ι : Type) [Fintype X] [Fintype E] [DecidableEq E] (V : X → Finset E) (n nb rb tb : ℕ) (Ω : Finset ι) (Γ : ι → Finset E) (L : List (Finset E)),
    Fintype.card X ≤ 2 ^ n → 1 ≤ nb → IsRb (beta n (Fintype.card E) nb) rb → IsTb (Fintype.card E) nb rb tb → IsFamily nb Ω Γ →
    Reached V nb (beta n (Fintype.card E) nb) rb tb Ω Γ L → L.length ≤ rb ∧ Ups V nb (beta n (Fintype.card E) nb) rb tb L ≤ 2
  /-- under the hypotheses of `ups_le`: every reached list has X(𝓛) ≤ (3/4)^r·2^β -/
  x_le : ∀ (X E ι : Type) [Fintype X] [Fintype E] [DecidableEq E] (V : X → Finset E) (n nb rb tb : ℕ) (Ω : Finset ι) (Γ : ι → Finset E) (L : List (Finset E)),
    Fintype.card X ≤ 2 ^ n → 1 ≤ nb → IsRb (beta n (Fintype.card E) nb) rb → IsTb (Fintype.card E) nb rb tb → IsFamily nb Ω Γ →
    Reached V nb (beta n (Fintype.card E) nb) rb tb Ω Γ L → 4 ^ L.length * Xsum V nb L ≤ 3 ^ L.length * 2 ^ beta n (Fintype.card E) nb
  /-- for any β, r̄, t̄ and any sets Γ_u, if Ω is not empty: a reached list with X(𝓛) > 0 has a
  reached extension (𝓛, Γ_u), u ∈ Ω -/
  progress : ∀ (X E ι : Type) [Fintype X] [Fintype E] [DecidableEq E] (V : X → Finset E) (nb β rb tb : ℕ) (Ω : Finset ι) (Γ : ι → Finset E) (L : List (Finset E)),
    Ω.Nonempty → Reached V nb β rb tb Ω Γ L → 0 < Xsum V nb L → ∃ u ∈ Ω, Reached V nb β rb tb Ω Γ (L ++ [Γ u])
  /-- under the hypotheses of `ups_le`: a reached list of r̄ checks has X = 0; with `ups_le`, the
  loop ends after at most r̄ rounds with X(𝓛) = 0 -/
  ends : ∀ (X E ι : Type) [Fintype X] [Fintype E] [DecidableEq E] (V : X → Finset E) (n nb rb tb : ℕ) (Ω : Finset ι) (Γ : ι → Finset E) (L : List (Finset E)),
    Fintype.card X ≤ 2 ^ n → 1 ≤ nb → IsRb (beta n (Fintype.card E) nb) rb → IsTb (Fintype.card E) nb rb tb → IsFamily nb Ω Γ →
    Reached V nb (beta n (Fintype.card E) nb) rb tb Ω Γ L → L.length = rb → Xsum V nb L = 0
  /-- the bounds at the end of Step 2, under the hypotheses of `ups_le`: every list whose X or F is
  needed (a reached list, or one with X > 0 and one more Γ_u, u ∈ Ω) has r ≤ r̄, |Λ_j| ≤ s̄ =
  16m/n̄, load(E) ≤ t̄ + 2 -/
  structure_ : ∀ (X E ι : Type) [Fintype X] [Fintype E] [DecidableEq E] (V : X → Finset E) (n nb rb tb : ℕ) (Ω : Finset ι) (Γ : ι → Finset E) (L L' : List (Finset E)),
    Fintype.card X ≤ 2 ^ n → 1 ≤ nb → IsRb (beta n (Fintype.card E) nb) rb → IsTb (Fintype.card E) nb rb tb → IsFamily nb Ω Γ →
    Reached V nb (beta n (Fintype.card E) nb) rb tb Ω Γ L → (L' = L ∨ (0 < Xsum V nb L ∧ ∃ u ∈ Ω, L' = L ++ [Γ u])) →
    L'.length ≤ rb ∧ (∀ Λ ∈ L', nb * #Λ ≤ 16 * Fintype.card E) ∧ ∀ e : E, load L' e ≤ tb + 2

end StepChoice

end AppVariables
