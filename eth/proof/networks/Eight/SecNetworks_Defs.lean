/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Paper.SecNetworks_Networks

/-! # Section 3 «Networks»: Definitions 2 and 3, and the counts of «A good grouping exists» (definitions and statements only)

The file proof/networks/Paper/SecNetworks_Networks.lean states Definitions 2 to 4 in the model of
the algorithms of this development: Ψ is defined from its factorization, S_a is all of {0,1}^{P_a},
values are «at most 2^B», a query costs t steps.
This file states Definitions 2 and 3 as the paper prints them: a network has the sets S_a, the
functions W_a and Ψ_{a,b}, the numbers c_{a,b} and the factorizations (f_{a,b}, f_{b,a}) as separate
data; S_a is a subset of {0,1}^{P_a}; values are
«below 2^B»; four procedures decide membership in S_a and compute W_a, Ψ_{a,b}, f_{a,b}; the (K,
λ)-clique is such a network.

What remains of the model of this development, here too: the node set is Fin g (the paper: [g]);
«operations» are steps of step machines (`Paper.StepMachine`); a bound S on the size of the states
is carried along; procedures get a context c, which
stands for whatever the calling algorithm holds in memory. This file has no proofs. -/

@[expose] public section

namespace Eight.SecNetworks

open Groundwork Groundwork.Prog Finset

/-! ## Definition 2: a network with parameters P, B, τ -/

/-- The data of a network on the node set [g] (Definition 2): for each node a the length P_a of its
settings, the set S_a of its settings and the function W_a; for each pair of nodes the function
Ψ_{a,b}, the number c_{a,b} of shared bits, and the functions f_{a,b}, f_{b,a} of a factorization.
Settings and indices θ are bit strings, written as lists. -/
structure Net (g : ℕ) where
  len : Fin g → ℕ
  S : Fin g → Finset (List Bool)
  W : Fin g → List Bool → ℤ
  Ψ : Fin g → Fin g → List Bool → List Bool → ℤ
  c : Fin g → Fin g → ℕ
  f : Fin g → Fin g → List Bool → List Bool → ℤ

namespace Net

variable {g : ℕ} (N : Net g)

/-- The value Z = Σ_z ∏_a W_a(z_a) ∏_{{a,b}} Ψ_{a,b}(z_a, z_b); z runs through all choices of one
setting z_a ∈ S_a for each node, the second product through the pairs a < b. -/
def value : ℤ := ∑ z ∈ Fintype.piFinset N.S, (∏ a, N.W a (z a)) * ∏ p ∈ pairs (Fin g), N.Ψ p.1 p.2 (z p.1) (z p.2)

/-- The total U = Σ_{(a,b) : a ≠ b} c_{a,b}, a sum over ordered pairs. -/
def U : ℕ := ∑ a, ∑ b ∈ univ.erase a, N.c a b

/-- **Definition 2**, all but (iii): N is a network on [g] with parameters P, B. -/
structure Is (P B : ℕ) : Prop where
  P_pos : 1 ≤ P
  B_pos : 1 ≤ B
  /-- the settings of a are bit strings of one fixed length P_a ≤ P -/
  len_S : ∀ a, ∀ z ∈ N.S a, z.length = N.len a
  len_le : ∀ a, N.len a ≤ P
  /-- Ψ_{b,a}(z_b, z_a) = Ψ_{a,b}(z_a, z_b) -/
  Ψ_symm : ∀ a b, a ≠ b → ∀ z ∈ N.S a, ∀ z' ∈ N.S b, N.Ψ b a z' z = N.Ψ a b z z'
  c_symm : ∀ a b, N.c a b = N.c b a
  /-- (f_{a,b}, f_{b,a}) is a factorization of Ψ_{a,b} through c_{a,b} bits -/
  fact : ∀ a b, a ≠ b → ∀ z ∈ N.S a, ∀ z' ∈ N.S b, N.Ψ a b z z' = ∑ θ ∈ words (N.c a b), N.f a b z θ * N.f b a z' θ
  /-- (i) -/
  i : ∀ a, ∑ b ∈ univ.erase a, N.c a b ≤ P
  /-- (ii) -/
  ii_W : ∀ a, ∀ z ∈ N.S a, |N.W a z| < 2 ^ B
  ii_Ψ : ∀ a b, a ≠ b → ∀ z ∈ N.S a, ∀ z' ∈ N.S b, |N.Ψ a b z z'| < 2 ^ B
  ii_f : ∀ a b, a ≠ b → ∀ z ∈ N.S a, ∀ θ ∈ words (N.c a b), |N.f a b z θ| < 2 ^ B

end Net

/-- A query for a value of Ψ: ((a, b), (z, z')). -/
abbrev PsiQ : Type := (ℕ × ℕ) × (List Bool × List Bool)

/-- What an algorithm is given of a network (Definition 2(iii)): the numbers P, B, P_a, c_{a,b}, and
four procedures: membership in S_a, W_a, Ψ_{a,b}, f_{a,b}. All may depend on a context c. -/
structure Procs (C : Type) : Type 1 where
  P : C → ℕ
  B : C → ℕ
  len : C → ℕ → ℕ
  cap : C → ℕ → ℕ → ℕ
  mem : Stepped (C × WQ) Bool
  W : Stepped (C × WQ) ℤ
  Ψ : Stepped (C × PsiQ) ℤ
  f : Stepped (C × FQ) ℤ

/-- **Definition 2(iii)**: in the context c the procedures give the numbers P, B, P_a, c_{a,b} of N,
decide membership in S_a for strings of P_a bits, and compute every value of W_a, Ψ_{a,b}, f_{a,b},
each within τ steps on states of size at most S. -/
structure Procs.Give {C : Type} (Np : Procs C) (c : C) {g : ℕ} (N : Net g) (P B τ S : ℕ) : Prop where
  P_eq : Np.P c = P
  B_eq : Np.B c = B
  len_eq : ∀ a : Fin g, Np.len c a = N.len a
  cap_eq : ∀ a b : Fin g, a ≠ b → Np.cap c a b = N.c a b
  mem_runs : ∀ (a : Fin g) (z : List Bool), z.length = N.len a → Np.mem.Runs (c, (a.val, z)) τ S (decide (z ∈ N.S a))
  W_runs : ∀ (a : Fin g), ∀ z ∈ N.S a, Np.W.Runs (c, (a.val, z)) τ S (N.W a z)
  Ψ_runs : ∀ (a b : Fin g), a ≠ b → ∀ z ∈ N.S a, ∀ z' ∈ N.S b, Np.Ψ.Runs (c, ((a.val, b.val), (z, z'))) τ S (N.Ψ a b z z')
  f_runs : ∀ (a b : Fin g), a ≠ b → ∀ z ∈ N.S a, ∀ θ ∈ words (N.c a b), Np.f.Runs (c, ((a.val, b.val), (z, θ))) τ S (N.f a b z θ)

/-- **Definition 2.** N is a network on [g] with parameters P, B, τ, given by the procedures Np in
the context c. -/
structure IsNetwork {C : Type} {g : ℕ} (Np : Procs C) (c : C) (N : Net g) (P B τ S : ℕ) : Prop where
  is : N.Is P B
  τ_pos : 1 ≤ τ
  given : Np.Give c N P B τ S

/-- An algorithm for networks in this form: from the procedures a computation on contexts. -/
structure NetAlg : Type 2 where
  app : {C : Type} → [HasSize C] → Procs C → Stepped C ℤ

/-- The lengths P_a and c_{a,b} are given in unary and the four procedures have polynomial-time
steps. -/
structure Procs.Keeps {C : Type} [Enc C] (Np : Procs C) : Prop where
  len : Unary fun p : C × ℕ => Np.len p.1 p.2
  cap : Unary fun p : C × ℕ × ℕ => Np.cap p.1 p.2.1 p.2.2
  mem : Nonempty (IsPolyT Np.mem)
  W : Nonempty (IsPolyT Np.W)
  Ψ : Nonempty (IsPolyT Np.Ψ)
  f : Nonempty (IsPolyT Np.f)

/-! ## Definition 3: the (K, λ)-clique as a network -/

/-- The place of the node w' among the K − 1 nodes other than w. -/
def place (w w' : ℕ) : ℕ := if w' < w then w' else w' - 1

/-- z_w(w'): the copy, held at w, of the string on the edge {w, w'}; a setting z_w is the
concatenation of its K − 1 strings of λ bits. -/
def copyAt (lam : ℕ) (w w' : ℕ) (z : List Bool) : List Bool := (z.drop (place w w' * lam)).take lam

/-- **Definition 3.** The (K, λ)-clique with tables W_1, …, W_K: S_w = ({0,1}^λ)^{K−1}, encoded by
concatenation, so P_w = (K − 1)λ; c_{w,w'} = λ; Ψ_{w,w'}(z_w, z_{w'}) = [z_w(w') = z_{w'}(w)];
f_{w,w'}(z_w, θ) = [z_w(w') = θ]. -/
def clique (K lam : ℕ) (W : Fin K → List Bool → ℤ) : Net K where
  len _ := (K - 1) * lam
  S _ := words ((K - 1) * lam)
  W := W
  Ψ w w' z z' := if copyAt lam w w' z = copyAt lam w' w z' then 1 else 0
  c _ _ := lam
  f w w' z θ := if copyAt lam w w' z = θ then 1 else 0

/-! ## «A good grouping exists», with the numbers of the proof, as counts over all K^g groupings -/

/-- Y_{γ,γ'} for numbers c_{a,b}: the sum of c_{a,b} over a ∈ G_γ, b ∈ G_{γ'}. -/
def Y {g K : ℕ} (c : Fin g → Fin g → ℕ) (χ : Fin g → Fin K) (γ γ' : Fin K) : ℕ := ∑ a with χ a = γ, ∑ b with χ b = γ', c a b

/-- A grouping is good: (G1) every group has at most 2g/K nodes; (G2) Y_{γ,γ'} ≤ (U + gP/K)/K² for
all γ ≠ γ' (multiplied by K³). -/
structure Good {g K : ℕ} (c : Fin g → Fin g → ℕ) (P : ℕ) (χ : Fin g → Fin K) : Prop where
  G1 : ∀ γ, K * #{a | χ a = γ} ≤ 2 * g
  G2 : ∀ γ γ', γ ≠ γ' → K ^ 3 * Y c χ γ γ' ≤ K * (∑ a, ∑ b ∈ univ.erase a, c a b) + g * P

/-- The steps of the paragraph «A good grouping exists», for g = 3K⁸, K ≥ 2, c symmetric with (i). A
probability p of an event is written as: the number of groupings in the event is at most p·K^g. -/
structure GroupingFacts : Prop where
  /-- by Chebyshev, Pr(Y_{γ,γ'} > U/K² + gP/K³) ≤ 4K⁶/g = 4/(3K²) -/
  cheb : ∀ (K P : ℕ) (c : Fin (3 * K ^ 8) → Fin (3 * K ^ 8) → ℕ), 2 ≤ K → (∀ a b, c a b = c b a) → (∀ a, ∑ b ∈ univ.erase a, c a b ≤ P) → ∀ γ γ' : Fin K, γ ≠ γ' →
    3 * K ^ 2 * #{χ : Fin (3 * K ^ 8) → Fin K | K * (∑ a, ∑ b ∈ univ.erase a, c a b) + 3 * K ^ 8 * P < K ^ 3 * Y c χ γ γ'} ≤ 4 * K ^ (3 * K ^ 8)
  /-- some pair violates this bound with probability less than 2/3 -/
  pairs : ∀ (K P : ℕ) (c : Fin (3 * K ^ 8) → Fin (3 * K ^ 8) → ℕ), 2 ≤ K → (∀ a b, c a b = c b a) → (∀ a, ∑ b ∈ univ.erase a, c a b ≤ P) →
    3 * #{χ : Fin (3 * K ^ 8) → Fin K | ∃ γ γ', γ ≠ γ' ∧ K * (∑ a, ∑ b ∈ univ.erase a, c a b) + 3 * K ^ 8 * P < K ^ 3 * Y c χ γ γ'} < 2 * K ^ (3 * K ^ 8)
  /-- a group exceeds 2g/K with probability at most K/g -/
  group : ∀ K : ℕ, 2 ≤ K → ∀ γ : Fin K, 3 * K ^ 8 * #{χ : Fin (3 * K ^ 8) → Fin K | 2 * (3 * K ^ 8) < K * #{a | χ a = γ}} ≤ K * K ^ (3 * K ^ 8)
  /-- some group does so with probability less than 1/3 (the paper: at most K²/g < 1/3) -/
  groups : ∀ K : ℕ, 2 ≤ K → 3 * #{χ : Fin (3 * K ^ 8) → Fin K | ∃ γ, 2 * (3 * K ^ 8) < K * #{a | χ a = γ}} < K ^ (3 * K ^ 8)
  /-- so a good grouping exists -/
  exists_good : ∀ (K P : ℕ) (c : Fin (3 * K ^ 8) → Fin (3 * K ^ 8) → ℕ), 2 ≤ K → (∀ a b, c a b = c b a) → (∀ a, ∑ b ∈ univ.erase a, c a b ≤ P) → ∃ χ : Fin (3 * K ^ 8) → Fin K, Good c P χ

end Eight.SecNetworks
