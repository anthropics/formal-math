/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Order.Fin.Basic

/-! Instances and their value Z (a sum, over all labellings of the edges of a complete graph, of a
product of one tensor per node), networks and their value, merging the nodes of a
network into classes, and the passage from a network to an instance.
Definitions only; the theorems are in Groundwork.Net.Calculus and Groundwork.Net.Net.

Conventions. Nodes: a finite linearly ordered type J. An unordered pair {a,b} of distinct nodes is
named by the
ordered pair (min a b, max a b), written pr a b. Tuples indexed by a subset of an index type are
total functions
that take a fixed default value off the subset, so that all index sets are Finsets of plain function
types. -/

namespace Groundwork

open Finset

variable {J J' σ τ A A' : Type*}

/-- The pairs a < b. -/
@[expose] public def pairs (J : Type*) [Fintype J] [LinearOrder J] : Finset (J × J) :=
  univ.filter fun p => p.1 < p.2

/-- The name of the unordered pair {a,b}. -/
@[expose] public def pr [LinearOrder J] (a b : J) : J × J := (min a b, max a b)

/-- Tuples (t i) with t i ∈ T i where P i holds and t i = d elsewhere. -/
@[expose] public def tuples {ι X : Type*} [Fintype ι] [DecidableEq ι] (P : ι → Prop) [DecidablePred P]
    (T : ι → Finset X) (d : X) : Finset (ι → X) :=
  Fintype.piFinset fun i => if P i then T i else {d}

/-! ### Instances -/

/-- A (J,A)-instance: R v reads the labels of the edges at v, as a function w ↦ label of {v,w};
at w = v it is always handed the default label (see Z). The problem on K nodes with λ-bit labels on
the edges (the (K,λ)-clique of
Definition 3 in the paper): J = Fin K, card A = 2^λ, and R v is the tensor W_v. -/
public abbrev Inst (J A : Type*) := J → (J → A) → ℤ

/-- The labellings of the edges of the complete graph on J: functions on J × J, free at a < b, equal
to d elsewhere. -/
@[expose] public def labellings (J : Type*) [Fintype J] [LinearOrder J] [Fintype A] (d : A) : Finset (J × J → A) :=
  tuples (fun p : J × J => p.1 < p.2) (fun _ => univ) d

/-- Λ_v: the labelling Λ on the edges at v. -/
@[expose] public def star [LinearOrder J] (Λ : J × J → A) (v : J) : J → A := fun w => Λ (pr v w)

/-- Z(R) = Σ_Λ ∏_v R_v(Λ_v). -/
@[expose] public def Inst.Z [Fintype J] [LinearOrder J] [Fintype A] (d : A) (R : Inst J A) : ℤ :=
  ∑ Λ ∈ labellings J d, ∏ v, R v (star Λ v)

/-- Padding to a larger alphabet: labels in A' are read through dec on the set D, and the value is 0
if a label at v lies
outside D. -/
@[expose] public def Inst.pad [Fintype J] [DecidableEq J] [DecidableEq A'] (R : Inst J A) (d : A)
    (D : Finset A') (dec : A' → A) : Inst J A' :=
  fun v θ => if ∀ w, w ≠ v → θ w ∈ D then R v (fun w => if w = v then d else dec (θ w)) else 0

/-! ### Networks -/

/-- A network on J with states in σ and labels in τ. Only Θ a b with a < b is used (see lab); f a b
is the factor on
a's side of the pair {a,b}. The interaction is defined by its factorisation (see Ψ). c is the table
of capacities: plain
numbers, which `value` does not read and on which the structure puts no condition; `U` reads only c,
and `Shaped.card_lab`
asks for at most 2^c labels. -/
public structure Network (J σ τ : Type*) where
  S : J → Finset σ
  W : J → σ → ℤ
  Θ : J → J → Finset τ
  f : J → J → σ → τ → ℤ
  c : J → J → ℕ

namespace Network

/-- The label set of the unordered pair {a,b}. -/
@[expose] public def lab [LinearOrder J] (N : Network J σ τ) (a b : J) : Finset τ := N.Θ (min a b) (max a b)

/-- Ψ_ab(z,z') = Σ_θ f_ab(z,θ) f_ba(z',θ). -/
@[expose] public def Ψ [LinearOrder J] (N : Network J σ τ) (a b : J) (z z' : σ) : ℤ :=
  ∑ θ ∈ N.lab a b, N.f a b z θ * N.f b a z' θ

/-- Z = Σ_z ∏_a W_a(z_a) ∏_{a<b} Ψ_ab(z_a,z_b). -/
@[expose] public def value [Fintype J] [LinearOrder J] (N : Network J σ τ) : ℤ :=
  ∑ z ∈ Fintype.piFinset N.S, (∏ a, N.W a (z a)) * ∏ p ∈ pairs J, N.Ψ p.1 p.2 (z p.1) (z p.2)

/-- U = Σ_{a≠b} c_ab, over ordered pairs. -/
@[expose] public def U [Fintype J] [DecidableEq J] (N : Network J σ τ) : ℕ :=
  ∑ a, ∑ b ∈ univ.erase a, N.c a b

/-- The shape of a network «of size P»: few states, symmetric capacities that sum to at most P at
every node,
and at most 2^c labels on a pair of capacity c. No bound on the values. -/
public structure Shaped [Fintype J] [LinearOrder J] (N : Network J σ τ) (P : ℕ) : Prop where
  card_S : ∀ a, #(N.S a) ≤ 2 ^ P
  c_symm : ∀ a b, N.c a b = N.c b a
  sum_c : ∀ a, ∑ b ∈ univ.erase a, N.c a b ≤ P
  card_lab : ∀ a b, a ≠ b → #(N.lab a b) ≤ 2 ^ N.c a b

/-- «Network of size P» all of whose values are bounded by 2^B. -/
public structure Sized [Fintype J] [LinearOrder J] (N : Network J σ τ) (P B : ℕ) : Prop extends Shaped N P where
  abs_W : ∀ a z, |N.W a z| ≤ 2 ^ B
  abs_f : ∀ a b z θ, |N.f a b z θ| ≤ 2 ^ B
  abs_Ψ : ∀ a b z z', a ≠ b → |N.Ψ a b z z'| ≤ 2 ^ B

/-- Merging along χ : J → J'. A state of the class G is a function on J: a state of a at the members
a of G, s₀ elsewhere.
A label of the classes G < G' is a function on J × J: a label of {a,b} at (a,b) with a in G and b in
G', t₀ elsewhere. -/
@[expose] public def merge [Fintype J] [LinearOrder J] [LinearOrder J'] (N : Network J σ τ) (χ : J → J') (s₀ : σ) (t₀ : τ) :
    Network J' (J → σ) (J × J → τ) where
  S G := tuples (fun a => χ a = G) N.S s₀
  W G z := (∏ a with χ a = G, N.W a (z a)) *
    ∏ p ∈ pairs J with χ p.1 = G ∧ χ p.2 = G, N.Ψ p.1 p.2 (z p.1) (z p.2)
  Θ G G' := tuples (fun p : J × J => χ p.1 = G ∧ χ p.2 = G') (fun p => N.lab p.1 p.2) t₀
  f G G' z t := ∏ p : J × J with χ p.1 = G ∧ χ p.2 = G', N.f p.1 p.2 (z p.1) (t (if G < G' then p else p.swap))
  c G G' := ∑ p : J × J with χ p.1 = G ∧ χ p.2 = G', N.c p.1 p.2

/-- From a network to an instance over A, padding of the label sets included: a label x ∈ A of the
pair {a,b} stands for the label
dec (min a b) (max a b) x of the network if x ∈ D (min a b) (max a b), and the factors vanish at all
other x.
N_a(θ) = Σ_z W_a(z) ∏_{b≠a} f_ab(z,θ_b). -/
@[expose] public def toInst [Fintype J] [LinearOrder J] [DecidableEq A] (N : Network J σ τ)
    (D : J → J → Finset A) (dec : J → J → A → τ) : Inst J A :=
  fun a θ => ∑ z ∈ N.S a, N.W a z *
    ∏ b ∈ univ.erase a, if θ b ∈ D (min a b) (max a b) then N.f a b z (dec (min a b) (max a b) (θ b)) else 0

end Network

end Groundwork
