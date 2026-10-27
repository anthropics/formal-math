/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import AppVariablesStatement
public import ToTuring.PolyT
public import StepMachines.Prog.Chunks

/-! # Lemma 13 (Family of checks) for the family that a program lists: «In time polynomial in m one can list sets Γ_u, u ∈ Ω»

The field GF(2^s) as a program. An element is a word of s bits, lowest bit first: the word (b_0, …,
b_(s−1)) stands for the residue of b_0 + b_1·X + … + b_(s−1)·X^(s−1) modulo a polynomial
X^s + g of degree s over the field with two elements; the word g of s bits holds the coefficients of
the lower part. Addition is `xorW`; multiplication by X is `mulX` (shift, and add g if the top
bit was set); multiplication is `mulW` (Horner's rule over the bits of the second factor); powers
are `powW` (repeated multiplication).

«An irreducible polynomial of degree s is found by search»: `modW s` is the first word g of s bits,
in the order of the numbers 0, 1, …, 2^s − 1, that passes the test `irrW`: every word other than 0
has an inverse under `mulW g`. The text does not say which test it means; for s ≥ 1 this one holds
exactly if X^s + g is irreducible (`irrW_iff`, proof/variables/VariableBound/Field/Search.lean).

`famD m a` is the list of the sets Γ_u, u ∈ Ω, for m clauses and v = 2^a, with s = ⌈log₂(16m)⌉; the
clauses are the numbers E < m, ι(E) = E, and ϑ_E is the word of s bits of the number E.
The two statements at the end are what the rest of Appendix D uses. -/

@[expose] public section

namespace VariableBound.Fld

open Groundwork

/-! ## The arithmetic -/

/-- The sum of two elements: bit by bit. -/
def xorW (x y : List Bool) : List Bool := (x.zip y).map fun p => xor p.1 p.2

/-- The word 0, as long as g. -/
def zeroW (g : List Bool) : List Bool := g.map fun _ => false

/-- The word 1, as long as g (if g is not empty). -/
def oneW (g : List Bool) : List Bool := true :: g.tail.map fun _ => false

/-- X·w modulo X^s + g: shift by one place, and add g if the top bit of w was set. -/
def mulX (g w : List Bool) : List Bool :=
  if w.getLast?.getD false then xorW ((false :: w).take w.length) g else (false :: w).take w.length

/-- x·y modulo X^s + g, by Horner's rule over the bits of y: x·(b + X·y') = b·x + X·(x·y'). -/
def mulW (g x y : List Bool) : List Bool :=
  y.foldr (fun b c => if b then xorW x (mulX g c) else mulX g c) (zeroW g)

/-- u^e modulo X^s + g, by repeated multiplication; u^0 = 1 also for u = 0. -/
def powW (g u : List Bool) (e : ℕ) : List Bool := (List.range e).foldl (fun c _ => mulW g c u) (oneW g)

/-- The inner product modulo 2 of two words. -/
def ipW (x y : List Bool) : Bool := decide (((x.zip y).countP fun p => p.1 && p.2) % 2 = 1)

/-! ## The search for the polynomial -/

/-- All words of s bits, in the order of the numbers 0, 1, …, 2^s − 1 that they write, lowest bit
first. -/
def wordsL (s : ℕ) : List (List Bool) := (List.range (2 ^ s)).map (toWord s)

/-- The test: every word of s bits other than 0 has an inverse modulo X^s + g, where s is the length
of g. -/
def irrW (g : List Bool) : Bool :=
  (wordsL g.length).all fun x => decide (x = zeroW g) || (wordsL g.length).any fun y => decide (mulW g x y = oneW g)

/-- The lower part of the first polynomial of degree s that passes the test. -/
def modW (s : ℕ) : List Bool := ((wordsL s).find? irrW).getD []

/-! ## The family -/

/-- Γ_u for u = (u₁, u₂, u₃, u₄), as the increasing list of the numbers E < m of its clauses: the
first a − 1 bits of u₁·ϑ_E + u₂ are 0, and ⟨u₃^E, u₄⟩ = 1. -/
def gamW (m a : ℕ) (g : List Bool) (u : List Bool × List Bool × List Bool × List Bool) : List ℕ :=
  (List.range m).filter fun E =>
    (((xorW (mulW g u.1 (toWord g.length E)) u.2.1).take (a - 1)).all fun b => !b) && ipW (powW g u.2.2.1 E) u.2.2.2

/-- The number s of bits: 16m ≤ 2^s < 32m for m ≥ 1. -/
def sD (m : ℕ) : ℕ := Nat.clog 2 (16 * m)

/-- The list of the sets Γ_u, u ∈ Ω, for m clauses and v = 2^a: all u ∈ 𝔽⁴ in lexicographic order,
those with |Γ_u| > 16m/v left out. -/
def famD (m a : ℕ) : List (List ℕ) :=
  ((wordsL (sD m) ×ˢ wordsL (sD m) ×ˢ wordsL (sD m) ×ˢ wordsL (sD m)).map (gamW m a (modW (sD m)))).filter fun l =>
    decide (2 ^ a * l.length ≤ 16 * m)

/-- A list of numbers of clauses as a set of clauses. -/
def setD (m : ℕ) (l : List ℕ) : Finset (Fin m) := Finset.univ.filter fun E => E.val ∈ l

/-! ## The statements -/

/-- Lemma 13 (Family of checks) for the listed family: for v = 2^a with 2 ≤ v ≤ m, the list is not
empty and has fewer than (32m)⁴ members, every member is an increasing list of numbers below m, and
the members, indexed by their places in the list, have (a), (b), (c). -/
def StFamD : Prop := ∀ m a : ℕ, 1 ≤ a → 2 ^ a ≤ m →
  famD m a ≠ [] ∧ (famD m a).length < (32 * m) ^ 4 ∧
  (∀ l ∈ famD m a, l.Pairwise (· < ·) ∧ l.Nodup ∧ ∀ E ∈ l, E < m) ∧
  AppVariables.IsFamily (2 ^ a) (Finset.univ : Finset (Fin (famD m a).length)) fun i => setD m ((famD m a).get i)

/-- Lemma 13 (Family of checks), second sentence: the list is computed in polynomial time, jointly
in m and a, both given in unary. -/
def StCertFamD : Prop := ∀ (α : Type) [Enc α] (m a : α → ℕ), Unary m → Unary a → PolyT fun x => famD (m x) (a x)

end VariableBound.Fld
