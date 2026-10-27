/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import Mathlib.RingTheory.Binomial
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Data.Finsupp.Multiset
public import Mathlib.Data.PNat.Basic
public import Mathlib.Data.Multiset.Sort
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import PiecesStatement
public import PartitionStatement

/-! # Appendix B: the ring V = ℚ[t₁, t₂, …], its operators a[r] and Q_s(a,b), the two lemmas on them, and the pieces with ρ = 1/√2

Definitions and statements only, in the order and in the words of the appendix; imports Mathlib and
the two statement files `PiecesStatement.lean` (pieces with parameters (ρ, c), without the
running time) and `PartitionStatement.lean` (the number p(E) of partitions). Every `def … : Prop` or
`structure … : Prop` below is a statement of the appendix; nothing is proved here.

Sums that the appendix writes as infinite sums with finitely many nonzero terms are `∑ᶠ` (Mathlib's
`finsum`, which is 0 if infinitely many terms are nonzero); each comes with the
statement that only finitely many terms are nonzero. -/

@[expose] public section

namespace AppHalfPieces

open Finset MvPolynomial

/-! ## The ring and its operators -/

/-- C(k, j) = k(k−1)⋯(k−j+1)/j! for integers k and j ≥ 0, and 0 for j < 0. -/
def binom (k j : ℤ) : ℤ := if 0 ≤ j then Ring.choose k j.toNat else 0

/-- Pascal's rule and Vandermonde's identity hold for all integers k, k'. (In the sum over j only
the terms with 0 ≤ j ≤ i are nonzero.) -/
structure BinomRules : Prop where
  pascal : ∀ k j : ℤ, binom (k + 1) (j + 1) = binom k j + binom k (j + 1)
  vandermonde : ∀ (k k' : ℤ) (i : ℕ), ∑ j ∈ range (i + 1), binom k (i - j) * binom k' j = binom (k + k') i

/-- A partition is a multiset of positive integers, its parts. -/
abbrev Ptn : Type := Multiset ℕ+

/-- |μ|, the sum of the parts: μ is a partition of |μ|. -/
def wt (μ : Ptn) : ℕ := (μ.map fun k : ℕ+ => (k : ℕ)).sum

/-- z_μ = ∏_k k^{m_k(μ)}·m_k(μ)!, where m_k(μ) = `μ.count k` is the number of parts equal to k. -/
def zz (μ : Ptn) : ℕ := ∏ k ∈ μ.toFinset, (k : ℕ) ^ μ.count k * (μ.count k).factorial

/-- The partitions of E. -/
def ptns (E : ℕ) : Finset Ptn := (univ : Finset (Nat.Partition E)).image fun q => q.parts.map Nat.toPNat'

/-- The partitions of an integer E; none if E < 0. -/
def ptnsZ (E : ℤ) : Finset Ptn := if 0 ≤ E then ptns E.toNat else ∅

/-- p(E) for an integer E: p(0) = 1 and p(E) = 0 for E < 0. -/
def pZ (E : ℤ) : ℕ := if 0 ≤ E then Partitions.p E.toNat else 0

/-- The partitions of E are the multisets of positive integers with sum E, there are p(E) of them,
and p(E) ≤ p(E+1). -/
structure PtnFacts : Prop where
  mem : ∀ (E : ℕ) (μ : Ptn), μ ∈ ptns E ↔ wt μ = E
  card : ∀ E : ℕ, #(ptns E) = Partitions.p E
  mono : ∀ E : ℕ, Partitions.p E ≤ Partitions.p (E + 1)

/-- V = ℚ[t₁, t₂, …]. -/
abbrev V : Type := MvPolynomial ℕ+ ℚ

/-- The monomial t^μ = ∏_i t_{μ_i}. -/
noncomputable def tpow (μ : Ptn) : V := monomial (Multiset.toFinsupp μ) 1

/-- The coefficient of t^μ in f. -/
noncomputable def coef (μ : Ptn) (f : V) : ℚ := coeff (Multiset.toFinsupp μ) f

/-- V_E, the span of the t^μ with |μ| = E: the polynomials of weight E. V_E = 0 for E < 0. -/
noncomputable def VE (E : ℤ) : Submodule ℚ V :=
  if 0 ≤ E then weightedHomogeneousSubmodule ℚ (fun k : ℕ+ => (k : ℕ)) E.toNat else ⊥

/-- The positive integer |k|, for an integer k ≠ 0. -/
def pn (k : ℤ) : ℕ+ := k.natAbs.toPNat'

/-- ∇_{−k} f = t_k·f and ∇_k f = k·∂f/∂t_k for k ≥ 1. (∇₀ is not defined in the appendix; here it is 0.) -/
noncomputable def nabla (k : ℤ) (f : V) : V :=
  if k < 0 then X (pn k) * f else if 0 < k then (k : ℚ) • pderiv (pn k) f else 0

/-- The choices in display (47): one nonzero integer k_i for each part μ_i, with Σ_i k_i = −r. -/
def Choices (μ : List ℕ+) (r : ℤ) : Set (List ℤ) := {ks | ks.length = μ.length ∧ (∀ k ∈ ks, k ≠ 0) ∧ ks.sum = -r}

/-- One term of display (47), applied to f: ∏_i C(−k_i−1, μ_i−1) · ∏_{i: k_i<0} ∇_{k_i} · ∏_{i:
k_i>0} ∇_{k_i}. The differentiations are applied first. -/
noncomputable def term (μ : List ℕ+) (ks : List ℤ) (f : V) : V :=
  (((List.zipWith (fun (m : ℕ+) (k : ℤ) => binom (-k - 1) ((m : ℤ) - 1)) μ ks).prod : ℤ) : ℚ) •
    (ks.filter (· < 0)).foldr nabla ((ks.filter (0 < ·)).foldr nabla f)

/-- Display (47): a[r] for the monomial a = t^μ whose parts are listed in μ. -/
noncomputable def opMon (μ : List ℕ+) (r : ℤ) (f : V) : V := ∑ᶠ ks ∈ Choices μ r, term μ ks f

/-- a[r] for all a ∈ V: display (47), extended linearly. -/
noncomputable def op (a : V) (r : ℤ) (f : V) : V := ∑ m ∈ a.support, coeff m a • opMon (Finsupp.toMultiset m).toList r f

/-- What the appendix says with display (47): on every f only finitely many terms are nonzero; the
order in which the parts are listed does not matter; a[r] is linear in f and in a;
and for a monomial it is the sum (47). -/
structure OpFacts : Prop where
  finite : ∀ (μ : List ℕ+) (r : ℤ) (f : V), {ks ∈ Choices μ r | term μ ks f ≠ 0}.Finite
  perm : ∀ (μ μ' : List ℕ+) (r : ℤ) (f : V), μ.Perm μ' → opMon μ r f = opMon μ' r f
  mono : ∀ (μ : List ℕ+) (r : ℤ) (f : V), op (tpow (μ : Multiset ℕ+)) r f = opMon μ r f
  add_right : ∀ (a : V) (r : ℤ) (f f' : V), op a r (f + f') = op a r f + op a r f'
  smul_right : ∀ (a : V) (r : ℤ) (q : ℚ) (f : V), op a r (q • f) = q • op a r f
  add_left : ∀ (a a' : V) (r : ℤ) (f : V), op (a + a') r f = op a r f + op a' r f
  smul_left : ∀ (a : V) (r : ℤ) (q : ℚ) (f : V), op (q • a) r f = q • op a r f

/-- All coefficients are integers. -/
def IsInt (f : V) : Prop := ∀ m, ∃ z : ℤ, coeff m f = z

/-- (O1): a[r] maps V_E to V_{E+r}, so a[r]f = 0 if f ∈ V_E and E + r < 0; it maps integer
polynomials to integer polynomials if a is one; and 1[r] = [r = 0]·Id. -/
structure O1 : Prop where
  maps : ∀ (a : V) (r E : ℤ) (f : V), f ∈ VE E → op a r f ∈ VE (E + r)
  zero : ∀ (a : V) (r E : ℤ) (f : V), f ∈ VE E → E + r < 0 → op a r f = 0
  int : ∀ (a : V) (r : ℤ) (f : V), IsInt a → IsInt f → IsInt (op a r f)
  one : ∀ (r : ℤ) (f : V), op 1 r f = if r = 0 then f else 0

/-- The number a[−h]·b, for b ∈ V_h. -/
noncomputable def pairing (h : ℕ) (a b : V) : ℚ := coeff 0 (op a (-(h : ℤ)) b)

/-- (O3): if b ∈ V_h, then a[−h]·b ∈ V₀ is a number, and only terms with all k_i positive contribute
to it. -/
structure O3 : Prop where
  number : ∀ (h : ℕ) (a b : V), b ∈ VE h → op a (-(h : ℤ)) b = C (pairing h a b)
  positive : ∀ (h : ℕ) (μ : List ℕ+) (b : V) (ks : List ℤ), b ∈ VE h → ks ∈ Choices μ (-(h : ℤ)) → (∃ k ∈ ks, k < 0) → term μ ks b = 0

/-- ā_{h'}, the part of a of weight h'. -/
noncomputable def part (h' : ℕ) (a : V) : V := weightedHomogeneousComponent (fun k : ℕ+ => (k : ℕ)) h' a

/-- a = Σ_{h'=0}^{h} ā_{h'} with ā_{h'} ∈ V_{h'}. -/
def WtLe (h : ℕ) (a : V) : Prop := a = ∑ h' ∈ range (h + 1), part h' a

/-- a^⟨i⟩ = Σ_{h'} C(h'+h, i)·ā_{h'}. -/
noncomputable def angle (h i : ℕ) (a : V) : V := ∑ h' ∈ range (h + 1), ((h' + h).choose i : ℚ) • part h' a

/-- Display (48): Q_s(a,b) = Σ_{i=0}^{2h} (−1)^i·a^⟨i⟩[s−h+i] b[h−s−i]. -/
noncomputable def Q (h : ℕ) (s : ℤ) (a b f : V) : V :=
  ∑ i ∈ range (2 * h + 1), (-1 : ℚ) ^ i • op (angle h i a) (s - h + i) (op b (h - s - i) f)

/-- The same with the two factors exchanged in all products. -/
noncomputable def Q' (h : ℕ) (s : ℤ) (a b f : V) : V :=
  ∑ i ∈ range (2 * h + 1), (-1 : ℚ) ^ i • op b (h - s - i) (op (angle h i a) (s - h + i) f)

/-- The lemma on the operators Q_s. Let h ≥ 1, b ∈ V_h and a = Σ_{h' ≤ h} ā_{h'}. On V_E, for every
E ≥ 0: (a) Q_s(a,b) does not change if the two factors are exchanged in all products of (48)
at once; (b) Q_s(a,b) = 0 for |s| > E + h; (c) Σ_{|s| ≤ E+h} Q_s(a,b) = (a[−h]b)·Id. -/
structure LemmaQ : Prop where
  a : ∀ (h : ℕ) (a b : V), 1 ≤ h → b ∈ VE h → WtLe h a → ∀ (E : ℕ) (f : V), f ∈ VE E → ∀ s : ℤ, Q h s a b f = Q' h s a b f
  b : ∀ (h : ℕ) (a b : V), 1 ≤ h → b ∈ VE h → WtLe h a → ∀ (E : ℕ) (f : V), f ∈ VE E → ∀ s : ℤ, (E : ℤ) + h < |s| → Q h s a b f = 0
  c : ∀ (h : ℕ) (a b : V), 1 ≤ h → b ∈ VE h → WtLe h a → ∀ (E : ℕ) (f : V), f ∈ VE E →
    ∑ s ∈ Icc (-((E : ℤ) + h)) ((E : ℤ) + h), Q h s a b f = pairing h a b • f

/-- y_n = Σ_{j=1}^{n} C(n,j)·t_j. -/
noncomputable def y (n : ℕ+) : V := ∑ j ∈ Icc 1 (n : ℕ), ((n : ℕ).choose j : ℚ) • X j.toPNat'

/-- a^μ = ∏_i (−1)^{μ_i−1}·y_{μ_i}. -/
noncomputable def aFam (μ : Ptn) : V := (μ.map fun n : ℕ+ => (-1 : ℚ) ^ ((n : ℕ) - 1) • y n).prod

/-- b^μ = (h!/z_μ)·t^μ, for a partition μ of h. -/
noncomputable def bFam (μ : Ptn) : V := (((wt μ).factorial : ℚ) / zz μ) • tpow μ

/-- The lemma on the dual families: a^μ[−h]·b^ν = h!·[μ = ν] for all partitions μ, ν of h. -/
def LemmaDual : Prop := ∀ (h : ℕ) (μ ν : Ptn), wt μ = h → wt ν = h → op (aFam μ) (-(h : ℤ)) (bFam ν) = C (if μ = ν then (h.factorial : ℚ) else 0)

/-- h!/z_μ is an integer. -/
def ZDvd : Prop := ∀ μ : Ptn, zz μ ∣ (wt μ).factorial

/-! ## The pieces -/

/-- The least integer h ≥ 2 with p(h) ≥ 2^λ. -/
noncomputable def hOf (lam : ℕ) : ℕ := sInf {h | 2 ≤ h ∧ 2 ^ lam ≤ Partitions.p h}

/-- Such an h exists, so `hOf lam` is the least integer h ≥ 2 with p(h) ≥ 2^λ. -/
def HOfSpec : Prop := ∀ lam : ℕ, 2 ≤ hOf lam ∧ 2 ^ lam ≤ Partitions.p (hOf lam) ∧ ∀ h, 2 ≤ h → 2 ^ lam ≤ Partitions.p h → hOf lam ≤ h

/-- A partition written as a nonincreasing sequence. -/
def desc (μ : Ptn) : List ℕ := (μ.map fun k : ℕ+ => (k : ℕ)).sort (· ≥ ·)

/-- The number of μ, counting from 0, in the lexicographic list of the partitions of h written as
nonincreasing sequences: the number of partitions of h that come before μ. -/
def lexNum (h : ℕ) (μ : Ptn) : ℕ := #{ν ∈ ptns h | desc ν < desc μ}

/-- A string read as an integer, first bit lowest. (The appendix does not say which bit is the
lowest.) -/
def val {lam : ℕ} (x : Pieces.Bits lam) : ℕ := ∑ i : Fin lam, if x i then 2 ^ (i : ℕ) else 0

/-- μ(x) is the partition of h with number x in that list. -/
def IsMu (lam h : ℕ) (mu : Pieces.Bits lam → Ptn) : Prop := ∀ x, mu x ∈ ptns h ∧ lexNum h (mu x) = val x

/-- A_s(x,y,u,v) = the coefficient of t^{μ(u)} in Q_s(a^{μ(x)}, b^{μ(v)})·t^{μ(y)}. -/
noncomputable def piece {lam : ℕ} (h : ℕ) (mu : Pieces.Bits lam → Ptn) (s : ℤ) (x y u v : Pieces.Bits lam) : ℚ :=
  coef (mu u) (Q h s (aFam (mu x)) (bFam (mu v)) (tpow (mu y)))

/-- R^row_s = Σ_{i=0}^{2h} p(s+i). -/
def Rrow (h : ℕ) (s : ℤ) : ℕ := ∑ i ∈ range (2 * h + 1), pZ (s + i)

/-- R^col_s = Σ_{i=0}^{2h} p(2h−s−i). -/
def Rcol (h : ℕ) (s : ℤ) : ℕ := ∑ i ∈ range (2 * h + 1), pZ (2 * h - s - i)

/-- The steps of the proof of the theorem on the pieces that are statements about the ring, for
partitions μ(x), μ(y), μ(u), μ(v) of h ≥ 1, written ξ, η, υ, ν. -/
structure PieceFacts : Prop where
  /-- a^μ is a combination of monomials of weight at most h, as (48) requires. -/
  wtLe : ∀ (h : ℕ) (μ : Ptn), wt μ = h → WtLe h (aFam μ)
  /-- Σ_s A_s = h!·[x = v]·[y = u]. -/
  sum : ∀ (h : ℕ) (ξ η υ ν : Ptn), 1 ≤ h → wt ξ = h → wt η = h → wt υ = h → wt ν = h →
    ∑ s ∈ Icc (-(2 * h : ℤ)) (2 * h), coef υ (Q h s (aFam ξ) (bFam ν) (tpow η)) = if ξ = ν ∧ η = υ then (h.factorial : ℚ) else 0
  /-- Display (54). -/
  row : ∀ (h : ℕ) (ξ η υ ν : Ptn) (s : ℤ), 1 ≤ h → wt ξ = h → wt η = h → wt υ = h → wt ν = h →
    coef υ (Q h s (aFam ξ) (bFam ν) (tpow η)) = ∑ i ∈ range (2 * h + 1), ∑ σ ∈ ptnsZ (s + i),
      (-1 : ℚ) ^ i * coef σ (op (angle h i (aFam ξ)) (s - h + i) (tpow η)) * coef υ (op (bFam ν) (h - s - i) (tpow σ))
  /-- Display (55). -/
  col : ∀ (h : ℕ) (ξ η υ ν : Ptn) (s : ℤ), 1 ≤ h → wt ξ = h → wt η = h → wt υ = h → wt ν = h →
    coef υ (Q h s (aFam ξ) (bFam ν) (tpow η)) = ∑ i ∈ range (2 * h + 1), ∑ σ ∈ ptnsZ (2 * h - s - i),
      (-1 : ℚ) ^ i * coef υ (op (angle h i (aFam ξ)) (s - h + i) (tpow σ)) * coef σ (op (bFam ν) (h - s - i) (tpow η))
  /-- All factors are integers. -/
  int_a : ∀ (h i : ℕ) (ξ σ : Ptn) (r : ℤ), IsInt (op (angle h i (aFam ξ)) r (tpow σ))
  int_b : ∀ (ν σ : Ptn) (r : ℤ), IsInt (op (bFam ν) r (tpow σ))
  /-- The numbers of terms are both at least 1. -/
  terms : ∀ (h : ℕ) (s : ℤ), |s| ≤ 2 * h → 1 ≤ Rrow h s ∧ 1 ≤ Rcol h s

/-- The theorem on the pieces with ρ = 1/√2, with the construction of its proof and without the
running time: for an absolute constant c and every λ ≥ 1, with h = `hOf λ` and μ(x) the partition of
h with number x in the lexicographic list, the functions A_s, s ∈ {−2h, …, 2h}, with d = h!, c^row_s =
⌈log R^row_s⌉ and c^col_s = ⌈log R^col_s⌉, have the properties (a), (b) and the sizes of
(c) of pieces with parameters (1/√2, c). -/
def ThmHalfPiecesPure : Prop := ∃ c : ℕ, ∀ lam : ℕ, 1 ≤ lam → ∃ (mu : Pieces.Bits lam → Ptn) (P : Pieces.Family lam),
  IsMu lam (hOf lam) mu ∧ P.Is (1 / Real.sqrt 2) c ∧ P.d = (hOf lam).factorial ∧ P.I = Icc (-(2 * hOf lam : ℤ)) (2 * hOf lam) ∧
    (∀ s x y u v, (P.A s x y u v : ℚ) = piece (hOf lam) mu s x y u v) ∧
    (∀ s, P.crow s = Nat.clog 2 (Rrow (hOf lam) s)) ∧ ∀ s, P.ccol s = Nat.clog 2 (Rcol (hOf lam) s)

end AppHalfPieces
