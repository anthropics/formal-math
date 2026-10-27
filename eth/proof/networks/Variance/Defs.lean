/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Eight.ViaGrouping.Defs

/-! # «Hence Var Y ≤ Σ c_{a,b}·4P = 4PU», summed from the covariances (definitions and statements only)

Proof of Lemma 1, «A good grouping exists»: «Each ordered pair (a,b) contributes with probability
1/K², so 𝔼Y_{γ,γ'} = U/K². The indicators of two ordered pairs have covariance 0 if the pairs are
disjoint and at most 1 otherwise, and by (i) the
ordered pairs that meet a fixed pair have c-values summing to at most 4P. Hence Var Y_{γ,γ'} ≤
Σ_{(a,b)∈[g]²: a≠b} c_{a,b}·4P = 4PU ≤ 4gP².»
proof/networks/Eight/SecNetworks_Grouping.lean states these sentences (`pair_prob`, `mean_Y`,
`cov_disjoint`, `meeting_le`, `var_Y`), but proves `mean_Y` and `var_Y` from the two moments of
proof/networks/Groundwork/Net/Colouring.lean (`sum_Ys`, `sum_Ys_sq`), not from the sentences before
them.
This folder proves them along the printed words: Y is the sum of c_{a,b} times the indicator of
(a,b); so its mean is the sum of the probabilities and its variance is the sum of c_p·c_q·Cov(p,q)
over all pairs of ordered pairs; the disjoint ones give 0, the others at most 1;
for each p the c-values of the q that meet p sum to at most 4P. Then the sentences that rest on the
variance of Y (Chebyshev for Y, the union bound over the pairs of groups) are also proved on top of
this. The sentences on the SIZES of the groups («A group has mean size g/K and variance at most g/K,
so it exceeds 2g/K with probability at most K/g; … some group does so with probability at most K²/g
< 1/3»)
do not rest on the variance of Y; the paper gives no derivation of the two moments of the size, and
their proofs in SecNetworks_Grouping.lean (`mean_size`, `var_size`, `cheb_size`, `some_group`) are
used as they are. So are `total_le` («4PU ≤ 4gP²»: U ≤ gP), `card_pairs_lt`, `Y_symm` and
`exists_good_of` (the last union bound).

**How the statements follow the paper's steps.** A step «hence» is stated, where that is possible,
for ARBITRARY data that satisfy what the paper derives it from (`StHence`, `StChebOfVar`,
`StSomePairOfCheb`): such a statement cannot be proved without using its hypotheses. The other
implications (`StSoMean`, `StGroupingOf`, `StSearchOfGrouping`) are between closed propositions.

As in SecNetworks_Grouping.lean, **probabilities are counts** over the K^g groupings χ : [g] → [K],
with denominators cleared: «Pr(E) = p» reads #{χ | E} = p·K^g. So the covariance of two indicators,
Pr(both) − (1/K²)², is multiplied by K⁴·K^g (`cov`).
This file has no proofs. -/

@[expose] public section

namespace Variance

open Finset Eight.SecNetworks

variable {g K : ℕ}

/-- The ordered pairs (a, b) of distinct nodes. -/
def ordered (g : ℕ) : Finset (Fin g × Fin g) := univ.filter fun p => p.1 ≠ p.2

/-- The ordered pair p = (a, b) «contributes» to Y_{γ,γ'} under the grouping χ: a ∈ G_γ and b ∈
G_{γ'}. -/
abbrev Contributes (γ γ' : Fin K) (χ : Fin g → Fin K) (p : Fin g × Fin g) : Prop := χ p.1 = γ ∧ χ p.2 = γ'

/-- The ordered pair q meets the ordered pair p: they have a node in common. «Disjoint» is the
negation. -/
abbrev Meets (p q : Fin g × Fin g) : Prop := q.1 = p.1 ∨ q.1 = p.2 ∨ q.2 = p.1 ∨ q.2 = p.2

/-- The covariance of the indicators of the ordered pairs p and q (pairs of distinct nodes),
multiplied by K⁴·K^g: Pr(both contribute) − (1/K²)·(1/K²) becomes K⁴·#{χ | both contribute} − K^g. -/
def cov (γ γ' : Fin K) (p q : Fin g × Fin g) : ℤ := (K : ℤ) ^ 4 * (#{χ : Fin g → Fin K | Contributes γ γ' χ p ∧ Contributes γ γ' χ q} : ℕ) - (K : ℤ) ^ g

/-- Y_{γ,γ'} is the sum of c_{a,b} over the ordered pairs that contribute (γ ≠ γ', so a pair (a, a)
never contributes). -/
def StYIsSum : Prop := ∀ (g K : ℕ) (c : Fin g → Fin g → ℕ) (χ : Fin g → Fin K) (γ γ' : Fin K), γ ≠ γ' →
  Y c χ γ γ' = ∑ p ∈ ordered g, if Contributes γ γ' χ p then c p.1 p.2 else 0

/-- «Each ordered pair (a,b) contributes with probability 1/K²». -/
def StPairProb : Prop := ∀ (g K : ℕ) (γ γ' : Fin K), ∀ p ∈ ordered g, #{χ : Fin g → Fin K | Contributes γ γ' χ p} * K ^ 2 = K ^ g

/-- «so 𝔼Y_{γ,γ'} = U/K²». -/
def StMean : Prop := ∀ (g K : ℕ) (c : Fin g → Fin g → ℕ) (γ γ' : Fin K), γ ≠ γ' →
  (∑ χ : Fin g → Fin K, Y c χ γ γ') * K ^ 2 = K ^ g * ∑ a, ∑ b ∈ univ.erase a, c a b

/-- The variance of a sum of multiples of indicators is the sum of the covariances: Var Y_{γ,γ'} =
Σ_p Σ_q c_p·c_q·Cov(p, q), both sides multiplied by K⁴·K^g. The paper uses this without words, in
«Hence». -/
def StVarIsSumOfCov : Prop := ∀ (g K : ℕ) (c : Fin g → Fin g → ℕ) (γ γ' : Fin K), γ ≠ γ' →
  ∑ χ : Fin g → Fin K, (((K ^ 2 : ℕ) : ℤ) * (Y c χ γ γ' : ℕ) - ((∑ a, ∑ b ∈ univ.erase a, c a b : ℕ) : ℤ)) ^ 2
    = ∑ p ∈ ordered g, ∑ q ∈ ordered g, ((c p.1 p.2 : ℕ) : ℤ) * ((c q.1 q.2 : ℕ) : ℤ) * cov γ γ' p q

/-- «The indicators of two ordered pairs have covariance 0 if the pairs are disjoint». -/
def StCovDisjoint : Prop := ∀ (g K : ℕ) (γ γ' : Fin K), ∀ p ∈ ordered g, ∀ q ∈ ordered g, ¬ Meets p q → cov γ γ' p q = 0

/-- «and at most 1 otherwise» (it holds for all pairs). -/
def StCovLeOne : Prop := ∀ (g K : ℕ) (γ γ' : Fin K) (p q : Fin g × Fin g), cov γ γ' p q ≤ (K : ℤ) ^ 4 * (K : ℤ) ^ g

/-- «by (i) the ordered pairs that meet a fixed pair have c-values summing to at most 4P». -/
def StMeeting : Prop := ∀ (g P : ℕ) (c : Fin g → Fin g → ℕ), (∀ a b, c a b = c b a) → (∀ a, ∑ b ∈ univ.erase a, c a b ≤ P) → ∀ p : Fin g × Fin g,
  ∑ q ∈ ordered g with Meets p q, c q.1 q.2 ≤ 4 * P

/-- «Hence Var Y_{γ,γ'} ≤ Σ_{(a,b)∈[g]²: a≠b} c_{a,b}·4P = 4PU»: Σ_χ (Y − U/K²)² ≤ 4PU·K^g,
multiplied by K⁴. Word for word the statement of `Eight.SecNetworks.var_Y`. -/
def StVar : Prop := ∀ (g K P : ℕ) (c : Fin g → Fin g → ℕ), (∀ a b, c a b = c b a) → (∀ a, ∑ b ∈ univ.erase a, c a b ≤ P) → ∀ γ γ' : Fin K, γ ≠ γ' →
  ∑ χ : Fin g → Fin K, (((K ^ 2 : ℕ) : ℤ) * (Y c χ γ γ' : ℕ) - ((∑ a, ∑ b ∈ univ.erase a, c a b : ℕ) : ℤ)) ^ 2
    ≤ ((4 * P * (∑ a, ∑ b ∈ univ.erase a, c a b) * K ^ 4 * K ^ g : ℕ) : ℤ)

/-- **The step «Hence»**, for arbitrary numbers κ(p, q) in the place of the covariances and an
arbitrary bound m ≥ 0 in the place of 1: if κ(p, q) = 0 for disjoint pairs and κ(p, q) ≤ m for all
pairs, then Σ_p Σ_q c_p·c_q·κ(p, q) ≤ Σ_p c_p·4P·m = 4PU·m, for c symmetric with (i). -/
def StHence : Prop := ∀ (g P : ℕ) (c : Fin g → Fin g → ℕ), (∀ a b, c a b = c b a) → (∀ a, ∑ b ∈ univ.erase a, c a b ≤ P) → ∀ (κ : Fin g × Fin g → Fin g × Fin g → ℤ) (m : ℤ), 0 ≤ m →
  (∀ p ∈ ordered g, ∀ q ∈ ordered g, ¬ Meets p q → κ p q = 0) → (∀ p q, κ p q ≤ m) →
  ∑ p ∈ ordered g, ∑ q ∈ ordered g, ((c p.1 p.2 : ℕ) : ℤ) * ((c q.1 q.2 : ℕ) : ℤ) * κ p q ≤ ((4 * P * (∑ a, ∑ b ∈ univ.erase a, c a b) : ℕ) : ℤ) * m

/-- «Hence Var Y ≤ 4PU», put together: the variance is the sum of the covariances; these are 0 for
disjoint pairs and at most 1 otherwise; the step «Hence». -/
def StVarOf : Prop := StVarIsSumOfCov → StCovDisjoint → StCovLeOne → StHence → StVar

/-- «so 𝔼Y = U/K²», with what it rests on in its hypotheses. -/
def StSoMean : Prop := StYIsSum → StPairProb → StMean

/-- «4PU ≤ 4gP²»: U ≤ gP, by (i). (The statement of `Eight.SecNetworks.total_le`.) -/
def StTotalLe : Prop := ∀ (g P : ℕ) (c : Fin g → Fin g → ℕ), (∀ a, ∑ b ∈ univ.erase a, c a b ≤ P) → ∑ a, ∑ b ∈ univ.erase a, c a b ≤ g * P

/-- Var Y_{γ,γ'} ≤ 4PU, for given numbers c, P and groups γ, γ' (multiplied by K⁴·K^g). -/
def VarBound {g K : ℕ} (c : Fin g → Fin g → ℕ) (P : ℕ) (γ γ' : Fin K) : Prop :=
  ∑ χ : Fin g → Fin K, (((K ^ 2 : ℕ) : ℤ) * (Y c χ γ γ' : ℕ) - ((∑ a, ∑ b ∈ univ.erase a, c a b : ℕ) : ℤ)) ^ 2 ≤ ((4 * P * (∑ a, ∑ b ∈ univ.erase a, c a b) * K ^ 4 * K ^ g : ℕ) : ℤ)

/-- Pr(Y_{γ,γ'} > U/K² + gP/K³) ≤ 4K⁶/g, for given numbers c, P and groups γ, γ' (the event
multiplied by K³). -/
def ChebBound {g K : ℕ} (c : Fin g → Fin g → ℕ) (P : ℕ) (γ γ' : Fin K) : Prop :=
  g * #{χ : Fin g → Fin K | K * (∑ a, ∑ b ∈ univ.erase a, c a b) + g * P < K ^ 3 * Y c χ γ γ'} ≤ 4 * K ^ 6 * K ^ g

/-- **«and by Chebyshev Pr(Y_{γ,γ'} > U/K² + gP/K³) ≤ 4K⁶/g»**, from the bound on the variance and U
≤ gP, for arbitrary numbers c and P for which these two hold. -/
def StChebOfVar : Prop := ∀ (g K P : ℕ) (c : Fin g → Fin g → ℕ) (γ γ' : Fin K), γ ≠ γ' → VarBound c P γ γ' → ∑ a, ∑ b ∈ univ.erase a, c a b ≤ g * P → ChebBound c P γ γ'

/-- **«By a union bound over the fewer than K²/2 pairs of groups, some pair violates this bound with
probability less than»** (K²/2)·(4K⁶/g), from the bound for each pair of groups, for arbitrary
symmetric numbers c for which that bound holds. -/
def StSomePairOfCheb : Prop := ∀ (g K P : ℕ) (c : Fin g → Fin g → ℕ), 1 ≤ K → (∀ a b, c a b = c b a) → (∀ γ γ' : Fin K, γ ≠ γ' → ChebBound c P γ γ') →
  g * #{χ : Fin g → Fin K | ∃ γ γ', γ ≠ γ' ∧ K * (∑ a, ∑ b ∈ univ.erase a, c a b) + g * P < K ^ 3 * Y c χ γ γ'} < 2 * K ^ 8 * K ^ g

/-- The paragraph at g = 3K⁸ with the numbers of the text (`Eight.SecNetworks.GroupingFacts`), from
the bound on the variance of Y through the two steps above; its fields on the sizes of the groups
are `Eight.SecNetworks.cheb_size` and `some_group`, and the last union bound is
`Eight.SecNetworks.exists_good_of`. -/
def StGroupingOf : Prop := StVar → StTotalLe → StChebOfVar → StSomePairOfCheb → GroupingFacts

/-- «Go through all K^g groupings (a constant) and fix the first good one»
(`Eight.ViaGrouping.StSearch`), from «a good grouping exists». -/
def StSearchOfGrouping : Prop := GroupingFacts → Eight.ViaGrouping.StSearch

end Variance
