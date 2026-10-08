/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Util.Asymptotics.UpperBounds

/-!
# Running times of Theorems 34 and 35 and Corollary 38, given what their proofs use: definitions

Corollary 38 and Theorem 35 are about algorithms on real numbers, and those of Theorem 35 are
randomized. The word RAM of `EndStatement.lean` has neither random bits nor real numbers, so the
running times of these two items are not stated about programs. Theorem 35 also rests on results
that the paper cites: [CVX22] behind Lemma 36. Theorem 34 is about a deterministic algorithm on
integers. Its running time is not stated about programs because it rests on Theorem 33 (after
[Zwi02] and [CVX21, Theorem 3.1]), which the paper proves and which is not proved here, and on μ,
which is defined through ω(1, μ, 1).

Everything in this file is conditional. No machine model is defined here, and no running time is
proved here. The three theorems `conditional_theorem_34`, `conditional_corollary_38` and
`conditional_theorem_35` are implications between running-time claims, valid for an arbitrary
interpretation `M : TimeModel` of sentences such as "is solved by a deterministic algorithm in time
T" or "is solved by a Las Vegas algorithm in expected time T". They check the paper's deductions of
the kind "Theorem 22 computes each of them in [...] time, and all of them in [...] time" or "answer
every comparison count by Corollary 38", and nothing else. They do not prove Theorem 34, Theorem 35,
Corollary 38 or any other theorem of the paper.

This file contains

* two small notions: `thinDim`, `RealProblem`;
* the record `TimeModel`;
* one closure property of the set of running times (namespace `Closure`), which is a hypothesis like
  the claims;
* the claims, each as a proposition about `M` (namespace `Claim`): time sentences of the paper,
  transfer claims ("if B is solved in time T then A is solved in time extra + calls · T") that the
  paper argues, Theorem 33, and the results it cites from the literature.

What the three theorems assume about `M`:

* two time sentences of Sections 3 and 4: the bound of Theorem 22 for the (min,+)-product (`h22`)
  and the last sentence of Corollary 26 (`h26`). About programs of the word RAM these two
  sentences are proved: `wordRam_theorem_22_second` and `wordRam_corollary_26_wanted`. No link from
  those theorems to `h22` and `h26` is stated or checked: `M` is arbitrary, and the two hypotheses
  are assumed like all the others;
* the transfer claims that the paper argues (cutting a rectangular product into squares in the proof
  of Theorem 34, Lemma 37, the restart argument in the proof of Theorem 35), and one closure
  property;
* Theorem 33, which the paper proves and which is not proved here, and Lemma 36, which rests on
  cited results.

A paragraph that begins with NOTE says where a definition departs from the printed text.

Conventions.

* The parameters of a running time. Sizes and dimensions (`n`, `N`, `m`, `D`) are exact. `w` and `p`
  (at most so many positions or pairs) and `u` (numbers of absolute value at most `u`) are upper
  bounds; `d` is the number of colors and bounds the lengths of the lists.
* Sizes are at least 1 and bounds `u` on numbers are at least 1. The value of a running time at size
  0 or at a bound below 1 has no meaning: `M.problem T` says nothing about it.
* Word length. The intended machine is the paper's word RAM (Section 2); its words are taken to have
  Θ(log of the sum of the size parameters) bits. Numbers need not fit into one word, since `u` is
  not bounded in terms of the size: a number of absolute value at most `u` has about `1 + log u`
  bits, and so takes at most that many words. This is why a factor `1 + log u` appears in an
  overhead. The problems of Section 5.2 are on a real RAM with such words.
* Calls. As in Section 3 of the paper ("the extra time plus the total time to solve B on each
  instance created"), a transfer claim charges a call of an algorithm exactly its running time, and
  everything else to the extra time. An algorithm that is called runs on the caller's machine, whose
  words may be longer than its own input would require.
* `O(·)` with several parameters is written with an explicit constant. For a running time, `O(·)` in
  `n` alone is `UpperBigOPow` or `UpperPowPolylog`: a running time is only ever bounded from
  above. The other quantities of Lemma 36 (numbers of calls, further time) are in the class
  `IsPowPolylog f a`, which says `|f(n)| = O(n^a (log n)^{O(1)})`.
* The paper treats n^μ and n^{1-μ} as integers. Here n^μ is `m = ⌈n^μ⌉` (`thinDim`), and the number
  n^{1-μ} of blocks is `⌈n/m⌉`.
* μ is a real parameter with explicit hypotheses; the exponent of matrix multiplication is not
  defined.
* `log` is the natural logarithm.
-/

@[expose] public section

namespace ThreeSumApsp

/-- Theorem 33: the paper's "n^μ" as a matrix dimension: `⌈n^μ⌉`. -/
noncomputable def thinDim (μ : ℝ) (n : ℕ) : ℕ := ⌈(n : ℝ) ^ μ⌉₊

/-- Theorem 35: the four problems "on real inputs": "3SUM on n numbers", "the (min,+)-product of two
n × n matrices, APSP with no negative cycles, and Exact Triangle". -/
inductive RealProblem : Type
  | threeSum
  | minPlusProduct
  | apsp
  | exactTriangle

namespace ConditionalTimes

/-- An interpretation of the sentences "is solved in time T" for the problems that occur in the
deductions of Sections 5.1 and 5.2. Each field is a predicate on running times. The intended meaning
of `M.problem T`: there is an algorithm that gives a correct answer on every input, and that takes
time at most `T(parameters)` on every input with these parameters. Unless a field says otherwise,
the algorithm is deterministic. The names in parentheses point to the definitions of the problems;
they explain the intended meaning and do not occur in the types. -/
structure TimeModel where
  /-- Theorem 5, and Corollary 26: given `X ∈ ℤ^{N×D}`, `Y ∈ ℤ^{D×N}` with entries
  of absolute value at most `u` and a set of at most `w` positions, compute the entries of `XY` at
  these positions. The arguments of the time are `N D w u`. -/
  thinProduct : (ℕ → ℕ → ℕ → ℝ → ℝ) → Prop
  /-- The (min,+)-product of two `n × n` integer matrices with entries of absolute value at most `u`
  (`IsMinPlusProduct`). Arguments `n u`. -/
  minPlusProduct : (ℕ → ℝ → ℝ) → Prop
  /-- Theorem 33: a deterministic algorithm for the (min,+)-product of an `n × m` matrix by
  an `m × n` matrix, both with integer entries of absolute value at most `u` (`IsMinPlusProduct`).
  The arguments of the time are `n m u`.

  NOTE. Theorem 33 says "can be computed" and adds: "If the algorithm for the product is
  deterministic, then so is the algorithm for APSP." Only this case is expressed. The algorithm that
  the proof of Theorem 34 supplies is deterministic. -/
  rectMinPlus : (ℕ → ℕ → ℝ → ℝ) → Prop
  /-- Theorems 33 and 34: a deterministic algorithm for APSP on directed `n`-vertex graphs with
  integer weights of absolute value at most `u` and no negative cycles. Arguments `n u`.

  NOTE. Theorem 33 says "can be solved" and adds: "If the algorithm for the product is
  deterministic, then so is the algorithm for APSP." Only this case is expressed. Theorem 34 says
  "by a deterministic algorithm". -/
  apsp : (ℕ → ℝ → ℝ) → Prop
  /-- Section 5.2, comparison counts: a deterministic algorithm "whose only operations on real
  numbers are comparisons" (Corollary 38) that, given `n` row lists and `n` column lists of at most
  `d` real numbers with colors in [d] and a set of at most `p` pairs, computes the counts γ(r,c),
  "with < or with ≤" (`ComparisonCounts.comparisonCount`). Arguments `n d p`. -/
  comparisonCounts : (ℕ → ℕ → ℕ → ℝ) → Prop
  /-- Theorem 35: a Las Vegas algorithm "In the real RAM in which the only operations allowed on
  real numbers are comparisons, additions, and subtractions", which never gives a wrong answer,
  solves the problem on inputs of size `n` (`n` numbers, `n × n` matrices, `n` vertices) in expected
  time at most `T n`. -/
  lasVegas : RealProblem → (ℕ → ℝ) → Prop
  /-- Theorem 35: "The bounds also hold with probability 1 - n^{-c}": an algorithm of the
  same kind takes time at most `T n` with probability at least 1 - n^{-c}. The real argument is
  `c`. -/
  lasVegasWhp : RealProblem → ℝ → (ℕ → ℝ) → Prop

namespace Closure

/-- An algorithm for the (min,+)-product of matrices with entries of absolute value at most
`f n u ≥ u` can be run on matrices with entries of absolute value at most `u`. (It is the same
algorithm; `f` is not computed.)

NOTE. This property is not in the paper. It is needed because `Claim.MinPlusInPolylog` bounds the
time only at the bound `n^κ` on the entries (the paper's n^ν), and not at smaller bounds. -/
def RelaxMinPlusBound (M : TimeModel) : Prop :=
  ∀ (T : ℕ → ℝ → ℝ) (f : ℕ → ℝ → ℝ), (∀ (n : ℕ) (u : ℝ), u ≤ f n u) → M.minPlusProduct T →
    M.minPlusProduct fun n u => T n (f n u)

end Closure

namespace Claim

/-! ### The two time sentences of Sections 3 and 4 that the deductions start from -/

/-- **Corollary 26**, last sentence: "Hence, for every set W of positions of an N × N
matrix, the entries (XY)[I,J], (I,J) ∈ W, can be computed deterministically in O(|W| D^{0.437} +
N²/D^{0.063}) time". The hypotheses are those of the first sentence: "Let N ≥ D^18, and let X ∈
ℤ^{N×D} and Y ∈ ℤ^{D×N} have entries of absolute value at most N^{O(1)}." `c` is the exponent hidden
in `N^{O(1)}`; the algorithm and the constant may depend on it.

NOTE. The paper states no lower bound on `D`; `D ≥ 1` is assumed. -/
def Corollary_26_wanted (M : TimeModel) : Prop :=
  ∀ c : ℝ, ∃ (C : ℝ) (T : ℕ → ℕ → ℕ → ℝ → ℝ), M.thinProduct T ∧
    ∀ (N D w : ℕ) (u : ℝ), 1 ≤ D → D ^ 18 ≤ N → u ≤ (N : ℝ) ^ c →
      T N D w u ≤ C * ((w : ℝ) * (D : ℝ) ^ (0.437 : ℝ) + (N : ℝ) ^ 2 / (D : ℝ) ^ (0.063 : ℝ))

/-- **Theorem 22**, the form of its bounds for the (min,+)-product: "Let ν be a constant. [...]
deterministic algorithms solve [...] the (min,+)-product of two n × n integer matrices with entries
of absolute value at most n^ν [...] in Õ(n^{3−1/1944}) [...] time. Using Corollary 26 instead, the
times are [...] Õ(n^{3−ε'/3})". `a` is the exponent and `κ` the paper's ν; the algorithm and the
constants may depend on `κ`. With `ε' = 0.00175` (Theorem 19), the second bound is
`MinPlusInPolylog M (3 - 0.00175 / 3)`.

NOTE. `κ ≥ 0` is assumed. -/
def MinPlusInPolylog (M : TimeModel) (a : ℝ) : Prop :=
  ∀ κ : ℝ, 0 ≤ κ → ∃ T : ℕ → ℝ → ℝ, M.minPlusProduct T ∧
    UpperPowPolylog (fun n => T n ((n : ℝ) ^ κ)) a

/-! ### 5.1 Directed APSP with small integer weights -/

/-- Proof of Theorem 34, as a transfer claim: "Cut the n × n^μ matrix into n^{1-μ}
blocks of n^μ consecutive rows, and the n^μ × n matrix into n^{1-μ} blocks of n^μ consecutive
columns. The (min,+)-product then consists of n^{2-2μ} products of two n^μ × n^μ matrices, one for
each pair of blocks."

NOTE. The paper treats n^μ and n^{1-μ} as integers. Here an `n × m` by `m × n` product has `⌈n/m⌉²`
pairs of blocks, of which the last may have to be padded, and the claim also allows
`C₀ m² (1 + log u)` for copying a pair of blocks and its product, which does not change the bound of
the proof. -/
def RectMinPlusFromSquare (M : TimeModel) : Prop :=
  ∃ C₀ : ℝ, ∀ T : ℕ → ℝ → ℝ, M.minPlusProduct T →
    M.rectMinPlus fun n m u =>
      (⌈(n : ℝ) / (m : ℝ)⌉₊ : ℝ) ^ 2 * (T m u + C₀ * ((m : ℝ) ^ 2 * (1 + logU u)))

/-- **Theorem 33** (after [Zwi02] and [CVX21, Theorem 3.1]), which the paper proves. The proof is
not formalized; the theorem is a hypothesis of `conditional_theorem_34`. "If the (min,+)-product of
an n × n^μ matrix by an n^μ × n matrix, both with integer entries of absolute value at most
Õ(n^{1-μ}), can be computed in O(n^{2+μ-ε₁}) time for a constant ε₁ > 0, then APSP in directed
n-vertex graphs with integer weights of absolute value polylog n and no negative cycles can be
solved in O(n^{2+μ-ε''}) time for a constant ε'' > 0 that depends on ε₁ and μ. If the algorithm for
the product is deterministic, then so is the algorithm for APSP." `μ` stands for the solution of
ω(1,μ,1) = 1 + 2μ.

NOTE. Both algorithms are deterministic here: this is the case of the last sentence, and the only
one that is expressed. "Õ(n^{1-μ})" is read as n^{1-μ}(log n + 1)^e for every natural number e,
which makes the premise stronger and so the claim weaker; the algorithm may depend on e. "polylog n"
is read as (log n + 1)^c for every natural number c, which covers (log n)^c for every constant c. -/
def Theorem_33 (M : TimeModel) (μ : ℝ) : Prop :=
  ∀ ε₁ : ℝ, 0 < ε₁ →
    (∀ e : ℕ, ∃ T : ℕ → ℕ → ℝ → ℝ, M.rectMinPlus T ∧
      UpperBigOPow (fun n => T n (thinDim μ n) ((n : ℝ) ^ (1 - μ) * (Real.log n + 1) ^ e))
        (2 + μ - ε₁)) →
    ∃ ε'' : ℝ, 0 < ε'' ∧ ∀ c : ℕ, ∃ T' : ℕ → ℝ → ℝ, M.apsp T' ∧
      UpperBigOPow (fun n => T' n ((Real.log n + 1) ^ c)) (2 + μ - ε'')

/-- **Theorem 34**: "There is a constant ε'' > 0 such that APSP in directed unweighted
n-vertex graphs, and more generally in directed n-vertex graphs with integer weights of absolute
value at most (log n)^c and no negative cycles, for any constant c, can be solved in O(n^{2+μ-ε''})
time by a deterministic algorithm." (Unweighted graphs are the case c = 0.)

NOTE. (log n)^c is read as (log n + 1)^c with a natural number c, as in `Theorem_33`. -/
def Theorem_34 (M : TimeModel) (μ : ℝ) : Prop :=
  ∃ ε'' : ℝ, 0 < ε'' ∧ ∀ c : ℕ, ∃ T' : ℕ → ℝ → ℝ, M.apsp T' ∧
    UpperBigOPow (fun n => T' n ((Real.log n + 1) ^ c)) (2 + μ - ε'')

/-! ### 5.2 3SUM, APSP, and Exact Triangle with real inputs -/

/-- **Lemma 37**, with the padding step of the proof of Corollary 38, as a transfer claim: "we can
build matrices X ∈ {0,…,d}^{n×D''} and Y ∈ {0,…,d}^{D''×n} and compute integers γ₂(r,c), (r,c) ∈ P,
with γ(r,c) = (XY)[r,c] + γ₂(r,c) for every (r,c) ∈ P, deterministically in O(nD'' + (|P| + nds +
ds²) log n) time", and "pad the product to the inner dimension D*". The block length `s` and the
padded inner dimension `Din` are given functions of `n` and `d`; they are parameters of the claim
because the algorithm has to compute them. Where the hypotheses on them fail, nothing is claimed
about the time.

NOTE. `log n` is written `log n + 1`, and nD'' is written `n * Din`, as in the proof of Corollary
38. `1 ≤ d ≤ n` is the standing assumption of Section 5.2 ("Throughout, d ∈ [n] is a parameter").
The last two sentences of the lemma, on the operations on real numbers and on ≤, belong to the
intended meaning of `M.comparisonCounts`. The time to compute `s` and `Din` is not charged
separately; the statements use the claim only for `s = blockLen` and `Din = Dstar`.
`M.comparisonCounts T'` speaks of an algorithm that is correct on every input, also where the
hypotheses on `s` and `Din` fail. -/
def Lemma_37 (M : TimeModel) (s Din : ℕ → ℕ → ℕ) : Prop :=
  ∃ C₀ : ℝ, ∀ T : ℕ → ℕ → ℕ → ℝ → ℝ, M.thinProduct T →
    ∃ T' : ℕ → ℕ → ℕ → ℝ, M.comparisonCounts T' ∧
      ∀ n d p : ℕ, 1 ≤ n → 1 ≤ d → d ≤ n → 1 ≤ s n d → ComparisonCounts.D'' n d (s n d) ≤ Din n d →
        T' n d p ≤ T n (Din n d) p d +
          C₀ * ((n : ℝ) * (Din n d : ℝ) +
            ((n : ℝ) * (d : ℝ) * (s n d : ℝ) + (d : ℝ) * (s n d : ℝ) ^ 2 + (p : ℝ)) *
              (Real.log n + 1))

/-- **Corollary 38**: "Let d ≤ n^{1/40}, and let n be larger than a suitable constant.
Given row lists R_r and column lists C_c as above and a set P ⊆ [n]², the counts γ(r,c), (r,c) ∈ P,
with < or with ≤, can be computed deterministically in O(|P| n^{0.0229} + n²/d^{0.126} + n^{2-1/440}
log n) time, by an algorithm whose only operations on real numbers are comparisons."

NOTE. `d ≥ 1` is the standing assumption of Section 5.2 ("Throughout, d ∈ [n] is a parameter"). As
in `Lemma_37`, `M.comparisonCounts T` speaks of an algorithm that is correct on every input, also
where the hypotheses on `n` and `d` fail. -/
def Corollary_38 (M : TimeModel) : Prop :=
  ∃ (C : ℝ) (n₀ : ℕ) (T : ℕ → ℕ → ℕ → ℝ), M.comparisonCounts T ∧
    ∀ n d p : ℕ, n₀ ≤ n → 1 ≤ d → (d : ℝ) ≤ (n : ℝ) ^ (1 / 40 : ℝ) →
      T n d p ≤ C * ((p : ℝ) * (n : ℝ) ^ (0.0229 : ℝ) + (n : ℝ) ^ 2 / (d : ℝ) ^ (0.126 : ℝ)
        + (n : ℝ) ^ (2 - 1 / 440 : ℝ) * Real.log n)

/-- CITED in part. **Lemma 36(a)**, after [CVX22, Section 3.2, Lemmas 3.4 and 4.2],
as a transfer claim, for one of the three problems (`prob` is meant to be `minPlusProduct`, `apsp`
or `exactTriangle`): they "reduce, with Las Vegas randomization, to Õ(n/d) counting calls and
Õ(n³/d) further time. A counting call consists of d comparison counts, each with n row lists and n
column lists of at most d numbers [...] and with pair sets P_1, …, P_d satisfying ∑_k |P_k| = n²;
forming its lists costs O(nd²) subtractions." `d` is a given function of `n` with 1 ≤ d ≤ n. `calls`
is the number of counting calls and `further` the further time; `B` is any bound on the cost of the
d comparison counts of a call, whatever the sizes `p k` of the pair sets.

NOTE. The clause "with at most one number of each color in a list" (left out in the quotation) is
dropped: `M.comparisonCounts` speaks of arbitrary lists, so the claim is weaker without it. `calls`,
`further` and `C₀` may depend on the function `d`, while the bounds of the paper are uniform in d;
this too makes the claim weaker. The statements use it only for `d = listLen`, which is ⌊n^{1/40}⌋.
The type does not exclude `prob = threeSum`. The last two sentences of Lemma 36, on ≤ and on the
operations on real numbers, belong to the intended meaning of `M.comparisonCounts` and
`M.lasVegas`; so also in `Lemma_36b`. -/
def Lemma_36a (M : TimeModel) (prob : RealProblem) (d : ℕ → ℕ) : Prop :=
  (∀ n : ℕ, 1 ≤ n → 1 ≤ d n ∧ d n ≤ n) →
  ∃ (calls further : ℕ → ℝ) (C₀ : ℝ), (∀ n, 0 ≤ calls n) ∧
    IsPowPolylog (fun n => calls n * (d n : ℝ)) 1 ∧
    IsPowPolylog (fun n => further n * (d n : ℝ)) 3 ∧
    ∀ T : ℕ → ℕ → ℕ → ℝ, M.comparisonCounts T →
      ∃ T' : ℕ → ℝ, M.lasVegas prob T' ∧
        ∀ (n : ℕ) (B : ℝ), 1 ≤ n →
          (∀ p : Fin (d n) → ℕ, ∑ k, p k = n ^ 2 → ∑ k, T n (d n) (p k) ≤ B) →
          T' n ≤ calls n * (B + C₀ * ((n : ℝ) * (d n : ℝ) ^ 2)) + further n

/-- CITED in part. **Lemma 36(b)**, after [CVX22, Section 3.3, Lemmas 3.9 and 4.6], as a transfer
claim: "3SUM on n real numbers reduces, with Las Vegas randomization, to polylogarithmically many
comparison counts, each with n row lists and n column lists of at most d numbers, all of the same
color, and a pair set P of size O(n²/d), and Õ(n²/d) further time; forming the lists of a comparison
count costs O(nd) subtractions." `Num` is the number of comparison counts, `K n²/d` the bound on the
size of P.

NOTE. That the numbers are "all of the same color" is not used: the comparison counts are answered
by an algorithm for arbitrary colors. `Num`, `further`, `C₀` and `K` may depend on the function `d`,
as in `Lemma_36a`. -/
def Lemma_36b (M : TimeModel) (d : ℕ → ℕ) : Prop :=
  (∀ n : ℕ, 1 ≤ n → 1 ≤ d n ∧ d n ≤ n) →
  ∃ (Num further : ℕ → ℝ) (C₀ K : ℝ), (∀ n, 0 ≤ Num n) ∧
    IsPowPolylog Num 0 ∧ IsPowPolylog (fun n => further n * (d n : ℝ)) 2 ∧
    ∀ T : ℕ → ℕ → ℕ → ℝ, M.comparisonCounts T →
      M.lasVegas RealProblem.threeSum fun n =>
        Num n * (T n (d n) ⌈K * (n : ℝ) ^ 2 / (d n : ℝ)⌉₊ + C₀ * ((n : ℝ) * (d n : ℝ))) + further n

/-- Proof of Theorem 35, "Las Vegas, and high probability", as a transfer claim: "we stop a run that
exceeds twice the bound on its expected time and start again, and c log₂ n runs all fail with
probability at most n^{-c}." The time is that of the runs, each of length 2T(n), up to a constant
factor.

NOTE. The number of runs is written `c log₂ n + 1` and the length of a run `T n + 1`, so that the
bound does not vanish where `c log₂ n` or `T n` is zero. The claim is made for every `T`, whether
the algorithm knows it or not; for a `T` that it does not know, a variant serves: interleave the
runs step by step and stop with the first that ends. `c ≥ 0` is assumed. -/
def Restart (M : TimeModel) : Prop :=
  ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ (prob : RealProblem) (T : ℕ → ℝ) (c : ℝ), 0 ≤ c → M.lasVegas prob T →
    M.lasVegasWhp prob c fun n => C₀ * ((c * Real.logb 2 n + 1) * (T n + 1))

/-- A Las Vegas algorithm solves the problem in `O(n^a)` expected time. -/
def LasVegasIn (M : TimeModel) (prob : RealProblem) (a : ℝ) : Prop :=
  ∃ T : ℕ → ℝ, M.lasVegas prob T ∧ UpperBigOPow T a

/-- The bound `O(n^a)` holds with probability 1 - n^{-c}, for every constant c (Theorem 35: "The
bounds also hold with probability 1 - n^{-c} for any constant c").

NOTE. The algorithm may depend on `c`, and it need not be the algorithm of `LasVegasIn`: the proof
of Theorem 35 obtains it from that algorithm by restarting. `c ≥ 0` is assumed. -/
def LasVegasWhpIn (M : TimeModel) (prob : RealProblem) (a : ℝ) : Prop :=
  ∀ c : ℝ, 0 ≤ c → ∃ T : ℕ → ℝ, M.lasVegasWhp prob c T ∧ UpperBigOPow T a

/-- **Theorem 35** (also the second half of **Theorem 2**): "In the real RAM in which the only
operations allowed on real numbers are comparisons, additions, and subtractions, Las Vegas
algorithms solve the following problems on real inputs: 3SUM on n numbers in O(n^{1.998}) expected
time, and the (min,+)-product of two n × n matrices, APSP with no negative cycles, and Exact
Triangle in O(n^{2.998}) expected time. The bounds also hold with probability 1 - n^{-c} for any
constant c."

NOTE. The opening clause, on the real RAM and its operations, is not expressed by the proposition;
it is part of the intended meaning of `M.lasVegas` and `M.lasVegasWhp`. The two halves speak of
separate algorithms; see `LasVegasWhpIn`. -/
def Theorem_35 (M : TimeModel) : Prop :=
  (LasVegasIn M .threeSum 1.998 ∧ LasVegasIn M .minPlusProduct 2.998 ∧ LasVegasIn M .apsp 2.998 ∧
    LasVegasIn M .exactTriangle 2.998) ∧
  (LasVegasWhpIn M .threeSum 1.998 ∧ LasVegasWhpIn M .minPlusProduct 2.998 ∧
    LasVegasWhpIn M .apsp 2.998 ∧ LasVegasWhpIn M .exactTriangle 2.998)

end Claim

end ConditionalTimes

end ThreeSumApsp
