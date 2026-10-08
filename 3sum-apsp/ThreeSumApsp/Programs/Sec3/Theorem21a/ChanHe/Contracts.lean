/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Lang.Tasks
public import ThreeSumApsp.Sec3.Theorem21a.ChanHe.Definitions
public import ThreeSumApsp.Util.Flag

/-!
# The reduction from 3SUM to Convolution-3SUM after Chan and He, as a program.  Specifications

Theorem 21(a), after [CH20, Theorem 5.1].  This file contains no program
and no proof.  It states the specifications of the routines of the reduction: the general library,
the routines below the recursion tree, the tree, and the routines that prepare the splittings.  The
proof of a routine uses only the specifications of the routines that it calls.

* The pure models are the definitions of the reduction themselves (`ChanHe.coll`, `heavy`,
  `modulus`, `Node.oneArray`, `nodes`, …), applied to finite sets.  A set lies in the memory as a
  list without repetitions, in any order, with its length passed beside its address (`SetAt`).
* The specification of a routine is a proposition `XSpec lim P p …`: "procedure number `p` of the
  program `P`, run on these arguments in a memory that satisfies this, ends within `tX` steps with
  this result in a memory that satisfies that" (`Meets`).  It is proved for every program that holds
  the body of X at the number `p` and meets the specifications of the routines that X calls.
* The last argument of most routines is the free pointer `fr`; such a routine writes only its output
  segments, the count table (which it leaves as it found it), and cells from `fr` on.
* The count table: `cap` cells from `cnt`, below every free pointer, all zeros between calls
  (`ZeroAt`).  A routine that uses it clears what it wrote.
* Time functions are definitions.  The time function of a caller is written in terms of those of its
  callees.
* Limits: one hypothesis `(xNeed …).Ok lim fr d`, or a field of the structure that collects the
  hypotheses of the routine.
-/

@[expose] public section

namespace Light.Sec3.ChanHe

open ThreeSumApsp ThreeSumApsp.ChanHe Finset

/-! ## Vocabulary -/

/-- The `len` cells from `a` hold the elements of the set `S`, each once, in some order. -/
def SetAt (μ : ℕ → ℤ) (a len : ℕ) (S : Finset ℤ) : Prop :=
  ∃ L : List ℤ, L.length = len ∧ Seg μ a L ∧ L.Nodup ∧ L.toFinset = S

/-- The `cap` cells from `cnt` hold zeros. -/
def ZeroAt (μ : ℕ → ℤ) (cnt cap : ℕ) : Prop := ∀ r < cap, μ (cnt + r) = 0

/-! ## Time functions and needs -/

/-- The time of a remainder of a number of absolute value at most `V`. -/
def tEmod (V : ℕ) : ℕ := 60 * (Nat.log 2 (V + 1) + 1) + 40
/-- What a remainder needs: words for doubled multiples of the modulus, and a cell for each of
them. -/
def emodNeed (V M : ℕ) : Need := ⟨4 * V + 4 * M + 16, Nat.log 2 (V + 1) + 2, 0⟩

/-- The remainders of `len` numbers. -/
def tResid (len V : ℕ) : ℕ := len * (tEmod V + 30) + 20
/-- One pass over `len` remainders that changes their counts. -/
def tTally (len : ℕ) : ℕ := 30 * len + 20
/-- The colliding pairs of a set of `len` numbers: remainders, counting, a pass that adds up, and
removing the counts. -/
def tColl (len V : ℕ) : ℕ := tResid len V + 2 * tTally len + 30 * len + 60
/-- The heavy elements of a set of `len` numbers: remainders, counting, a pass that copies, and
removing the counts. -/
def tHeavy (len V : ℕ) : ℕ := tResid len V + 2 * tTally len + 40 * len + 60
/-- One search: every candidate prime costs three collision counts. -/
def tSearch (np l₁ l₂ l₃ V : ℕ) : ℕ := np * (tColl l₁ V + tColl l₂ V + tColl l₃ V + 120) + 40
/-- The modulus of a node: two searches, and the collision counts modulo the first prime. -/
def tModulus (np l₁ l₂ l₃ V : ℕ) : ℕ := 2 * tSearch np l₁ l₂ l₃ V + tColl l₁ V + tColl l₂ V +
  tColl l₃ V + 160
/-- The array of a node: the padding pattern, and for each of the three sets remainders, counting, a
pass that writes, and removing the counts. -/
def tNodeArray (m l₁ l₂ l₃ V : ℕ) : ℕ :=
  80 * (2 * m ^ 2) + (tResid l₁ V + tResid l₂ V + tResid l₃ V) +
    2 * (tTally l₁ + tTally l₂ + tTally l₃) + 60 * (l₁ + l₂ + l₃) + 200

/-- The words that the routines below the tree need, for sets of at most `n` numbers of absolute
value at most `V` and moduli up to `M`: products of a collision count and a number of primes,
thresholds of the searches, entries and indices of the arrays. -/
def wordNeed (n V M : ℕ) : ℕ := 64 * (n + 1) ^ 2 * (M + 1) * (V + 1)

/-- The needs.  A caller's need covers its callees': the remainders of a set take `len` cells, a
long division `log₂ (V + 1) + 2`; the depth is the number of levels of calls below the routine. -/
def residNeed (len V M : ℕ) : Need := ⟨wordNeed len V M, Nat.log 2 (V + 1) + 2, 1⟩
/-- The need of coll and of heavy. -/
def collNeed (len V M : ℕ) : Need := ⟨wordNeed len V M, len + Nat.log 2 (V + 1) + 2, 2⟩
/-- The need of modulus; the moduli are at most `m²`. -/
def modulusNeed (n V m : ℕ) : Need := ⟨wordNeed n V (m * m), n + Nat.log 2 (V + 1) + 2, 4⟩
/-- The need of nodeArray. -/
def nodeArrayNeed (n V m : ℕ) : Need := ⟨wordNeed n V (m * m), n + Nat.log 2 (V + 1) + 2, 2⟩

/-! ## The generic library

The logarithms, the remainder, the sieve and sorting of the general library meet these
specifications (`EmodSpec` is below). -/

/-- The time of log2. -/
def tLog2 (x : ℕ) : ℕ := 30 * (Nat.log 2 x + 1) + 20

/-- log2(x) returns `⌊log₂ x⌋` (0 for `x = 0`); it touches no cell. -/
def Log2Spec (lim : Limits) (P : Program) (p : ℕ) : Prop :=
  ∀ (d x : ℕ) (μ : ℕ → ℤ), (4 * x + 4 : ℤ) ≤ lim.word →
    Meets lim P p d [x] μ (tLog2 x) fun r μ' => r = (Nat.log 2 x : ℤ) ∧ μ' = μ

/-- clog2(x) returns `⌈log₂ x⌉` (0 for `x ≤ 1`); it touches no cell. -/
def Clog2Spec (lim : Limits) (P : Program) (p : ℕ) : Prop :=
  ∀ (d x : ℕ) (μ : ℕ → ℤ), (4 * x + 4 : ℤ) ≤ lim.word →
    Meets lim P p d [x] μ (tLog2 x + 30) fun r μ' => r = (Nat.clog 2 x : ℤ) ∧ μ' = μ

/-- The time of the sieve. -/
def tPrimes (m : ℕ) : ℕ := 60 * m * (Nat.log 2 m + 2) + 60
/-- The need of the sieve: a table of `m + 1` cells. -/
def primesNeed (m : ℕ) : Need := ⟨4 * m + 16, m + 1, 0⟩

/-- primes(m, out, fr) writes the primes up to `m` in ascending order to `out` (room for `m` cells)
and returns their number. -/
def PrimesSpec (lim : Limits) (P : Program) (p : ℕ) : Prop :=
  ∀ (d fr m out : ℕ) (μ : ℕ → ℤ), out + m ≤ fr → (primesNeed m).Ok lim fr d →
    Meets lim P p d [m, out, fr] μ (tPrimes m) fun r μ' =>
      r = (#(Nat.primesLE m) : ℤ) ∧
        Seg μ' out (((Nat.primesLE m).sort (· ≤ ·)).map fun q : ℕ => (q : ℤ)) ∧
        KeptBut μ μ' fr out m

/-- The time of sorting. -/
def tSort (n : ℕ) : ℕ := 80 * n * (Nat.log 2 n + 2) + 60
/-- The need of sorting: `n` cells, and a level of calls for each halving. -/
def sortNeed (n V : ℕ) : Need := ⟨2 * V + 4 * n + 16, n, Nat.log 2 n + 2⟩

/-- sort(n, a, fr) sorts the `n` cells from `a` in place, in ascending order. -/
def SortSpec (lim : Limits) (P : Program) (p : ℕ) : Prop :=
  ∀ (d fr a V : ℕ) (L : List ℤ) (μ : ℕ → ℤ), Seg μ a L → AbsLe L V → a + L.length ≤ fr →
    (sortNeed L.length V).Ok lim fr d →
    Meets lim P p d [L.length, a, fr] μ (tSort L.length) fun _ μ' =>
      (∃ L' : List ℤ, Seg μ' a L' ∧ L'.Perm L ∧ L'.Pairwise (· ≤ ·)) ∧ KeptBut μ μ' fr a L.length

/-! ## Remainders, counts, collisions, heavy elements -/

/-- emod(x, M, fr) returns `x % M`, for `M ≥ 1`. -/
def EmodSpec (lim : Limits) (P : Program) (p : ℕ) : Prop :=
  ∀ (d fr V M : ℕ) (x : ℤ) (μ : ℕ → ℤ), 1 ≤ M → |x| ≤ (V : ℤ) → (emodNeed V M).Ok lim fr d →
    Meets lim P p d [x, M, fr] μ (tEmod V) fun r μ' => r = x % (M : ℤ) ∧ Kept μ μ' fr

/-- resid(len, s, sg, M, key, fr) writes the remainders of `sg · x` modulo `M`, for the `len`
numbers `x` from `s`, to `key`.  `sg` is 1 or -1. -/
def ResidSpec (lim : Limits) (P : Program) (p : ℕ) : Prop :=
  ∀ (d fr V M s key : ℕ) (sg : ℤ) (L : List ℤ) (μ : ℕ → ℤ), 1 ≤ M → (sg = 1 ∨ sg = -1) → AbsLe L V →
    Seg μ s L →
    s + L.length ≤ fr → key + L.length ≤ fr → Apart s L.length key L.length →
    (residNeed L.length V M).Ok lim fr d →
    Meets lim P p d [L.length, s, sg, M, key, fr] μ (tResid L.length V) fun _ μ' =>
      Seg μ' key (L.map fun x => (sg * x) % (M : ℤ)) ∧ KeptBut μ μ' fr key L.length

/-- tally(len, key, cnt, δ) adds `δ` to the cell `cnt + k` for each of the `len` numbers `k` from
`key`. -/
def TallySpec (lim : Limits) (P : Program) (p : ℕ) : Prop :=
  ∀ (d key cnt cap : ℕ) (δ : ℤ) (K : List ℕ) (μ : ℕ → ℤ), (∀ k ∈ K, k < cap) → (δ = 1 ∨ δ = -1) →
    Seg μ key (K.map fun k : ℕ => (k : ℤ)) → Apart key K.length cnt cap →
    (∀ r < cap, |μ (cnt + r)| ≤ (K.length : ℤ)) →
    key + K.length ≤ lim.space → cnt + cap ≤ lim.space → (lim.space : ℤ) ≤ lim.word →
    (2 * K.length + 2 : ℤ) ≤ lim.word →
    Meets lim P p d [K.length, key, cnt, δ] μ (tTally K.length) fun _ μ' =>
      (∀ r < cap, μ' (cnt + r) = μ (cnt + r) + δ * (K.count r : ℤ)) ∧ SameOutside μ μ' cnt cap

/-- A set of `len` numbers of absolute value at most `V` at `s`, and a table of zeros at `cnt` with
a cell for each remainder modulo `M`; both below the free pointer, and apart. -/
structure BucketMem (μ : ℕ → ℤ) (fr V M s len cnt cap : ℕ) (S : Finset ℤ) : Prop where
  modulus_pos : 1 ≤ M
  modulus_le : M ≤ cap
  bdd : Bdd V S
  set : SetAt μ s len S
  zero : ZeroAt μ cnt cap
  belowSet : s + len ≤ fr
  belowTable : cnt + cap ≤ fr
  apart : Apart s len cnt cap

/-- coll(len, s, M, cnt, fr) returns the number of colliding ordered pairs of the set at `s` modulo
`M`. -/
def CollSpec (lim : Limits) (P : Program) (p : ℕ) : Prop :=
  ∀ (d fr V M s len cnt cap : ℕ) (S : Finset ℤ) (μ : ℕ → ℤ), BucketMem μ fr V M s len cnt cap S →
    (collNeed len V M).Ok lim fr d →
    Meets lim P p d [len, s, M, cnt, fr] μ (tColl len V) fun r μ' =>
      r = (coll S M : ℤ) ∧ Kept μ μ' fr

/-- Where the output of heavy stands: below the free pointer, apart from the set and the table. -/
structure HeavyOut (fr s cnt cap out len : ℕ) : Prop where
  below : out + len ≤ fr
  apartSet : Apart s len out len
  apartTable : Apart out len cnt cap

/-- heavy(len, s, M, out, cnt, fr) writes the heavy elements of the set at `s` modulo `M` to `out`
(room for `len` cells) and returns their number. -/
def HeavySpec (lim : Limits) (P : Program) (p : ℕ) : Prop :=
  ∀ (d fr V M s len out cnt cap : ℕ) (S : Finset ℤ) (μ : ℕ → ℤ),
    BucketMem μ fr V M s len cnt cap S → HeavyOut fr s cnt cap out len →
    (collNeed len V M).Ok lim fr d →
    Meets lim P p d [len, s, M, out, cnt, fr] μ (tHeavy len V) fun r μ' =>
      r = (#(heavy S M) : ℤ) ∧ SetAt μ' out #(heavy S M) (heavy S M) ∧ KeptBut μ μ' fr out len

/-! ## The modulus of a node -/

/-- The primes up to `m`, in ascending order, lie in the `np` cells from `pr`. -/
def PrimesAt (μ : ℕ → ℤ) (pr np m : ℕ) : Prop :=
  np = #(Nat.primesLE m) ∧ Seg μ pr (((Nat.primesLE m).sort (· ≤ ·)).map fun q : ℕ => (q : ℤ))

/-- A set in the memory: the address and the length of its list, and the set. -/
structure Slot : Type where
  (addr len : ℕ)
  set : Finset ℤ

/-- What the routines below the recursion tree share: the free pointer `fr`; the bounds `n` on the
sizes of the sets and `V` on their elements; the bound `m` on the primes, their number `np` and the
address `pr` of their list; the address `cnt` of the count table of `m²` cells. -/
structure Env : Type where
  (fr n V m np pr cnt : ℕ)

/-- The primes up to `m` and the count table are in the memory, below the free pointer and apart. -/
structure Env.Ok (μ : ℕ → ℤ) (e : Env) : Prop where
  primes : PrimesAt μ e.pr e.np e.m
  zero : ZeroAt μ e.cnt (e.m * e.m)
  belowPr : e.pr + e.np ≤ e.fr
  belowCnt : e.cnt + e.m * e.m ≤ e.fr
  apartPr : Apart e.pr e.np e.cnt (e.m * e.m)

/-- A set of at most `n` numbers of absolute value at most `V` is in the memory, below the free
pointer and apart from the count table. -/
structure Slot.Ok (μ : ℕ → ℤ) (e : Env) (X : Slot) : Prop where
  set : SetAt μ X.addr X.len X.set
  le : X.len ≤ e.n
  bdd : Bdd e.V X.set
  below : X.addr + X.len ≤ e.fr
  apart : Apart X.addr X.len e.cnt (e.m * e.m)

/-- A node of the recursion tree in the memory: its three sets, and what the routines share. -/
structure NodeArgs : Type extends Env where
  (X₁ X₂ X₃ : Slot)

/-- The addresses and lengths of the three sets, as the routines are given them. -/
@[simp] abbrev NodeArgs.sets (a : NodeArgs) : List ℤ :=
  [a.X₁.addr, a.X₁.len, a.X₂.addr, a.X₂.len, a.X₃.addr, a.X₃.len]

/-- The three sets of a node, the primes and the count table are in the memory. -/
structure NodeMem (μ : ℕ → ℤ) (a : NodeArgs) : Prop where
  envOk : a.toEnv.Ok μ
  set₁ : a.X₁.Ok μ a.toEnv
  set₂ : a.X₂.Ok μ a.toEnv
  set₃ : a.X₃.Ok μ a.toEnv

/-- The arguments of search: a node, the factor `mult` of the moduli, and a bound for each set. -/
structure SearchArgs : Type extends NodeArgs where
  (mult b₁ b₂ b₃ : ℕ)

/-- The values of the arguments of search. -/
@[simp] abbrev SearchArgs.vals (x : SearchArgs) : List ℤ :=
  (x.mult : ℤ) :: x.sets ++ [(x.b₁ : ℤ), x.b₂, x.b₃, x.np, x.pr, x.cnt, x.fr]

/-- A candidate `q` is good: each of the three sets has at most `bᵢ / np` colliding pairs modulo
`mult · q`. -/
def SearchArgs.Good (x : SearchArgs) (q : ℕ) : Prop :=
  coll x.X₁.set (x.mult * q) * x.np ≤ x.b₁ ∧ coll x.X₂.set (x.mult * q) * x.np ≤ x.b₂ ∧
    coll x.X₃.set (x.mult * q) * x.np ≤ x.b₃

instance (x : SearchArgs) : DecidablePred x.Good := fun q => by
  unfold SearchArgs.Good
  infer_instance

/-- The need of search. -/
def searchNeed (n V m : ℕ) : Need := ⟨wordNeed n V (m * m), n + Nat.log 2 (V + 1) + 2, 3⟩

/-- search(mult, s₁, l₁, s₂, l₂, s₃, l₃, b₁, b₂, b₃, np, pr, cnt, fr) returns the least good prime
up to `m`, and 1 if there is none. -/
def SearchSpec (lim : Limits) (P : Program) (p : ℕ) : Prop :=
  ∀ (x : SearchArgs) (μ : ℕ → ℤ), NodeMem μ x.toNodeArgs → 1 ≤ x.mult → x.mult ≤ x.m →
    ∀ d, (searchNeed x.n x.V x.m).Ok lim x.fr d →
    Meets lim P p d x.vals μ (tSearch x.np x.X₁.len x.X₂.len x.X₃.len x.V) fun r μ' =>
      r = (pick {q ∈ Nat.primesLE x.m | x.Good q} : ℤ) ∧ Kept μ μ' x.fr

/-- The values of the arguments of modulus. -/
@[simp] abbrev NodeArgs.modulusVals (a : NodeArgs) (Λ : ℕ) : List ℤ :=
  a.sets ++ [(Λ : ℤ), a.np, a.pr, a.cnt, a.fr]

/-- modulus(s₁, l₁, s₂, l₂, s₃, l₃, Λ, np, pr, cnt, fr) returns the modulus of the node. -/
def ModulusSpec (lim : Limits) (P : Program) (p : ℕ) : Prop :=
  ∀ (a : NodeArgs) (Λ : ℕ) (μ : ℕ → ℤ), NodeMem μ a → Λ ≤ a.V + 2 →
    ∀ d, (modulusNeed a.n a.V a.m).Ok lim a.fr d →
    Meets lim P p d (a.modulusVals Λ) μ
      (tModulus a.np a.X₁.len a.X₂.len a.X₃.len a.V) fun r μ' =>
      r = (modulus (Nat.primesLE a.m) Λ a.X₁.set a.X₂.set a.X₃.set : ℤ) ∧ Kept μ μ' a.fr

/-! ## The array of a node -/

/-- Where the array of a node is written: `8 m²` cells from `y`, below the free pointer and apart
from the three sets and the count table. -/
structure NodeArrayOut (a : NodeArgs) (y : ℕ) : Prop where
  below : y + 8 * a.m ^ 2 ≤ a.fr
  apart₁ : Apart y (8 * a.m ^ 2) a.X₁.addr a.X₁.len
  apart₂ : Apart y (8 * a.m ^ 2) a.X₂.addr a.X₂.len
  apart₃ : Apart y (8 * a.m ^ 2) a.X₃.addr a.X₃.len
  apartCnt : Apart y (8 * a.m ^ 2) a.cnt (a.m * a.m)

/-- nodeArray(M, s₁, l₁, s₂, l₂, s₃, l₃, V, m, y, cnt, fr) writes the first `8 m²` cells of the
one-array instance of the node to `y`. -/
def NodeArraySpec (lim : Limits) (P : Program) (p : ℕ) : Prop :=
  ∀ (a : NodeArgs) (M y : ℕ) (μ : ℕ → ℤ), NodeMem μ a → 1 ≤ M → M ≤ a.m * a.m →
    NodeArrayOut a y →
    ∀ d, (nodeArrayNeed a.n a.V a.m).Ok lim a.fr d →
    Meets lim P p d ((M : ℤ) :: a.sets ++ [(a.V : ℤ), a.m, y, a.cnt, a.fr]) μ
      (tNodeArray a.m a.X₁.len a.X₂.len a.X₃.len a.V) fun _ μ' =>
      (∀ u < 8 * a.m ^ 2,
        μ' (y + u) = Node.oneArray ⟨a.X₁.set, a.X₂.set, a.X₃.set, M⟩ a.V u) ∧
        KeptBut μ μ' a.fr y (8 * a.m ^ 2)

/-! ## The recursion tree -/

/-- The number of calls of the recursive procedure: one for the triple, and those of the three
children if the triple is a node. -/
def treeCalls (Q : Finset ℕ) (Λ : ℕ) : ℕ → Finset ℤ → Finset ℤ → Finset ℤ → ℕ
  | 0, _, _, _ => 1
  | f + 1, S₁, S₂, S₃ =>
    if S₁ = ∅ ∨ S₂ = ∅ ∨ S₃ = ∅ then 1 else
      1 + (treeCalls Q Λ f (heavy S₁ (modulus Q Λ S₁ S₂ S₃)) S₂ S₃ +
        treeCalls Q Λ f S₁ (heavy S₂ (modulus Q Λ S₁ S₂ S₃)) S₃ +
        treeCalls Q Λ f S₁ S₂ (heavy S₃ (modulus Q Λ S₁ S₂ S₃)))

/-- The cost of one node, when a Convolution-3SUM solver takes `T N B` steps: the modulus, the
array, the call, and the three sets of heavy elements. -/
def tNode (T : ℕ → ℕ → ℕ) (n V m np : ℕ) : ℕ :=
  tModulus np n n n V + tNodeArray m n n n V + T (8 * m ^ 2) (60 * V + 40) + 3 * tHeavy n V + 300

/-- The time of the recursive procedure. -/
def tNodes (T : ℕ → ℕ → ℕ) (n V m np calls : ℕ) : ℕ := calls * (tNode T n V m np + 60)

/-- What the recursive procedure needs with `f` levels to go: a set of heavy elements for each
level, one array, and what the solver needs. -/
def nodesNeed (r : ℕ → ℕ → Need) (n V m f : ℕ) : Need :=
  ⟨max (modulusNeed n V m).word (r (8 * m ^ 2) (60 * V + 40)).word,
    f * n + 8 * m ^ 2 + max (modulusNeed n V m).cells (r (8 * m ^ 2) (60 * V + 40)).cells,
    f + 1 + max (modulusNeed n V m).depth (r (8 * m ^ 2) (60 * V + 40)).depth⟩

/-- The block of parameters that the recursive procedure gets by its address `cx`: `V`, `m`, `Λ`,
`np`, `pr`, `cnt`. -/
def CtxAt (μ : ℕ → ℤ) (cx V m Λ np pr cnt : ℕ) : Prop := Seg μ cx [(V : ℤ), m, Λ, np, pr, cnt]

/-- What the recursive procedure assumes with `f` levels to go: the memory of a node, the block of
parameters at `cx`, below the free pointer and apart from the count table, and the limits. -/
structure NodesPre (lim : Limits) (r : ℕ → ℕ → Need) (μ : ℕ → ℤ) (a : NodeArgs) (Λ cx f d : ℕ) :
    Prop where
  mem : NodeMem μ a
  ctx : CtxAt μ cx a.V a.m Λ a.np a.pr a.cnt
  belowCtx : cx + 6 ≤ a.fr
  apartCtx : Apart cx 6 a.cnt (a.m * a.m)
  V_pos : 1 ≤ a.V
  m_pos : 1 ≤ a.m
  lam : Λ = Lam a.V
  primes : (Nat.primesLE a.m).Nonempty
  ok : (nodesNeed r a.n a.V a.m f).Ok lim a.fr d

/-- The number of calls of the procedure for the tree with `f` levels below a node. -/
abbrev NodeArgs.calls (a : NodeArgs) (Λ f : ℕ) : ℕ :=
  treeCalls (Nat.primesLE a.m) Λ f a.X₁.set a.X₂.set a.X₃.set

/-- Some node of the tree of a three-set input gives a yes-instance. -/
def TreeYes (m Λ f V : ℕ) (S₁ S₂ S₃ : Finset ℤ) : Prop :=
  ∃ ν ∈ nodes (Nat.primesLE m) Λ f S₁ S₂ S₃, ConvOne (8 * m ^ 2) (ν.oneArray V)

/-- The one-array instance of some node of the tree with `f` levels below a node in the memory is a
yes-instance. -/
abbrev NodeArgs.Yes (a : NodeArgs) (Λ f : ℕ) : Prop :=
  TreeYes a.m Λ f a.V a.X₁.set a.X₂.set a.X₃.set

/-- The specification of nodes for trees with `f` levels: see `NodesSpec`. -/
def NodesSpecAt (lim : Limits) (P : Program) (p : ℕ) (T : ℕ → ℕ → ℕ) (r : ℕ → ℕ → Need) (f : ℕ) :
    Prop :=
  ∀ (a : NodeArgs) (Λ cx : ℕ) (μ : ℕ → ℤ) (d : ℕ), NodesPre lim r μ a Λ cx f d →
    Meets lim P p d ((f : ℤ) :: a.sets ++ [(cx : ℤ), a.fr]) μ
      (tNodes T a.n a.V a.m a.np (a.calls Λ f)) fun res μ' =>
        res = ThreeSumApsp.flag (a.Yes Λ f) ∧ Kept μ μ' a.fr

/-- nodes(f, s₁, l₁, s₂, l₂, s₃, l₃, cx, fr) returns 1 if the one-array instance of some node of the
tree with `f` levels is a yes-instance at length `8 m²`, and 0 if not.  `T` and `r` are the time and
the need of the Convolution-3SUM solver that it calls. -/
def NodesSpec (lim : Limits) (P : Program) (p : ℕ) (T : ℕ → ℕ → ℕ) (r : ℕ → ℕ → Need) : Prop :=
  ∀ f, NodesSpecAt lim P p T r f

/-! ## The front: distinct values, multiplicities, binary digits, the splittings -/

/-- The time of distinct. -/
def tDistinct (n : ℕ) : ℕ := 60 * n + 40
/-- The time of twice. -/
def tTwice (n : ℕ) : ℕ := 60 * n + 40
/-- The time of zeroThree. -/
def tZeroThree (n : ℕ) : ℕ := 40 * n + 40
/-- The time of bits. -/
def tBits (len Λ : ℕ) : ℕ := len * (60 * Λ + 40) + 40 * Λ + 60
/-- The time of pick. -/
def tPick (len : ℕ) : ℕ := 90 * len + 40

/-- What distinct assumes: the sorted list stands at `a`; the three regions lie in the memory and do
not meet; addresses and counts fit in a word. -/
structure Distinct.Ctx (lim : Limits) (μ : ℕ → ℤ) (a val mul : ℕ) (L : List ℤ) : Prop where
  sorted : L.Pairwise (· ≤ ·)
  seg : Seg μ a L
  apartVal : Apart a L.length val L.length
  apartMul : Apart a L.length mul L.length
  apart : Apart val L.length mul L.length
  spaceSrc : a + L.length ≤ lim.space
  spaceVal : val + L.length ≤ lim.space
  spaceMul : mul + L.length ≤ lim.space
  space_le : (lim.space : ℤ) ≤ lim.word
  word : (2 * L.length + 8 : ℤ) ≤ lim.word

/-- distinct(n, a, val, mul): the `n` cells from `a` hold a sorted list.  Writes its distinct values
to `val` and how often each occurs to `mul` (room for `n` cells each), and returns the number of
distinct values. -/
def DistinctSpec (lim : Limits) (P : Program) (p : ℕ) : Prop :=
  ∀ (d a val mul : ℕ) (L : List ℤ) (μ : ℕ → ℤ), Distinct.Ctx lim μ a val mul L →
    Meets lim P p d [L.length, a, val, mul] μ (tDistinct L.length) fun r μ' =>
      (∃ D : List ℤ, r = (D.length : ℤ) ∧ D.Nodup ∧ D.toFinset = L.toFinset ∧ Seg μ' val D ∧
        Seg μ' mul (D.map fun x => (L.count x : ℤ))) ∧
      SameOutside2 μ μ' val L.length mul L.length

/-- The doubles of the values that are not 0 and occur at least twice. -/
def twiceList (D C : List ℤ) : List ℤ :=
  ((D.zip C).filter fun q => decide (q.1 ≠ 0 ∧ 2 ≤ q.2)).map fun q => 2 * q.1

/-- What twice assumes: the values, of absolute value at most `V`, stand at `val` and as many
multiplicities at `mul`; the three regions lie in the memory, and the output meets neither of the
others; addresses and doubled values fit in a word. -/
structure Twice.Ctx (lim : Limits) (μ : ℕ → ℤ) (val mul out V : ℕ) (D C : List ℤ) : Prop where
  len : C.length = D.length
  bounded : AbsLe D V
  segVal : Seg μ val D
  segMul : Seg μ mul C
  apartVal : Apart val D.length out D.length
  apartMul : Apart mul D.length out D.length
  spaceVal : val + D.length ≤ lim.space
  spaceMul : mul + D.length ≤ lim.space
  spaceOut : out + D.length ≤ lim.space
  space_le : (lim.space : ℤ) ≤ lim.word
  word : (2 * V + 2 * D.length + 8 : ℤ) ≤ lim.word

/-- twice(nd, val, mul, out) writes the doubles of the values that are not 0 and occur at least
twice to `out` (room for `nd` cells), and returns their number. -/
def TwiceSpec (lim : Limits) (P : Program) (p : ℕ) : Prop :=
  ∀ (d val mul out V : ℕ) (D C : List ℤ) (μ : ℕ → ℤ), Twice.Ctx lim μ val mul out V D C →
    Meets lim P p d [D.length, val, mul, out] μ (tTwice D.length) fun r μ' =>
      r = ((twiceList D C).length : ℤ) ∧ Seg μ' out (twiceList D C) ∧ SameOutside μ μ' out D.length

/-- zeroThree(nd, val, mul) returns 1 if the value 0 occurs at least three times, and 0 if not; it
writes no cell. -/
def ZeroThreeSpec (lim : Limits) (P : Program) (p : ℕ) : Prop :=
  ∀ (d val mul : ℕ) (D C : List ℤ) (μ : ℕ → ℤ), C.length = D.length → Seg μ val D → Seg μ mul C →
    val + D.length ≤ lim.space → mul + D.length ≤ lim.space → (lim.space : ℤ) ≤ lim.word →
    (2 * D.length + 8 : ℤ) ≤ lim.word →
    Meets lim P p d [D.length, val, mul] μ (tZeroThree D.length) fun r μ' =>
      r = ThreeSumApsp.flag (∃ q ∈ D.zip C, q.1 = 0 ∧ 3 ≤ q.2) ∧ μ' = μ

/-- The table of the binary digits of the labels: digit `β` of the label of the `i`-th element in
cell `i Λ + β`. -/
def bitTable (V Λ : ℕ) (L : List ℤ) : List ℤ :=
  L.flatMap fun x => (List.range Λ).map fun β => if (lab V x).testBit β then 1 else 0

/-- What bits assumes: the list of numbers of absolute value at most `V` stands at `s`; the labels
have `Λ` binary digits, and `2^Λ` is not much larger than they are; the list and the table lie in
the memory and do not meet; addresses and doubled labels fit in a word. -/
structure Bits.Ctx (lim : Limits) (μ : ℕ → ℤ) (s V Λ bt : ℕ) (L : List ℤ) : Prop where
  bounded : AbsLe L V
  lt_pow : 2 * V < 2 ^ Λ
  pow_le : 2 ^ Λ ≤ 4 * V + 4
  seg : Seg μ s L
  apart : Apart s L.length bt (L.length * Λ)
  spaceSrc : s + L.length ≤ lim.space
  spaceTable : bt + L.length * Λ ≤ lim.space
  space_le : (lim.space : ℤ) ≤ lim.word
  word : (8 * V + 16 : ℤ) ≤ lim.word

/-- bits(len, s, V, Λ, bt, fr) writes the table of the binary digits of the labels `x + V` of the
`len` numbers from `s` to `bt` (`len Λ` cells).  It does not use the free pointer. -/
def BitsSpec (lim : Limits) (P : Program) (p : ℕ) : Prop :=
  ∀ (d fr s bt V Λ : ℕ) (L : List ℤ) (μ : ℕ → ℤ), Bits.Ctx lim μ s V Λ bt L →
    Meets lim P p d [L.length, s, V, Λ, bt, fr] μ (tBits L.length Λ) fun _ μ' =>
      Seg μ' bt (bitTable V Λ L) ∧ SameOutside μ μ' bt (L.length * Λ)

/-- The elements whose digit `β` is `x` and, unless `two = 0`, whose digit `β'` is `x'`. -/
def pickList (Λ β β' : ℕ) (x x' two : ℤ) (L BT : List ℤ) : List ℤ :=
  ((List.range L.length).filter fun i =>
    decide (BT.getD (i * Λ + β) 0 = x ∧ (two = 0 ∨ BT.getD (i * Λ + β') 0 = x'))).map
    fun i => L.getD i 0

/-- What pick assumes: the list stands at `s` and the table of its digits at `bt`, `Λ` cells for
each element; the two positions are below `Λ`; the three regions lie in the memory, and the output
meets neither of the others; addresses fit in a word. -/
structure Pick.Ctx (lim : Limits) (μ : ℕ → ℤ) (s bt out Λ β β' : ℕ) (L BT : List ℤ) : Prop where
  lenTable : BT.length = L.length * Λ
  posA : β < Λ
  posB : β' < Λ
  segSrc : Seg μ s L
  segTable : Seg μ bt BT
  apartSrc : Apart s L.length out L.length
  apartTable : Apart bt (L.length * Λ) out L.length
  spaceSrc : s + L.length ≤ lim.space
  spaceTable : bt + L.length * Λ ≤ lim.space
  spaceOut : out + L.length ≤ lim.space
  space_le : (lim.space : ℤ) ≤ lim.word
  word : (8 : ℤ) ≤ lim.word

/-- pick(len, s, bt, Λ, β, x, β', x', two, out) writes the elements selected by one binary digit
(`two = 0`) or by two to `out` (room for `len` cells) and returns their number. -/
def PickSpec (lim : Limits) (P : Program) (p : ℕ) : Prop :=
  ∀ (d s bt out Λ β β' : ℕ) (x x' two : ℤ) (L BT : List ℤ) (μ : ℕ → ℤ),
    Pick.Ctx lim μ s bt out Λ β β' L BT →
    Meets lim P p d [L.length, s, bt, Λ, β, x, β', x', two, out] μ (tPick L.length) fun r μ' =>
      r = ((pickList Λ β β' x x' two L BT).length : ℤ) ∧
        Seg μ' out (pickList Λ β β' x x' two L BT) ∧ SameOutside μ μ' out L.length

end Light.Sec3.ChanHe
