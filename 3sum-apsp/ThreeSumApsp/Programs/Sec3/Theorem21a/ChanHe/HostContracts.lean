/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec3.Theorem21a.ChanHe.FrontFacts
public import ThreeSumApsp.Programs.Sec3.Theorem21a.ChanHe.GridContracts
public import ThreeSumApsp.Programs.Sec3.Theorem21a.ChanHe.Time

/-!
# 3SUM from Convolution-3SUM: the memory map of core; specifications of params, prep, core

Theorem 21(a), after [CH20, Theorem 5.1].  core decides 3SUM with a solver
of Convolution-3SUM.  It first calls params, which computes the three parameters of the reduction,
and prep, which fills the arrays that the rest of core works on.  The arrays stand one after the
other from a base address `b`.  This file fixes their layout (`Map`) and the specifications of
params, prep and core.
-/

@[expose] public section

open ThreeSumApsp

namespace Light.Sec3.ChanHe

open ThreeSumApsp.ChanHe ThreeSumApsp.Spec Finset

/-! ## The memory map -/

/-- The addresses of the arrays of core, for the base address `b`, `n` numbers, `Λ` binary digits
and primes up to `m`. -/
structure Map : Type where
  /-- The base address. -/
  b : ℕ
  /-- The number of integers of the input. -/
  n : ℕ
  /-- The number of binary digits of a label. -/
  Λ : ℕ
  /-- The bound on the primes. -/
  m : ℕ

namespace Map
variable (a : Map)
/-- The block of parameters of the recursive procedure, 6 cells. -/
def cx : ℕ := a.b
/-- The primes, `m` cells. -/
def pr : ℕ := a.b + 6
/-- The count table, `m²` cells. -/
def cnt : ℕ := a.pr + a.m
/-- The sorted copy of the input, `n` cells. -/
def srt : ℕ := a.cnt + a.m * a.m
/-- The distinct values, `n` cells. -/
def val : ℕ := a.srt + a.n
/-- How often they occur, `n` cells. -/
def mul : ℕ := a.val + a.n
/-- The binary digits of the labels, `n Λ` cells. -/
def bt : ℕ := a.mul + a.n
/-- The three sets of a splitting, `3n` cells. -/
def A : ℕ := a.bt + a.n * a.Λ
/-- The doubles of the repeated values, `n` cells. -/
def tw : ℕ := a.A + 3 * a.n
/-- One cell that holds 0: the set {0}. -/
def one : ℕ := a.tw + a.n
/-- The free pointer behind the arrays. -/
def top : ℕ := a.one + 1

/-- The arrays stand one after the other: each address is the one before plus the length of the
array that stands there.  A proof begins with `have hmap := a.layout`, which states the whole
map. -/
theorem layout : a.cx = a.b ∧ a.pr = a.cx + 6 ∧ a.cnt = a.pr + a.m ∧ a.srt = a.cnt + a.m * a.m ∧
    a.val = a.srt + a.n ∧ a.mul = a.val + a.n ∧ a.bt = a.mul + a.n ∧ a.A = a.bt + a.n * a.Λ ∧
    a.tw = a.A + 3 * a.n ∧ a.one = a.tw + a.n ∧ a.top = a.one + 1 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end Map

/-! ## params -/

/-- params(n, V, out) writes `Lam V`, `mPar n V` and `fuel n` to the three cells from `out`. -/
def ParamsSpec (lim : Limits) (P : Program) (p : ℕ) : Prop :=
  ∀ (d n V out : ℕ) (μ : ℕ → ℤ), out + 3 ≤ lim.space → (lim.space : ℤ) ≤ lim.word →
    ((8 * (mPar n V + 1) ^ 2 + 8 * V + 4 * n + 64 : ℕ) : ℤ) ≤ lim.word → d + 1 ≤ lim.depth →
    Meets lim P p d [n, V, out] μ (tParams n V) fun _ μ' =>
      Seg μ' out [(Lam V : ℤ), mPar n V, fuel n] ∧ SameOutside μ μ' out 3

/-! ## prep -/

/-- What prep needs: the size of a word, the number of cells behind the arrays (the sieve's table
and the scratch space of sorting stand there), and the depth of calls. -/
def prepNeed (n V Λ m : ℕ) : Need :=
  ⟨8 * (m + 1) ^ 2 + 8 * V + 4 * n + 64, m + n + Λ + 4, Nat.log 2 n + 3⟩

/-- What prep assumes about its arguments: the input `X` has `n` numbers of absolute value at most
`V` and stands below the base; `Λ` is the number of binary digits for `V`; and the limits allow for
what prep needs behind the arrays. -/
structure Prep.Ctx (lim : Limits) (d : ℕ) (a : Map) (V x : ℕ) (X : List ℤ) : Prop where
  /-- The input has `n` numbers. -/
  len : X.length = a.n
  /-- They have absolute value at most `V`. -/
  bounded : AbsLe X V
  /-- The input stands below the base. -/
  below : x + a.n ≤ a.b
  /-- `V` is not 0. -/
  bound_pos : 1 ≤ V
  /-- `Λ` is the number of binary digits for `V`. -/
  digits : a.Λ = Lam V
  /-- The limits allow for what prep needs. -/
  ok : (prepNeed a.n V a.Λ a.m).Ok lim a.top d

/-- What the routines that run through the splittings are given, for the arrays of a map and the
distinct values `D`. -/
@[simp] def Map.front (a : Map) (V : ℕ) (D : List ℤ) : FrontArgs where
  fr := a.top
  n := a.n
  V := V
  m := a.m
  np := #(Nat.primesLE a.m)
  pr := a.pr
  cnt := a.cnt
  Λ := a.Λ
  nd := D.length
  val := a.val
  bt := a.bt
  A := a.A
  cx := a.cx
  D := D

/-- prep(n, V, Λ, m, x, b): the input `X` stands at `x`.  Fills the arrays of the map `a` with base
`b`: the primes, zeros in the count table, the distinct values `D` and how often they occur, the
binary digits of their labels, the block of parameters, and 0 in the cell `one`.  Returns the number
of distinct values. -/
def PrepSpec (lim : Limits) (P : Program) (p : ℕ) : Prop :=
  ∀ (d : ℕ) (a : Map) (V x : ℕ) (X : List ℤ) (μ : ℕ → ℤ), Prep.Ctx lim d a V x X → Seg μ x X →
    Meets lim P p d [a.n, V, a.Λ, a.m, x, a.b] μ (tPrep a.n a.Λ a.m) fun res μ' =>
      (∃ D C : List ℤ, res = (D.length : ℤ) ∧ Values a.n X D C ∧ Seg μ' a.mul C ∧ μ' a.one = 0 ∧
        FrontMem μ' (a.front V D)) ∧
      Kept μ μ' a.b

/-! ## core -/

/-- core(n, V, x, b), with `V = 2U`: the input `X`, `n` numbers of absolute value at most `U`,
stands at `x`, below the free pointer `b`.  Returns 1 if three of the numbers, at different
positions, sum to 0, and 0 if not.  `T` and `r` are the time and the need of the Convolution-3SUM
solver. -/
def CoreSpec (lim : Limits) (P : Program) (p : ℕ) (T : ℕ → ℕ → ℕ) (r : ℕ → ℕ → Need) : Prop :=
  ∀ (d n U x b : ℕ) (X : List ℤ) (μ : ℕ → ℤ), X.length = n → AbsLe X U → Seg μ x X → x + n ≤ b →
    1 ≤ n → 1 ≤ U → (coreNeed r n (2 * U)).Ok lim b d →
    Meets lim P p d [n, ((2 * U : ℕ) : ℤ), x, b] μ (coreTime T n (2 * U)) fun res μ' =>
      res = flag (ThreeSum (vecOf n X)) ∧ Kept μ μ' b

end Light.Sec3.ChanHe
