/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Lang.Lib.ArrayAt
public import ThreeSumApsp.Lang.Tactics
public import ThreeSumApsp.Lang.Tasks
public import ThreeSumApsp.Spec.Sec3.Problems
public import ThreeSumApsp.Util.Flag

/-!
# The problems of the paper as tasks

* The problems for Section 3.4 have a size and a bound (`Task`).
* The problems of Theorem 5 and of Section 3.1 have the parameters `N`, `D`, `w` and `U` (`TaskN`).
  The calling convention is the same: sizes, the bound, the addresses of the arrays, the address of
  the output, and the free pointer last.  The three tasks: the wanted entries of a thin matrix
  product (`thinTask`; Theorem 5 and Corollary 26), #Lop-AE-SparseTri (`lopCountTask`;
  Definition 14) and Lop-AE-SparseTri (`lopDetectTask`; Definition 13).  All three have the same
  instances (`ThinInst`).
* What "solved in time `T`" means for them: `ThinSolvedIn`, `LopSolvedIn`.
-/

@[expose] public section

open ThreeSumApsp

namespace Light

open ThreeSumApsp.Spec

/-! ## The problems for Section 3.4 -/

/-- Three `n × n` matrices of weights in the memory. -/
structure TriInst : Type where
  n : ℕ
  U : ℕ
  ab : ℕ
  bc : ℕ
  ac : ℕ
  AB : List ℤ
  BC : List ℤ
  AC : List ℤ

/-- The three matrices lie below the free pointer, and their entries are bounded by `U`. -/
structure TriInst.Pre (x : TriInst) (μ : ℕ → ℤ) (fr : ℕ) : Prop where
  n_pos : 1 ≤ x.n
  U_pos : 1 ≤ x.U
  lenAB : x.AB.length = x.n * x.n
  lenBC : x.BC.length = x.n * x.n
  lenAC : x.AC.length = x.n * x.n
  segAB : Seg μ x.ab x.AB
  segBC : Seg μ x.bc x.BC
  segAC : Seg μ x.ac x.AC
  leAB : AbsLe x.AB x.U
  leBC : AbsLe x.BC x.U
  leAC : AbsLe x.AC x.U
  belowAB : x.ab + x.n * x.n ≤ fr
  belowBC : x.bc + x.n * x.n ≤ fr
  belowAC : x.ac + x.n * x.n ≤ fr

/-- An instance stays where it is if no cell below the free pointer changes. -/
theorem TriInst.Pre.keep {x : TriInst} {μ μ' : ℕ → ℤ} {fr : ℕ} (h : x.Pre μ fr)
    (hs : Kept μ μ' fr := by light_keep) : x.Pre μ' fr := by
  light_facts h
  exact { h with segAB := h.segAB.keep, segBC := h.segBC.keep, segAC := h.segAC.keep }

/-- The free pointer may grow. -/
theorem TriInst.Pre.mono {x : TriInst} {μ : ℕ → ℤ} {fr fr' : ℕ} (h : x.Pre μ fr) (hfr : fr ≤ fr') :
    x.Pre μ fr' :=
  { h with
    belowAB := h.belowAB.trans hfr
    belowBC := h.belowBC.trans hfr
    belowAC := h.belowAC.trans hfr }

/-- Three matrices one after the other, with the free pointer behind them, are an instance. -/
theorem triPre_of_arrays {n U base : ℕ} {AB BC AC : List ℤ} {μ : ℕ → ℤ} (hn : 1 ≤ n) (hU : 1 ≤ U)
    (hAB : ArrayAt μ base AB (n * n) U (base + 3 * (n * n)))
    (hBC : ArrayAt μ (base + n * n) BC (n * n) U (base + 3 * (n * n)))
    (hAC : ArrayAt μ (base + 2 * (n * n)) AC (n * n) U (base + 3 * (n * n))) :
    (⟨n, U, base, base + n * n, base + 2 * (n * n), AB, BC, AC⟩ : TriInst).Pre μ
      (base + 3 * (n * n)) :=
  ⟨hn, hU, hAB.len, hBC.len, hAC.len, hAB.seg, hBC.seg, hAC.seg, hAB.bound, hBC.bound, hAC.bound,
    hAB.below, hBC.below, hAC.below⟩

/-- **Exact Triangle**: et(n, U, ab, bc, ac, fr) returns 1 if there is a zero triangle and 0 if not.
-/
noncomputable def etTask : Task where
  Inst := TriInst
  size x := x.n
  bound x := x.U
  args x := [x.n, x.U, x.ab, x.bc, x.ac]
  Pre := TriInst.Pre
  Post x μ fr r μ' := r = flag (triOf x.n x.AB x.BC x.AC).HasZeroTriangle ∧ Kept μ μ' fr

/-- **Negative Triangle**: nt(n, U, ab, bc, ac, fr) returns 1 if there is a negative triangle and 0
if not. -/
noncomputable def ntTask : Task where
  Inst := TriInst
  size x := x.n
  bound x := x.U
  args x := [x.n, x.U, x.ab, x.bc, x.ac]
  Pre := TriInst.Pre
  Post x μ fr r μ' := r = flag (triOf x.n x.AB x.BC x.AC).HasNegativeTriangle ∧ Kept μ μ' fr

/-- A list of `N` numbers in the memory. -/
structure VecInst : Type where
  N : ℕ
  U : ℕ
  a : ℕ
  X : List ℤ

/-- The list lies below the free pointer, and its entries are bounded by `U`. -/
structure VecInst.Pre (x : VecInst) (μ : ℕ → ℤ) (fr : ℕ) : Prop where
  N_pos : 1 ≤ x.N
  U_pos : 1 ≤ x.U
  len : x.X.length = x.N
  seg : Seg μ x.a x.X
  le : AbsLe x.X x.U
  below : x.a + x.N ≤ fr

/-- **Convolution-3SUM**: c3(N, U, x, fr) returns 1 if `x_i + x_j = x_{i+j}` for some `i`, `j`, and
0 if not. -/
noncomputable def c3Task : Task where
  Inst := VecInst
  size x := x.N
  bound x := x.U
  args x := [x.N, x.U, x.a]
  Pre := VecInst.Pre
  Post x μ fr r μ' := r = flag (Convolution3SUM (vecOf x.N x.X)) ∧ Kept μ μ' fr

/-- **3SUM**: s3(n, U, x, fr) returns 1 if three of the numbers, at different positions, sum to 0,
and 0 if not. -/
noncomputable def s3Task : Task where
  Inst := VecInst
  size x := x.N
  bound x := x.U
  args x := [x.N, x.U, x.a]
  Pre := VecInst.Pre
  Post x μ fr r μ' := r = flag (ThreeSum (vecOf x.N x.X)) ∧ Kept μ μ' fr

/-- Two `n × n` matrices in the memory, and the place for a third. -/
structure MatInst : Type where
  n : ℕ
  U : ℕ
  a : ℕ
  b : ℕ
  c : ℕ
  A : List ℤ
  B : List ℤ

/-- The two matrices and the place for the product lie below the free pointer; the place for the
product does not meet the two matrices. -/
structure MatInst.Pre (x : MatInst) (μ : ℕ → ℤ) (fr : ℕ) : Prop where
  n_pos : 1 ≤ x.n
  U_pos : 1 ≤ x.U
  lenA : x.A.length = x.n * x.n
  lenB : x.B.length = x.n * x.n
  segA : Seg μ x.a x.A
  segB : Seg μ x.b x.B
  leA : AbsLe x.A x.U
  leB : AbsLe x.B x.U
  belowA : x.a + x.n * x.n ≤ fr
  belowB : x.b + x.n * x.n ≤ fr
  belowC : x.c + x.n * x.n ≤ fr
  apartA : Apart x.a (x.n * x.n) x.c (x.n * x.n)
  apartB : Apart x.b (x.n * x.n) x.c (x.n * x.n)

/-- **The (min,+)-product**: mp(n, U, a, b, c, fr) writes the product of the matrices at `a` and `b`
to `c`. -/
def mpTask : Task where
  Inst := MatInst
  size x := x.n
  bound x := x.U
  args x := [x.n, x.U, x.a, x.b, x.c]
  Pre := MatInst.Pre
  Post x μ fr _ μ' := Seg μ' x.c (minPlusList x.n x.A x.B) ∧ KeptBut μ μ' fr x.c (x.n * x.n)

/-- A directed graph in the memory: adjacency matrix and weights, and the place for the `2n²` cells
of the answer. -/
structure GraphInst : Type where
  n : ℕ
  U : ℕ
  adj : ℕ
  w : ℕ
  out : ℕ
  ADJ : List ℤ
  W : List ℤ

/-- The graph and the place for the answer lie below the free pointer; the graph has no negative
cycle. -/
structure GraphInst.Pre (x : GraphInst) (μ : ℕ → ℤ) (fr : ℕ) : Prop where
  n_pos : 1 ≤ x.n
  U_pos : 1 ≤ x.U
  lenADJ : x.ADJ.length = x.n * x.n
  lenW : x.W.length = x.n * x.n
  segADJ : Seg μ x.adj x.ADJ
  segW : Seg μ x.w x.W
  zeroOne : ∀ e ∈ x.ADJ, e = 0 ∨ e = 1
  leW : AbsLe x.W x.U
  belowADJ : x.adj + x.n * x.n ≤ fr
  belowW : x.w + x.n * x.n ≤ fr
  belowOut : x.out + 2 * (x.n * x.n) ≤ fr
  apartADJ : Apart x.adj (x.n * x.n) x.out (2 * (x.n * x.n))
  apartW : Apart x.w (x.n * x.n) x.out (2 * (x.n * x.n))
  noNegativeCycle : NoNegativeCycle (graphOf x.n x.ADJ x.W)

/-- **APSP**: ap(n, U, adj, w, out, fr) writes two cells for each pair `(i, j)`, at
`out + 2 (i n + j)`: 1 and the distance from `i` to `j` if `j` can be reached from `i`, and 0 in the
first cell if not. -/
def apTask : Task where
  Inst := GraphInst
  size x := x.n
  bound x := x.U
  args x := [x.n, x.U, x.adj, x.w, x.out]
  Pre := GraphInst.Pre
  Post x μ fr _ μ' :=
    (∃ dist : Fin x.n → Fin x.n → WithTop ℤ, IsDistanceMatrix (graphOf x.n x.ADJ x.W) dist ∧
    ∀ i j : Fin x.n,
      (dist i j = ⊤ → μ' (x.out + 2 * (i.val * x.n + j.val)) = 0) ∧
      ∀ z : ℤ, dist i j = (z : WithTop ℤ) →
        μ' (x.out + 2 * (i.val * x.n + j.val)) = 1 ∧
          μ' (x.out + 2 * (i.val * x.n + j.val) + 1) = z) ∧
    KeptBut μ μ' fr x.out (2 * (x.n * x.n))

/-! ## The thin matrix product and the lopsided triangle problems -/

/-- Matrices `X` (`N × D`) and `Y` (`D × N`), row by row, `w` wanted positions (rows in `WI`,
columns in `WJ`), and the place for `w` answers. -/
structure ThinInst : Type where
  /-- The number of rows of `X` and of columns of `Y`. -/
  N : ℕ
  /-- The number of columns of `X` and of rows of `Y`. -/
  D : ℕ
  /-- The number of wanted positions. -/
  w : ℕ
  /-- The bound on the absolute values of the entries. -/
  U : ℕ
  /-- The address of `X`. -/
  x : ℕ
  /-- The address of `Y`. -/
  y : ℕ
  /-- The address of `WI`. -/
  wi : ℕ
  /-- The address of `WJ`. -/
  wj : ℕ
  /-- The address of the answers. -/
  out : ℕ
  /-- The first matrix, row by row. -/
  X : List ℤ
  /-- The second matrix, row by row. -/
  Y : List ℤ
  /-- The rows of the wanted positions. -/
  WI : List ℕ
  /-- The columns of the wanted positions. -/
  WJ : List ℕ

/-- Everything lies below the free pointer, the entries are bounded by `U`, the positions are
distinct positions of an `N × N` matrix, and the place for the answers meets none of the inputs. -/
structure ThinInst.Pre (x : ThinInst) (μ : ℕ → ℤ) (fr : ℕ) : Prop where
  N_pos : 1 ≤ x.N
  D_pos : 1 ≤ x.D
  U_pos : 1 ≤ x.U
  lenX : x.X.length = x.N * x.D
  lenY : x.Y.length = x.D * x.N
  lenWI : x.WI.length = x.w
  lenWJ : x.WJ.length = x.w
  segX : Seg μ x.x x.X
  segY : Seg μ x.y x.Y
  segWI : SegN μ x.wi x.WI
  segWJ : SegN μ x.wj x.WJ
  leX : AbsLe x.X x.U
  leY : AbsLe x.Y x.U
  ltWI : ∀ i ∈ x.WI, i < x.N
  ltWJ : ∀ j ∈ x.WJ, j < x.N
  nodup : (x.WI.zip x.WJ).Nodup
  belowX : x.x + x.N * x.D ≤ fr
  belowY : x.y + x.D * x.N ≤ fr
  belowWI : x.wi + x.w ≤ fr
  belowWJ : x.wj + x.w ≤ fr
  belowOut : x.out + x.w ≤ fr
  apartX : Apart x.out x.w x.x (x.N * x.D)
  apartY : Apart x.out x.w x.y (x.D * x.N)
  apartWI : Apart x.out x.w x.wi x.w
  apartWJ : Apart x.out x.w x.wj x.w

/-! The ten arguments of a procedure for one of these tasks, as local variables. -/

namespace ThinArg

/-- N. -/
abbrev Rows : ℕ := 0
/-- D. -/
abbrev Cols : ℕ := 1
/-- The number w of wanted positions. -/
abbrev Wanted : ℕ := 2
/-- The bound U on the entries. -/
abbrev Bound : ℕ := 3
/-- The address of X. -/
abbrev AdrX : ℕ := 4
/-- The address of Y. -/
abbrev AdrY : ℕ := 5
/-- The address of the rows of the wanted positions. -/
abbrev AdrWI : ℕ := 6
/-- The address of their columns. -/
abbrev AdrWJ : ℕ := 7
/-- The address of the output. -/
abbrev AdrOut : ℕ := 8
/-- The free pointer. -/
abbrev Free : ℕ := 9

end ThinArg

/-- The entries of both matrices are 0 or 1. -/
def ThinInst.ZeroOne (x : ThinInst) : Prop := (∀ v ∈ x.X, v = 0 ∨ v = 1) ∧ ∀ v ∈ x.Y, v = 0 ∨ v = 1

/-- The entry `(XY)[I, J]`. -/
def thinEntry (N D : ℕ) (X Y : List ℤ) (I J : ℕ) : ℤ :=
  ((List.range D).map fun k => X.getD (I * D + k) 0 * Y.getD (k * N + J) 0).sum

/-- The wanted entries, in the order of the positions. -/
def thinOut (N D : ℕ) (X Y : List ℤ) (WI WJ : List ℕ) : List ℤ :=
  (WI.zip WJ).map fun q => thinEntry N D X Y q.1 q.2

/-- **The wanted entries of a thin matrix product** (Theorem 5, Corollary 26):
`thin(N, D, w, U, x, y, wi, wj, out, fr)`. -/
def thinTask : TaskN where
  Inst := ThinInst
  pars x := [x.N, x.D, x.w, x.U]
  args x := [x.N, x.D, x.w, x.U, x.x, x.y, x.wi, x.wj, x.out]
  Pre := ThinInst.Pre
  Post x μ fr _ μ' := Seg μ' x.out (thinOut x.N x.D x.X x.Y x.WI x.WJ) ∧ KeptBut μ μ' fr x.out x.w

/-- **#Lop-AE-SparseTri** (Definition 14), the graph given by its two biadjacency matrices: the same
call with `U = 1` on matrices of zeros and ones; the answers are the numbers of common
neighbours. -/
def lopCountTask : TaskN where
  Inst := ThinInst
  pars x := [x.N, x.D, x.w]
  args x := [x.N, x.D, x.w, x.U, x.x, x.y, x.wi, x.wj, x.out]
  Pre x μ fr := x.Pre μ fr ∧ x.ZeroOne ∧ x.U = 1
  Post x μ fr _ μ' := Seg μ' x.out (thinOut x.N x.D x.X x.Y x.WI x.WJ) ∧ KeptBut μ μ' fr x.out x.w

/-- **Lop-AE-SparseTri** (Definition 13): the answer is 1 if the pair has a common neighbour and 0
if not. -/
def lopDetectTask : TaskN where
  Inst := ThinInst
  pars x := [x.N, x.D, x.w]
  args x := [x.N, x.D, x.w, x.U, x.x, x.y, x.wi, x.wj, x.out]
  Pre x μ fr := x.Pre μ fr ∧ x.ZeroOne ∧ x.U = 1
  Post x μ fr _ μ' :=
    Seg μ' x.out ((thinOut x.N x.D x.X x.Y x.WI x.WJ).map fun v => if v = 0 then 0 else 1) ∧
      KeptBut μ μ' fr x.out x.w

/-- "The thin matrix product is solved in time `T N D w' u`", where `w'` is an upper bound on the
number `w` of wanted positions and `u` one on the bound `U`. -/
def ThinSolvedIn (T : ℕ → ℕ → ℕ → ℝ → ℝ) : Prop :=
  ∃ (P : Program) (p : ℕ) (Tn : List ℕ → ℕ) (need : List ℕ → Need), PolyNeedN need ∧
    SolvesN thinTask P p Tn need ∧
    ∀ (N D w w' U : ℕ) (u : ℝ), 1 ≤ N → 1 ≤ D → 1 ≤ U → w ≤ w' → (U : ℝ) ≤ u →
      (Tn [N, D, w, U] : ℝ) ≤ T N D w' u

/-- "The task (one of the two lopsided triangle problems) is solved in time `T n D w'`", where `w'`
is an upper bound on the number `w` of query pairs. -/
def LopSolvedIn (task : TaskN) (T : ℕ → ℕ → ℕ → ℝ) : Prop :=
  ∃ (P : Program) (p : ℕ) (Tn : List ℕ → ℕ) (need : List ℕ → Need), PolyNeedN need ∧
    SolvesN task P p Tn need ∧
    ∀ (n D w w' : ℕ), 1 ≤ n → 1 ≤ D → w ≤ w' → (Tn [n, D, w] : ℝ) ≤ T n D w'

end Light
