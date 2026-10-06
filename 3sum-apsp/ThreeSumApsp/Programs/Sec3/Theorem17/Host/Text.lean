/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec3.Theorem17.Hashing.ChoosePrime
public import ThreeSumApsp.Programs.Sec3.Theorem17.Host.Loop
public import ThreeSumApsp.Programs.Sec3.Theorem17.Instances.Chunks
public import ThreeSumApsp.Programs.Sec3.Theorem17.Parameters.Sizes
public import ThreeSumApsp.Programs.Sec3.Theorem17.Witnesses.BruteForce

/-!
# The host of Theorem 17: the top procedure

The host procedure et17(n, U, ab, bc, ac, fr) decides Exact Triangle with the help of an arbitrary
solver of Lop-AE-SparseTri (proof of Theorem 17).  It computes the parameters `D` and `g` by two
procedures that are parameters of the construction, and `s = ⌊√D⌋`.  For small `n`
(`D < 16`, `n < D`, `g < 1` or `s < g`) it runs the brute force.  Otherwise it chooses the prime,
computes the largest number of query pairs, the number of vertices of a piece and the number of
pieces, lays out its arrays from the free pointer on, computes the residues of the weights, sorts
the pairs `(a, b)` into classes, cuts the classes into chunks, and runs the loop over the instances.

This file holds the program (`et17Body`), its time and its need (`hostTime`, `hostNeed`), what it
assumes about the program around it (`Et17Ctx`), and the data, the addresses and the local variables
of a run.

**The way through the files on the host**, each named by its main result.

1. The instances as data, with no program in sight: what the host writes, what the solver answers
   and which scans succeed (`HostData`); a zero triangle is found if and only if there is one
   (`HostData.found_m`); a failed scan belongs to a false positive of its own
   (`HostData.sum_fails_le`); there are at most 4ng instances (`HostData.m_le`).
2. The loop over the instances (`hostLoop_spec`).
3. The text of the top procedure (this file), in three parts and the small case.
4. The parts: the parameters and the small case (`et17Params_spec`, `et17Small_spec`); the prime,
   the sizes and the addresses (`et17Sizes_spec`, `et17Addr_spec`); the arrays and the call of the
   loop (`et17Tables_spec`).
5. What the parts need: the limits cover what the called procedures ask for (`choosePre_of_ok`,
   `hostLim_of_ok`), and the time of a run is within the worst case (`hostRunTime_le`).
6. The parts together: et17 decides Exact Triangle (`et17_spec`).
7. The list of the procedures with their numbers; with a solver it is a solver (`et17Procs`,
   `et17_solves`).
8. For the claim: the need is polynomially bounded (`hostNeed_poly`), the time obeys the bound of
   Theorem 17 (`obeysBound17_hostTime`), and so the claim holds for programs of the light language
   (`claim17_of_host`, `claim_theorem_17₅`, `claim_theorem_17₂₆`).

The layout, from the free pointer `fr` on: the table of doubles (`len + 1` cells, where
`len = bitLen U` is the number of binary digits of `U`; cell `j` holds `2^j p`, for residues without
division); the residues of `w(a,b)`, `w(b,c)`, `w(a,c)` (`n²` each); the starts of the classes
(`p + 1`); running places (`p`; while the pairs are sorted, cell `ϱ` holds the next free place of
the class `ϱ`); rows and columns of the sorted pairs (`n²` each); the three components of the table
of chunks (`n² + p` each); `X` (`n D`); `Y` (`D n`); the answers (`cap`); the solver's free pointer.

Notation: `κ` is the exponent in `|w(e)| ≤ n^κ`, the paper's ν; as in the paper, `F(p)` is the
number of false positives of `p`, that is, of triples with `S(a,b,c) = w(a,b) + w(b,c) + w(a,c) ≠ 0`
and `p ∣ S(a,b,c)`.
-/

@[expose] public section

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec

/-! ## The procedure -/

/-- The numbers of the procedures that et17 calls, directly or through the procedures that it
calls: the two parameter procedures, sqrt, brute, scan, choosePrime, queryCapNat, ceilDiv, bitLen,
dblTable, resid, residues, classes, chunks, hostLoop, the solver, writeX, writeY, scanPairs, and
the procedures below choosePrime. -/
structure Et17Nums : Type where
  pD : ℕ
  pG : ℕ
  pSqrt : ℕ
  pBrute : ℕ
  pScan : ℕ
  pChoose : ℕ
  pCap : ℕ
  pCeil : ℕ
  pBitLen : ℕ
  pDbl : ℕ
  pResid : ℕ
  pResidues : ℕ
  pClasses : ℕ
  pChunks : ℕ
  pLoop : ℕ
  pS : ℕ
  pWriteX : ℕ
  pWriteY : ℕ
  pScanPairs : ℕ
  ch : ChNums

namespace Et17

/-- The locals of `et17`.  The arguments: `n`, `U`, the addresses of the three arrays of weights,
and the free pointer (the table of doubles is there).  Then `D`, `g`, `s = ⌊√D⌋`, the prime `p`,
`cap`, the number `q` of vertices of a piece, the number `h` of pieces, `len = bitLen U`, and `n²`.
Then the addresses of the residues of `w(a,b)`, `w(b,c)`, `w(a,c)`, of the starts of the classes,
the running places, the rows and the columns of the sorted pairs, the three components of the table
of chunks, `X`, `Y`, the answers, and the solver's free pointer.  Then `n² + p`, the number of
chunks, the number of instances, a flag (also the place for results that are not used), and `n D`.
-/
abbrev Size : ℕ := 0
@[inherit_doc Size] abbrev Bound : ℕ := 1
@[inherit_doc Size] abbrev AdrAB : ℕ := 2
@[inherit_doc Size] abbrev AdrBC : ℕ := 3
@[inherit_doc Size] abbrev AdrAC : ℕ := 4
@[inherit_doc Size] abbrev Free : ℕ := 5
@[inherit_doc Size] abbrev ParD : ℕ := 6
@[inherit_doc Size] abbrev ParG : ℕ := 7
@[inherit_doc Size] abbrev RootD : ℕ := 8
@[inherit_doc Size] abbrev ThePrime : ℕ := 9
@[inherit_doc Size] abbrev Cap : ℕ := 10
@[inherit_doc Size] abbrev PieceLen : ℕ := 11
@[inherit_doc Size] abbrev NumPieces : ℕ := 12
@[inherit_doc Size] abbrev Bits : ℕ := 13
@[inherit_doc Size] abbrev SizeSq : ℕ := 14
@[inherit_doc Size] abbrev ResAB : ℕ := 16
@[inherit_doc Size] abbrev ResBC : ℕ := 17
@[inherit_doc Size] abbrev ResAC : ℕ := 18
@[inherit_doc Size] abbrev Cls : ℕ := 19
@[inherit_doc Size] abbrev Cur : ℕ := 20
@[inherit_doc Size] abbrev Rows : ℕ := 21
@[inherit_doc Size] abbrev Cols : ℕ := 22
@[inherit_doc Size] abbrev TabR : ℕ := 23
@[inherit_doc Size] abbrev TabL : ℕ := 24
@[inherit_doc Size] abbrev TabW : ℕ := 25
@[inherit_doc Size] abbrev MatX : ℕ := 26
@[inherit_doc Size] abbrev MatY : ℕ := 27
@[inherit_doc Size] abbrev AdrOut : ℕ := 28
@[inherit_doc Size] abbrev SolverFree : ℕ := 29
@[inherit_doc Size] abbrev Room : ℕ := 30
@[inherit_doc Size] abbrev NumChunks : ℕ := 31
@[inherit_doc Size] abbrev NumInst : ℕ := 32
@[inherit_doc Size] abbrev Small : ℕ := 33
@[inherit_doc Size] abbrev Area : ℕ := 34

end Et17

open Et17 in
/-- The first part of et17: `D`, `g`, `s`, and the flag that says whether `n` is small. -/
def et17Params (ν : Et17Nums) : Stmt :=
  .call ν.pD [v Size] ParD ;;
  .call ν.pG [v ParD] ParG ;;
  .call ν.pSqrt [v ParD] RootD ;;
  .ite (v ParD <' k 16) (.set Small (k 1)) (.set Small (v Small)) ;;
  .ite (v Size <' v ParD) (.set Small (k 1)) (.set Small (v Small)) ;;
  .ite (v ParG <' k 1) (.set Small (k 1)) (.set Small (v Small)) ;;
  .ite (v RootD <' v ParG) (.set Small (k 1)) (.set Small (v Small)) ;;
  .skip

open Et17 in
/-- The end of the second part: the sizes n², nD, n² + p, and the addresses of the arrays. -/
def et17Addr : Stmt :=
  .set SizeSq (v Size *' v Size) ;;
  .set Area (v Size *' v ParD) ;;
  .set Room (v SizeSq +' v ThePrime) ;;
  .set ResAB (v Free +' (v Bits +' k 1)) ;;
  .set ResBC (v ResAB +' v SizeSq) ;;
  .set ResAC (v ResBC +' v SizeSq) ;;
  .set Cls (v ResAC +' v SizeSq) ;;
  .set Cur (v Cls +' (v ThePrime +' k 1)) ;;
  .set Rows (v Cur +' v ThePrime) ;;
  .set Cols (v Rows +' v SizeSq) ;;
  .set TabR (v Cols +' v SizeSq) ;;
  .set TabL (v TabR +' v Room) ;;
  .set TabW (v TabL +' v Room) ;;
  .set MatX (v TabW +' v Room) ;;
  .set MatY (v MatX +' v Area) ;;
  .set AdrOut (v MatY +' v Area) ;;
  .set SolverFree (v AdrOut +' v Cap) ;;
  .skip

open Et17 in
/-- The second part: the prime, the sizes, and the addresses of the arrays. -/
def et17Sizes (ν : Et17Nums) : Stmt :=
  .call ν.pChoose [v Size, v Bound, v AdrAB, v AdrBC, v AdrAC, v ParD, v Free] ThePrime ;;
  .call ν.pCap [v Size, v ParD] Cap ;;
  .call ν.pCeil [v RootD, v ParG] PieceLen ;;
  .call ν.pCeil [v Size, v PieceLen] NumPieces ;;
  .call ν.pBitLen [v Bound] Bits ;;
  et17Addr

open Et17 in
/-- The third part: the residues, the classes, the chunks, and the loop over the instances. -/
def et17Tables (ν : Et17Nums) : Stmt :=
  .call ν.pDbl [v Free, v ThePrime, v Bits] Small ;;
  .call ν.pResidues [v AdrAB, v ResAB, v SizeSq, v Free, v Bits] Small ;;
  .call ν.pResidues [v AdrBC, v ResBC, v SizeSq, v Free, v Bits] Small ;;
  .call ν.pResidues [v AdrAC, v ResAC, v SizeSq, v Free, v Bits] Small ;;
  .call ν.pClasses [v ResAB, v Size, v ThePrime, v Cls, v Cur, v Rows, v Cols] Small ;;
  .call ν.pChunks [v Cls, v ThePrime, v Cap, v TabR, v TabL, v TabW] NumChunks ;;
  .set NumInst (v NumPieces *' v NumChunks) ;;
  .call ν.pLoop [v Size, v ParD, v ThePrime, v PieceLen, v NumChunks, v NumInst, v AdrAB, v AdrBC,
    v AdrAC, v ResAC, v ResBC, v Rows, v Cols, v TabR, v TabL, v TabW, v MatX, v MatY, v AdrOut,
    v SolverFree] 0

open Et17 in
/-- et17(n, U, ab, bc, ac, fr). -/
def et17Body (ν : Et17Nums) : Stmt :=
  et17Params ν ;;
  .ite (v Small =' k 1)
    (.call ν.pBrute [v Size, v Bound, v AdrAB, v AdrBC, v AdrAC, v Free] 0)
    (et17Sizes ν ;; et17Tables ν)

/-! ## Time and need

The additive constants in the time functions are upper bounds for the cost of evaluating arguments,
of calls and of tests.  They are not meant to be tight. -/

/-- n is small for the parameters D and g: the host runs the brute force. -/
def SmallCase (n D g : ℕ) : Prop := D < 16 ∨ n < D ∨ g < 1 ∨ Nat.sqrt D < g

instance (n D g : ℕ) : Decidable (SmallCase n D g) := by unfold SmallCase; infer_instance

/-- The largest time of the solver on an instance with at most cap query pairs. -/
def supTime (Tn : List ℕ → ℕ) (n D cap : ℕ) : ℕ :=
  (Finset.range (cap + 1)).sup fun w => Tn [n, D, w]

/-- The largest need of the solver on an instance with at most cap query pairs. -/
def supNeed (need : List ℕ → Need) (n D cap : ℕ) : Need :=
  ⟨(Finset.range (cap + 1)).sup fun w => (need [n, D, w]).word,
    (Finset.range (cap + 1)).sup fun w => (need [n, D, w]).cells,
    (Finset.range (cap + 1)).sup fun w => (need [n, D, w]).depth⟩

/-- Proof of Theorem 17: "F(p) = O(n³ log(3n^ν)/√D) = O(ν n³ log n/√D)" for the selected prime.
Here the second form, with the constant `Hashing.falsePositiveConst` and with κ = kappaOf n U =
max(1, log U / log n), so that U ≤ n^κ. -/
noncomputable def falsePositiveBound (n U D : ℕ) : ℕ :=
  ⌊Hashing.falsePositiveConst * (kappaOf n U * (n : ℝ) ^ 3 * Real.log n / Real.sqrt D)⌋₊

/-- The time of the parameter procedures, of the square root and of the tests. -/
def hostSetup (tD tG : ℕ → ℕ) (n D : ℕ) : ℕ := tD n + tG D + (18 * Nat.sqrt D + 12) + 60

/-- A bound on the time of the loop over the instances: at most 4ng instances, with pieces of at
most q vertices and at most cap query pairs, and at most falsePositiveBound + 1 scans. -/
noncomputable def hostLoopBound (Tn : List ℕ → ℕ) (n U D g : ℕ) : ℕ :=
  4 * n * g *
      (tWrites n D (pieceSizeNat D g) + supTime Tn n D (queryCapNat n D)
        + tAnswers (queryCapNat n D))
    + tScanCall (pieceSizeNat D g) * (falsePositiveBound n U D + 1) + 14

/-- The time of et17 after the tests, if n is not small. -/
noncomputable def hostMain (Tn : List ℕ → ℕ) (n U D g : ℕ) : ℕ :=
  chooseTime n U D + tQueryCapNat n D + tCeilDiv (Nat.sqrt D) g + tCeilDiv n (pieceSizeNat D g)
    + tBitLen U + tDblTable (bitLen U) + 3 * tResidues (n * n) (bitLen U) + tClasses n (Nat.sqrt D)
    + tChunks (Nat.sqrt D) (4 * n * g) + hostLoopBound Tn n U D g + 300

/-- **A bound on the time of the host in the worst case**, for the parameter functions Dfun, Gfun
with the times tD, tG, over a solver with the time Tn. -/
noncomputable def hostTime (Dfun Gfun tD tG : ℕ → ℕ) (Tn : List ℕ → ℕ) (n U : ℕ) : ℕ :=
  hostSetup tD tG n (Dfun n) +
    if SmallCase n (Dfun n) (Gfun (Dfun n)) then tBrute n + 20
    else hostMain Tn n U (Dfun n) (Gfun (Dfun n))

/-- The cells of the arrays of et17, with s in place of the prime. -/
def hostLayout (n U D : ℕ) : ℕ :=
  (bitLen U + 1) + 3 * (n * n) + (Nat.sqrt D + 1) + Nat.sqrt D + 2 * (n * n)
    + 3 * (n * n + Nat.sqrt D) + 2 * (n * D) + queryCapNat n D

/-- The largest number that et17 and the procedures below it form, apart from the solver; a and b
bound the numbers that the two parameter procedures form. -/
def hostWord (a b n U D g : ℕ) : ℕ :=
  a + b                                                     -- the two parameter procedures
    + (4 * D + 4)                                           -- the square root, the primes up to √D
    + (3 * U + 1)                                           -- a sum of three weights
    + (2 * U + 2)                                           -- the number of binary digits of U
    + (2 * n + 1)                                           -- the power of two above n
    + Nat.sqrt D * 2 ^ (bitLen U + 1)                       -- the table of doubles
    + 4 * (16 ^ Nat.clog 2 n * Nat.sqrt D)                  -- the entries in Strassen's algorithm
    + n * n * (16 ^ Nat.clog 2 n * Nat.sqrt D)              -- the count for a prime
    + (4 * n ^ 4 + D + 2)                                   -- cap
    + (Nat.sqrt D + g + 1)                                  -- the size of a piece
    + (n + pieceSizeNat D g + 1)                                -- the number of pieces
    + 4 * n * g                                             -- the number of instances
    + 100

/-- The need of the host for given parameters D and g. -/
def hostNeedAt (a b : ℕ) (need : List ℕ → Need) (n U D g : ℕ) : Need :=
  ⟨hostWord a b n U D g + (supNeed need n D (queryCapNat n D)).word,
    chooseCells n U D + hostLayout n U D + (supNeed need n D (queryCapNat n D)).cells + 2,
    2 * Nat.clog 2 n + 8 + (supNeed need n D (queryCapNat n D)).depth⟩

/-- **The need of the host**, over a solver with the need `need`; wD and wG bound the numbers that
the parameter procedures form. -/
def hostNeed (Dfun Gfun wD wG : ℕ → ℕ) (need : List ℕ → Need) (n U : ℕ) : Need :=
  hostNeedAt (wD n) (wG (Dfun n)) need n U (Dfun n) (Gfun (Dfun n))

/-! ## The context -/

/-- A procedure that computes a function of one number and changes no cell; t is its time, w bounds
the numbers it forms, and it nests calls at most three deep. -/
def ParamProc (P : Program) (p : ℕ) (f t w : ℕ → ℕ) : Prop :=
  ∀ (lim : Limits) (d x : ℕ) (μ : ℕ → ℤ), 1 ≤ x → (lim.space : ℤ) ≤ lim.word →
    ((w x : ℕ) : ℤ) ≤ lim.word → d + 4 ≤ lim.depth →
    Meets lim P p (d + 1) [(x : ℤ)] μ (t x) fun r μ' => r = (f x : ℕ) ∧ μ' = μ

/-- The context of et17: the solver and what hostLoop calls; the procedures of the host; the
two parameter procedures. -/
structure Et17Ctx (P₀ R : Program) (ν : Et17Nums) (Tn : List ℕ → ℕ) (need : List ℕ → Need)
    (Dfun Gfun tD tG wD wG : ℕ → ℕ) : Prop where
  loop : HostCtx P₀ R ν.pS ν.pWriteX ν.pWriteY ν.pScanPairs ν.pScan Tn need
  hLoop : (P₀ ++ R)[ν.pLoop]? = some (hostLoopBody ν.pS ν.pWriteX ν.pWriteY ν.pScanPairs)
  hSqrt : (P₀ ++ R)[ν.pSqrt]? = some sqrtBody
  hBrute : (P₀ ++ R)[ν.pBrute]? = some (bruteBody ν.pScan)
  hChoose : (P₀ ++ R)[ν.pChoose]? = some (choosePrimeBody ν.ch)
  ch : ChCtx (P₀ ++ R) ν.ch
  hCap : (P₀ ++ R)[ν.pCap]? = some queryCapNatBody
  hCeil : (P₀ ++ R)[ν.pCeil]? = some ceilDivBody
  hBitLen : (P₀ ++ R)[ν.pBitLen]? = some bitLenBody
  hDbl : (P₀ ++ R)[ν.pDbl]? = some dblTableBody
  hResid : (P₀ ++ R)[ν.pResid]? = some residBody
  hResidues : (P₀ ++ R)[ν.pResidues]? = some (residuesBody ν.pResid)
  hClasses : (P₀ ++ R)[ν.pClasses]? = some classesBody
  hChunks : (P₀ ++ R)[ν.pChunks]? = some chunksBody
  dProc : ParamProc (P₀ ++ R) ν.pD Dfun tD wD
  gProc : ParamProc (P₀ ++ R) ν.pG Gfun tG wG
  D_pos : ∀ n, 1 ≤ n → 1 ≤ Dfun n

/-! ## The data, the addresses and the local variables of a run -/

/-- The data of the loop over the instances, for the parameters D and g. -/
def hostData (x : TriInst) (D g : ℕ) : HostData :=
  ⟨x.n, D, chosenPrime x.n D x.AB x.BC x.AC, pieceSizeNat D g, queryCapNat x.n D, x.AB, x.BC, x.AC⟩

/-- The address of the residues of `w(a,b)`; the table of doubles is at fr. -/
def aRab (_X : HostData) (U fr : ℕ) : ℕ := fr + (bitLen U + 1)
/-- The address of the residues of `w(b,c)`. -/
def aRbc (X : HostData) (U fr : ℕ) : ℕ := aRab X U fr + X.n * X.n
/-- The address of the residues of `w(a,c)`. -/
def aRac (X : HostData) (U fr : ℕ) : ℕ := aRbc X U fr + X.n * X.n
/-- The address of the starts of the classes. -/
def aCls (X : HostData) (U fr : ℕ) : ℕ := aRac X U fr + X.n * X.n
/-- The address of the running places. -/
def aCur (X : HostData) (U fr : ℕ) : ℕ := aCls X U fr + (X.p + 1)
/-- The address of the rows of the sorted pairs. -/
def aQi (X : HostData) (U fr : ℕ) : ℕ := aCur X U fr + X.p
/-- The address of the columns of the sorted pairs. -/
def aQj (X : HostData) (U fr : ℕ) : ℕ := aQi X U fr + X.n * X.n
/-- The address of the residues of the chunks. -/
def aCr (X : HostData) (U fr : ℕ) : ℕ := aQj X U fr + X.n * X.n
/-- The address of the starts of the chunks. -/
def aCl (X : HostData) (U fr : ℕ) : ℕ := aCr X U fr + (X.n * X.n + X.p)
/-- The address of the lengths of the chunks. -/
def aCw (X : HostData) (U fr : ℕ) : ℕ := aCl X U fr + (X.n * X.n + X.p)
/-- The address of the matrix `matX` of an instance. -/
def aX (X : HostData) (U fr : ℕ) : ℕ := aCw X U fr + (X.n * X.n + X.p)
/-- The address of the matrix `matY` of an instance. -/
def aY (X : HostData) (U fr : ℕ) : ℕ := aX X U fr + X.n * X.D
/-- The address of the answers. -/
def aOut (X : HostData) (U fr : ℕ) : ℕ := aY X U fr + X.n * X.D
/-- The free pointer that is handed to the solver. -/
def aFr (X : HostData) (U fr : ℕ) : ℕ := aOut X U fr + X.cap

/-- The arrays of the host stand one after the other. -/
theorem host_places (X : HostData) (U fr : ℕ) :
    aRab X U fr = fr + (bitLen U + 1) ∧ aRbc X U fr = aRab X U fr + X.n * X.n ∧
      aRac X U fr = aRbc X U fr + X.n * X.n ∧ aCls X U fr = aRac X U fr + X.n * X.n ∧
      aCur X U fr = aCls X U fr + (X.p + 1) ∧ aQi X U fr = aCur X U fr + X.p ∧
      aQj X U fr = aQi X U fr + X.n * X.n ∧ aCr X U fr = aQj X U fr + X.n * X.n ∧
      aCl X U fr = aCr X U fr + (X.n * X.n + X.p) ∧ aCw X U fr = aCl X U fr + (X.n * X.n + X.p) ∧
      aX X U fr = aCw X U fr + (X.n * X.n + X.p) ∧ aY X U fr = aX X U fr + X.n * X.D ∧
      aOut X U fr = aY X U fr + X.n * X.D ∧ aFr X U fr = aOut X U fr + X.cap :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The addresses that hostLoop gets. -/
def hostAddr (x : TriInst) (X : HostData) (fr : ℕ) : HostAddr :=
  ⟨x.ab, x.bc, x.ac, aRac X x.U fr, aRbc X x.U fr, aQi X x.U fr, aQj X x.U fr, aCr X x.U fr,
    aCl X x.U fr, aCw X x.U fr, aX X x.U fr, aY X x.U fr, aOut X x.U fr, aFr X x.U fr⟩

/-- The locals at the start: the arguments, then zeros. -/
def et17Loc0 (x : TriInst) (fr : ℕ) : List ℤ :=
  [(x.n : ℤ), (x.U : ℤ), (x.ab : ℤ), (x.bc : ℤ), (x.ac : ℤ), (fr : ℤ), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- The locals after the first part. -/
def et17LocA (x : TriInst) (fr D g : ℕ) : List ℤ :=
  [(x.n : ℤ), (x.U : ℤ), (x.ab : ℤ), (x.bc : ℤ), (x.ac : ℤ), (fr : ℤ), (D : ℤ), (g : ℤ),
    ((Nat.sqrt D : ℕ) : ℤ), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    (if SmallCase x.n D g then 1 else 0), 0]

/-- The locals of the third part, for the data X of the loop: those after the second part, with the
number of chunks in NumChunks and the result of the last call in Small.  ParG and RootD are not
read. -/
abbrev Et17.locals (x : TriInst) (X : HostData) (fr : ℕ) (g s nch res : ℤ) : List ℤ :=
  [(X.n : ℤ), (x.U : ℤ), (x.ab : ℤ), (x.bc : ℤ), (x.ac : ℤ), (fr : ℤ), (X.D : ℤ), g, s, (X.p : ℤ),
    (X.cap : ℤ), (X.q : ℤ), (X.h : ℤ), ((bitLen x.U : ℕ) : ℤ), ((X.n * X.n : ℕ) : ℤ), 0,
    ((aRab X x.U fr : ℕ) : ℤ), ((aRbc X x.U fr : ℕ) : ℤ), ((aRac X x.U fr : ℕ) : ℤ),
    ((aCls X x.U fr : ℕ) : ℤ), ((aCur X x.U fr : ℕ) : ℤ), ((aQi X x.U fr : ℕ) : ℤ),
    ((aQj X x.U fr : ℕ) : ℤ), ((aCr X x.U fr : ℕ) : ℤ), ((aCl X x.U fr : ℕ) : ℤ),
    ((aCw X x.U fr : ℕ) : ℤ), ((aX X x.U fr : ℕ) : ℤ), ((aY X x.U fr : ℕ) : ℤ),
    ((aOut X x.U fr : ℕ) : ℤ), ((aFr X x.U fr : ℕ) : ℤ), ((X.n * X.n + X.p : ℕ) : ℤ), nch, 0, res,
    ((X.n * X.D : ℕ) : ℤ)]

/-- The locals after the second part (n is not small, so the flag is 0). -/
def et17LocB (x : TriInst) (fr D g : ℕ) : List ℤ :=
  Et17.locals x (hostData x D g) fr g (Nat.sqrt D : ℕ) 0 0

/-- The time of the third part in a run: it depends on the data. -/
def hostRunTime (Tn : List ℕ → ℕ) (X : HostData) (U : ℕ) : ℕ :=
  tDblTable (bitLen U) + 3 * tResidues (X.n * X.n) (bitLen U) + tClasses X.n X.p
    + tChunks X.p X.chunkCount + tHostLoop Tn X + 80

end Light.Sec3
