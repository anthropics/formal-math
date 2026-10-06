/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Lang.Lib.Copy
public import ThreeSumApsp.Programs.Sec3.Theorem17.Hashing.SizeTable
public import ThreeSumApsp.Programs.Sec3.Theorem17.Hashing.StrassenFacts

/-!
# Strassen's algorithm for matrices over ℤ[x]/(x^p - 1) in Z-order

"Computing PQ takes […] O(n^{log₂ 7}) with Strassen's algorithm" (proof of Theorem 17).

strassen(dst, a, b, j, szt, p, scr): dst := a · b for 2^j × 2^j matrices whose entries are vectors
of p numbers, stored in Z-order, so that the four quadrants of a matrix are the four quarters of its
segment.  szt is the address of the table of the sizes 4^i p, and scr is scratch space.

* At level 0 the product is one product in the ring (`strassen_zero`).
* At level j + 1 the routine clears dst and runs seven phases (`strassen_succ`).  phase(a1, a2, sA,
  b1, b2, sB, c1, s1, c2, s2, j, szt, p, scr, q) forms S = a1 + sA a2 and T = b1 + sB b2 in the
  scratch space, M = S · T by a recursive call, and adds s1 M to c1 and s2 M to c2 (`phase_meets`).
* Between two phases the four quarters of dst hold four lists, and the operands and the table are in
  place (`StrInv`); a phase changes two of the lists (`phase_step`).  After the seven phases the
  four lists are the four quadrants of the product (`sevenPhases_spec`).
* `strassen_spec` is the induction on the level: the product stands at dst after at most
  `strSteps p j` steps, and nothing has changed outside dst and `strScr p j` cells of scratch space.
  The recursion `strSteps` is bounded where the running times are added up.
-/

@[expose] public section

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec

/-! ## The program -/

/-- The numbers of the procedures that Strassen's algorithm consists of. -/
structure StrNums : Type where
  pVlin : ℕ
  pCconv : ℕ
  pFill : ℕ
  pPhase : ℕ
  pStr : ℕ

namespace Phase

/-- The local variables of phase: the arguments a1, a2, sA, b1, b2, sB, c1, s1, c2, s2, j, szt, p,
scr, q, and a local that takes the results of the calls. -/
abbrev OpA1 : ℕ := 0
@[inherit_doc OpA1] abbrev OpA2 : ℕ := 1
@[inherit_doc OpA1] abbrev SignA : ℕ := 2
@[inherit_doc OpA1] abbrev OpB1 : ℕ := 3
@[inherit_doc OpA1] abbrev OpB2 : ℕ := 4
@[inherit_doc OpA1] abbrev SignB : ℕ := 5
@[inherit_doc OpA1] abbrev Out1 : ℕ := 6
@[inherit_doc OpA1] abbrev Sign1 : ℕ := 7
@[inherit_doc OpA1] abbrev Out2 : ℕ := 8
@[inherit_doc OpA1] abbrev Sign2 : ℕ := 9
@[inherit_doc OpA1] abbrev Level : ℕ := 10
@[inherit_doc OpA1] abbrev Sizes : ℕ := 11
@[inherit_doc OpA1] abbrev Prime : ℕ := 12
@[inherit_doc OpA1] abbrev Scr : ℕ := 13
@[inherit_doc OpA1] abbrev Size : ℕ := 14
@[inherit_doc OpA1] abbrev Res : ℕ := 15

end Phase

open Phase in
/-- The operands of a phase: S := a1 + sA a2 at scr, and T := b1 + sB b2 at scr + q. -/
def phaseOpnds (ν : StrNums) : Stmt :=
  .call ν.pVlin [v Scr, v OpA1, v OpA2, v Size, v SignA] Res ;;
  .call ν.pVlin [v Scr +' v Size, v OpB1, v OpB2, v Size, v SignB] Res

open Phase in
/-- The end of a phase: c1 := c1 + s1 M and c2 := c2 + s2 M, where M stands at scr + 2 q. -/
def phaseAccum (ν : StrNums) : Stmt :=
  .call ν.pVlin [v Out1, v Out1, v Scr +' v Size +' v Size, v Size, v Sign1] Res ;;
  .call ν.pVlin [v Out2, v Out2, v Scr +' v Size +' v Size, v Size, v Sign2] Res

open Phase in
/-- phase(a1, a2, sA, b1, b2, sB, c1, s1, c2, s2, j, szt, p, scr, q): the operands; M := S · T at
scr + 2 q, with the scratch space from scr + 3 q on; the end. -/
def phaseBody (ν : StrNums) : Stmt :=
  phaseOpnds ν ;;
  .call ν.pStr [v Scr +' v Size +' v Size, v Scr, v Scr +' v Size, v Level, v Sizes, v Prime,
    v Scr +' v Size +' v Size +' v Size] Res ;;
  phaseAccum ν

namespace Str

/-- The local variables of strassen: the arguments dst, a, b, j, szt, p, scr; the numbers q, 2q, 3q,
where q is the size of a quarter; j - 1; a local that is not used; a local that takes the results of
the calls. -/
abbrev Dst : ℕ := 0
@[inherit_doc Dst] abbrev ArgA : ℕ := 1
@[inherit_doc Dst] abbrev ArgB : ℕ := 2
@[inherit_doc Dst] abbrev Level : ℕ := 3
@[inherit_doc Dst] abbrev Sizes : ℕ := 4
@[inherit_doc Dst] abbrev Prime : ℕ := 5
@[inherit_doc Dst] abbrev Scr : ℕ := 6
@[inherit_doc Dst] abbrev Size1 : ℕ := 7
@[inherit_doc Dst] abbrev Size2 : ℕ := 8
@[inherit_doc Dst] abbrev Size3 : ℕ := 9
@[inherit_doc Dst] abbrev Below : ℕ := 10
@[inherit_doc Dst] abbrev Res : ℕ := 12

end Str

open Str in
/-- The address of the quarter number t of the segment whose address is in local x. -/
@[simp] def qAddr (x : ℕ) : ℕ → Expr
  | 0 => v x
  | 1 => v x +' v Size1
  | 2 => v x +' v Size2
  | _ => v x +' v Size3

/-- The sign 1. -/
@[simp] def sPos : Expr := k 1

/-- The sign 0. -/
@[simp] def sNil : Expr := k 0

/-- The sign -1. -/
@[simp] def sNeg : Expr := k 0 -' k 1

open Str in
/-- A call of phase from the body of strassen: the operands are the quarters number a1, a2 of a and
b1, b2 of b, and the results go to the quarters number c1, c2 of dst. -/
def phaseCall (ν : StrNums) (a1 a2 : ℕ) (sA : Expr) (b1 b2 : ℕ) (sB : Expr) (c1 : ℕ) (s1 : Expr)
    (c2 : ℕ) (s2 : Expr) : Stmt :=
  .call ν.pPhase [qAddr ArgA a1, qAddr ArgA a2, sA, qAddr ArgB b1, qAddr ArgB b2, sB, qAddr Dst c1,
    s1, qAddr Dst c2, s2, v Below, v Sizes, v Prime, v Scr, v Size1] Res

/-- The seven phases. -/
def sevenPhases (ν : StrNums) : Stmt :=
  phaseCall ν 0 3 sPos 0 3 sPos 0 sPos 3 sPos ;;
  phaseCall ν 2 3 sPos 0 0 sNil 2 sPos 3 sNeg ;;
  phaseCall ν 0 0 sNil 1 3 sNeg 1 sPos 3 sPos ;;
  phaseCall ν 3 3 sNil 2 0 sNeg 0 sPos 2 sPos ;;
  phaseCall ν 0 1 sPos 3 3 sNil 0 sNeg 1 sPos ;;
  phaseCall ν 2 0 sNeg 0 1 sPos 3 sPos 0 sNil ;;
  phaseCall ν 1 3 sNeg 2 3 sPos 0 sPos 3 sNil

open Str in
/-- strassen(dst, a, b, j, szt, p, scr). -/
def strBody (ν : StrNums) : Stmt :=
  .ite (v Level =' k 0)
    (.call ν.pCconv [v Dst, v ArgA, v ArgB, v Prime] Res)
    (.set Below (v Level -' k 1) ;;
     .set Size1 (M (v Sizes +' v Below)) ;;
     .set Size2 (v Size1 +' v Size1) ;;
     .set Size3 (v Size2 +' v Size1) ;;
     .call ν.pFill [v Dst, v Size3 +' v Size1, k 0] Res ;;
     sevenPhases ν)

/-- The procedures of Strassen's algorithm stand in the program at their numbers. -/
structure StrProg (P : Program) (ν : StrNums) : Prop where
  vlin : P[ν.pVlin]? = some vlinBody
  cconv : P[ν.pCconv]? = some cconvBody
  fill : P[ν.pFill]? = some fillBody
  phase : P[ν.pPhase]? = some (phaseBody ν)
  str : P[ν.pStr]? = some (strBody ν)

/-! ## The specification -/

/-- The scratch space of strassen at level j. -/
def strScr (p : ℕ) : ℕ → ℕ
  | 0 => 0
  | j + 1 => 3 * (4 ^ j * p) + strScr p j

/-- The steps of strassen at level j.  At level j + 1, with q = 4^j p: seven phases, each with a
recursive call and 92 q further steps, and the clearing of 4 q cells in 13 steps each, so that
696 = 7 · 92 + 4 · 13; the 900 covers the steps that do not depend on q. -/
def strSteps (p : ℕ) : ℕ → ℕ
  | 0 => 32 * p * p + 21 * p + 16
  | j + 1 => 7 * strSteps p j + 696 * (4 ^ j * p) + 900

variable {lim : Limits} {P : Program} {d : ℕ}

/-- The arguments of strassen other than the level, with the data behind them: the operands `A` and
`B` have `len` numbers each, bounded by `α` and `β`, and the table of sizes reaches level `J`. -/
structure StrArgs : Type where
  (dst a b szt p scr : ℕ)
  (len J : ℕ)
  (A B : List ℤ)
  (α β : ℤ)

/-- The values of the arguments of strassen at level j. -/
abbrev StrArgs.vals (x : StrArgs) (j : ℕ) : List ℤ := [x.dst, x.a, x.b, j, x.szt, x.p, x.scr]

/-- What strassen assumes at level j.  The operands have len = 4^j p numbers each.  They and the
table of sizes lie below dst, and dst lies below the scratch space. -/
structure StrPre (lim : Limits) (μ : ℕ → ℤ) (j : ℕ) (x : StrArgs) : Prop where
  size : x.len = 4 ^ j * x.p
  prime : 1 ≤ x.p
  opA : ArrayAt μ x.a x.A x.len x.α x.dst
  opB : ArrayAt μ x.b x.B x.len x.β x.dst
  table : ListAt μ x.szt (szList x.p x.J) (x.J + 1) x.dst
  oneA : 1 ≤ x.α := by light_arith
  oneB : 1 ≤ x.β := by light_arith
  word : 4 * strassenBound x.p j x.α x.β ≤ lim.word := by light_arith
  level : j ≤ x.J := by light_arith
  dstBelow : x.dst + x.len ≤ x.scr := by light_arith
  space : x.scr + strScr x.p j ≤ lim.space := by light_arith
  room : 8 * x.len < lim.space := by light_arith

/-- What strassen assumes still holds when no cell below dst has changed. -/
theorem StrPre.keep {μ μ' : ℕ → ℤ} {j : ℕ} {x : StrArgs} (pre : StrPre lim μ j x)
    (hs : Kept μ μ' x.dst := by light_keep) : StrPre lim μ' j x :=
  { pre with opA := pre.opA.keep, opB := pre.opB.keep, table := pre.table.keep }

/-- What strassen does at level j, in the program P: it writes the product to dst and changes
nothing else but the scratch space. -/
def StrSpec (lim : Limits) (P : Program) (ν : StrNums) (j : ℕ) : Prop :=
  ∀ (x : StrArgs) (μ : ℕ → ℤ), StrPre lim μ j x → ∀ d, d + 2 * j + 1 ≤ lim.depth →
    Meets lim P ν.pStr d (x.vals j) μ (strSteps x.p j) fun _ μ' =>
      Seg μ' x.dst (strassenList x.p j x.A x.B) ∧ SameOutside2 μ μ' x.dst x.len x.scr (strScr x.p j)

/-! ## A phase -/

/-- The arguments of phase other than the level, with the data behind them: the six lists that stand
at the six addresses, the bounds `α` and `β` on the operands, and the level `J` that the table of
sizes reaches. -/
structure PhaseArgs : Type where
  (a1 a2 : ℕ) (sA : ℤ) (b1 b2 : ℕ) (sB : ℤ) (c1 : ℕ) (s1 : ℤ) (c2 : ℕ) (s2 : ℤ)
  (szt p scr q J : ℕ)
  (A1 A2 B1 B2 C1 C2 : List ℤ)
  (α β : ℤ)

namespace PhaseArgs

variable (x : PhaseArgs) (j : ℕ)

/-- The values of the arguments of phase at level j. -/
abbrev vals : List ℤ :=
  [x.a1, x.a2, x.sA, x.b1, x.b2, x.sB, x.c1, x.s1, x.c2, x.s2, j, x.szt, x.p, x.scr, x.q]

/-- The first operand of the product of the phase, S = A1 + sA A2. -/
abbrev S : List ℤ := vlinList x.sA x.A1 x.A2

/-- The second operand of the product of the phase, T = B1 + sB B2. -/
abbrev T : List ℤ := vlinList x.sB x.B1 x.B2

/-- The product of the phase, M = S · T. -/
abbrev prod : List ℤ := phaseM x.p j x.sA x.A1 x.A2 x.sB x.B1 x.B2

/-- The arguments of the recursive call: S stands at scr, T at scr + q, the product goes to
scr + 2 q, and the scratch space begins at scr + 3 q. -/
@[simp] def inner : StrArgs :=
  { dst := x.scr + x.q + x.q, a := x.scr, b := x.scr + x.q, szt := x.szt, p := x.p
    scr := x.scr + x.q + x.q + x.q, len := x.q, J := x.J, A := x.S, B := x.T
    α := 2 * x.α, β := 2 * x.β }

end PhaseArgs

/-- What a phase assumes at level j + 1.  The six lists have q = 4^j p numbers each.  All of them
and the table of sizes lie below the scratch space, and the two results do not meet. -/
structure PhasePre (lim : Limits) (μ : ℕ → ℤ) (j : ℕ) (x : PhaseArgs) : Prop where
  size : x.q = 4 ^ j * x.p
  prime : 1 ≤ x.p
  opA1 : ArrayAt μ x.a1 x.A1 x.q x.α x.scr
  opA2 : ArrayAt μ x.a2 x.A2 x.q x.α x.scr
  opB1 : ArrayAt μ x.b1 x.B1 x.q x.β x.scr
  opB2 : ArrayAt μ x.b2 x.B2 x.q x.β x.scr
  out1 : ArrayAt μ x.c1 x.C1 x.q (2 * strassenBound x.p (j + 1) x.α x.β) x.scr
  out2 : ArrayAt μ x.c2 x.C2 x.q (2 * strassenBound x.p (j + 1) x.α x.β) x.scr
  table : ListAt μ x.szt (szList x.p x.J) (x.J + 1) x.scr
  signA : |x.sA| ≤ 1
  signB : |x.sB| ≤ 1
  sign1 : |x.s1| ≤ 1
  sign2 : |x.s2| ≤ 1
  oneA : 1 ≤ x.α
  oneB : 1 ≤ x.β
  word : 4 * strassenBound x.p (j + 1) x.α x.β ≤ lim.word
  space : x.scr + strScr x.p (j + 1) ≤ lim.space
  apart : Apart x.c1 x.q x.c2 x.q := by light_arith
  level : j ≤ x.J := by light_arith
  room : 8 * x.q < lim.space := by light_arith

/-- What a phase promises: s1 M has been added to the list at c1 and s2 M to the list at c2, and
nothing else has changed but the scratch space. -/
structure PhasePost (μ : ℕ → ℤ) (j : ℕ) (x : PhaseArgs) (μ' : ℕ → ℤ) : Prop where
  out1 : Seg μ' x.c1 (vlinList x.s1 x.C1 (x.prod j))
  out2 : Seg μ' x.c2 (vlinList x.s2 x.C2 (x.prod j))
  same : SameOutside3 μ μ' x.c1 x.q x.c2 x.q x.scr (strScr x.p (j + 1))

section phase

variable {ν : StrNums} {μ μ' : ℕ → ℤ} {j : ℕ} {x : PhaseArgs}

namespace PhasePre

/-- The product of a phase has q numbers. -/
theorem length_prod (pre : PhasePre lim μ j x) : (x.prod j).length = x.q := by
  have hq := pre.size
  rw [hq]
  exact length_strassenList x.p j _ _ (hq ▸ length_vlinList _ pre.opA1.len pre.opA2.len)
    (hq ▸ length_vlinList _ pre.opB1.len pre.opB2.len)

/-- The bound of level j for operands that are sums of two is not negative. -/
theorem bound_nonneg (pre : PhasePre lim μ j x) :
    0 ≤ strassenBound x.p j (2 * x.α) (2 * x.β) :=
  strassenBound_nonneg (by have := pre.oneA; omega) (by have := pre.oneB; omega)

/-- The product of a phase is bounded by strassenBound p j (2 α) (2 β). -/
theorem absLe_prod (pre : PhasePre lim μ j x) :
    AbsLe (x.prod j) (strassenBound x.p j (2 * x.α) (2 * x.β)) := by
  have hα := pre.oneA
  have hβ := pre.oneB
  exact absLe_strassenList x.p j _ _ (2 * x.α) (2 * x.β)
    ((pre.opA1.bound.vlinList pre.opA2.bound pre.signA).trans_le (by omega))
    ((pre.opB1.bound.vlinList pre.opB2.bound pre.signB).trans_le (by omega)) (by omega) (by omega)

/-- The scratch space of level j + 1: three lists of q numbers, and the scratch space of level j. -/
theorem space_inner (pre : PhasePre lim μ j x) : x.scr + (3 * x.q + strScr x.p j) ≤ lim.space := by
  have := pre.space
  rwa [strScr, ← pre.size] at this

/-- What a phase assumes still holds when no cell below scr has changed. -/
theorem keep (pre : PhasePre lim μ j x) (hs : Kept μ μ' x.scr := by light_keep) :
    PhasePre lim μ' j x :=
  { pre with
    opA1 := pre.opA1.keep, opA2 := pre.opA2.keep, opB1 := pre.opB1.keep, opB2 := pre.opB2.keep
    out1 := pre.out1.keep, out2 := pre.out2.keep, table := pre.table.keep }

/-- What the recursive call of a phase assumes, once the two operands stand in the scratch space. -/
theorem inner (pre : PhasePre lim μ j x) (segS : Seg μ x.scr x.S)
    (segT : Seg μ (x.scr + x.q) x.T) : StrPre lim μ j x.inner := by
  have hB4 := strassenBound_succ x.p j x.α x.β
  have hB0 := pre.bound_nonneg
  have space := pre.space_inner
  light_facts pre
  exact
    { size := pre.size, prime := pre.prime, table := pre.table.mono
      opA := pre.opA1.vlinList pre.opA2.len pre.opA2.bound pre.signA segS
      opB := pre.opB1.vlinList pre.opB2.len pre.opB2.bound pre.signB segT }

end PhasePre

variable (prog : StrProg P ν) (hw : (lim.space : ℤ) ≤ lim.word)
include prog hw

/-- **The operands of a phase.** -/
theorem phaseOpnds_spec (pre : PhasePre lim μ j x) (hd : d < lim.depth) :
    Ends lim P d (phaseOpnds ν) ⟨frame (x.vals j), μ⟩ (46 * x.q + 28) fun σ' =>
      ∃ (r : ℤ) (μ' : ℕ → ℤ), σ' = ⟨frame (x.vals j ++ [r]), μ'⟩ ∧
        Seg μ' x.scr x.S ∧ Seg μ' (x.scr + x.q) x.T ∧ SameOutside μ μ' x.scr (2 * x.q) := by
  have space := pre.space_inner
  have word := pre.word
  have hleα := le_strassenBound_left (j := j + 1) pre.prime pre.oneA pre.oneB
  have hleβ := le_strassenBound_right (j := j + 1) pre.prime pre.oneA pre.oneB
  have lenS := length_vlinList x.sA pre.opA1.len pre.opA2.len
  light_facts pre.opA1 pre.opA2 pre.opB1 pre.opB2
  -- S := a1 + sA a2
  light_call (vlin_meets prog.vlin hw (dst := x.scr) (V := x.α)
    { opA := pre.opA1.mono, opB := pre.opA2.mono, sign := pre.signA }) with _ μ₁ ⟨segS, rest₁⟩
  -- T := b1 + sB b2
  light_call (vlin_meets prog.vlin hw (dst := x.scr + x.q) (V := x.β)
    { opA := pre.opB1.keep.mono, opB := pre.opB2.keep.mono, sign := pre.signB })
    with r μ₂ ⟨segT, rest₂⟩
  exact ⟨r, μ₂, rfl, segS.keep, segT, by light_keep⟩

/-- **The end of a phase.** -/
theorem phaseAccum_spec (pre : PhasePre lim μ j x) (segM : Seg μ (x.scr + x.q + x.q) (x.prod j))
    (hd : d < lim.depth) (r : ℤ) :
    Ends lim P d (phaseAccum ν) ⟨frame (x.vals j ++ [r]), μ⟩ (46 * x.q + 34) fun σ' =>
      Seg σ'.mem x.c1 (vlinList x.s1 x.C1 (x.prod j)) ∧
        Seg σ'.mem x.c2 (vlinList x.s2 x.C2 (x.prod j)) ∧
        SameOutside2 μ σ'.mem x.c1 x.q x.c2 x.q := by
  have space := pre.space_inner
  have word := pre.word
  have apart := pre.apart
  have hB4 := strassenBound_succ x.p j x.α x.β
  have hB0 := pre.bound_nonneg
  have len1 := length_vlinList x.s1 pre.out1.len pre.length_prod
  light_facts pre.out1 pre.out2
  have opM : ArrayAt μ (x.scr + x.q + x.q) (x.prod j) x.q (2 * strassenBound x.p (j + 1) x.α x.β)
      lim.space :=
    { len := pre.length_prod, seg := segM, bound := pre.absLe_prod.trans_le (by omega) }
  -- c1 := c1 + s1 M
  light_call (vlin_meets prog.vlin hw (dst := x.c1)
    { opA := pre.out1.mono, opB := opM, sign := pre.sign1 }) with _ μ₁ ⟨seg1, rest₁⟩
  -- c2 := c2 + s2 M
  light_call (vlin_meets prog.vlin hw (dst := x.c2)
    { opA := pre.out2.keep.mono, opB := opM.keep, sign := pre.sign2 }) with _ μ₂ ⟨seg2, rest₂⟩
  exact ⟨seg1.keep, seg2, by light_keep⟩

/-- **A phase** adds s1 M to c1 and s2 M to c2, where M = (a1 + sA a2) · (b1 + sB b2), and changes
nothing else but the scratch space. -/
theorem phase_meets (H : StrSpec lim P ν j) (pre : PhasePre lim μ j x)
    (hd : d + 2 * j + 2 ≤ lim.depth) :
    Meets lim P ν.pPhase d (x.vals j) μ (92 * x.q + 83 + strSteps x.p j) fun _ =>
      PhasePost μ j x := by
  have space := pre.space_inner
  have hscr : strScr x.p (j + 1) = 3 * x.q + strScr x.p j := by rw [strScr, pre.size]
  refine Meets.of_body prog.phase ?_
  -- S := a1 + sA a2; T := b1 + sB b2
  light_piece (phaseOpnds_spec prog hw pre (by omega)) with _ ⟨r, μ₁, rfl, segS, segT, rest₁⟩
  -- M := S · T
  light_call (H x.inner μ₁ (pre.keep.inner segS segT) _ (by omega)) with r' μ₂ ⟨segM, rest₂⟩
  dsimp only [PhaseArgs.inner] at segM rest₂
  -- c1 := c1 + s1 M; c2 := c2 + s2 M
  light_piece (phaseAccum_spec prog hw pre.keep segM (by omega) r') with σ' ⟨seg1, seg2, rest₃⟩
  exact ⟨seg1, seg2, by light_keep⟩

end phase

/-! ## Between two phases -/

/-- A row of the table of Strassen's seven products.  With a[t], b[t] and c[t] for the quarters
number t of the operands and of the result, the product is
M = (a[a1] + sA a[a2]) · (b[b1] + sB b[b2]), and s1 M is added to c[c1] and s2 M to c[c2]. -/
structure PhaseRow : Type where
  (a1 a2 : ℕ) (sA : ℤ) (b1 b2 : ℕ) (sB : ℤ) (c1 : ℕ) (s1 : ℤ) (c2 : ℕ) (s2 : ℤ)

/-- The entries of a row are numbers of quarters and signs, and the two results are different
quarters. -/
structure PhaseRow.Ok (row : PhaseRow) : Prop where
  a1 : row.a1 < 4
  a2 : row.a2 < 4
  b1 : row.b1 < 4
  b2 : row.b2 < 4
  c1 : row.c1 < 4
  c2 : row.c2 < 4
  ne : row.c1 ≠ row.c2
  sA : |row.sA| ≤ 1
  sB : |row.sB| ≤ 1
  s1 : |row.s1| ≤ 1
  s2 : |row.s2| ≤ 1

/-- The arguments of the phase of a row, called from strassen with the arguments x, when a
quarter has q numbers and the four quarters of dst hold the lists L 0, …, L 3. -/
@[simp] def StrArgs.phase (x : StrArgs) (q : ℕ) (L : ℕ → List ℤ) (row : PhaseRow) : PhaseArgs :=
  { a1 := x.a + row.a1 * q, a2 := x.a + row.a2 * q, sA := row.sA
    b1 := x.b + row.b1 * q, b2 := x.b + row.b2 * q, sB := row.sB
    c1 := x.dst + row.c1 * q, s1 := row.s1, c2 := x.dst + row.c2 * q, s2 := row.s2
    szt := x.szt, p := x.p, scr := x.scr, q := q, J := x.J
    A1 := quarter q row.a1 x.A, A2 := quarter q row.a2 x.A
    B1 := quarter q row.b1 x.B, B2 := quarter q row.b2 x.B
    C1 := L row.c1, C2 := L row.c2, α := x.α, β := x.β }

/-- The four lists after the phase of a row. -/
def StrArgs.after (x : StrArgs) (j q : ℕ) (L : ℕ → List ℤ) (row : PhaseRow) : ℕ → List ℤ :=
  Function.update (Function.update L row.c1 (vlinList row.s1 (L row.c1) ((x.phase q L row).prod j)))
    row.c2 (vlinList row.s2 (L row.c2) ((x.phase q L row).prod j))

/-- The state of strassen at level j + 1 after κ phases: what strassen assumes still holds, and the
four quarters of dst hold the lists L 0, …, L 3, of q = 4^j p numbers each, bounded by κ times the
bound on a product. -/
structure StrInv (lim : Limits) (μ : ℕ → ℤ) (j q : ℕ) (x : StrArgs) (L : ℕ → List ℤ) (κ : ℕ) : Prop
    extends StrPre lim μ (j + 1) x where
  quarterLen : q = 4 ^ j * x.p
  out : ∀ t < 4, ArrayAt μ (x.dst + t * q) (L t) q (κ * strassenBound x.p j (2 * x.α) (2 * x.β))
    x.scr

/-- Two different quarters do not meet. -/
theorem quarter_apart {t t' : ℕ} (q : ℕ) (h : t ≠ t') :
    t * q + q ≤ t' * q ∨ t' * q + q ≤ t * q :=
  (Nat.lt_or_gt_of_ne h).imp (fun h' => Nat.mul_add_le_mul h' le_rfl)
    fun h' => Nat.mul_add_le_mul h' le_rfl

/-- A property of the four lists after two of them have been replaced. -/
theorem forall_update_update {Φ : ℕ → List ℤ → Prop} {L : ℕ → List ℤ} {t₁ t₂ : ℕ}
    {X₁ X₂ : List ℤ} (h : ∀ t < 4, t ≠ t₁ → t ≠ t₂ → Φ t (L t)) (h₁ : Φ t₁ X₁) (h₂ : Φ t₂ X₂) :
    ∀ t < 4, Φ t (Function.update (Function.update L t₁ X₁) t₂ X₂ t) := by
  intro t ht
  by_cases e₂ : t = t₂
  · rw [e₂, Function.update_self]
    exact h₂
  by_cases e₁ : t = t₁
  · rw [Function.update_of_ne e₂, e₁, Function.update_self]
    exact h₁
  · rw [Function.update_of_ne e₂, Function.update_of_ne e₁]
    exact h t ht e₁ e₂

section step

variable {ν : StrNums} {μ μ' : ℕ → ℤ} {j q κ : ℕ} {x : StrArgs} {L : ℕ → List ℤ} {row : PhaseRow}

namespace StrInv

/-- An operand has four quarters. -/
theorem size_eq (inv : StrInv lim μ j q x L κ) : x.len = 4 * q := by
  rw [inv.size, inv.quarterLen]
  ring

/-- What the phase of a row assumes holds between two phases. -/
theorem phasePre (inv : StrInv lim μ j q x L κ) (hκ : κ ≤ 7) (hr : row.Ok) :
    PhasePre lim μ j (x.phase q L row) := by
  have hB0 : 0 ≤ strassenBound x.p j (2 * x.α) (2 * x.β) :=
    strassenBound_nonneg (by have := inv.oneA; omega) (by have := inv.oneB; omega)
  have hbound : (κ : ℤ) * strassenBound x.p j (2 * x.α) (2 * x.β) ≤
      2 * strassenBound x.p (j + 1) x.α x.β := by
    rw [strassenBound_succ]
    calc (κ : ℤ) * strassenBound x.p j (2 * x.α) (2 * x.β)
        ≤ 8 * strassenBound x.p j (2 * x.α) (2 * x.β) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hκ.trans (by norm_num)) hB0
      _ = 2 * (4 * strassenBound x.p j (2 * x.α) (2 * x.β)) := by ring
  have hq := inv.size_eq
  have opA := (hq ▸ inv.opA).mono le_rfl (Nat.le_of_add_right_le inv.dstBelow)
  have opB := (hq ▸ inv.opB).mono le_rfl (Nat.le_of_add_right_le inv.dstBelow)
  have hapart := quarter_apart q hr.ne
  light_facts inv.toStrPre
  exact
    { size := inv.quarterLen, prime := inv.prime, table := inv.table.mono
      opA1 := opA.quarter hr.a1, opA2 := opA.quarter hr.a2
      opB1 := opB.quarter hr.b1, opB2 := opB.quarter hr.b2
      out1 := (inv.out _ hr.c1).mono hbound le_rfl, out2 := (inv.out _ hr.c2).mono hbound le_rfl
      signA := hr.sA, signB := hr.sB, sign1 := hr.s1, sign2 := hr.s2
      oneA := inv.oneA, oneB := inv.oneB, word := inv.word, space := inv.space }

/-- The state after a phase: two of the four lists are replaced, the rest is as before. -/
theorem step (inv : StrInv lim μ j q x L κ) (hκ : κ ≤ 7) (hr : row.Ok)
    (post : PhasePost μ j (x.phase q L row) μ') :
    StrInv lim μ' j q x (x.after j q L row) (κ + 1) := by
  have pre := inv.phasePre hκ hr
  have hB0 : 0 ≤ strassenBound x.p j (2 * x.α) (2 * x.β) := pre.bound_nonneg
  have hsucc : ((κ + 1 : ℕ) : ℤ) * strassenBound x.p j (2 * x.α) (2 * x.β) =
      κ * strassenBound x.p j (2 * x.α) (2 * x.β) + strassenBound x.p j (2 * x.α) (2 * x.β) := by
    push_cast
    ring
  have hq := inv.size_eq
  have dstBelow := inv.dstBelow
  have same : SameOutside3 μ μ' (x.dst + row.c1 * q) q (x.dst + row.c2 * q) q x.scr
      (strScr x.p (j + 1)) := post.same
  have pre' : StrPre lim μ' (j + 1) x := inv.toStrPre.keep
  refine
    { toStrPre := pre'
      quarterLen := inv.quarterLen
      out := forall_update_update
        (Φ := fun t X => ArrayAt μ' (x.dst + t * q) X q _ x.scr) (fun t ht e₁ e₂ => ?_)
        ((inv.out _ hr.c1).vlinList pre.length_prod pre.absLe_prod hr.s1 post.out1 hsucc.ge
          pre.out1.below)
        ((inv.out _ hr.c2).vlinList pre.length_prod pre.absLe_prod hr.s2 post.out2 hsucc.ge
          pre.out2.below) }
  · have hapart₁ := quarter_apart q e₁
    have hapart₂ := quarter_apart q e₂
    have hin : t * q + q ≤ 4 * q := Nat.mul_add_le_mul ht le_rfl
    exact (inv.out t ht).keep.mono

end StrInv

/-- **A phase, called from the body of strassen**: with M the product of the row, s1 M is added to
the list number c1 and s2 M to the list number c2. -/
theorem phase_step (prog : StrProg P ν) (hw : (lim.space : ℤ) ≤ lim.word)
    (H : StrSpec lim P ν j) (inv : StrInv lim μ j q x L κ) (hd : d + 2 * j + 2 ≤ lim.depth)
    (row : PhaseRow) (hκ : κ ≤ 7 := by omega)
    (hr : row.Ok := by constructor <;> simp) :
    Meets lim P ν.pPhase d ((x.phase q L row).vals j) μ (92 * q + 83 + strSteps x.p j) fun _ μ' =>
      StrInv lim μ' j q x (x.after j q L row) (κ + 1) ∧
        SameOutside2 μ μ' x.dst (4 * q) x.scr (strScr x.p (j + 1)) := by
  refine (phase_meets prog hw H (inv.phasePre hκ hr) hd).mono le_rfl fun _ μ' post => ?_
  have hin₁ : row.c1 * q + q ≤ 4 * q := Nat.mul_add_le_mul hr.c1 le_rfl
  have hin₂ : row.c2 * q + q ≤ 4 * q := Nat.mul_add_le_mul hr.c2 le_rfl
  have same : SameOutside3 μ μ' (x.dst + row.c1 * q) q (x.dst + row.c2 * q) q x.scr
      (strScr x.p (j + 1)) := post.same
  exact ⟨inv.step hκ hr post, by light_keep⟩

end step

/-- Four lists of q numbers in the four quarters of a segment are one list. -/
theorem seg_of_quarters {μ : ℕ → ℤ} {dst q : ℕ} {L : ℕ → List ℤ}
    (seg : ∀ t < 4, Seg μ (dst + t * q) (L t)) (len : ∀ t < 4, (L t).length = q) :
    Seg μ dst (L 0 ++ L 1 ++ L 2 ++ L 3) := by
  rw [seg_append, seg_append, seg_append]
  simp only [List.length_append, len 0 (by omega), len 1 (by omega), len 2 (by omega)]
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · simpa using seg 0 (by omega)
  · simpa using seg 1 (by omega)
  · rw [show dst + (q + q) = dst + 2 * q by ring]
    exact seg 2 (by omega)
  · rw [show dst + (q + q + q) = dst + 3 * q by ring]
    exact seg 3 (by omega)

/-- A quarter of a cleared segment is cleared. -/
theorem seg_zeros_quarter {μ : ℕ → ℤ} {dst q t : ℕ} (h : Seg μ dst (List.replicate (4 * q) 0))
    (ht : t < 4) : Seg μ (dst + t * q) (zeros q) := by
  intro i hi
  have hi' : i < q := by simpa [zeros] using hi
  have hin : t * q + q ≤ 4 * q := Nat.mul_add_le_mul ht le_rfl
  have hcell := h (t * q + i) (by simp; omega)
  rw [List.getElem_replicate, ← Nat.add_assoc] at hcell
  simpa [zeros] using hcell

/-! ## The seven phases -/

section levels

variable {ν : StrNums} {μ : ℕ → ℤ} {j q : ℕ} {x : StrArgs} (prog : StrProg P ν)
  (hw : (lim.space : ℤ) ≤ lim.word)
include prog hw

/-- **The seven phases** turn four cleared quarters into the product. -/
theorem sevenPhases_spec (H : StrSpec lim P ν j)
    (inv : StrInv lim μ j q x (fun _ => zeros q) 0) (hd : d + 2 * j + 3 ≤ lim.depth)
    (lvl z r : ℤ) :
    Ends lim P d (sevenPhases ν)
      ⟨frame [x.dst, x.a, x.b, lvl, x.szt, x.p, x.scr, q, (2 * q : ℕ), (3 * q : ℕ), j, z, r], μ⟩
      (7 * (92 * q + 123 + strSteps x.p j)) fun σ' =>
        Seg σ'.mem x.dst (strassenList x.p (j + 1) x.A x.B) ∧
        SameOutside2 μ σ'.mem x.dst x.len x.scr (strScr x.p (j + 1)) := by
  have hq := inv.size_eq
  have hd' : d + 1 + 2 * j + 2 ≤ lim.depth := by omega
  light_facts inv.toStrPre inv.opA inv.opB
  -- M₁ = (a₀ + a₃) (b₀ + b₃) goes to the quarters 0 and 3
  refine Ends.callToThen (phase_step prog hw H inv hd' ⟨0, 3, 1, 0, 3, 1, 0, 1, 3, 1⟩) ?_
    (hT := by simp; omega)
  rintro _ μ₁ ⟨inv₁, rest₁⟩
  -- M₂ = (a₂ + a₃) b₀ goes to 2 and, with the sign -1, to 3
  refine Ends.callToThen (phase_step prog hw H inv₁ hd' ⟨2, 3, 1, 0, 0, 0, 2, 1, 3, -1⟩) ?_
    (hT := by simp; omega)
  rintro _ μ₂ ⟨inv₂, rest₂⟩
  -- M₃ = a₀ (b₁ - b₃) goes to 1 and 3
  refine Ends.callToThen (phase_step prog hw H inv₂ hd' ⟨0, 0, 0, 1, 3, -1, 1, 1, 3, 1⟩) ?_
    (hT := by simp; omega)
  rintro _ μ₃ ⟨inv₃, rest₃⟩
  -- M₄ = a₃ (b₂ - b₀) goes to 0 and 2
  refine Ends.callToThen (phase_step prog hw H inv₃ hd' ⟨3, 3, 0, 2, 0, -1, 0, 1, 2, 1⟩) ?_
    (hT := by simp; omega)
  rintro _ μ₄ ⟨inv₄, rest₄⟩
  -- M₅ = (a₀ + a₁) b₃ goes, with the sign -1, to 0, and to 1
  refine Ends.callToThen (phase_step prog hw H inv₄ hd' ⟨0, 1, 1, 3, 3, 0, 0, -1, 1, 1⟩) ?_
    (hT := by simp; omega)
  rintro _ μ₅ ⟨inv₅, rest₅⟩
  -- M₆ = (a₂ - a₀) (b₀ + b₁) goes to 3
  refine Ends.callToThen (phase_step prog hw H inv₅ hd' ⟨2, 0, -1, 0, 1, 1, 3, 1, 0, 0⟩) ?_
    (hT := by simp; omega)
  rintro _ μ₆ ⟨inv₆, rest₆⟩
  -- M₇ = (a₁ - a₃) (b₂ + b₃) goes to 0
  refine Ends.callTo (phase_step prog hw H inv₆ hd' ⟨1, 3, -1, 2, 3, 1, 0, 1, 3, 0⟩) ?_
    (hT := by simp; omega)
  rintro _ μ₇ ⟨inv₇, rest₇⟩
  -- The four lists are the four quadrants of the product.
  have hseg := seg_of_quarters (fun t ht => (inv₇.out t ht).seg) fun t ht => (inv₇.out t ht).len
  simp only [StrArgs.after, StrArgs.phase, Function.update_apply, Nat.reduceEqDiff, reduceIte,
    OfNat.zero_ne_ofNat, OfNat.ofNat_ne_zero, OfNat.one_ne_ofNat, OfNat.ofNat_ne_one, zero_ne_one,
    one_ne_zero] at hseg
  have key := strassenList_succ_eq_phases x.p j x.A x.B (inv.opA.len.trans inv.size)
    (inv.opB.len.trans inv.size)
  simp only [← inv.quarterLen] at key
  exact ⟨key ▸ hseg, by light_keep⟩

/-! ## The two cases and the induction -/

/-- **Level 0**: one product in the ring. -/
theorem strassen_zero : StrSpec lim P ν 0 := by
  intro x μ pre d hd
  have hq : x.len = x.p := by simpa using pre.size
  have hword : (x.p : ℤ) * (x.α * x.β) ≤ lim.word := by
    have h := pre.word
    have h0 : (0 : ℤ) ≤ x.p * (x.α * x.β) := by have := pre.oneA; have := pre.oneB; positivity
    rw [strassenBound, pow_zero, one_mul, mul_assoc] at h
    omega
  light_facts pre pre.opA pre.opB
  refine Meets.of_body prog.str ?_
  -- if j = 0 then cconv(dst, a, b, p)
  refine Ends.iteLast (fun _ => ?_) (fun hc => absurd (by simp) hc) (hT := by simp [strSteps])
  refine Ends.callTo (cconv_meets prog.cconv hw (dst := x.dst)
    { opA := (hq ▸ pre.opA).mono, opB := (hq ▸ pre.opB).mono, word := hword }) ?_
    (hT := by simp [strSteps]; omega)
  rintro _ μ' ⟨seg, rest⟩
  exact ⟨seg, by light_keep⟩

/-- **Level j + 1**: clear the result, then the seven phases. -/
theorem strassen_succ (H : StrSpec lim P ν j) : StrSpec lim P ν (j + 1) := by
  intro x μ pre d hd
  obtain ⟨q, hq⟩ : ∃ q, q = 4 ^ j * x.p := ⟨_, rfl⟩
  have hsize : x.len = 4 * q := by rw [pre.size, hq]; ring
  light_facts pre pre.opA pre.opB pre.table
  have hread : μ (x.szt + j) = q := by
    rw [pre.table.read (by omega), hq]
    simp [szList, show j < x.J + 1 by omega]
  refine Meets.of_body prog.str ?_
  rw [show strSteps x.p (j + 1) = 7 * strSteps x.p j + 696 * q + 900 by rw [strSteps, hq]]
  -- if level = 0 … else; the level is j + 1
  refine Ends.iteLast (fun hc => absurd hc (by simp; omega)) fun _ => ?_
  -- below := level - 1, which is j; q := szt[below]; q2 := q + q; q3 := q2 + q
  light_set j
  light_set q using hread
  light_set (2 * q : ℕ)
  light_set (3 * q : ℕ)
  -- fill(dst, 4 q, 0)
  light_call (fill_meets prog.fill (dst := x.dst) (n := 4 * q) (x := 0) hw (by omega))
    with r μ₁ ⟨segF, rest⟩
  have inv : StrInv lim μ₁ j q x (fun _ => zeros q) 0 :=
    { toStrPre := pre.keep
      quarterLen := hq
      out := fun t ht =>
        { len := by simp [zeros], seg := seg_zeros_quarter segF ht
          bound := by simpa using absLe_zeros q
          below := by have := Nat.mul_add_le_mul ht (le_refl q); omega } }
  -- the seven phases
  light_piece (sevenPhases_spec prog hw H inv (by omega) _ _ _) with σ' ⟨seg, rest'⟩
  exact ⟨seg, by light_keep⟩

/-- **Strassen's algorithm**, at every level. -/
theorem strassen_spec : ∀ j, StrSpec lim P ν j
  | 0 => strassen_zero prog hw
  | j + 1 => strassen_succ prog hw (strassen_spec j)

end levels

end Light.Sec3
