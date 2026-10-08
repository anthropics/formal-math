/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec3.Theorem17.Host.Correct

/-!
# The host of Theorem 17: the program, assembled

The procedures of the host are appended to a program `P₀` that already holds a solver of
Lop-AE-SparseTri and the two procedures that compute the parameters `D` and `g`.  This file has the
list of the procedures (`et17Procs`), their numbers (`et17NumsAt`), the proof that the program so
obtained is the context that the top procedure assumes (`et17Ctx_assembled`), and the
result: the host solves Exact Triangle (`et17_solves`).
-/

@[expose] public section

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec

/-- The numbers of the procedures of Strassen's algorithm, if the list of the procedures of the host
starts at the number `o`. -/
def strNumsAt (o : ℕ) : StrNums := ⟨o + 12, o + 13, o + 14, o + 15, o + 16⟩

/-- The numbers of the procedures that countPrime calls. -/
def cpNumsAt (o : ℕ) : CpNums := ⟨o + 5, o + 6, o + 7, o + 8, o + 9, o + 10, o + 11, strNumsAt o⟩

/-- The numbers of the procedures that choosePrime calls. -/
def chNumsAt (o : ℕ) : ChNums := ⟨o + 3, o + 4, o + 17, cpNumsAt o, o, o + 28⟩

/-- The numbers of the procedures that the top procedure calls: `pS` is the solver, `pD` and `pG`
compute the parameters. -/
def et17NumsAt (pS pD pG o : ℕ) : Et17Nums where
  pD := pD
  pG := pG
  pSqrt := o
  pBrute := o + 2
  pScan := o + 1
  pChoose := o + 18
  pCap := o + 19
  pCeil := o + 20
  pBitLen := o + 4
  pDbl := o + 5
  pResid := o + 6
  pResidues := o + 7
  pClasses := o + 21
  pChunks := o + 22
  pLoop := o + 26
  pS := pS
  pWriteX := o + 23
  pWriteY := o + 24
  pScanPairs := o + 25
  ch := chNumsAt o

/-- The procedures of the host: procedure number `i` of this list gets the number `o + i`.  The top
procedure has the number `o + 27`; behind it stands the sieve of Eratosthenes, which `primes`
calls. -/
def et17Procs (pS pD pG o : ℕ) : Program :=
  let ν := et17NumsAt pS pD pG o
  [sqrtBody,                                                -- 0
    scanBody,                                               -- 1
    bruteBody ν.pScan,                                      -- 2
    primesBody ν.ch.pSqrt ν.ch.pSieve,                      -- 3
    bitLenBody,                                             -- 4
    dblTableBody,                                           -- 5
    residBody,                                              -- 6
    residuesBody ν.pResid,                                  -- 7
    spreadTableBody,                                        -- 8
    szTableBody,                                            -- 9
    buildZBody,                                             -- 10
    countZeroBody,                                          -- 11
    vlinBody,                                               -- 12
    cconvBody,                                              -- 13
    fillBody,                                               -- 14
    phaseBody ν.ch.cp.str,                                  -- 15
    strBody ν.ch.cp.str,                                    -- 16
    countPrimeBody ν.ch.cp,                                 -- 17
    choosePrimeBody ν.ch,                                   -- 18
    queryCapNatBody,                                              -- 19
    ceilDivBody,                                            -- 20
    classesBody,                                            -- 21
    chunksBody,                                             -- 22
    writeXBody,                                             -- 23
    writeYBody,                                             -- 24
    scanPairsBody ν.pScan,                                  -- 25
    hostLoopBody pS ν.pWriteX ν.pWriteY ν.pScanPairs,       -- 26
    et17Body ν,                                             -- 27
    sieveBody]                                              -- 28

variable {P₀ : Program} {pS pD pG : ℕ} {Tn : List ℕ → ℕ} {need : List ℕ → Need}
  {Dfun Gfun tD tG wD wG : ℕ → ℕ}

/-- **The context of the top procedure**, in the assembled program with anything appended to
it. -/
theorem et17Ctx_assembled (hsol : SolvesN lopDetectTask P₀ pS Tn need)
    (hD : ∀ R, ParamProc (P₀ ++ R) pD Dfun tD wD) (hG : ∀ R, ParamProc (P₀ ++ R) pG Gfun tG wG)
    (hpos : ∀ n, 1 ≤ n → 1 ≤ Dfun n) (R : Program) :
    Et17Ctx P₀ (et17Procs pS pD pG P₀.length ++ R) (et17NumsAt pS pD pG P₀.length) Tn need Dfun Gfun
      tD tG wD wG := by
  -- Procedure number `i` of the list.
  have L : ∀ {i : ℕ} {body : Stmt}, (et17Procs pS pD pG P₀.length)[i]? = some body →
      (P₀ ++ (et17Procs pS pD pG P₀.length ++ R))[P₀.length + i]? = some body :=
    fun h => getElem?_append_append R h
  exact
    { loop := ⟨hsol, L rfl, L rfl, L rfl, L rfl⟩
      hLoop := L rfl
      hSqrt := L (i := 0) rfl
      hBrute := L rfl
      hChoose := L rfl
      ch := ⟨L rfl, L rfl, L rfl,
        ⟨L rfl, L rfl, L rfl, L rfl, L rfl,
          L rfl, L rfl,
          ⟨L rfl, L rfl, L rfl, L rfl, L rfl⟩⟩,
        ⟨L (i := 0) rfl, L rfl⟩⟩
      hCap := L rfl
      hCeil := L rfl
      hBitLen := L rfl
      hDbl := L rfl
      hResid := L rfl
      hResidues := L rfl
      hClasses := L rfl
      hChunks := L rfl
      dProc := hD _
      gProc := hG _
      D_pos := hpos }

/-- **The host of Theorem 17 as a solver of Exact Triangle**: from a solver of Lop-AE-SparseTri and
two procedures that compute the parameters, in one program `P₀`, the appended procedures make a
solver of Exact Triangle with the time `hostTime` and the need `hostNeed`. -/
theorem et17_solves (hsol : SolvesN lopDetectTask P₀ pS Tn need)
    (hD : ∀ R, ParamProc (P₀ ++ R) pD Dfun tD wD) (hG : ∀ R, ParamProc (P₀ ++ R) pG Gfun tG wG)
    (hpos : ∀ n, 1 ≤ n → 1 ≤ Dfun n) :
    Solves etTask (P₀ ++ et17Procs pS pD pG P₀.length) (P₀.length + 27)
      (hostTime Dfun Gfun tD tG Tn) (hostNeed Dfun Gfun wD wG need) := by
  refine ⟨et17Body (et17NumsAt pS pD pG P₀.length), ?_, fun R lim d x μ fr hpre hok => ?_⟩
  · have htop := getElem?_append_append (P₀ := P₀) (B := et17Procs pS pD pG P₀.length) [] (i := 27)
      rfl
    rwa [List.append_nil] at htop
  · rw [List.append_assoc]
    exact et17_spec (et17Ctx_assembled hsol hD hG hpos R) x μ fr hpre hok

end Light.Sec3
