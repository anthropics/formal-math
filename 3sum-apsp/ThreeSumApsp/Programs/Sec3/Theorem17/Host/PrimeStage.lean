/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec3.Theorem17.Host.Need

/-!
# The host of Theorem 17: the prime, the sizes, the addresses

This file proves the specification of the second part of the host procedure `et17` (Exact Triangle
by Theorem 17), which chooses the prime and computes the sizes and the addresses of the arrays:
five calls (`et17Sizes_spec`) and then seventeen assignments (`et17Addr_spec`).
-/

@[expose] public section

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec

variable {lim : Limits} {P : Program} {d : ℕ}

/-- **The sizes and the addresses.**  Of the locals that are set before, only Size, Free, ParD,
ThePrime, Cap and Bits are read. -/
theorem et17Addr_spec {μ : ℕ → ℤ} (x : TriInst) (X : HostData) {fr : ℕ} {g s : ℤ}
    (hw : (lim.space : ℤ) ≤ lim.word) (htop : aFr X x.U fr ≤ lim.space) :
    Ends lim P d et17Addr
      ⟨frame [(X.n : ℤ), (x.U : ℤ), (x.ab : ℤ), (x.bc : ℤ), (x.ac : ℤ), (fr : ℤ), (X.D : ℤ), g, s,
        (X.p : ℤ), (X.cap : ℤ), (X.q : ℤ), (X.h : ℤ), ((bitLen x.U : ℕ) : ℤ), 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], μ⟩
      et17Addr.blockCost fun σ' => σ' = ⟨frame (Et17.locals x X fr g s 0 0), μ⟩ := by
  have hplaces := host_places X x.U fr
  have hsquare : (0 : ℤ) ≤ (X.n : ℤ) * X.n := by positivity
  have harea : (0 : ℤ) ≤ (X.n : ℤ) * X.D := by positivity
  unfold et17Addr
  -- SizeSq := Size * Size ; Area := Size * ParD ; Room := SizeSq + ThePrime
  light_set (X.n * X.n : ℕ)
  light_set (X.n * X.D : ℕ)
  light_set (X.n * X.n + X.p : ℕ)
  -- ResAB := Free + (Bits + 1) ; ResBC := ResAB + SizeSq ; ResAC := ResBC + SizeSq
  light_set (aRab X x.U fr)
  light_set (aRbc X x.U fr)
  light_set (aRac X x.U fr)
  -- Cls := ResAC + SizeSq ; Cur := Cls + (ThePrime + 1) ; Rows := Cur + ThePrime
  light_set (aCls X x.U fr)
  light_set (aCur X x.U fr)
  light_set (aQi X x.U fr)
  -- Cols := Rows + SizeSq ; TabR := Cols + SizeSq ; TabL := TabR + Room ; TabW := TabL + Room
  light_set (aQj X x.U fr)
  light_set (aCr X x.U fr)
  light_set (aCl X x.U fr)
  light_set (aCw X x.U fr)
  -- MatX := TabW + Room ; MatY := MatX + Area ; AdrOut := MatY + Area
  light_set (aX X x.U fr)
  light_set (aY X x.U fr)
  light_set (aOut X x.U fr)
  -- SolverFree := AdrOut + Cap
  light_set (aFr X x.U fr)
  rfl

/-- What the second part uses: the parameters are not small, and the limits allow for one more
level of calls, for the arrays and for the numbers that the four small procedures form. -/
structure SizesReady (lim : Limits) (d : ℕ) (x : TriInst) (fr D g : ℕ) : Prop where
  one_le_D : 1 ≤ D
  one_le_g : 1 ≤ g
  one_le_piece : 1 ≤ pieceSizeNat D g
  depth : d < lim.depth
  top : aFr (hostData x D g) x.U fr ≤ lim.space
  wordCap : ((4 * x.n ^ 4 + D + 2 : ℕ) : ℤ) ≤ lim.word
  wordPiece : ((Nat.sqrt D + g + 1 : ℕ) : ℤ) ≤ lim.word
  wordPieces : ((x.n + pieceSizeNat D g + 1 : ℕ) : ℤ) ≤ lim.word
  wordBits : ((2 * x.U + 2 : ℕ) : ℤ) ≤ lim.word

/-- The need of the host provides what the second part uses. -/
theorem sizesReady_of {need : List ℕ → Need} {x : TriInst} {fr D g a b : ℕ}
    (hbig : BigCase x.n D g) (hok : (hostNeedAt a b need x.n x.U D g).Ok lim fr d) :
    SizesReady lim d x fr D g := by
  have hD16 : 16 ≤ D := hbig.sixteen_le
  have hg1 : 1 ≤ g := hbig.one_le_g
  have hsqrt : 4 ≤ Nat.sqrt D := Nat.le_sqrt.2 (by omega)
  have hdepth := hok.depth
  have hcells := hok.cells
  have htop := aFr_le (x := x) (g := g) hD16 fr
  simp only [hostNeedAt] at hdepth hcells
  exact
    { one_le_D := by omega
      one_le_g := hg1
      one_le_piece := (Nat.lt_ceilDiv_iff hg1).2 (by omega)
      depth := by omega
      top := by omega
      wordCap := le_word_of_le_hostWord hok
      wordPiece := le_word_of_le_hostWord hok
      wordPieces := le_word_of_le_hostWord hok
      wordBits := le_word_of_le_hostWord hok }

/-- **The second part of et17**: the prime, the sizes and the addresses are in the locals; only
cells from the free pointer on have changed. -/
theorem et17Sizes_spec {P₀ R : Program} {ν : Et17Nums} {Tn : List ℕ → ℕ} {need : List ℕ → Need}
    {Dfun Gfun tD tG wD wG : ℕ → ℕ} (C : Et17Ctx P₀ R ν Tn need Dfun Gfun tD tG wD wG)
    (x : TriInst) (μ : ℕ → ℤ) (fr D g a b : ℕ) (hpre : x.Pre μ fr)
    (hbig : BigCase x.n D g) (hok : (hostNeedAt a b need x.n x.U D g).Ok lim fr d) :
    Ends lim (P₀ ++ R) d (et17Sizes ν) ⟨frame (et17LocA x fr D g), μ⟩
      (chooseTime x.n x.U D + tQueryCapNat x.n D + tCeilDiv (Nat.sqrt D) g +
        tCeilDiv x.n (pieceSizeNat D g) + tBitLen x.U + 120)
      fun σ' => ∃ μ', σ' = ⟨frame (et17LocB x fr D g), μ'⟩ ∧ Kept μ μ' fr := by
  have hr := sizesReady_of (x := x) hbig hok
  have hdepth := hr.depth
  unfold et17Sizes et17LocA
  rw [if_neg (not_smallCase_iff.2 hbig)]
  -- ThePrime := pChoose(Size, Bound, AdrAB, AdrBC, AdrAC, ParD, Free)
  light_call (choosePrime_meets C.hChoose C.ch (choosePre_of_ok hpre hok)) with _ μ₁ ⟨rfl, hμ₁⟩
  -- Cap := pCap(Size, ParD)
  light_call (queryCapNat_meets C.hCap hr.one_le_D hr.wordCap) with _ μ₁ ⟨rfl, rfl⟩
  -- PieceLen := pCeil(RootD, ParG)
  light_call (ceilDiv_meets C.hCeil hr.one_le_g hr.wordPiece) with _ μ₁ ⟨rfl, rfl⟩
  -- NumPieces := pCeil(Size, PieceLen)
  light_call (ceilDiv_meets C.hCeil hr.one_le_piece hr.wordPieces) using pieceSizeNat
    with _ μ₁ ⟨rfl, rfl⟩
  -- Bits := pBitLen(Bound)
  light_call (bitLen_meets C.hBitLen hr.wordBits) with _ μ₁ ⟨rfl, rfl⟩
  -- the sizes and the addresses
  refine (et17Addr_spec x (hostData x D g) hok.space hr.top).mono (by simp [et17Addr]; omega) ?_
  rintro _ rfl
  exact ⟨μ₁, rfl, fun c hc => hμ₁ c (Or.inl hc)⟩

end Light.Sec3
