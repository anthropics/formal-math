/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec3.Theorem17.Host.Need

/-!
# The host of Theorem 17: the parameters and the small case

The first part of the host procedure `et17` (Exact Triangle by Theorem 17) computes `D`, `g` and
`s = ⌊√D⌋` and tests whether `n` is small (`et17Params_spec`).  If it is, the host calls the brute
force (`et17Small_spec`; proof of Theorem 19: "smaller instances are solved by brute force").
-/

public section

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec

variable {P₀ R : Program} {ν : Et17Nums} {Tn : List ℕ → ℕ} {need : List ℕ → Need}
  {Dfun Gfun tD tG wD wG : ℕ → ℕ} {lim : Limits} {d : ℕ}

/-- **The first part of et17**: the parameters, and whether n is small.  No cell changes. -/
theorem et17Params_spec (C : Et17Ctx P₀ R ν Tn need Dfun Gfun tD tG wD wG) (x : TriInst)
    (μ : ℕ → ℤ) (fr : ℕ) (hpre : x.Pre μ fr)
    (hok : (hostNeed Dfun Gfun wD wG need x.n x.U).Ok lim fr d) :
    Ends lim (P₀ ++ R) d (et17Params ν) ⟨frame (et17Loc0 x fr), μ⟩
      (tD x.n + tG (Dfun x.n) + (18 * Nat.sqrt (Dfun x.n) + 12) + 40)
      fun σ' => σ' = ⟨frame (et17LocA x fr (Dfun x.n) (Gfun (Dfun x.n))), μ⟩ := by
  have hn := hpre.n_pos
  have hDpos := C.D_pos x.n hn
  unfold hostNeed at hok
  have hdepth := hok.depth
  simp only [hostNeedAt] at hdepth
  generalize hD : Dfun x.n = D at *
  generalize hg : Gfun D = g at *
  -- The numbers that this part forms fit in a word.
  have hwD : ((wD x.n : ℕ) : ℤ) ≤ lim.word := le_word_of_le_hostWord hok
  have hwG : ((wG D : ℕ) : ℤ) ≤ lim.word := le_word_of_le_hostWord hok
  have hsqrt : ((3 * D + 4 : ℕ) : ℤ) ≤ lim.word := le_word_of_le_hostWord hok
  have h16 : ((16 : ℕ) : ℤ) ≤ lim.word := le_word_of_le_hostWord hok
  unfold et17Params et17Loc0 et17LocA
  -- D := Dfun(n); g := Gfun(D)
  light_call (C.dProc lim d x.n μ hn hok.space hwD (by omega)) with _ μ ⟨rfl, rfl⟩
  rw [hD]
  light_call (C.gProc lim d D μ hDpos hok.space hwG (by omega)) with _ μ ⟨rfl, rfl⟩
  rw [hg]
  -- s := sqrt(D)
  light_call (sqrt_meets (K := D) C.hSqrt μ hsqrt) with _ μ ⟨rfl, rfl⟩
  -- the four tests: D < 16, n < D, g < 1, s < g
  refine Ends.block ⟨by simp; omega, ?_⟩
  by_cases hD16 : D < 16 <;> by_cases hnD : x.n < D <;> by_cases hg0 : g = 0 <;>
    by_cases hsg : Nat.sqrt D < g <;> simp [update_frame_setLocal, SmallCase, hD16, hnD, hg0, hsg]

open Et17 in
/-- **The small case**: the call of the brute force. -/
theorem et17Small_spec (C : Et17Ctx P₀ R ν Tn need Dfun Gfun tD tG wD wG) (x : TriInst)
    (μ : ℕ → ℤ) (fr D g a b : ℕ) (hpre : x.Pre μ fr)
    (hok : (hostNeedAt a b need x.n x.U D g).Ok lim fr d) :
    Ends lim (P₀ ++ R) d (.call ν.pBrute [v Size, v Bound, v AdrAB, v AdrBC, v AdrAC, v Free] 0)
      ⟨frame (et17LocA x fr D g), μ⟩ (tBrute x.n + 8)
      fun σ' => etTask.Post x μ fr (σ'.loc 0) σ'.mem := by
  have hbrute : (bruteNeed x.n x.U).Ok lim fr (d + 1) :=
    hok.mono (by simp only [bruteNeed, hostNeedAt, hostWord]; omega)
      (by simp only [bruteNeed]; omega) (by simp only [bruteNeed, hostNeedAt]; omega)
  have hdepth := hok.depth
  simp only [hostNeedAt] at hdepth
  refine Ends.callTo (brute_meets C.hBrute C.loop.scan x μ fr hpre hbrute) ?_ (by simp [et17LocA])
  rintro _ _ ⟨rfl, rfl⟩
  exact ⟨by simp [et17LocA], fun _ _ => rfl⟩

end Light.Sec3
