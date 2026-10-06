/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec4.ChoosingParameters.Program

/-!
# A data structure for the entries of a thin matrix product, placed anywhere in the memory

The proof of Corollary 40 uses the data structure of Corollary 26 (for τ < 1/18) and that of
Corollary 31 (for general τ) in the same way; the first is the second at c = 21, θ = 1/9.  A kit
(`DsKit`) collects what the phase programs of Corollary 40 use: the preprocessing
pre(N, D, aX, aY, fr) works on matrices at any addresses below fr and changes only the cells from fr
up to (not including) fr + size N D; the query query(I, J, N, D, aX, aY, fr) returns the entry
(XY)[I, J] and keeps the structure ready.

The kit is an interface: it keeps Section 4 out of the proofs about the phase programs.  It has one
instance, `kit31`.
-/

@[expose] public section

namespace Light.Sec5

open ThreeSumApsp Light.Sec4

/-- **What both routines of a kit are given**: matrices X and Y of sizes at least 1 with entries
bounded by U, the addresses aX and aY of their cells, which lie below the address fr of the
structure, and limits that suffice; `Lim` is the kit's condition on the limits. -/
structure KitInput (Lim : Limits → ℕ → ℕ → ℕ → ℤ → Prop) (lim : Limits) {N D₀ : ℕ}
    (X : Matrix (Fin N) (Fin D₀) ℤ) (Y : Matrix (Fin D₀) (Fin N) ℤ) (aX aY fr : ℕ) (U : ℤ) :
    Prop where
  one_le_D : 1 ≤ D₀
  one_le_N : 1 ≤ N
  lim : Lim lim N D₀ fr U
  absX : ∀ i j, |X i j| ≤ U
  absY : ∀ i j, |Y i j| ≤ U
  belowX : aX + N * D₀ ≤ fr
  belowY : aY + D₀ * N ≤ fr

/-- **The kit**: a relocatable data structure for the entries of XY in the program P, at the
procedure numbers `Proc.pre31` and `Proc.query31`. -/
structure DsKit (P : Program) where
  /-- The cells from fr on hold what a query to XY needs; X and Y lie at aX and aY. -/
  Ready : ∀ {N D₀ : ℕ}, Matrix (Fin N) (Fin D₀) ℤ → Matrix (Fin D₀) (Fin N) ℤ → ℕ → ℕ → ℕ →
    (ℕ → ℤ) → Prop
  /-- The limits that the two routines need, for a structure at fr and entries of absolute value at
  most U. -/
  Lim : Limits → ℕ → ℕ → ℕ → ℤ → Prop
  /-- The number of cells of a structure. -/
  size : ℕ → ℕ → ℕ
  /-- The levels of calls that the preprocessing needs. -/
  depPre : ℕ → ℕ
  /-- The time of the preprocessing. -/
  tPre : ℕ → ℕ → ℕ
  /-- The time of a query. -/
  tQ : ℕ → ℕ
  three_le_size : ∀ N D₀, 3 ≤ size N D₀
  std : ∀ {lim : Limits} {N D₀ fr : ℕ} {U : ℤ}, Lim lim N D₀ fr U → Std lim
  space : ∀ {lim : Limits} {N D₀ fr : ℕ} {U : ℤ}, Lim lim N D₀ fr U → fr + size N D₀ ≤ lim.space
  /-- The preprocessing makes the structure ready and changes only its cells. -/
  pre : ∀ {lim : Limits} {N D₀ aX aY fr : ℕ} {X : Matrix (Fin N) (Fin D₀) ℤ}
    {Y : Matrix (Fin D₀) (Fin N) ℤ} {U : ℤ} {μ : ℕ → ℤ},
    KitInput Lim lim X Y aX aY fr U → MatAt μ aX X → MatAt μ aY Y →
    ∀ d, d + depPre D₀ ≤ lim.depth →
    Meets lim P Proc.pre31 d [N, D₀, aX, aY, fr] μ (tPre N D₀) fun _ μ' =>
      Ready X Y aX aY fr μ' ∧ SameOutside μ μ' fr (size N D₀)
  /-- A query returns the entry (I, J) of XY, keeps the structure ready and changes only its cells.
  -/
  query : ∀ {lim : Limits} {N D₀ aX aY fr : ℕ} {X : Matrix (Fin N) (Fin D₀) ℤ}
    {Y : Matrix (Fin D₀) (Fin N) ℤ} {U : ℤ} {μ : ℕ → ℤ},
    KitInput Lim lim X Y aX aY fr U → Ready X Y aX aY fr μ → ∀ (I J : Fin N),
    ∀ d, d + 3 ≤ lim.depth →
    Meets lim P Proc.query31 d [(I : ℕ), (J : ℕ), N, D₀, aX, aY, fr] μ (tQ D₀) fun r μ' =>
      r = (X * Y) I J ∧ Ready X Y aX aY fr μ' ∧ SameOutside μ μ' fr (size N D₀)
  /-- What a query needs depends only on the cells of X, of Y, and on the cells from fr on. -/
  ready_congr : ∀ {N D₀ : ℕ} {X : Matrix (Fin N) (Fin D₀) ℤ} {Y : Matrix (Fin D₀) (Fin N) ℤ}
    {aX aY fr : ℕ} {μ μ' : ℕ → ℤ},
    Ready X Y aX aY fr μ →
    (∀ a, aX ≤ a → a < aX + N * D₀ → μ' a = μ a) →
    (∀ a, aY ≤ a → a < aY + D₀ * N → μ' a = μ a) →
    (∀ a, fr ≤ a → μ' a = μ a) → Ready X Y aX aY fr μ'

/-- What both routines of the kit K are given. -/
abbrev DsKit.Input {P : Program} (K : DsKit P) (lim : Limits) {N D₀ : ℕ}
    (X : Matrix (Fin N) (Fin D₀) ℤ) (Y : Matrix (Fin D₀) (Fin N) ℤ) (aX aY fr : ℕ) (U : ℤ) : Prop :=
  KitInput K.Lim lim X Y aX aY fr U

/-- A structure stays ready if neither X, nor Y, nor the cells from fr on change. -/
theorem DsKit.Ready.keep {P : Program} {K : DsKit P} {N D₀ aX aY fr : ℕ}
    {X : Matrix (Fin N) (Fin D₀) ℤ} {Y : Matrix (Fin D₀) (Fin N) ℤ} {μ μ' : ℕ → ℤ}
    (h : K.Ready X Y aX aY fr μ)
    (hs : SameOn (fun b => Inside aX (N * D₀) b ∨ Inside aY (D₀ * N) b ∨ fr ≤ b) μ μ' := by
      light_keep) :
    K.Ready X Y aX aY fr μ' :=
  K.ready_congr h (fun a h₁ h₂ => hs a (.inl ⟨h₁, h₂⟩)) (fun a h₁ h₂ => hs a (.inr (.inl ⟨h₁, h₂⟩)))
    fun a ha => hs a (.inr (.inr ha))

/-- What the limits of a kit imply: an address fits in a word, so do the constants of the programs,
and the structure, of at least three cells, fits in the memory. -/
theorem DsKit.basics {P : Program} (K : DsKit P) {lim : Limits} {N D₀ fr : ℕ} {U : ℤ}
    (h : K.Lim lim N D₀ fr U) :
    (lim.space : ℤ) ≤ lim.word ∧ 100 ≤ lim.word ∧ fr + K.size N D₀ ≤ lim.space ∧
      3 ≤ K.size N D₀ :=
  ⟨(K.std h).space_le, (K.std h).const_le, K.space h, K.three_le_size N D₀⟩

/-! ## The lengths of the structures do not depend on where they lie, and are at least 3 -/

theorem sharedEnd_eq_add (p : Sec2.Par) (b0 : ℕ) : p.sharedEnd b0 = b0 + p.sharedEnd 0 := by
  simp only [Sec2.Par.sharedEnd, Sec2.Par.aZS, Sec2.Par.aARR, Sec2.Par.aENCB, Sec2.Par.aENCA,
    Sec2.Par.aDIG4, Sec2.Par.aDIG3, Sec2.Par.aBLOCK, Sec2.Par.aBAND, Sec2.Par.aMASK, Sec2.Par.aPSI,
    Sec2.Par.aPHI, Sec2.Par.aPAS, Sec2.Par.aP10, Sec2.Par.aP7, Sec2.Par.aP4, Sec2.Par.aP3]
  omega

theorem top_eq_add (p : Sec2.Par) (t b0 : ℕ) : top p t b0 = b0 + top p t 0 := by
  have h1 := top_sub_eq p t b0
  have h2 := top_sub_eq p t 0
  have h3 := base_le_top p t b0
  have h4 := sharedEnd_eq_add p b0
  omega

theorem structEnd_eq_add (G : RatParams) (N D₀ fr : ℕ) :
    structEnd G N D₀ fr = fr + structEnd G N D₀ 0 := by
  unfold structEnd
  split_ifs
  · omega
  · rw [top_eq_add _ _ (blockAt N D₀ fr), top_eq_add _ _ (blockAt N D₀ 0)]
    unfold blockAt
    omega

theorem three_le_structEnd (G : RatParams) (N D₀ : ℕ) : 3 ≤ structEnd G N D₀ 0 := by
  unfold structEnd
  split_ifs
  · omega
  · have h1 := base_le_top (parOf G N D₀) (switchOf31 G D₀) (blockAt N D₀ 0)
    have h2 : 3 ≤ blockAt N D₀ 0 := by unfold blockAt; omega
    omega

/-! ## The instance -/

/-- What the routines of the kit are given is what the routines of Corollary 31 are given. -/
theorem KitInput.input31 {G : RatParams} {lim : Limits} {N D₀ aX aY fr : ℕ}
    {X : Matrix (Fin N) (Fin D₀) ℤ} {Y : Matrix (Fin D₀) (Fin N) ℤ} {U : ℤ}
    (h : KitInput (fun lim N D₀ fr U => Lim31 lim G N D₀ fr U) lim X Y aX aY fr U) :
    Input31 lim G X Y aX aY fr U :=
  { one_le_D := h.one_le_D, one_le_N := h.one_le_N, lim := h.lim, absX := h.absX, absY := h.absY
    belowX := h.belowX, belowY := h.belowY }

/-- **The data structure of Corollary 31** with the parameters G, in the program for G followed by
further procedures R. -/
def kit31 (G : RatParams) (R : Program) : DsKit (program31 G ++ R) where
  Ready X Y aX aY fr μ := Ready31 G X Y aX aY fr μ
  Lim lim N D₀ fr U := Lim31 lim G N D₀ fr U
  size N D₀ := structEnd G N D₀ 0
  depPre D₀ := G.L (logFour D₀) + 7
  tPre N D₀ := tPre31 cShared30 G N D₀
  tQ D₀ := tQuery31 G D₀
  three_le_size := three_le_structEnd G
  std h := h.std
  space h := by rw [← structEnd_eq_add]; exact h.space
  pre {lim N D₀ aX aY fr X Y U μ} hin mX mY d hd := by
    have h := (pre31_program31 G lim N D₀ aX aY fr X Y U μ hin.input31 mX mY d hd).append R
    have e : structEnd G N D₀ fr - fr = structEnd G N D₀ 0 := by rw [structEnd_eq_add]; omega
    rwa [e] at h
  query {lim N D₀ aX aY fr X Y U μ} hin hR I J d hd := by
    refine ((query31_program31 G lim N D₀ aX aY fr X Y U μ I J hin.input31 hR d hd).append R).mono
      le_rfl ?_
    rintro r μ' ⟨h1, h2, h3⟩
    refine ⟨h1, h2, fun a ha => h3 a ?_⟩
    have e := structEnd_eq_add G N D₀ fr
    have := three_le_structEnd G N D₀
    omega
  ready_congr h hX hY hfr := ready31_congr h hX hY hfr

end Light.Sec5
