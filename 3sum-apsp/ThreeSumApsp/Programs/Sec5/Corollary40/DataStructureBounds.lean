/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec4.ChoosingParameters.RealParameters
public import ThreeSumApsp.Programs.Sec4.Corollary26.Regime
public import ThreeSumApsp.Programs.Sec5.Corollary40.DataStructure

/-!
# Time, space and limits of the relocatable data structure

The programs for Corollary 40 call the preprocessing and the query routine of a data structure for
the entries of a thin matrix product, placed at an address fr of their choice.  `KitRates` collects
what they use about it: bounds on the two running times and on the number of cells, and limits
within which the routines run for matrices of zeros and ones.  The limits are a function of the
number sp of memory cells and serve every structure that lies within the memory, so that several
structures can lie side by side.  `kit31_rates` proves this for all parameters and all bounds that
dominate the two costs of Theorem 30; `kitRates_corollary26` (Corollary 26) and
`kitRates_corollary31` (Corollary 31) are its instances.
-/

@[expose] public section

namespace Light.Sec5

open ThreeSumApsp Light.Sec4

/-! ## The bounds on the two running times -/

/-- The bound on the preprocessing of Corollary 26 is at most `N²`. -/
theorem preBound26_le_sq {D₀ : ℕ} (hD : 1 ≤ D₀) (N : ℕ) : preBound26 D₀ N ≤ (N : ℝ) ^ 2 :=
  div_le_self (by positivity) (Real.one_le_rpow (Nat.one_le_cast.2 hD) (by norm_num))

/-- `(log D + 1)²/D^γ` is bounded, so the bound on the preprocessing is `O(N²)`. -/
theorem exists_preBound31_le_sq {γ : ℝ} (hγ : 0 < γ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ N D₀ : ℕ, 1 ≤ D₀ → preBound31 γ N D₀ ≤ B * (N : ℝ) ^ 2 := by
  obtain ⟨B, hB, hlog⟩ := dominated_log_add_one_pow_rpow hγ 2
  refine ⟨B, hB, fun N D₀ hD => ?_⟩
  rw [preBound31, div_le_iff₀ (by positivity)]
  calc (N : ℝ) ^ 2 * (Real.log D₀ + 1) ^ 2 ≤ (N : ℝ) ^ 2 * (B * (D₀ : ℝ) ^ γ) :=
        mul_le_mul_of_nonneg_left (hlog _ (Nat.one_le_cast.2 hD)) (by positivity)
    _ = B * (N : ℝ) ^ 2 * (D₀ : ℝ) ^ γ := by ring

/-- For D ≤ F the bound on the preprocessing is at least 1/F^γ. -/
theorem one_le_rpow_mul_preBound31 {γ : ℝ} (hγ : 0 < γ) {N D F : ℕ} (hD : 1 ≤ D) (hN : 1 ≤ N)
    (hDF : D ≤ F) : 1 ≤ (F : ℝ) ^ γ * preBound31 γ N D := by
  have hD1 : (1 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hlog : 0 ≤ Real.log D := Real.log_nonneg hD1
  have hDle : (D : ℝ) ^ γ ≤ (F : ℝ) ^ γ :=
    Real.rpow_le_rpow (by linarith) (by exact_mod_cast hDF) hγ.le
  have hpos : 0 < (D : ℝ) ^ γ := by positivity
  have hnum : 1 ≤ (N : ℝ) ^ 2 * (Real.log D + 1) ^ 2 :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ hN1) (one_le_pow₀ (by linarith))
  unfold preBound31
  rw [← mul_div_assoc, le_div_iff₀ hpos, one_mul]
  calc (D : ℝ) ^ γ ≤ (F : ℝ) ^ γ := hDle
    _ = (F : ℝ) ^ γ * 1 := (mul_one _).symm
    _ ≤ (F : ℝ) ^ γ * ((N : ℝ) ^ 2 * (Real.log D + 1) ^ 2) :=
      mul_le_mul_of_nonneg_left hnum (by positivity)

/-- The bound on a query is at least 1. -/
theorem one_le_queryBound31 {q : ℝ} (hq : 0 ≤ q) {D : ℕ} (hD : 1 ≤ D) : 1 ≤ queryBound31 q D := by
  have hD1 : (1 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD
  exact one_le_mul_of_one_le_of_one_le (Real.one_le_rpow hD1 hq)
    (by linarith [Real.log_nonneg hD1])

/-! ## The limits -/

/-- The first cell after an input with no wanted positions: three sizes and the two matrices. -/
def kitInputEnd (N D₀ : ℕ) : ℕ := 3 + 2 * (N * D₀)

/-- The limits of Section 4 for a structure that lies directly after such an input, for matrices of
zeros and ones. -/
def baseLim (G : RatParams) (N D₀ : ℕ) : Limits := lim31 G N D₀ (kitInputEnd N D₀) 0

/-- Limits for the routines with general parameters on matrices of zeros and ones, with `sp` cells
of memory.  Only the number of cells depends on the place of a structure.  So the bound on the words
and the depth are those of `baseLim`, with `sp` more for the addresses and 20 more levels of calls
for the procedures that call the routines. -/
def limKit31 (G : RatParams) (N D₀ sp : ℕ) : Limits :=
  ⟨(baseLim G N D₀).word + sp, sp, (baseLim G N D₀).depth + 20⟩

@[simp] theorem limKit31_word (G : RatParams) (N D₀ sp : ℕ) :
    (limKit31 G N D₀ sp).word = (baseLim G N D₀).word + sp :=
  rfl

@[simp] theorem limKit31_space (G : RatParams) (N D₀ sp : ℕ) : (limKit31 G N D₀ sp).space = sp :=
  rfl

@[simp] theorem limKit31_depth (G : RatParams) (N D₀ sp : ℕ) :
    (limKit31 G N D₀ sp).depth = (baseLim G N D₀).depth + 20 :=
  rfl

/-- **One set of limits for all places**: the limits serve every structure that ends within the
memory. -/
theorem limKit31_ok (G : RatParams) (N D₀ sp fr : ℕ) (h : fr + structEnd G N D₀ 0 ≤ sp) :
    Lim31 (limKit31 G N D₀ sp) G N D₀ fr 1 := by
  have h0 : Lim31 (baseLim G N D₀) G N D₀ (kitInputEnd N D₀) 1 := by
    simpa [baseLim] using lim31_ok G N D₀ (kitInputEnd N D₀) 0
  have up {x : ℤ} (hx : x ≤ (baseLim G N D₀).word) : x ≤ (limKit31 G N D₀ sp).word := by
    rw [limKit31_word]
    omega
  have hspace : ((limKit31 G N D₀ sp).space : ℤ) ≤ (limKit31 G N D₀ sp).word := by
    have hconst := h0.std.const_le
    rw [limKit31_word, limKit31_space]
    omega
  have htop : structEnd G N D₀ fr ≤ sp := by rwa [structEnd_eq_add]
  refine ⟨⟨hspace, up h0.std.const_le⟩, htop, up h0.pow, up h0.mword, up h0.m0word, up h0.ip,
    fun hm => ?_⟩
  have hl := h0.large hm
  refine ⟨⟨hspace, up hl.std.const_le⟩, ?_, up hl.value, up hl.enc, up hl.pow⟩
  rwa [structEnd, if_neg (by omega)] at htop

/-- The limits are polynomial in `n` if the memory is, for `D₀ ≤ N ≤ n`. -/
theorem small_limKit31 {G : RatParams} {sp N D₀ n k s : ℕ} (hD : 1 ≤ D₀) (hDN : D₀ ≤ N)
    (hyp : G.m₀ ≤ logFour D₀ → Hyp30 (parOf G N D₀) (switchOf31 G D₀)) (hNn : N ≤ n) (hk : 40 ≤ k)
    (hss : slopeExp31 G ≤ s) (hsp : sp ≤ polyBound s k [n]) :
    Small (s + 1) k [n] (limKit31 G N D₀ sp) := by
  have hs : Small (slopeExp31 G) 20 [N, D₀] (baseLim G N D₀) :=
    small_lim31 (fr := kitInputEnd N D₀) 0 hD hDN (blockAt_le hD hDN (Nat.zero_le _)) hyp
  have hB : polyBound (slopeExp31 G) 20 [N, D₀] ≤ polyBound s k [n] :=
    (polyBound_pair_le hNn (hDN.trans hNn)).trans (polyBound_mono hss hk [n])
  have h2 : polyBound (s + 1) k [n] = 2 * polyBound s k [n] := by
    rw [Nat.add_comm, ← polyBound_mul, pow_one]
  have h20 : 20 ≤ polyBound s k [n] :=
    calc 20 ≤ 2 ^ 9 * 1 := by norm_num
      _ ≤ 2 ^ 9 * polyBound 0 k [n] := Nat.mul_le_mul_left _ (one_le_polyBound 0 k [n])
      _ = polyBound (9 + 0) k [n] := polyBound_mul 0 9 k [n]
      _ ≤ polyBound s k [n] := polyBound_mono ((nine_le_slopeExp31 G).trans hss) le_rfl [n]
  have hword : (baseLim G N D₀).word ≤ (polyBound s k [n] : ℤ) :=
    hs.word.trans (by exact_mod_cast hB)
  have hdepth := hs.depth.trans hB
  have hnonneg := hs.nonneg
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [limKit31_word]
    omega
  · rw [limKit31_word, h2]
    push_cast
    omega
  · rw [limKit31_space]
    omega
  · rw [limKit31_depth]
    omega

/-! ## What the programs use about a kit -/

/-- **What the programs of Corollary 40 use about a kit** at the sizes N and D: the preprocessing
takes at most C tp steps and a query at most C tq; a structure has at most A N² cells; the limits
limK sp, for a memory of sp cells, serve every place within the memory, allow 22 levels of calls
more than the preprocessing needs, and are polynomial in n ≥ N if sp is. -/
structure KitRates {P : Program} (K : DsKit P) (limK : ℕ → Limits) (A s₀ : ℕ) (C : ℝ) (N D : ℕ)
    (tp tq : ℝ) : Prop where
  tPre_le : (K.tPre N D : ℝ) ≤ C * tp
  tQ_le : (K.tQ D : ℝ) ≤ C * tq
  size_le : K.size N D ≤ A * (N * N)
  lim_ok : ∀ sp fr : ℕ, fr + K.size N D ≤ sp → K.Lim (limK sp) N D fr 1
  space_eq : ∀ sp : ℕ, (limK sp).space = sp
  depth_le : ∀ sp : ℕ, K.depPre D + 22 ≤ (limK sp).depth
  /-- The degree 40 is twice the degree 20 of the limits of Section 4, which are polynomial in N and
  D (`polyBound_pair_le`). -/
  small : ∀ n k s sp : ℕ, N ≤ n → 40 ≤ k → s₀ ≤ s → sp ≤ polyBound s k [n] →
    Small (s + 1) k [n] (limK sp)

section
variable {P : Program} {K : DsKit P} {limK : ℕ → Limits} {A s₀ : ℕ} {C : ℝ} {N D : ℕ} {tp tq : ℝ}

/-- Two bounds can be replaced by bounds that are at least 1/E times as large; the factor E goes
into the constant. -/
theorem KitRates.mono (h : KitRates K limK A s₀ C N D tp tq) (hC : 0 ≤ C) {E tp' tq' : ℝ}
    (htp : tp ≤ E * tp') (htq : tq ≤ E * tq') : KitRates K limK A s₀ (C * E) N D tp' tq' :=
  { h with
    tPre_le := h.tPre_le.trans ((mul_le_mul_of_nonneg_left htp hC).trans_eq (mul_assoc _ _ _).symm)
    tQ_le := h.tQ_le.trans ((mul_le_mul_of_nonneg_left htq hC).trans_eq (mul_assoc _ _ _).symm) }

/-- x preprocessings take at most C E X steps if x tp ≤ E X. -/
theorem KitRates.mul_tPre_le (h : KitRates K limK A s₀ C N D tp tq) (hC : 0 ≤ C) {x E X : ℝ}
    (hx : 0 ≤ x) (hle : x * tp ≤ E * X) : x * (K.tPre N D : ℝ) ≤ C * (E * X) :=
  calc x * (K.tPre N D : ℝ) ≤ x * (C * tp) := mul_le_mul_of_nonneg_left h.tPre_le hx
    _ = C * (x * tp) := by ring
    _ ≤ C * (E * X) := mul_le_mul_of_nonneg_left hle hC

/-- x queries take at most C E X steps if x tq ≤ E X. -/
theorem KitRates.mul_tQ_le (h : KitRates K limK A s₀ C N D tp tq) (hC : 0 ≤ C) {x E X : ℝ}
    (hx : 0 ≤ x) (hle : x * tq ≤ E * X) : x * (K.tQ D : ℝ) ≤ C * (E * X) :=
  calc x * (K.tQ D : ℝ) ≤ x * (C * tq) := mul_le_mul_of_nonneg_left h.tQ_le hx
    _ = C * (x * tq) := by ring
    _ ≤ C * (E * X) := mul_le_mul_of_nonneg_left hle hC

/-- The limits for a memory that ends after one structure at fr: they serve this structure, every
address fits in a word, and 22 levels of calls are left. -/
theorem KitRates.lim_at (h : KitRates K limK A s₀ C N D tp tq) (fr : ℕ) :
    K.Lim (limK (fr + K.size N D)) N D fr 1 ∧
      ((fr + K.size N D : ℕ) : ℤ) ≤ (limK (fr + K.size N D)).word ∧
      K.depPre D + 22 ≤ (limK (fr + K.size N D)).depth := by
  have hlim := h.lim_ok _ fr le_rfl
  have hword := (K.std hlim).space_le
  rw [h.space_eq] at hword
  exact ⟨hlim, hword, h.depth_le _⟩

end

/-! ## The data structure of Section 4 as a kit -/

/-- **The rates of the data structure with the parameters G**, for all bounds tp, tq ≥ 1 that
dominate the two costs of Theorem 30 from the threshold on, with tp = O(N²). -/
theorem kit31_rates (G : RatParams) {C B : ℝ} (hC : 0 ≤ C) :
    ∃ (A : ℕ) (C' : ℝ), 0 ≤ C' ∧
      ∀ (R : Program) {N D : ℕ} {tp tq : ℝ}, CostsWithin G C N D tp tq → tp ≤ B * (N : ℝ) ^ 2 →
        KitRates (kit31 G R) (limKit31 G N D) A (slopeExp31 G) C' N D tp tq := by
  obtain ⟨Ap, hAp0, hAp⟩ := exists_tPre31_le G hC cShared30
  obtain ⟨Aq, hAq0, hAq⟩ := exists_tQuery31_le G hC
  obtain ⟨As, hAs0, hAs⟩ := exists_structEnd_le G hC
  refine ⟨⌈As * B⌉₊, Ap + Aq, by positivity, fun R {N D tp tq} hc htpN => ?_⟩
  have hpre := hAp hc
  have hquery := hAq hc
  have hcells := hAs hc
  obtain ⟨-, hD, hDN, htp, htq, hbig⟩ := hc
  have hsize : ((structEnd G N D 0 : ℕ) : ℝ) ≤ ((⌈As * B⌉₊ * (N * N) : ℕ) : ℝ) := by
    push_cast
    rw [← pow_two]
    calc ((structEnd G N D 0 : ℕ) : ℝ) ≤ As * tp := hcells
      _ ≤ As * (B * (N : ℝ) ^ 2) := mul_le_mul_of_nonneg_left htpN hAs0
      _ = As * B * (N : ℝ) ^ 2 := by ring
      _ ≤ (⌈As * B⌉₊ : ℝ) * (N : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_right (Nat.le_ceil _) (by positivity)
  exact
    { tPre_le := hpre.trans (mul_le_mul_of_nonneg_right (by linarith) (by linarith))
      tQ_le := hquery.trans (mul_le_mul_of_nonneg_right (by linarith) (by linarith))
      size_le := by exact_mod_cast hsize
      lim_ok := fun sp fr hfr => limKit31_ok G N D sp fr hfr
      space_eq := fun _ => rfl
      depth_le := fun sp => by
        -- the preprocessing needs L + 7 levels of calls, and `baseLim` allows L + 10
        have hdepth : G.L (logFour D) + 10 ≤ (baseLim G N D).depth :=
          (lim31_facts G N D (kitInputEnd N D) 0).1
        change G.L (logFour D) + 7 + 22 ≤ (baseLim G N D).depth + 20
        omega
      small := fun n k s sp hNn hk hss hsp =>
        small_limKit31 hD hDN (fun hm => (hbig hm).1) hNn hk hss hsp }

/-- **Corollary 26's data structure as a kit**: for N ≥ D^18 the preprocessing takes O(N²/D^{0.063})
steps and a query O(D^{0.437}). -/
theorem kitRates_corollary26 :
    ∃ (A : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ (R : Program) (N D : ℕ), 1 ≤ D → D ^ 18 ≤ N →
      KitRates (kit31 ratParams26 R) (limKit31 ratParams26 N D) A (slopeExp31 ratParams26) C N D
        ((N : ℝ) ^ 2 / (D : ℝ) ^ (0.063 : ℝ)) ((D : ℝ) ^ (0.437 : ℝ)) := by
  obtain ⟨C, hC, hreg⟩ := regime26
  obtain ⟨A, C', hC', hrates⟩ := kit31_rates ratParams26 (B := 1) hC
  refine ⟨A, C', hC', fun R N D hD hN => ?_⟩
  exact hrates R (hreg N D hD hN) (by rw [one_mul]; exact preBound26_le_sq hD N)

/-- **The data structure with general parameters as a kit** (Corollary 31), for admissible c, θ, ε,
with γ = γ(c, θ) and q = q(θ): for 1 ≤ D ≤ N^ε the preprocessing takes O(N² (log D + 1)²/D^γ) steps
and a query O(D^q (log D + 1)).  The threshold m₀ ≥ M is as large as one likes, and D ≤ N^ε is asked
only above the threshold: below it D ≤ 4^{m₀}, and the constant takes care of it. -/
theorem kitRates_corollary31 {c θ ε : ℝ} (hadm : Admissible c θ ε) (M : ℕ) :
    ∃ (G : RatParams) (A : ℕ) (C : ℝ), M ≤ G.m₀ ∧ 0 ≤ C ∧
      ∀ (R : Program) (N D : ℕ), 1 ≤ D → D ≤ N → (G.m₀ ≤ logFour D → (D : ℝ) ≤ (N : ℝ) ^ ε) →
        KitRates (kit31 G R) (limKit31 G N D) A (slopeExp31 G) C N D
          (preBound31 (gammaOf c θ) N D) (queryBound31 (qOf θ) D) := by
  obtain ⟨G, C, hC, h⟩ := exists_ratParams hadm
  -- the same parameters with the threshold `max m₀ M`
  obtain ⟨G', hG'⟩ : ∃ G' : RatParams,
      G' = { G with m₀ := max G.m₀ M, hm₀ := le_trans G.hm₀ (le_max_left _ _) } := ⟨_, rfl⟩
  have hm : G'.m₀ = max G.m₀ M := by rw [hG']
  have hL (m : ℕ) : G'.L m = G.L m := by rw [hG']; rfl
  have ht (D : ℕ) : switchOf31 G' D = switchOf31 G D := by rw [hG']; rfl
  have hp (N D : ℕ) : parOf G' N D = parOf G N D := by rw [hG']; rfl
  have hγ := hadm.gamma_pos
  obtain ⟨B, hB, hsq⟩ := exists_preBound31_le_sq hγ
  -- below the threshold the bound on the preprocessing is at least `1/E`
  set E : ℝ := ((4 ^ G'.m₀ : ℕ) : ℝ) ^ gammaOf c θ
  have hE1 : 1 ≤ E :=
    Real.one_le_rpow (by exact_mod_cast Nat.one_le_pow _ _ (by norm_num)) hγ.le
  obtain ⟨A, C', hC', hrates⟩ := kit31_rates G' (B := E * B) hC
  refine ⟨G', A, C' * E, by rw [hm]; exact le_max_right _ _, by positivity,
    fun R N D hD hDN hDε => ?_⟩
  have hN : 1 ≤ N := hD.trans hDN
  have hTp0 : 0 ≤ preBound31 (gammaOf c θ) N D := by unfold preBound31; positivity
  have hTq := one_le_queryBound31 (qOf_nonneg θ hadm.θ_pos hadm.θ_lt) hD
  have habove : G'.m₀ ≤ logFour D → _ := fun hbig => h N D hN hD (hDε hbig)
  refine (hrates R (tp := E * preBound31 (gammaOf c θ) N D) ⟨hN, hD, hDN, ?_, hTq, fun hbig => ?_⟩
    ?_).mono hC' le_rfl (le_mul_of_one_le_left (by linarith) hE1)
  · by_cases hsmall : logFour D < G'.m₀
    · exact one_le_rpow_mul_preBound31 hγ hD hN
        ((Nat.clog_le_iff_le_pow (by norm_num)).1 hsmall.le)
    · exact one_le_mul_of_one_le_of_one_le hE1 (habove (by omega)).one_le_pre
  · obtain ⟨hyp, hcost, hquery⟩ :=
      (habove hbig).above (le_trans (le_max_left _ _) (hm ▸ hbig))
    rw [hL, ht, hp]
    exact ⟨hyp, hcost.trans (mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hTp0 hE1) hC), hquery⟩
  · rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (hsq N D hD) (by linarith)

end Light.Sec5
