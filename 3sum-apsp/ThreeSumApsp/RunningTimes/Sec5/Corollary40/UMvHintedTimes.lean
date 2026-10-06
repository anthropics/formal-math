/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec5.Corollary40.DataStructureBounds
public import ThreeSumApsp.Programs.Sec5.Corollary40.UMvHinted
public import ThreeSumApsp.RunningTimes.Sec5.Corollary40.ToMachine
public import ThreeSumApsp.Sec5.Corollary40.GeneralParameters
public import ThreeSumApsp.Sec5.Corollary40.RoundingThreshold

/-!
# Corollary 40, Conjecture 5.12: the running times of uMv-hinted uMv

Proof of Corollary 40: "Cut the n rows of U into n/t₂ blocks of t₂ rows, and preprocess each of the
n/t₂ products of a block with Y [...].  So Phase 3 costs (n/t₂) · O(t₂²/D^0.063) =
O(n^{1+τ₂−0.063τ₁}) time.  In Phase 4, [...] t₂ queries [...] take O(t₂ D^0.437) = O(n^{τ₂+0.437τ₁})
time.  Phase 2 only stores I."

The argument is made for a data structure with given rates at the sizes N = t₂ = ⌊n^{τ₂}⌋ and
D = t₁ = ⌊n^{τ₁}⌋ (`achievesUMvHinted_of_rates`).  Phase 3 takes the time of ⌈n/t₂⌉ preprocessings
and O(t₁ t₂ + n) steps more, Phase 4 the time of t₂ queries and O(t₂) steps more.  With the rates of
Corollary 26 this gives the statement for τ₁ < τ₂/18 (`achievesUMvHinted_of_lt_eighteenth`).

Two things differ from the paper's text.  The input of a phase is written into the memory when the
phase starts, so Phase 2 has nothing to store and returns at once.  The blocks are counted from the
last row upwards, and if t₂ does not divide n, the block that starts at row 0 overlaps the next
one.  The structure of the block with the first row s lies s A t₂² cells after a common base; so
the memory has room for n such distances, and one choice of the limits serves all places
(`uMvLim_of_rates`).

"General τ" (proof of Corollary 40): "For Conjecture 5.12, we use the same blocks, which requires
n^{τ₁} ≤ n^{ετ₂}, that is, τ₁ ≤ ετ₂ for some ε < ε*."  This is `achievesUMvHinted_of_rates` with the
rates of Corollary 31 (`achievesUMvHinted_of_genParams`, `achievesUMvHinted_of_lt_epsStar`).  After
the rounding the condition t₁ ≤ t₂^ε can fail for small t₁; `exists_hint_threshold` gives a constant
such that it holds as soon as t₁ exceeds it.  The data structure needs the condition only above its
threshold, below which it answers queries by inner products; so the threshold is chosen at least as
large as that constant (`kitRates_corollary31`).
-/

@[expose] public section

open ThreeSumApsp

namespace Light.Sec5

open ThreeSumApsp.WordRam ThreeSumApsp.HintedMv Light.Sec4

/-- A procedure that does nothing and serves as Phase 1 and as Phase 2, Phases 3 and 4, and their
three routines, as procedures o to o + 5.  A is the numeral in the program text that fixes the
distance of the structures. -/
def uMvProcsAt (A o : ℕ) : Program :=
  [.skip, uMvPhase3Body A (o + 3) (o + 4), uMvPhase4Body A (o + 5), gatherBody, blocksBody,
    scanBody]

/-- The inputs, the output, Y, the table and n distances of A t₂² cells are polynomially many cells.
-/
theorem uMvTop_le {n t₁ t₂ A s : ℕ} (hn : 1 ≤ n) (h1 : t₁ ≤ n) (h2 : t₂ ≤ n) :
    uMvTop A n t₁ t₂ ≤ polyBound (s + Nat.size (A + 8)) 40 [n] := by
  refine le_polyBound_of_le_pow (e := 3) (by norm_num) ?_
  have hcube : (n + 1) ^ 3 = n * n * n + 3 * (n * n) + 3 * n + 1 := by ring
  have hU : n * t₁ ≤ n * n := Nat.mul_le_mul_left _ h1
  have hV : t₂ * n ≤ n * n := Nat.mul_le_mul_right _ h2
  have hY : t₁ * t₂ ≤ n * n := Nat.mul_le_mul h1 h2
  have hblocks : n * (A * (t₂ * t₂)) ≤ A * (n + 1) ^ 3 :=
    calc n * (A * (t₂ * t₂)) ≤ n * (A * (n * n)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.mul_le_mul h2 h2))
      _ = A * (n * n * n) := by ring
      _ ≤ A * (n + 1) ^ 3 := Nat.mul_le_mul_left _ (by omega)
  have hnn : n ≤ n * n := Nat.le_mul_of_pos_left _ hn
  have hsplit : (A + 8) * (n + 1) ^ 3 = A * (n + 1) ^ 3 + 8 * (n + 1) ^ 3 := by ring
  simp only [uMvTop, uMvBase, uMvS, uMvY, uMvFree, uMvOut, uMvQ, uMvJ, uMvI, uMvV, uMvN, uMvSz]
  omega

/-- The structure of the block with the first row s lies within the cells that are used. -/
theorem uMvFr_add_le {A n t₁ t₂ s sz : ℕ} (h2 : 1 ≤ t₂) (hs : s + t₂ ≤ n)
    (hsz : sz ≤ A * (t₂ * t₂)) :
    uMvFr A n t₁ t₂ s + sz ≤ uMvTop A n t₁ t₂ := by
  have h : (s + 1) * uMvSz A t₂ ≤ n * uMvSz A t₂ := Nat.mul_le_mul_right _ (by omega)
  have e : (s + 1) * uMvSz A t₂ = s * uMvSz A t₂ + uMvSz A t₂ := by ring
  have hz : sz ≤ uMvSz A t₂ := hsz
  unfold uMvFr uMvTop
  omega

/-- **One choice of the limits serves the structures of all blocks**: the limits for a memory that
ends after the last structure. -/
theorem uMvLim_of_rates {P : Program} {K : DsKit P} {limK : ℕ → Limits} {A s₀ n t₁ t₂ : ℕ}
    {C tp tq : ℝ} (hK : KitRates K limK A s₀ C t₂ t₁ tp tq) (hn : 1 ≤ n) (ht₂ : 1 ≤ t₂)
    (ht₂n : t₂ ≤ n) :
    UMvLim K (limK (uMvTop A n t₁ t₂)) A n t₁ t₂ ∧
      ((uMvTop A n t₁ t₂ : ℕ) : ℤ) ≤ (limK (uMvTop A n t₁ t₂)).word ∧
      n ≤ uMvTop A n t₁ t₂ := by
  have hlim := fun s (hs : s + t₂ ≤ n) => hK.lim_ok (uMvTop A n t₁ t₂) _
    (uMvFr_add_le (t₁ := t₁) ht₂ hs hK.size_le)
  have hdepth := hK.depth_le (uMvTop A n t₁ t₂)
  have hw := (K.std (hlim 0 (by omega))).space_le
  rw [hK.space_eq] at hw
  have hA : A ≤ uMvTop A n t₁ t₂ := by
    have : A ≤ n * uMvSz A t₂ :=
      calc A = 1 * (A * (1 * 1)) := by ring
        _ ≤ n * (A * (t₂ * t₂)) :=
          Nat.mul_le_mul hn (Nat.mul_le_mul_left _ (Nat.mul_le_mul ht₂ ht₂))
    unfold uMvTop
    omega
  exact ⟨⟨hlim, by rw [hK.space_eq], by omega, le_trans (by exact_mod_cast hA) hw⟩, hw,
    by simp only [uMvTop, uMvBase]; omega⟩

/-- The numbers of the six procedures after a program of o procedures. -/
theorem uMvProcsAt_lookup (P₀ : Program) (A : ℕ) {o : ℕ} (ho : o = P₀.length) :
    UMvProcs (P₀ ++ uMvProcsAt A o) A o (o + 1) (o + 2) (o + 3) (o + 4) (o + 5) := by
  subst ho
  exact ⟨getElem?_append_length_add P₀ (i := 0) rfl, getElem?_append_length_add P₀ (i := 1) rfl,
    getElem?_append_length_add P₀ (i := 2) rfl, getElem?_append_length_add P₀ (i := 3) rfl,
    getElem?_append_length_add P₀ (i := 4) rfl, getElem?_append_length_add P₀ (i := 5) rfl⟩

section times
variable {P : Program} {K : DsKit P} {limK : ℕ → Limits} {A s₀ n t₁ t₂ : ℕ} {C E X tp tq : ℝ}

/-- **The time of Phase 3**: c = ⌈n/t₂⌉ preprocessings, c C tp ≤ C E X, and
19 t₁ t₂ + 29 t₁ + 13 c t₂ + 50 c + 89 steps, where t₁ ≤ t₁ t₂ ≤ X and c ≤ c t₂ ≤ 2 n ≤ 2 X. -/
theorem tPhase3_le_of_rates (hK : KitRates K limK A s₀ C t₂ t₁ tp tq) (hC : 0 ≤ C) (hE : 0 ≤ E)
    (ht₂ : 1 ≤ t₂) (ht₂n : t₂ ≤ n) (htp : ∀ c : ℕ, c * t₂ < n + t₂ → (c : ℝ) * tp ≤ E * X)
    (hwrite : (t₁ : ℝ) * t₂ ≤ X) (hlinear : (n : ℝ) ≤ X) :
    ((tGather t₁ t₂ + tBlocks K n t₁ t₂ + 75 : ℕ) : ℝ) ≤ (C * E + 600) * (X + 1) := by
  have hCE : 0 ≤ C * E := mul_nonneg hC hE
  obtain ⟨c, hc⟩ : ∃ c, c = (n + t₂ - 1) / t₂ := ⟨_, rfl⟩
  have hblocks : c * t₂ < n + t₂ := hc ▸ Nat.ceilDiv_mul_lt ht₂
  have hsteps : ((tGather t₁ t₂ + tBlocks K n t₁ t₂ + 75 : ℕ) : ℝ) =
      (t₁ : ℝ) * (19 * (t₂ : ℝ) + 29) + (c : ℝ) * ((K.tPre t₂ t₁ : ℝ) + 13 * (t₂ : ℝ) + 50)
        + 89 := by
    unfold tGather tBlocks
    rw [← hc]
    push_cast
    ring
  have hpre := hK.mul_tPre_le hC (Nat.cast_nonneg c) (htp c hblocks)
  have hone : (1 : ℝ) ≤ (t₂ : ℝ) := by exact_mod_cast ht₂
  have hrows := blocks_mul_le ht₂n hblocks
  have hcount : (c : ℝ) ≤ (c : ℝ) * (t₂ : ℝ) := le_mul_of_one_le_right (by positivity) hone
  have hinner : (t₁ : ℝ) ≤ (t₁ : ℝ) * (t₂ : ℝ) := le_mul_of_one_le_right (by positivity) hone
  rw [hsteps]
  linarith

/-- **The time of Phase 4**: t₂ queries, t₂ C tq ≤ C E X, and 40 t₂ + 114 steps, where t₂ ≤ X. -/
theorem tPhase4_le_of_rates (hK : KitRates K limK A s₀ C t₂ t₁ tp tq) (hC : 0 ≤ C) (hE : 0 ≤ E)
    (htq : (t₂ : ℝ) * tq ≤ E * X) (hlinear : (t₂ : ℝ) ≤ X) :
    ((tScan K t₁ t₂ + 102 : ℕ) : ℝ) ≤ (C * E + 600) * (X + 1) := by
  have hCE : 0 ≤ C * E := mul_nonneg hC hE
  have hsteps : ((tScan K t₁ t₂ + 102 : ℕ) : ℝ) = (t₂ : ℝ) * ((K.tQ t₁ : ℝ) + 40) + 114 := by
    unfold tScan
    push_cast
    ring
  have hquery := hK.mul_tQ_le hC (Nat.cast_nonneg t₂) htq
  have hnonneg : (0 : ℝ) ≤ (t₂ : ℝ) := Nat.cast_nonneg t₂
  rw [hsteps]
  linarith

end times

/-- **Rates for the blocks of uMv-hinted uMv**: what the running times use about the data structure
with the parameters G at the sizes N = t₂ = ⌊n^{τ₂}⌋ and D = t₁ = ⌊n^{τ₁}⌋. -/
structure BlockRates (τ₁ τ₂ a₃ a₄ : ℝ) (G : RatParams) (A : ℕ) (C E : ℝ) (tp tq : ℕ → ℝ) :
    Prop where
  C_nonneg : 0 ≤ C
  E_nonneg : 0 ≤ E
  /-- The preprocessing takes at most C tp n steps and a query at most C tq n. -/
  kit : ∀ (R : Program) (n : ℕ), 1 ≤ n →
    KitRates (kit31 G R) (limKit31 G (hintSize τ₂ n) (hintSize τ₁ n)) A (slopeExp31 G) C
      (hintSize τ₂ n) (hintSize τ₁ n) (tp n) (tq n)
  /-- The preprocessing of the ⌈n/t₂⌉ blocks is O(n^a₃). -/
  pre_le : ∀ n c : ℕ, 1 ≤ n → c * hintSize τ₂ n < n + hintSize τ₂ n →
    (c : ℝ) * tp n ≤ E * (n : ℝ) ^ a₃
  /-- Writing Y = N_{I,J} is O(n^a₃). -/
  copy_le : ∀ n : ℕ, 1 ≤ n → (hintSize τ₁ n : ℝ) * (hintSize τ₂ n : ℝ) ≤ (n : ℝ) ^ a₃
  /-- t₂ queries are O(n^a₄). -/
  query_le : ∀ n : ℕ, 1 ≤ n → (hintSize τ₂ n : ℝ) * tq n ≤ E * (n : ℝ) ^ a₄

/-- **uMv-hinted uMv over a data structure with given rates.**  Let 0 ≤ τ₁ ≤ τ₂ ≤ 1, 1 ≤ a₃ and
τ₂ ≤ a₄.  With rates as in `BlockRates`, Phase 2 takes O(n^{τ₁}), Phase 3 takes O(n^a₃) and Phase 4
takes O(n^a₄) time on the word RAM. -/
theorem achievesUMvHinted_of_rates {τ₁ τ₂ a₃ a₄ C E : ℝ} {G : RatParams} {A : ℕ} {tp tq : ℕ → ℝ}
    (h0 : 0 ≤ τ₁) (h12 : τ₁ ≤ τ₂) (h2 : τ₂ ≤ 1) (ha₃ : 1 ≤ a₃) (ha₄ : τ₂ ≤ a₄)
    (hrates : BlockRates τ₁ τ₂ a₃ a₄ G A C E tp tq) : AchievesUMvHinted τ₁ τ₂ τ₁ a₃ a₄ := by
  have hC := hrates.C_nonneg
  have hE := hrates.E_nonneg
  have hCE : 0 ≤ C * E := mul_nonneg hC hE
  -- the six procedures are appended to the program of the data structure, from number o on
  obtain ⟨o, ho⟩ : ∃ o, o = (program31 G).length := ⟨_, rfl⟩
  refine achievesUMvHinted_of_light (a₁ := 0) (A := C * E + 600) (program31 G ++ uMvProcsAt A o) o o
    (o + 1) (o + 2) (slopeExp31 G + Nat.size (A + 8) + 1) 40 fun n hn U N V I J i j => ?_
  have ht₁ := one_le_hintSize (τ := τ₁) hn h0
  have ht₂ := one_le_hintSize (τ := τ₂) hn (h0.trans h12)
  have ht₂n := hintSize_le (τ := τ₂) hn h2
  have ht₁n := hintSize_le (τ := τ₁) hn (h12.trans h2)
  have hK := hrates.kit (uMvProcsAt A o) n hn
  obtain ⟨hlim, hword, hn_le⟩ := uMvLim_of_rates (t₁ := hintSize τ₁ n) hK hn ht₂ ht₂n
  obtain ⟨c₁, c₂, c₃, c₄, hsteps₁, hsteps₂, hsteps₃, hsteps₄, hrun⟩ :=
    uMv_lightPhases (kit31 G (uMvProcsAt A o)) (uMvProcsAt_lookup (program31 G) A ho) ht₁ ht₂ ht₂n
      hK.size_le hlim U N V I J i j
  refine ⟨_, c₁, c₂, c₃, c₄, {
    small := hK.small n 40 (slopeExp31 G + Nat.size (A + 8)) _ ht₂n le_rfl (by omega)
      (uMvTop_le hn ht₁n ht₂n)
    sizes_le := by
      simpa using And.intro (le_trans (by exact_mod_cast hn_le) hword)
        (And.intro (le_trans (by exact_mod_cast ht₁n.trans hn_le) hword)
          (le_trans (by exact_mod_cast ht₂n.trans hn_le) hword))
    steps := .cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ .nil)))
    run := hrun }⟩ <;> unfold Within
  · -- Phase 1 returns at once
    have hsteps : (c₁ : ℝ) ≤ 4 := by exact_mod_cast hsteps₁
    rw [Real.rpow_zero]
    linarith
  · -- Phase 2 returns at once
    have hsteps : (c₂ : ℝ) ≤ 4 := by exact_mod_cast hsteps₂
    have hpow : (0 : ℝ) ≤ (n : ℝ) ^ τ₁ := by positivity
    have hprod : 0 ≤ C * E * (n : ℝ) ^ τ₁ := mul_nonneg hCE hpow
    linarith
  · -- Phase 3
    exact le_trans (by exact_mod_cast hsteps₃) (tPhase3_le_of_rates hK hC hE ht₂ ht₂n
      (fun c hc => hrates.pre_le n c hn hc) (hrates.copy_le n hn)
      (by simpa using natCast_rpow_le_rpow hn ha₃))
  · -- Phase 4
    exact le_trans (by exact_mod_cast hsteps₄) (tPhase4_le_of_rates hK hC hE
      (hrates.query_le n hn) ((hintSize_le_rpow n τ₂).trans (natCast_rpow_le_rpow hn ha₄)))

/-- **Corollary 40, Conjecture 5.12, 0 < τ₁ < τ₂/18, τ₂ < 1**: uMv-hinted uMv is solved on the word
RAM with Phase 2 in O(n^{τ₁}), Phase 3 in O(n^{1+τ₂−0.063τ₁}) and Phase 4 in O(n^{τ₂+0.437τ₁}) time.
-/
theorem achievesUMvHinted_of_lt_eighteenth {τ₁ τ₂ : ℝ} (h0 : 0 < τ₁) (h1 : τ₁ < τ₂ / 18)
    (h2 : τ₂ < 1) :
    AchievesUMvHinted τ₁ τ₂ τ₁ (1 + τ₂ - 0.063 * τ₁) (τ₂ + 0.437 * τ₁) := by
  obtain ⟨A, C, hC, hrates⟩ := kitRates_corollary26
  exact achievesUMvHinted_of_rates h0.le (by linarith) h2.le (by linarith) (by linarith)
    { C_nonneg := hC
      E_nonneg := show (0 : ℝ) ≤ 4 by norm_num
      kit := fun R n hn => hrates R _ _ (one_le_hintSize hn h0.le)
        (hintSize_pow_eighteen_le_hintSize hn h1.le)
      pre_le := fun n c hn hc => by
        rw [← mul_div_assoc]
        exact blocks_sq_div_le hn h0.le h2.le hc
      copy_le := fun n hn =>
        (hintSize_mul_hintSize_le hn τ₁ τ₂).trans (natCast_rpow_le_rpow hn (by linarith))
      query_le := fun n hn => (hintSize_mul_hintSize_rpow_le hn τ₁ τ₂).trans
        (le_mul_of_one_le_left (by positivity) (by norm_num)) }

/-- **Corollary 40, Conjecture 5.12, general τ**: for parameters c, θ, ε, γ as in `GenParams`,
0 < τ₁ < ε τ₂ and 0 < τ₂ < 1, uMv-hinted uMv is solved on the word RAM with Phase 2 in O(n^{τ₁}),
Phase 3 in O(n^{1+τ₂−γτ₁}) and Phase 4 in O(n^{τ₂+τ₁/2}) time. -/
theorem achievesUMvHinted_of_genParams {c θ ε γ τ₁ τ₂ : ℝ} (p : GenParams c θ ε γ) (h0 : 0 < τ₁)
    (h1 : τ₁ < ε * τ₂) (hτ2 : 0 < τ₂) (h2 : τ₂ < 1) :
    AchievesUMvHinted τ₁ τ₂ τ₁ (1 + τ₂ - γ * τ₁) (τ₂ + τ₁ / 2) := by
  -- 0 < ε < ε* < 1, so that τ₁ ≤ τ₂
  have hεs := p.ε_lt_epsStar
  have hs := sec4_epsStar_numeric.2
  have hε0 : 0 < ε := by
    by_contra hneg
    have : ε * τ₂ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (not_lt.1 hneg) hτ2.le
    linarith
  have h12 : τ₁ ≤ τ₂ := h1.le.trans (mul_le_of_le_one_left hτ2.le (by linarith))
  have hγτ : γ * τ₁ ≤ τ₁ := mul_le_of_le_one_left h0.le p.γ_le
  have hhalf : τ₁ < 1 / 2 := by
    have : ε * τ₂ ≤ ε := mul_le_of_le_one_right hε0.le h2.le
    linarith
  obtain ⟨Mt, hMt⟩ := exists_hint_threshold h0 hτ2.le h1 hε0.le (by linarith)
  obtain ⟨G, A, C, hGM, hC, hb⟩ := kitRates_corollary31 p.toAdmissible Mt
  obtain ⟨C₁, hC₁, hpre⟩ := general_umv_pre_le p.γ_pos.le p.γ_lt
  obtain ⟨C₂, hC₂, hquery⟩ := general_umv_query_le (qOf_nonneg θ p.θ_pos p.θ_lt) p.q_lt
  -- t₁ ≤ t₂, because τ₁ ≤ τ₂
  have ht₁₂ (n : ℕ) (hn : 1 ≤ n) : hintSize τ₁ n ≤ hintSize τ₂ n := by
    simpa using hintSize_pow_le_hintSize (τ := τ₁) hn 1 (σ := τ₂) (by push_cast; linarith [h12])
  exact achievesUMvHinted_of_rates h0.le h12 h2.le (by linarith [hγτ, h12]) (by linarith [h0])
    { C_nonneg := hC
      E_nonneg := add_nonneg hC₁ hC₂
      kit := fun R n hn => hb R _ _ (one_le_hintSize hn h0.le) (ht₁₂ n hn)
        fun hm => hMt n hn (hGM.trans hm)
      pre_le := fun n b hn hb => by
        have hblocks := hpre n b τ₁ τ₂ hn h0.le h2.le hb
        unfold preBound31
        rw [← mul_div_assoc, ← mul_assoc]
        exact hblocks.trans (mul_le_mul_of_nonneg_right (by linarith [hC₂]) (by positivity))
      -- t₁ t₂ ≤ n^{τ₁ + τ₂}, and τ₁ + τ₂ ≤ 1 + τ₂ − γ τ₁ because γ τ₁ ≤ τ₁ < 1/2
      copy_le := fun n hn => (hintSize_mul_hintSize_le hn τ₁ τ₂).trans
        (natCast_rpow_le_rpow hn (by linarith [hγτ, hhalf]))
      query_le := fun n hn => by
        have hqueries := hquery n τ₁ τ₂ hn h0.le
        rw [mul_assoc] at hqueries
        exact hqueries.trans (mul_le_mul_of_nonneg_right (by linarith [hC₁]) (by positivity)) }

/-- **The uMv part of Corollary 40, "General τ"**: for 0 < τ₁ < ε* τ₂ and τ₂ < 1 there is a saving
γ > 0. -/
theorem achievesUMvHinted_of_lt_epsStar {τ₁ τ₂ : ℝ} (h0 : 0 < τ₁) (h1 : τ₁ < epsStar * τ₂)
    (h2 : τ₂ < 1) :
    ∃ γ : ℝ, 0 < γ ∧ AchievesUMvHinted τ₁ τ₂ τ₁ (1 + τ₂ - γ * τ₁) (τ₂ + τ₁ / 2) := by
  have hs := sec4_epsStar_numeric.1
  have hτ2 : 0 < τ₂ := by
    by_contra hneg
    have : epsStar * τ₂ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) (not_lt.1 hneg)
    linarith
  obtain ⟨c, θ, ε, γ, p, hτ⟩ := exists_genParams_mul hτ2 h1
  exact ⟨γ, p.γ_pos, achievesUMvHinted_of_genParams p h0 hτ hτ2 h2⟩

end Light.Sec5
