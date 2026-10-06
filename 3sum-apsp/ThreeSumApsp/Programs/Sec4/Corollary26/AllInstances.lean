/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec4.ChoosingParameters.Program
public import ThreeSumApsp.Programs.Sec4.Corollary26.Regime

/-!
# Corollary 26, the offline form, on all instances

Corollary 26 is about matrices with N ≥ D^18. A solver that other procedures call has to be right on
every instance. allInstances26(N, D, w, U, x, y, wi, wj, out, fr) tests whether D^18 ≤ N, calls the
offline routine offline32 if so and the brute force if not. The texts are `allInstances26Body` and
`regimeTest26Body`.

* *The routine.* It solves the task `thinTask` on every instance, within the time
  `allInstancesTime26` and the need `allInstancesNeed26` (`allInstances26_solves`). It tests whether
  D^18 ≤ N (`regimeTest26_meets`). In that regime it calls the offline routine of Corollary 26,
  whose demands on the limits are covered by the need (`lim31_of_need`, `offline32_meets_thinTask`);
  outside it calls the brute force.
* *The time in the regime.* For N ≥ D^18 the time is O(w D^{0.437} + N²/D^{0.063}), the bound of
  Corollary 26: the time of the offline routine is at most a constant times tp + w tq for all bounds
  that dominate the two costs of Theorem 30 (`exists_tOffline32_le`), and in the regime the two
  bounds of Corollary 26 do (`regime26`).
* *The need is polynomial in the parameters.* Every summand of the need is a numeral times a product
  of at most 20 factors N + 1, D and U. With Q = (N + 1) (D + 1) (w + 1) (U + 1) each factor is at
  most Q, so each product is at most Q^20 (`le_pow_twenty`). So the largest number, the cells and
  the levels of calls are at most 2^11 Q^20 (`word_le`, `cells_le`, `depth_le`).
-/

@[expose] public section

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.Spec

/-! ## Time and need -/

/-- The time of allInstances26, for the parameters N, D, w, U; c is the constant of the shared
stage. -/
def allInstancesTime26 (c : ℕ) : List ℕ → ℕ
  | [N, D, w, _] =>
    400 + (if D ^ 18 ≤ N then tOffline32 c ratParams26 N D w else 40 * ((w + 1) * (D + 1)))
  | _ => 0

/-- What allInstances26 needs, for the parameters N, D, w, U: the largest number formed, the cells
from the free pointer on, the levels of calls. With B = (N + 1)^5, which bounds 10^L in the regime
(`below`). -/
def allInstancesNeed26 : List ℕ → Need
  | [N, D, _, U] =>
    ⟨1000 + 100 * D + N * D + D * (U * U) + ((N + 1) ^ 5) ^ 3 * (U * U) + 7 * ((N + 1) ^ 5 * U)
        + 10 * (N + 1) ^ 5,
      4 + N + 8 * (N * D) + 222 * ((N + 1) ^ 5) ^ 4, 84 * D + 12⟩
  | _ => ⟨0, 0, 0⟩

/-! ## The test -/

/-- regimeTest26(N, D) returns 1 if D^18 ≤ N and 0 if not, and changes no cell. -/
theorem regimeTest26_ends {lim : Limits} {P : Program} {d : ℕ} (N D : ℕ) (hD : 1 ≤ D)
    (hword : ((4 * D + N * D + 100 : ℕ) : ℤ) ≤ lim.word) (μ : ℕ → ℤ) :
    Ends lim P d regimeTest26Body ⟨frame [(N : ℤ), (D : ℤ)], μ⟩ 336 fun σ' =>
      σ'.mem = μ ∧ ((σ'.loc 0 = 1 ∧ D ^ 18 ≤ N) ∨ (σ'.loc 0 = 0 ∧ N < D ^ 18)) := by
  unfold regimeTest26Body
  refine Ends.seq 334 2 ((Sec2.regimePow_spec N D hD hword μ _ (by simp) (by simp)).mono le_rfl ?_)
      (by omega)
  rintro ⟨loc', μ'⟩ ⟨em, -, h⟩
  simp only at em h
  exact Ends.set trivial (by simp) ⟨em, by simpa using h⟩

/-- The procedure regimeTest26 returns 1 if D^18 ≤ N and 0 if not, and changes no cell. -/
theorem regimeTest26_meets {lim : Limits} {P : Program} {d : ℕ}
    (hP : P[Proc.regimeTest26]? = some regimeTest26Body)
    (N D : ℕ) (hD : 1 ≤ D) (hword : ((4 * D + N * D + 100 : ℕ) : ℤ) ≤ lim.word) (μ : ℕ → ℤ) :
    Meets lim P Proc.regimeTest26 d [N, D] μ 336 fun r μ' =>
      μ' = μ ∧ ((r = 1 ∧ D ^ 18 ≤ N) ∨ (r = 0 ∧ N < D ^ 18)) :=
  .of_body hP (regimeTest26_ends N D hD hword μ)

/-! ## The limits -/

section need

variable {lim : Limits} {N D₀ w U fr d : ℕ}

/-- A number that is at most the first part of the need fits in a word. -/
private theorem fits_of_need (ok : (allInstancesNeed26 [N, D₀, w, U]).Ok lim fr d) {n : ℕ}
    (hn : n ≤ 1000 + 100 * D₀ + N * D₀ + D₀ * (U * U) + ((N + 1) ^ 5) ^ 3 * (U * U) +
      7 * ((N + 1) ^ 5 * U) + 10 * (N + 1) ^ 5) : (n : ℤ) ≤ lim.word :=
  le_trans (by exact_mod_cast hn) ok.word

/-- The block of Theorem 30, behind the two padded matrices, ends within the cells of the need. -/
private theorem top_le_of_need (hD : 1 ≤ D₀) (H : Hyp30 (par26 N D₀) (switch26 D₀))
    (ok : (allInstancesNeed26 [N, D₀, w, U]).Ok lim fr d) :
    top (par26 N D₀) (switch26 D₀) (blockAt N D₀ fr) ≤ lim.space := by
  have hcells : fr + (4 + N + 8 * (N * D₀) + 222 * ((N + 1) ^ 5) ^ 4) ≤ lim.space := ok.cells
  have hblock : top (par26 N D₀) (switch26 D₀) (blockAt N D₀ fr) - blockAt N D₀ fr
      ≤ 222 * ((N + 1) ^ 5) ^ 4 := top_sub_le_pow H (below H) _
  -- each padded matrix has N 4^m ≤ 4 N D₀ cells
  have hpad : N * D (logFour D₀) ≤ 4 * (N * D₀) :=
    (Nat.mul_le_mul_left N (Nat.pow_clog_le_mul (b := 4) (by norm_num) hD)).trans_eq (by ring)
  have hbase : blockAt N D₀ fr = fr + 3 + N * D (logFour D₀) + N * D (logFour D₀) := rfl
  omega

/-- If B bounds 10^L, 7^L and 10^m, the three numbers in the limits of Theorem 30 are at most B³ U²,
7 B U and 10 B. -/
private theorem lim30_of_below {p : Sec2.Par} {t b0 B : ℕ} (hB : Below p t B) (std : Std lim)
    (hspace : top p t b0 ≤ lim.space)
    (fits : ∀ n : ℕ, n ≤ B ^ 3 * (U * U) + 7 * (B * U) + 10 * B → (n : ℤ) ≤ lim.word) :
    Lim30 lim p t b0 (U : ℤ) := by
  have hten := hB.T
  have hseven := hB.S7
  have htenm := hB.tenm
  have hvalue : 10 ^ p.m * ((7 ^ p.L * U) * (7 ^ p.L * U)) ≤ B ^ 3 * (U * U) :=
    calc 10 ^ p.m * ((7 ^ p.L * U) * (7 ^ p.L * U)) ≤ B * ((B * U) * (B * U)) := by gcongr
      _ = B ^ 3 * (U * U) := by ring
  have henc : 7 ^ (p.L + 1) * U ≤ 7 * (B * U) :=
    calc 7 ^ (p.L + 1) * U = 7 * (7 ^ p.L * U) := by ring
      _ ≤ 7 * (B * U) := by gcongr
  have hpow : 10 ^ (p.L + 1) ≤ 10 * B :=
    calc 10 ^ (p.L + 1) = 10 * 10 ^ p.L := by ring
      _ ≤ 10 * B := by gcongr
  exact {
    std := std
    space := hspace
    value := by exact_mod_cast fits _ (hvalue.trans (by omega))
    enc := by exact_mod_cast fits _ (henc.trans (by omega))
    pow := fits _ (hpow.trans (by omega)) }

/-- In the regime, the need of allInstances26 covers what offline32 asks of the limits. -/
theorem lim31_of_need (hD : 1 ≤ D₀) (hN : D₀ ^ 18 ≤ N)
    (ok : (allInstancesNeed26 [N, D₀, w, U]).Ok lim fr d) :
    Lim31 lim ratParams26 N D₀ fr (U : ℤ) := by
  have hcells : fr + (4 + N + 8 * (N * D₀) + 222 * ((N + 1) ^ 5) ^ 4) ≤ lim.space := ok.cells
  have fits {n : ℕ} := fits_of_need ok (n := n)
  -- 4^m ≤ 4 D₀ and m ≤ 4 D₀
  have h4 : 4 ^ logFour D₀ ≤ 4 * D₀ := Nat.pow_clog_le_mul (b := 4) (by norm_num) hD
  have hm4 : logFour D₀ ≤ 4 * D₀ := logFour_le_four_mul hD
  have std : Std lim := ⟨ok.space, by exact_mod_cast fits (n := 100) (by omega)⟩
  have large (hm : 60 ≤ logFour D₀) : Lim30 lim (par26 N D₀) (switch26 D₀) (blockAt N D₀ fr)
      (U : ℤ) :=
    have H := hyp30_26 hN hm
    lim30_of_below (B := (N + 1) ^ 5) (below H) std (top_le_of_need hD H ok)
      fun n hn => fits (hn.trans (by omega))
  exact {
    std := std
    space := by
      unfold structEnd
      rw [parOf_ratParams26, switchOf31_ratParams26]
      split_ifs with h
      · omega
      · exact (large (not_lt.mp h)).space
    pow := fits (by omega)
    mword := fits (by change 21 * logFour D₀ + 1 + 1 * logFour D₀ + 9 ≤ _; omega)
    m0word := fits (n := 60) (by omega)
    ip := by exact_mod_cast fits (n := D₀ * (U * U)) (by omega)
    large := fun hm => by rw [parOf_ratParams26, switchOf31_ratParams26]; exact large hm }

end need

/-! ## The matrices of an instance -/

/-- The first matrix of an instance. -/
def thinMX (x : ThinInst) : Matrix (Fin x.N) (Fin x.D) ℤ := fun i j => x.X.getD (i * x.D + j) 0

/-- The second matrix of an instance. -/
def thinMY (x : ThinInst) : Matrix (Fin x.D) (Fin x.N) ℤ := fun i j => x.Y.getD (i * x.N + j) 0

theorem matAt_thinMX {x : ThinInst} {μ : ℕ → ℤ} {fr : ℕ} (h : x.Pre μ fr) : MatAt μ x.x
    (thinMX x) := by
  intro i j
  have hlt : (i : ℕ) * x.D + j < x.X.length := by
    rw [h.lenX]
    have := Nat.mul_add_le_mul i.isLt (le_refl x.D)
    have := j.isLt
    omega
  rw [Nat.add_assoc, h.segX.getD hlt 0]
  rfl

theorem matAt_thinMY {x : ThinInst} {μ : ℕ → ℤ} {fr : ℕ} (h : x.Pre μ fr) : MatAt μ x.y
    (thinMY x) := by
  intro i j
  have hlt : (i : ℕ) * x.N + j < x.Y.length := by
    rw [h.lenY]
    have := Nat.mul_add_le_mul i.isLt (le_refl x.N)
    have := j.isLt
    omega
  rw [Nat.add_assoc, h.segY.getD hlt 0]
  rfl

/-- The entry of the product of the two matrices is the entry that the task asks for. -/
theorem entryN_thin (x : ThinInst) {I J : ℕ} (hI : I < x.N) (hJ : J < x.N) :
    entryN (thinMX x) (thinMY x) I J = thinEntry x.N x.D x.X x.Y I J := by
  rw [entryN, dif_pos ⟨hI, hJ⟩, Matrix.mul_apply, thinEntry, List.sum_map_range, Finset.sum_range]
  rfl

/-! ## The routine -/

/-- The answers of the offline routine are those that the task asks for. -/
theorem map_entryN_thin {x : ThinInst} {μ : ℕ → ℤ} {fr : ℕ} (h : x.Pre μ fr) :
    (x.WI.zip x.WJ).map (fun q => entryN (thinMX x) (thinMY x) q.1 q.2)
      = thinOut x.N x.D x.X x.Y x.WI x.WJ :=
  List.map_congr_left fun _ hq =>
    entryN_thin x (h.ltWI _ (List.of_mem_zip hq).1) (h.ltWJ _ (List.of_mem_zip hq).2)

/-- **In the regime** the offline routine solves the task. -/
theorem offline32_meets_thinTask {lim : Limits} {P : Program} {c d : ℕ}
    (task : OfflineSpec32 lim P c ratParams26) {x : ThinInst} {μ : ℕ → ℤ} {fr : ℕ}
    (hpre : x.Pre μ fr) (hreg : x.D ^ 18 ≤ x.N)
    (ok : (allInstancesNeed26 [x.N, x.D, x.w, x.U]).Ok lim fr d) :
    Meets lim P Proc.offline32 (d + 1) [x.N, x.D, x.w, x.U, x.x, x.y, x.wi, x.wj, x.out, fr] μ
      (tOffline32 c ratParams26 x.N x.D x.w) fun r μ' => thinTask.Post x μ fr r μ' := by
  have hU0 : (0 : ℤ) ≤ (x.U : ℤ) := by positivity
  have hdepth : d + (84 * x.D + 12) ≤ lim.depth := ok.depth
  have hm4 := logFour_le_four_mul hpre.D_pos
  have spec := task x.N x.D x.x x.y x.wi x.wj x.out fr (thinMX x) (thinMY x) (x.U : ℤ) (x.U : ℤ) μ
    x.WI x.WJ
    { one_le_D := hpre.D_pos, one_le_N := hpre.N_pos
      lim := lim31_of_need hpre.D_pos hreg ok
      absX := fun i j => hpre.leX.abs_getD_le hU0 _
      absY := fun i j => hpre.leY.abs_getD_le hU0 _
      belowX := hpre.belowX, belowY := hpre.belowY }
    { matX := matAt_thinMX hpre, matY := matAt_thinMY hpre
      rows := hpre.segWI, cols := hpre.segWJ
      length_eq := by rw [hpre.lenWI, hpre.lenWJ]
      rows_lt := hpre.ltWI, cols_lt := hpre.ltWJ
      rows_le := by rw [hpre.lenWI]; exact hpre.belowWI
      cols_le := by rw [hpre.lenWI]; exact hpre.belowWJ
      out_le := by rw [hpre.lenWI]; exact hpre.belowOut
      out_matX := by rw [hpre.lenWI]; exact hpre.apartX
      out_matY := by rw [hpre.lenWI]; exact hpre.apartY
      out_rows := by rw [hpre.lenWI]; exact hpre.apartWI
      out_cols := by rw [hpre.lenWI]; exact hpre.apartWJ }
  rw [hpre.lenWI, ratParams26_L, map_entryN_thin hpre] at spec
  exact (spec _ (by omega)).mono le_rfl fun r μ' h => ⟨h.1, fun a ha => h.2 a ha.1 ha.2⟩

/-- **allInstances26 solves the task on all instances**, in every program that holds allInstances26,
regimeTest26 and the brute force at their numbers and in which offline32 satisfies `OfflineSpec32`
at the parameters of Corollary 26, also after more procedures are appended. -/
theorem allInstances26_solves {P : Program} {c : ℕ}
    (hall : P[Proc.allInstances26]? = some allInstances26Body)
    (htest : P[Proc.regimeTest26]? = some regimeTest26Body)
    (hbrute : P[Sec2.pThinBrute]? = some Sec2.thinBruteBody)
    (task : ∀ (R : Program) (lim : Limits), OfflineSpec32 lim (P ++ R) c ratParams26) :
    SolvesN thinTask P Proc.allInstances26 (allInstancesTime26 c) allInstancesNeed26 := by
  refine ⟨allInstances26Body, hall, fun R lim d x μ fr hpre hok => ?_⟩
  have ok : (allInstancesNeed26 [x.N, x.D, x.w, x.U]).Ok lim fr d := hok
  have hword := ok.word
  have hcells := ok.cells
  have hdepth := ok.depth
  simp only [allInstancesNeed26] at hword hcells hdepth
  have hfits : ∀ n : ℕ, n ≤ 1000 + 100 * x.D + x.N * x.D + x.D * (x.U * x.U) → (n : ℤ) ≤ lim.word :=
    fun n hn => le_trans (by exact_mod_cast (by omega)) hword
  have h100 := hfits 100 (by omega)
  have hroom : fr + x.N + 1 ≤ lim.space := by omega
  clear hword hcells
  change Ends lim (P ++ R) d allInstances26Body
    ⟨frame [x.N, x.D, x.w, x.U, x.x, x.y, x.wi, x.wj, x.out, fr], μ⟩
    (400 + if x.D ^ 18 ≤ x.N then tOffline32 c ratParams26 x.N x.D x.w
      else 40 * ((x.w + 1) * (x.D + 1))) _
  unfold allInstances26Body
  -- regime := regimeTest26(N, D)
  refine Ends.callToThen (regimeTest26_meets (getElem?_append_of_eq_some htest R) x.N x.D hpre.D_pos
    (hfits _ (by omega)) μ) ?_ (hT := by simp; omega)
  rintro r μ ⟨rfl, hr⟩
  -- if 0 < regime
  refine Ends.iteLast (fun hpos => ?_) (fun hneg => ?_)
  · -- return offline32(N, D, w, U, x, y, wi, wj, out, fr)
    have hreg : x.D ^ 18 ≤ x.N := by
      rcases hr with ⟨-, h⟩ | ⟨rfl, -⟩
      · exact h
      · simp at hpos
    rw [if_pos hreg]
    exact Ends.callTo (offline32_meets_thinTask (task R lim) hpre hreg ok) fun _ _ h => h
  · -- return thinBrute(N, D, w, U, x, y, wi, wj, out, fr)
    have hreg : ¬ x.D ^ 18 ≤ x.N := by
      rcases hr with ⟨rfl, -⟩ | ⟨-, h⟩
      · simp at hneg
      · omega
    rw [if_neg hreg]
    have hbrute : Meets lim (P ++ R) Sec2.pThinBrute (d + 1)
        [x.N, x.D, x.w, x.U, x.x, x.y, x.wi, x.wj, x.out, fr] μ (40 * ((x.w + 1) * (x.D + 1)))
        fun r μ' => thinTask.Post x μ fr r μ' :=
      .of_body (getElem?_append_of_eq_some hbrute R) (Sec2.thinBrute_spec
        ⟨ok.space, by exact_mod_cast h100⟩ x μ fr (x.U : ℤ) hpre hroom (hfits _ (by omega)))
    exact Ends.callTo hbrute fun _ _ h => h

/-! ## The time in the regime -/

/-- **The time of allInstances26 in the regime is within the bound of Corollary 26.** -/
theorem allInstancesTime26_le (c : ℕ) : ∃ C : ℝ, ∀ N D₀ w U : ℕ, 1 ≤ D₀ → D₀ ^ 18 ≤ N →
    (allInstancesTime26 c [N, D₀, w, U] : ℝ)
      ≤ C * ((w : ℝ) * (D₀ : ℝ) ^ (0.437 : ℝ) + (N : ℝ) ^ 2 / (D₀ : ℝ) ^ (0.063 : ℝ)) := by
  obtain ⟨C, hC, hreg⟩ := regime26
  obtain ⟨A, hA⟩ := exists_tOffline32_le ratParams26 hC c 400
  refine ⟨A, fun N D₀ w U hD hN => ?_⟩
  have htime : (allInstancesTime26 c [N, D₀, w, U] : ℝ)
      = (tOffline32 c ratParams26 N D₀ w : ℝ) + (400 : ℕ) := by
    simp only [allInstancesTime26, if_pos hN]
    push_cast
    ring
  rw [htime]
  refine (hA w (hreg N D₀ hD hN)).trans (le_of_eq ?_)
  simp only [preBound26]
  ring

/-! ## The need is polynomial in the parameters -/

private theorem le_pow_twenty {Q x : ℕ} (hQ : 1 ≤ Q) (i : ℕ) (hi : i ≤ 20) (h : x ≤ Q ^ i) :
    x ≤ Q ^ 20 :=
  h.trans (Nat.pow_le_pow_right hQ hi)

section summands

variable {N D U Q : ℕ}

/-- The largest number that allInstances26 forms. -/
private theorem word_le (hN : N + 1 ≤ Q) (hD : D ≤ Q) (hU : U ≤ Q) :
    1000 + 100 * D + N * D + D * (U * U) + ((N + 1) ^ 5) ^ 3 * (U * U) +
      7 * ((N + 1) ^ 5 * U) + 10 * (N + 1) ^ 5 ≤ 2 ^ 11 * Q ^ 20 := by
  have hQ : 1 ≤ Q := by omega
  have hN' : N ≤ Q := by omega
  have h1 : 1 ≤ Q ^ 20 := Nat.one_le_pow _ _ hQ
  have hD1 : D ≤ Q ^ 20 := le_pow_twenty hQ 1 (by norm_num) (by simpa using hD)
  have hND : N * D ≤ Q ^ 20 := le_pow_twenty hQ 2 (by norm_num) <|
    calc N * D ≤ Q * Q := by gcongr
      _ = Q ^ 2 := by ring
  have hDUU : D * (U * U) ≤ Q ^ 20 := le_pow_twenty hQ 3 (by norm_num) <|
    calc D * (U * U) ≤ Q * (Q * Q) := by gcongr
      _ = Q ^ 3 := by ring
  have hvalue : ((N + 1) ^ 5) ^ 3 * (U * U) ≤ Q ^ 20 := le_pow_twenty hQ 17 (by norm_num) <|
    calc ((N + 1) ^ 5) ^ 3 * (U * U) ≤ (Q ^ 5) ^ 3 * (Q * Q) := by gcongr
      _ = Q ^ 17 := by ring
  have henc : (N + 1) ^ 5 * U ≤ Q ^ 20 := le_pow_twenty hQ 6 (by norm_num) <|
    calc (N + 1) ^ 5 * U ≤ Q ^ 5 * Q := by gcongr
      _ = Q ^ 6 := by ring
  have hpow : (N + 1) ^ 5 ≤ Q ^ 20 := le_pow_twenty hQ 5 (by norm_num) (by gcongr)
  -- 1000 + 100 + 1 + 1 + 1 + 7 + 10 = 1120 ≤ 2^11
  omega

/-- The cells that allInstances26 uses. -/
private theorem cells_le (hN : N + 1 ≤ Q) (hD : D ≤ Q) :
    4 + N + 8 * (N * D) + 222 * ((N + 1) ^ 5) ^ 4 ≤ 2 ^ 11 * Q ^ 20 := by
  have hQ : 1 ≤ Q := by omega
  have hN' : N ≤ Q := by omega
  have h1 : 1 ≤ Q ^ 20 := Nat.one_le_pow _ _ hQ
  have hN1 : N ≤ Q ^ 20 := le_pow_twenty hQ 1 (by norm_num) (by simpa using hN')
  have hND : N * D ≤ Q ^ 20 := le_pow_twenty hQ 2 (by norm_num) <|
    calc N * D ≤ Q * Q := by gcongr
      _ = Q ^ 2 := by ring
  have hblock : ((N + 1) ^ 5) ^ 4 ≤ Q ^ 20 :=
    calc ((N + 1) ^ 5) ^ 4 ≤ (Q ^ 5) ^ 4 := by gcongr
      _ = Q ^ 20 := by ring
  omega

/-- The levels of calls that allInstances26 needs. -/
private theorem depth_le (hQ : 1 ≤ Q) (hD : D ≤ Q) : 84 * D + 12 ≤ 2 ^ 11 * Q ^ 20 := by
  have h1 : 1 ≤ Q ^ 20 := Nat.one_le_pow _ _ hQ
  have hD1 : D ≤ Q ^ 20 := le_pow_twenty hQ 1 (by norm_num) (by simpa using hD)
  omega

end summands

/-- Three of four positive factors are at most the product. -/
private theorem le_prod_four {a b c e : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (he : 0 < e) :
    a ≤ a * (b * (c * e)) ∧ b ≤ a * (b * (c * e)) ∧ e ≤ a * (b * (c * e)) :=
  ⟨Nat.le_mul_of_pos_right a (by positivity),
    (Nat.le_mul_of_pos_right b (by positivity)).trans (Nat.le_mul_of_pos_left _ ha),
    ((Nat.le_mul_of_pos_left e hc).trans (Nat.le_mul_of_pos_left _ hb)).trans
      (Nat.le_mul_of_pos_left _ ha)⟩

/-- The need is polynomial in the parameters. -/
theorem allInstancesNeed26_poly : PolyNeedN allInstancesNeed26 := by
  refine ⟨11, 20, fun ps => ?_⟩
  match ps with
  | [N, D, w, U] =>
    obtain ⟨hN, hD, hU⟩ := le_prod_four N.succ_pos D.succ_pos w.succ_pos U.succ_pos
    rw [show polyBound 11 20 [N, D, w, U] =
      2 ^ 11 * ((N + 1) * ((D + 1) * ((w + 1) * (U + 1)))) ^ 20 by simp [polyBound]]
    generalize (N + 1) * ((D + 1) * ((w + 1) * (U + 1))) = Q at *
    exact ⟨word_le hN (by omega) (by omega), cells_le hN (by omega), depth_le (by omega) (by omega)⟩
  | [] | [_] | [_, _] | [_, _, _] | _ :: _ :: _ :: _ :: _ :: _ =>
    exact ⟨Nat.zero_le _, Nat.zero_le _, Nat.zero_le _⟩

end Light.Sec4
