/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec5.Corollary40.VHinted
public import ThreeSumApsp.RunningTimes.Sec5.Corollary40.ColumnTimes
public import ThreeSumApsp.RunningTimes.Sec5.Corollary40.ToMachine

/-!
# Corollary 40, Conjecture 5.2: the running times of v-hinted Mv

Proof of Corollary 40: "In Phase 2, we preprocess X := M and Y := V by Corollary 26, in
O(n²/D^0.063) = O(n^{2−0.063τ}) time.  In Phase 3, the n entries of column i of MV are n queries,
which take O(n D^0.437) = O(n^{1+0.437τ}) time."  Proof of Corollary 40, "General τ": "the arguments
above go through with Phase 2 in O(n²/D^γ) = O(n^{2−γτ}) time and Phase 3 in O(n D^{1/2}) =
O(n^{1+τ/2}) time".

The argument is made once, for a data structure with given rates (`achievesVHinted_of_rates`): the
phase procedures are appended to the program of the data structure, Phase 2 takes the time of the
preprocessing and Phase 3 the time of n queries, each up to O(n) more steps
(`KitRates.phaseRun_column`).  With the rates of Corollary 26 it gives the statement for τ < 1/18
(`achievesVHinted_of_lt_eighteenth`), with the rates of Corollary 31 the statement for general τ
(`achievesVHinted_of_genParams`).
-/

@[expose] public section

open ThreeSumApsp

namespace Light.Sec5

open ThreeSumApsp.WordRam ThreeSumApsp.HintedMv Light.Sec4

/-- The three phases, and the routine `col` that Phase 3 calls for a column of the product, as
procedures o to o + 3. -/
def vProcsAt (o : ℕ) : Program := [vPhase1Body, vPhase2Body, vPhase3Body (o + 3), colBody]

/-- **v-hinted Mv over a data structure with given rates.**  Let 0 ≤ τ ≤ 1 and 1 ≤ a₃.  If at the
sizes N = n and D = t = ⌊n^τ⌋ the preprocessing takes O(n^a₂) steps and n queries take O(n^a₃), then
Phase 2 takes O(n^a₂) and Phase 3 takes O(n^a₃) time on the word RAM. -/
theorem achievesVHinted_of_rates {τ a₂ a₃ C : ℝ} {G : RatParams} {A : ℕ} (hC : 0 ≤ C)
    (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) (ha₃ : 1 ≤ a₃) (hrates : ColumnRates τ a₂ a₃ G A C) :
    AchievesVHinted τ a₂ a₃ := by
  -- the four procedures are appended to the program of the data structure, from number o on
  obtain ⟨o, ho⟩ : ∃ o, o = (program31 G).length := ⟨_, rfl⟩
  have hp {i : ℕ} {body : Stmt} (h : (vProcsAt o)[i]? = some body) :
      (program31 G ++ vProcsAt o)[o + i]? = some body := by
    subst ho
    exact getElem?_append_length_add _ h
  refine achievesVHinted_of_light (a₁ := 0) (A := C + 100) (program31 G ++ vProcsAt o) o (o + 1)
    (o + 2) (slopeExp31 G + Nat.size (A + 8) + 1) 40 fun n hn M V i => ?_
  have ht := one_le_hintSize (τ := τ) hn hτ0
  have htn := hintSize_le (τ := τ) hn hτ1
  have hK := hrates (vProcsAt o) n hn
  -- the memory ends after the data structure, which lies after the inputs and the output
  obtain ⟨hlim, -, hdepth⟩ := hK.lim_at (vFr n (hintSize τ n))
  obtain ⟨c₁, c₂, c₃, h₁, h₂, h₃, hrun⟩ := v_lightPhases (kit31 G (vProcsAt o)) (hp (i := 0) rfl)
    (hp (i := 1) rfl) (hp (i := 2) rfl) (hp (i := 3) rfl) hn ht hlim (by omega) (by omega) M V i
  have hnt : n * hintSize τ n ≤ n * n := Nat.mul_le_mul_left _ htn
  have hnn : n ≤ n * n := Nat.le_mul_of_pos_left _ hn
  have hpow : (0 : ℝ) ≤ (n : ℝ) ^ a₂ := by positivity
  exact ⟨_, c₁, c₂, c₃, hK.phaseRun_column hC hn htn ha₃ (by unfold vFr; omega)
    (by unfold vFr; omega) (w := 40) (by push_cast; linarith) h₁ h₂ (by omega) hrun⟩

/-- **Corollary 40, Conjecture 5.2, 0 < τ < 1/18**: v-hinted Mv is solved on the word RAM with
Phase 2 in O(n^{2−0.063τ}) and Phase 3 in O(n^{1+0.437τ}) time. -/
theorem achievesVHinted_of_lt_eighteenth {τ : ℝ} (h0 : 0 < τ) (h1 : τ < 1 / 18) :
    AchievesVHinted τ (2 - 0.063 * τ) (1 + 0.437 * τ) := by
  obtain ⟨G, A, C, hC, hrates⟩ := columnRates_of_lt_eighteenth h0 h1
  exact achievesVHinted_of_rates hC h0.le (by linarith) (by linarith) hrates

/-- **Corollary 40, Conjecture 5.2, general τ**: for parameters c, θ, ε, γ as in `GenParams` and
every 0 < τ < ε, v-hinted Mv is solved on the word RAM with Phase 2 in O(n^{2−γτ}) and Phase 3 in
O(n^{1+τ/2}) time. -/
theorem achievesVHinted_of_genParams {c θ ε γ τ : ℝ} (p : GenParams c θ ε γ) (h0 : 0 < τ)
    (hτ : τ < ε) : AchievesVHinted τ (2 - γ * τ) (1 + τ / 2) := by
  obtain ⟨G, A, C, hC, hrates⟩ := columnRates_of_genParams p h0 hτ
  exact achievesVHinted_of_rates hC h0.le
    (by linarith [p.ε_lt_epsStar, sec4_epsStar_numeric.2]) (by linarith) hrates

end Light.Sec5
