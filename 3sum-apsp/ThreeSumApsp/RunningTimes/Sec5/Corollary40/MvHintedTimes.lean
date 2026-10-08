/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec5.Corollary40.MvHinted
public import ThreeSumApsp.RunningTimes.Sec5.Corollary40.ColumnTimes
public import ThreeSumApsp.RunningTimes.Sec5.Corollary40.ToMachine

/-!
# Corollary 40, Conjecture 5.7: the running times of Mv-hinted Mv

Proof of Corollary 40: "The proof is the same, with X := N_{[n],I} and Y := V, which are both known
in Phase 2".

The argument is that of v-hinted Mv, for a data structure with given rates
(`achievesMvHinted_of_rates`, from `KitRates.phaseRun_column`).  The one difference is that Phase 2
first writes the matrix N_{[n],I}, which takes O(n t) steps; so the exponent of Phase 2 has to allow
for n t as well.  With the rates of Corollary 26 this gives the statement for τ < 1/18
(`achievesMvHinted_of_lt_eighteenth`), because n t ≤ n^{2−0.063τ}.  With the rates of Corollary 31
it gives the statement for general τ (`achievesMvHinted_of_genParams`), where n t is within the
bound for γ ≤ 1 and τ ≤ 1/2.
-/

@[expose] public section

open ThreeSumApsp

namespace Light.Sec5

open ThreeSumApsp.WordRam ThreeSumApsp.HintedMv Light.Sec4

/-- The three phases, and the routine `col` that Phase 3 calls for a column of the product, as
procedures o to o + 3. -/
def mvProcsAt (o : ℕ) : Program := [mvPhase1Body, mvPhase2Body, mvPhase3Body (o + 3), colBody]

/-- **Mv-hinted Mv over a data structure with given rates.**  Let 0 ≤ τ ≤ 1 and 1 ≤ a₂, a₃.  If at
the sizes N = n and D = t = ⌊n^τ⌋ the preprocessing takes O(n^a₂) steps and n queries take O(n^a₃),
and n t ≤ n^a₂, then Phase 2 takes O(n^a₂) and Phase 3 takes O(n^a₃) time on the word RAM. -/
theorem achievesMvHinted_of_rates {τ a₂ a₃ C : ℝ} {G : RatParams} {A : ℕ} (hC : 0 ≤ C)
    (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) (ha₂ : 1 ≤ a₂) (ha₃ : 1 ≤ a₃) (hrates : ColumnRates τ a₂ a₃ G A C)
    (hcopy : ∀ n : ℕ, 1 ≤ n → (n : ℝ) * (hintSize τ n : ℝ) ≤ (n : ℝ) ^ a₂) :
    AchievesMvHinted τ a₂ a₃ := by
  -- the four procedures are appended to the program of the data structure, from number o on
  obtain ⟨o, ho⟩ : ∃ o, o = (program31 G).length := ⟨_, rfl⟩
  have hp {i : ℕ} {body : Stmt} (h : (mvProcsAt o)[i]? = some body) :
      (program31 G ++ mvProcsAt o)[o + i]? = some body := by
    subst ho
    exact getElem?_append_length_add _ h
  refine achievesMvHinted_of_light (a₁ := 0) (A := C + 100) (program31 G ++ mvProcsAt o) o (o + 1)
    (o + 2) (slopeExp31 G + Nat.size (A + 8) + 1) 40 fun n hn N V I j => ?_
  have ht := one_le_hintSize (τ := τ) hn hτ0
  have htn := hintSize_le (τ := τ) hn hτ1
  have hK := hrates (mvProcsAt o) n hn
  -- the memory ends after the data structure, which lies after the inputs, the output and X
  obtain ⟨hlim, -, hdepth⟩ := hK.lim_at (mvFr n (hintSize τ n))
  obtain ⟨c₁, c₂, c₃, h₁, h₂, h₃, hrun⟩ := mv_lightPhases (kit31 G (mvProcsAt o)) (hp (i := 0) rfl)
    (hp (i := 1) rfl) (hp (i := 2) rfl) (hp (i := 3) rfl) hn ht htn hlim (by omega) (by omega)
    N V I j
  have hnt : n * hintSize τ n ≤ n * n := Nat.mul_le_mul_left _ htn
  have hnn : n ≤ n * n := Nat.le_mul_of_pos_left _ hn
  -- writing X and the rest of Phase 2 take 19 n t + 26 n + 61 steps, where n t ≤ n^a₂ and n ≤ n^a₂
  have hlinear : (n : ℝ) ≤ (n : ℝ) ^ a₂ := by simpa using natCast_rpow_le_rpow hn ha₂
  have hwrite := hcopy n hn
  exact ⟨_, c₁, c₂, c₃, hK.phaseRun_column hC hn htn ha₃ (by unfold mvFr; omega)
    (by unfold mvFr; omega) (w := tMvGather n (hintSize τ n) + 55)
    (by unfold tMvGather; push_cast; linarith) h₁ (by omega) h₃ hrun⟩

/-- **Corollary 40, Conjecture 5.7, 0 < τ < 1/18**: Mv-hinted Mv is solved on the word RAM with
Phase 2 in O(n^{2−0.063τ}) and Phase 3 in O(n^{1+0.437τ}) time. -/
theorem achievesMvHinted_of_lt_eighteenth {τ : ℝ} (h0 : 0 < τ) (h1 : τ < 1 / 18) :
    AchievesMvHinted τ (2 - 0.063 * τ) (1 + 0.437 * τ) := by
  obtain ⟨G, A, C, hC, hrates⟩ := columnRates_of_lt_eighteenth h0 h1
  exact achievesMvHinted_of_rates hC h0.le (by linarith) (by linarith) (by linarith) hrates
    fun n hn => mul_hintSize_le hn h1.le

/-- **Corollary 40, Conjecture 5.7, general τ**: for parameters c, θ, ε, γ as in `GenParams` and
every 0 < τ < ε with τ ≤ 1/2, Mv-hinted Mv is solved on the word RAM with Phase 2 in O(n^{2−γτ}) and
Phase 3 in O(n^{1+τ/2}) time. -/
theorem achievesMvHinted_of_genParams {c θ ε γ τ : ℝ} (p : GenParams c θ ε γ) (h0 : 0 < τ)
    (hτ : τ < ε) (hτ1 : τ ≤ 1 / 2) : AchievesMvHinted τ (2 - γ * τ) (1 + τ / 2) := by
  obtain ⟨G, A, C, hC, hrates⟩ := columnRates_of_genParams p h0 hτ
  have hγτ : γ * τ ≤ τ := mul_le_of_le_one_left h0.le p.γ_le
  refine achievesMvHinted_of_rates hC h0.le (by linarith) (by linarith) (by linarith) hrates
    fun n hn => ?_
  -- n t ≤ n^{1+τ} ≤ n^{2−γτ}
  have hnt := rpow_mul_hintSize_le hn τ 1
  rw [Real.rpow_one] at hnt
  exact hnt.trans (natCast_rpow_le_rpow hn (by linarith))

end Light.Sec5
