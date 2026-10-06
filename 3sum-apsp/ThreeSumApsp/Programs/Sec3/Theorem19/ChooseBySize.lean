/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Lang.PolyBounded
public import ThreeSumApsp.Lang.Renumber
public import ThreeSumApsp.Programs.LightModel

/-!
# Two algorithms for Exact Triangle and a threshold on the number of vertices

For every threshold n₀ there is a constant C₀ such that, if Exact Triangle is solved in time T₁ and
in time T₂, then it is solved in time T₁ + C₀ for n < n₀ and T₂ + C₀ for n ≥ n₀.  This is
`Closure.ChooseBySize`, with "Exact Triangle is solved in time T" read as `SolvedIn etTask T`
(`closure_chooseBySize`).  It is used in the proof of Theorem 19, where the bounds hold
for large n only.

Two solvers are put into one program, the second behind the first (`solves_behind`), and one more
procedure looks at the number of vertices and calls the first solver below a fixed threshold n₀ and
the second one from the threshold on (`bySize_spec`).  The need stays polynomial
(`polyNeed_bySize`).
-/

@[expose] public section

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec

variable {lim : Limits} {d : ℕ}

/-- choose(n, U, ab, bc, ac, fr): calls procedure p₁ if n < n₀, and procedure p₂ if not, on the same
arguments: the number n of vertices in a part, the bound U on the weights, the addresses ab, bc, ac
of the three matrices of weights, and the free pointer fr. -/
def bySizeBody (n₀ p₁ p₂ : ℕ) : Stmt :=
  .ite (v 0 <' k n₀) (.call p₁ [v 0, v 1, v 2, v 3, v 4, v 5] 0)
    (.call p₂ [v 0, v 1, v 2, v 3, v 4, v 5] 0)

/-- The number of steps of choose. -/
def bySizeTime (n₀ : ℕ) (T₁ T₂ : ℕ → ℕ → ℕ) (n U : ℕ) : ℕ := (if n < n₀ then T₁ n U else T₂ n U) +
    12

/-- What choose needs: a word for the threshold, one more level of calls, and what the two solvers
need. -/
def bySizeNeed (n₀ : ℕ) (r₁ r₂ : ℕ → ℕ → Need) (n U : ℕ) : Need :=
  ⟨n₀ + (r₁ n U).word + (r₂ n U).word, (r₁ n U).cells + (r₂ n U).cells, 1 + (r₁ n U).depth +
    (r₂ n U).depth⟩

namespace ChooseHost

/-- A solver stays a solver, with its number shifted, when its program is placed behind another
program. -/
theorem solves_behind {task : Task} {P : Program} {p : ℕ} {T : ℕ → ℕ → ℕ} {need : ℕ → ℕ → Need}
    (h : Solves task P p T need)
    (Q : Program) : Solves task (Program.behind Q P) (p + Q.length) T need := by
  obtain ⟨body, hp, hb⟩ := h
  refine ⟨body.shift Q.length, Program.getElem?_behind_right Q hp, fun R lim d x μ fr hpre hok =>
    ?_⟩
  have := hb [] lim d x μ fr hpre hok
  rw [List.append_nil] at this
  exact this.shift_append Q R

/-- **choose** solves Exact Triangle. -/
theorem bySize_spec {P₀ R : Program} {n₀ p₁ p₂ : ℕ} {T₁ T₂ : ℕ → ℕ → ℕ} {r₁ r₂ : ℕ → ℕ → Need}
    (h₁ : Solves etTask P₀ p₁ T₁ r₁) (h₂ : Solves etTask P₀ p₂ T₂ r₂) {x : TriInst} {μ : ℕ → ℤ}
    {fr : ℕ} (hpre : x.Pre μ fr) (hok : (bySizeNeed n₀ r₁ r₂ x.n x.U).Ok lim fr d) :
    Ends lim (P₀ ++ R) d (bySizeBody n₀ p₁ p₂) ⟨frame (etTask.args x ++ [(fr : ℤ)]), μ⟩
      (bySizeTime n₀ T₁ T₂ x.n x.U) fun σ' => etTask.Post x μ fr (σ'.loc 0) σ'.mem := by
  have hword : ((n₀ + (r₁ x.n x.U).word + (r₂ x.n x.U).word : ℕ) : ℤ) ≤ lim.word := hok.word
  have hdep : d + (1 + (r₁ x.n x.U).depth + (r₂ x.n x.U).depth) ≤ lim.depth := hok.depth
  have hok₁ : (r₁ x.n x.U).Ok lim fr (d + 1) := hok.mono (by simp only [bySizeNeed]; omega)
    (by simp only [bySizeNeed]; omega) (by simp only [bySizeNeed]; omega)
  have hok₂ : (r₂ x.n x.U).Ok lim fr (d + 1) := hok.mono (by simp only [bySizeNeed]; omega)
    (by simp only [bySizeNeed]; omega) (by simp only [bySizeNeed]; omega)
  have hm₁ : Meets lim (P₀ ++ R) p₁ (d + 1) [x.n, x.U, x.ab, x.bc, x.ac, fr] μ (T₁ x.n x.U)
      (etTask.Post x μ fr) := h₁.meets R x fr hpre hok₁
  have hm₂ : Meets lim (P₀ ++ R) p₂ (d + 1) [x.n, x.U, x.ab, x.bc, x.ac, fr] μ (T₂ x.n x.U)
      (etTask.Post x μ fr) := h₂.meets R x fr hpre hok₂
  change Ends lim (P₀ ++ R) d (bySizeBody n₀ p₁ p₂) ⟨frame [x.n, x.U, x.ab, x.bc, x.ac, fr], μ⟩ _ _
  unfold bySizeTime
  -- if n < n₀ then the first solver else the second
  refine Ends.iteLast (fun hc => ?_) (fun hc => ?_)
  · rw [if_pos (show x.n < n₀ by simp at hc; omega)]
    exact Ends.callTo hm₁ fun _ _ h => h
  · rw [if_neg (show ¬ x.n < n₀ by simp at hc; omega)]
    exact Ends.callTo hm₂ fun _ _ h => h

/-- The need of choose is polynomially bounded if the needs of the two solvers are. -/
theorem polyNeed_bySize (n₀ : ℕ) {r₁ r₂ : ℕ → ℕ → Need} (h₁ : PolyNeed r₁) (h₂ : PolyNeed r₂) :
    PolyNeed (bySizeNeed n₀ r₁ r₂) := by
  unfold bySizeNeed
  poly_need [h₁.word, h₁.cells, h₁.depth, h₂.word, h₂.cells, h₂.depth]

end ChooseHost

open ChooseHost

/-- **Two algorithms, chosen by the size of the instance.** -/
theorem closure_chooseBySize : Closure.ChooseBySize lightModel := by
  refine fun n₀ => ⟨12, fun T₁ T₂ hT₁ hT₂ => ?_⟩
  obtain ⟨Q₁, p₁, Tn₁, r₁, hr₁, hs₁, ht₁⟩ := hT₁
  obtain ⟨Q₂, p₂, Tn₂, r₂, hr₂, hs₂, ht₂⟩ := hT₂
  have g₁ : Solves etTask (Program.behind Q₁ Q₂) p₁ Tn₁ r₁ := hs₁.append _
  have g₂ : Solves etTask (Program.behind Q₁ Q₂) (p₂ + Q₁.length) Tn₂ r₂ := solves_behind hs₂ Q₁
  refine ⟨Program.behind Q₁ Q₂ ++ [bySizeBody n₀ p₁ (p₂ + Q₁.length)],
    (Program.behind Q₁ Q₂).length, bySizeTime n₀ Tn₁ Tn₂,
    bySizeNeed n₀ r₁ r₂, polyNeed_bySize n₀ hr₁ hr₂, ?_, fun n U u hn hU hu => ?_⟩
  · refine ⟨bySizeBody n₀ p₁ (p₂ + Q₁.length), by simp, fun R lim d x μ fr hpre hok => ?_⟩
    rw [List.append_assoc]
    exact bySize_spec g₁ g₂ hpre hok
  · simp only [bySizeTime]
    push_cast
    split_ifs
    · linarith [ht₁ n U u hn hU hu]
    · linarith [ht₂ n U u hn hU hu]

end Light.Sec3
