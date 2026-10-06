/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec4.ChoosingParameters.Costs
public import ThreeSumApsp.Programs.Sec4.ChoosingParameters.OfflineLayout
public import ThreeSumApsp.Programs.Sec4.Theorem30.OfflineStatement

/-!
# Section 4.4, the offline form as a light program

Sections 4.1 and 4.4. The routine offline32 preprocesses the two matrices and then asks one query
for each wanted position. Its parameters c = a/b, θ = p/q and the threshold m₀ are part of the
program text (`RatParams`). This file passes from the specification of the routine to a statement
about the light program on the input of the problem (`programSolves_of_costsWithin`), with the
regime and the two bounds as parameters: for a set `dom` of instances and functions `Tp`, `Tq` such
that on `dom` the two cost expressions of Theorem 30 are at most `C Tp` and `C Tq`, the wanted
entries are computed in time `O(Tp + |W| Tq)`. The offline statements of Section 4 (Corollaries 26
and 32, Theorem 25) are instances; the compiler takes the statement to the word RAM in
`solves_of_costsWithin`.
-/

public section

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.Spec ThreeSumApsp.WordRam

/-- **The offline form as a light program**: on the regime the wanted entries are computed in time
O(Tp + |W| Tq). -/
theorem programSolves_of_costsWithin {P : Program} {c0 : ℕ} (G : RatParams) {C : ℝ} (hC : 0 ≤ C)
    (e : ℕ) (dom : ThinInstance → Prop) (Tp Tq : ThinInstance → ℝ)
    (hdom : ∀ x, dom x → x.U = x.N ^ e ∧ CostsWithin G C x.N x.D (Tp x) (Tq x))
    (hmain : P[Proc.offlineMain32]? = some offlineMain32Body)
    (htask : ∀ lim, OfflineSpec32 lim P c0 G) :
    ∃ (A : ℝ) (s k : ℕ), ProgramSolves (thinProduct []) P Proc.offlineMain32 false s k dom
      (fun x => A * (Tp x + (x.W.length : ℝ) * Tq x)) := by
  obtain ⟨A, hA⟩ := exists_tOffline32_le G hC c0 70
  refine ⟨A, slopeExp31 G, 20 + 2 * e, fun x hx => ?_⟩
  obtain ⟨hU, hc⟩ := hdom x hx
  have hN1 := hc.one_le_N
  have hD := hc.one_le_D
  -- the limits
  obtain ⟨fr, hfr⟩ : ∃ fr, fr = offlineFree x.N x.D x.W.length := ⟨_, rfl⟩
  have hfre : fr = 3 + 2 * (x.N * x.D) + 3 * x.W.length := hfr
  have hlim := lim31_ok G x.N x.D fr e
  obtain ⟨hdepth, hNe⟩ := lim31_facts G x.N x.D fr e
  have hfr3 := add_three_le_structEnd G x.N x.D fr
  have hword : ∀ z : ℕ, z ≤ fr → (z : ℤ) ≤ (lim31 G x.N x.D fr e).word :=
    fun _ hz => lim31_natCast_le G x.N x.D fr e hz
  have hNfr : x.N ≤ fr := by have := Nat.le_mul_of_pos_right x.N hD; omega
  have hDfr : x.D ≤ fr := by have := Nat.le_mul_of_pos_left x.D hN1; omega
  have hUe : (x.U : ℤ) = (x.N : ℤ) ^ e := by rw [hU]; push_cast; rfl
  -- the run of the program
  obtain ⟨σ', n, hexec, hn, -, hanswers⟩ := (offlineMain32_meets hmain (htask _) x hD hN1
    (fun i j => hUe ▸ x.boundX i j) (fun i j => hUe ▸ x.boundY i j) (hfr ▸ hlim) hdepth
    (offlineLayout32_input x)).main (by omega)
      (le_trans (by push_cast; linarith) (hA x.W.length hc))
  refine ⟨_, σ', n, hexec, hn,
    abs_thinInstance_input_le (hword _ hNfr) (hword _ hDfr) (hword _ (by omega)) (hUe ▸ hNe)
      (by simp),
    small_lim31 e hD hc.D_le_N (hfr ▸ blockAt_le hD hc.D_le_N (length_le_sq x.nodup)) hc.hyp,
    rfl, fun i hi => ?_⟩
  have hcell := hanswers i (by simpa using hi)
  rw [List.getElem_map] at hcell
  exact (congrArg (fun a => σ'.mem (a + i))
    ((length_thinInstance_input x []).trans rfl)).trans hcell

end Light.Sec4
