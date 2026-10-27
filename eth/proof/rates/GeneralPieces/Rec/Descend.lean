/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import GeneralPieces.Defs
public import ClauseBound.Alg.Descend

/-! # All levels, with every step in order in the sense of case (ii) of Lemma 8

This is the induction on ℓ in the proof of part (b) of the theorem on the general recursion
(Appendix A), for the value that the algorithm returns.
`descendG` starts from the state "sum 0, factor 1, work list [I]" and applies the steps of the
schedule; `solveG` evaluates the instances that are left by brute force, adds the sum and divides
by the factor. If every step of the schedule is in order (`ChainG2`) and the pad (an extra input
whose length bounds the length of every state that the program keeps, see `cap`) is long enough
(`FitsG`), the result is the value of the instance at the top. What one level does
(`StExpandG2`) is a hypothesis. Difference from the paper: the recursion is unrolled into a work
list that passes through the levels from the top down, and the divisions by d^|R| of all
levels are done at once at the end. -/

public section

namespace GeneralPieces.Descend

open Groundwork Groundwork.Prog PaddedDescent.F PaddedDescent.F.Lists ClauseBound.Alg ClauseBound.Alg.Descend

/-! ### All levels -/

/-- The steps of the schedule, applied to any state that is in order: the factor is multiplied by
some q ≥ 1, and the sum plus the results of brute force on the work list at the end is q times
the sum plus the values Z of the work list at the start. -/
theorem descend_state2 (P : PiecesF) (hX : StExpandG2 P) {pad : U} {K₀ : ℕ} : ∀ (sched : List Step) {Kup lam B cnt z : ℕ} (st fin : DState),
    ChainG2 P K₀ Kup lam sched → FitsG P pad.length Kup lam B cnt z sched → st.2.1.length = lam → st.2.2.length ≤ cnt →
    (∀ I ∈ st.2.2, WFe Kup lam B I) → st.1.1.natAbs < 2 ^ z → st.1.2 < 2 ^ z →
    sched.foldl (fun st s => cap pad ((0, 1), [], []) (stepG P pad st s)) st = fin →
    ∃ c : ℕ, 1 ≤ c ∧ fin.1.2 = c * st.1.2 ∧
      fin.1.1 + (fin.2.2.map (bruteF pad K₀)).sum = c * (st.1.1 + (st.2.2.map (zval Kup)).sum)
  | [], Kup, lam, B, cnt, z, st, fin, hC, hF, hl, _, hw, _, _, hfin => by
    have hK : Kup = K₀ := hC
    subst hK
    rw [List.foldl_nil] at hfin
    subst hfin
    refine ⟨1, le_rfl, (one_mul _).symm, ?_⟩
    rw [Nat.cast_one, one_mul]
    refine congrArg (fun l : List ℤ => st.1.1 + l.sum) (List.map_congr_left fun I hI => stBrute pad Kup I ?_)
    rw [(hw I hI).2]
    exact hF.2
  | s :: r, Kup, lam, B, cnt, z, st, fin, hC, hF, hl, hc, hw, hs, hf, hfin => by
    obtain ⟨hK, hL, hC'⟩ := hC
    obtain ⟨-, hB, hF'⟩ := hF
    subst hK
    subst hl
    have hE := fun I (hI : I ∈ st.2.2) => hX pad s st.2.1.length B I hL (hw I hI) hB
    have hD := pow_le_two_pow_size (P.d s.h st.2.1.length) (nRectG s.p s.d)
    have hn : 1 ≤ nPat P s st.2.1.length := Nat.one_le_pow _ _ hL.spec.cnt_pos
    have h1 : (stepG P pad st s).2.1.length = lamNextG P s st.2.1.length := List.length_replicate
    have h2 : (stepG P pad st s).2.2.length ≤ cnt * nPat P s st.2.1.length := by
      refine le_trans ?_ (Nat.mul_le_mul_right _ hc)
      show ((st.2.2.map (expandG P pad s)).flatMap Prod.snd).length ≤ _
      rw [List.flatMap_map]
      exact length_flatMap_le _ _ _ fun I hI => (hE I hI).2.2.1
    have h3 : ∀ J ∈ (stepG P pad st s).2.2, WFe s.K (lamNextG P s st.2.1.length) (bNextG P s st.2.1.length B) J := by
      intro J hJ
      obtain ⟨x, hx, hJ'⟩ := List.mem_flatMap.1 hJ
      obtain ⟨I, hI, rfl⟩ := List.mem_map.1 hx
      exact (hE I hI).2.1 J hJ'
    have h4 : (stepG P pad st s).1.1.natAbs < 2 ^ (z + nRectG s.p s.d * Nat.size (P.d s.h st.2.1.length) +
        Nat.size (cnt * nPat P s st.2.1.length) + Nof s st.2.1.length +
        s.d ^ 2 * (s.p * B + s.p ^ 2 * P.bits s.h st.2.1.length + 1) + 2) := by
      have hb : ((st.2.2.map (expandG P pad s)).map Prod.fst).sum.natAbs ≤ cnt * 2 ^ (Nat.size (nPat P s st.2.1.length) +
          (Nof s st.2.1.length + s.d ^ 2 * (s.p * B + s.p ^ 2 * P.bits s.h st.2.1.length + 1))) := by
        rw [List.map_map]
        refine (natAbs_sum_map_le _ _ _ fun I hI => ?_).trans (Nat.mul_le_mul_right _ hc)
        rw [← Nat.add_assoc]
        exact (hE I hI).2.2.2
      have := sum_lt hs hD hn hb
      rw [← Nat.add_assoc] at this
      exact this
    have h5 : (stepG P pad st s).1.2 < 2 ^ (z + nRectG s.p s.d * Nat.size (P.d s.h st.2.1.length) +
        Nat.size (cnt * nPat P s st.2.1.length) + Nof s st.2.1.length +
        s.d ^ 2 * (s.p * B + s.p ^ 2 * P.bits s.h st.2.1.length + 1) + 2) := by
      have := factor_lt (x := Nat.size (cnt * nPat P s st.2.1.length) + Nof s st.2.1.length +
        s.d ^ 2 * (s.p * B + s.p ^ 2 * P.bits s.h st.2.1.length + 1) + 2) hf hD
      simp only [← Nat.add_assoc] at this
      exact this
    have hfit : len (stepG P pad st s) ≤ pad.length := (len_state_le _ h1 h2 h3 h4 h5).trans (fitsG_head hF')
    rw [List.foldl_cons, cap_eq hfit] at hfin
    obtain ⟨c, hc1, hc2, hc3⟩ := descend_state2 P hX r _ fin hC' hF' h1 h2 h3 h4 h5 hfin
    refine ⟨c * P.d s.h st.2.1.length ^ nRectG s.p s.d, Nat.mul_pos hc1 (Nat.pow_pos hL.spec.d_pos), ?_, ?_⟩
    · rw [hc2]
      show c * (st.1.2 * _) = _
      ring
    · rw [hc3]
      have key := sum_fst_add_sum_snd st.2.2 (expandG P pad s) (zval (s.p * s.d)) (zval s.K)
        ((P.d s.h st.2.1.length : ℤ) ^ nRectG s.p s.d) fun I hI => (hE I hI).1
      show (c : ℤ) * (st.1.1 * ((P.d s.h st.2.1.length ^ nRectG s.p s.d : ℕ) : ℤ) + ((st.2.2.map (expandG P pad s)).map Prod.fst).sum +
        (((st.2.2.map (expandG P pad s)).flatMap Prod.snd).map (zval s.K)).sum) = _
      rw [add_assoc, key]
      push_cast
      ring

/-- `StSolveG2`: all levels, brute force at the bottom and one division compute the sum Z of the
instance at the top. -/
theorem stSolveG2 (P : PiecesF) (hX : StExpandG2 P) : StSolveG2 P := by
  intro pad K₀ sched Kup lam B I hC hF hI
  have hw : ∀ J ∈ [I], WFe Kup lam B J := fun J hJ => by rw [List.mem_singleton.1 hJ]; exact hI
  have hfit : len (((0, 1), I.1, [I]) : DState) ≤ pad.length :=
    (len_state_le _ hI.2 le_rfl hw (by norm_num) (by norm_num)).trans (fitsG_head hF)
  obtain ⟨c, hc1, hc2, hc3⟩ := descend_state2 P hX sched ((0, 1), I.1, [I]) (descendG P pad sched I) hC hF hI.2 le_rfl hw
    (by norm_num) (by norm_num) (by unfold descendG; rw [cap_eq hfit])
  unfold solveG
  rw [hc3, hc2]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, zero_add, mul_one]
  exact Int.mul_ediv_cancel_left _ (by exact_mod_cast (by omega : c ≠ 0))

end GeneralPieces.Descend
