/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import GeneralPieces.Group.Lemma
public import ClauseBound.Alg.Level

/-! # One level, by case (ii) of Lemma 8

This follows the step from ℓ to ℓ+1 in the proof of part (b) of Theorem A (Appendix A), at the
sentence "Case (ii) of Lemma 8 applies to the network with the
smaller total". `cases_ii` checks the hypotheses of case (ii), `Lof_le_lamNext` compares the lemma's
L with the label length of the program, `child_spec2` calls
the lemma (`GeneralPieces.grouping_general`) for one term of the sum over ι, and `stExpandG2` is the
whole level. Differences from the paper: ζ is written 3/(2D) for a natural number D ≥ 2; one label
length serves all ι; the cost appears as lower bounds on the length of the pad, not as a number of
operations. The program also handles steps marked thin, where the column network is summed by
enumeration (`enum_spec2`); no step of the schedule (40) is thin. -/

public section

namespace GeneralPieces.Level

open Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.Level Finset

/-! ### Case (ii) of the lemma applies -/

/-- 0 < ζ ≤ 1 for ζ = 3/(2D), D ≥ 2. -/
theorem zetaOf_mem {s : Step} (hD : 2 ≤ s.D) : 0 < zetaOf s ∧ zetaOf s ≤ 1 := by
  have hDr : (2 : ℝ) ≤ s.D := by exact_mod_cast hD
  unfold zetaOf
  exact ⟨by positivity, by rw [div_le_one (by positivity)]; linarith⟩

/-- "Case (ii) of the lemma applies to the network with the smaller total": K divides g, c_{a,a'} ≤
g²λ = P/g, and 2ζ²g ≥ K·ln(2gK). Here the network has p nodes, each a merged row or column of d
nodes,
its parameter is P = m·p·d²·λ, and two nodes share at most d²·m·λ = P/p bits. -/
theorem cases_ii {P : PiecesF} {s : Step} {lam : ℕ} (hL : LevelOK2 P s lam) (N : Network (Fin s.p) (List Bool) (List Bool))
    (hM : ∀ a b, a ≠ b → N.c a b ≤ s.d ^ 2 * (P.m * lam)) : AppRunningTime.Cases s.K s.p (zetaOf s) (P.m * (s.p * s.d ^ 2 * lam)) N.c := by
  refine Or.inr ⟨hL.dvd, fun a b hab => ?_, hL.hoeffding⟩
  have hp : (0 : ℝ) < s.p := by exact_mod_cast (by have := hL.two_le_p; omega : 0 < s.p)
  rw [le_div_iff₀ hp]
  have h : N.c a b * s.p ≤ P.m * (s.p * s.d ^ 2 * lam) := by
    calc N.c a b * s.p ≤ s.d ^ 2 * (P.m * lam) * s.p := Nat.mul_le_mul_right _ (hM a b hab)
      _ = P.m * (s.p * s.d ^ 2 * lam) := by ring
  exact_mod_cast h

/-- "The number L depends on ι; the bound holds for every ι": the lemma's L = ⌈(U + 2ζgP)/K²⌉ is at
most the label length `lamNextG` that the program uses for all ι, if U is at most the bound
`ubarG` for the smaller total. -/
theorem Lof_le_lamNext {P : PiecesF} {s : Step} {lam : ℕ} (hL : LevelOK2 P s lam) (Uv : ℕ) (hU : Uv ≤ ubarG P s lam) :
    AppRunningTime.Lof s.K s.p (zetaOf s) (P.m * (s.p * s.d ^ 2 * lam)) Uv ≤ lamNextG P s lam := by
  have hD0 : 0 < s.D * s.K ^ 2 := by
    have h1 := hL.D_ge
    have h2 := hL.two_le
    positivity
  have hβ : s.D * Uv + 3 * s.p ^ 2 * (s.d ^ 2 * (P.m * lam)) ≤ s.D * s.K ^ 2 * lamNextG P s lam :=
    (Nat.add_le_add_right (Nat.mul_le_mul_left _ hU) _).trans (le_mul_div_succ _ hD0)
  have hβr : (s.D : ℝ) * Uv + 3 * (s.p : ℝ) ^ 2 * ((s.d : ℝ) ^ 2 * (P.m * lam)) ≤ s.D * (s.K : ℝ) ^ 2 * lamNextG P s lam := by exact_mod_cast hβ
  have hDr : (0 : ℝ) < s.D := by exact_mod_cast (by have := hL.D_ge; omega : 0 < s.D)
  have hKr : (0 : ℝ) < s.K := by exact_mod_cast (by have := hL.two_le; omega : 0 < s.K)
  unfold AppRunningTime.Lof zetaOf
  rw [Nat.ceil_le, div_le_iff₀ (by positivity)]
  push_cast
  have e3 : (s.D : ℝ) * ((Uv : ℝ) + 2 * (3 / (2 * (s.D : ℝ))) * s.p * (P.m * (s.p * (s.d : ℝ) ^ 2 * lam))) =
      s.D * Uv + 3 * (s.p : ℝ) ^ 2 * ((s.d : ℝ) ^ 2 * (P.m * lam)) := by field_simp
  refine le_of_mul_le_mul_left ?_ hDr
  rw [e3]
  linarith

/-! ### A term that is rebalanced -/

/-- One term of the sum over ι (a pattern, numbered y) whose network, on g = p nodes that are merged
rows or columns of e = d nodes, is rebalanced, by case (ii) of Lemma 8: the new instance has the
value of the
network and is well formed. -/
theorem child_spec2 (P : PiecesF) (pad : U) (s : Step) (lam B : ℕ) (I : PInst) (y : ℕ) (hL : LevelOK2 P s lam) (hlam : I.1.length = lam)
    (hb : BudG P pad.length s lam) (hy : y < nPat P s lam) (hc : (s.thin && colSide P s lam y) = false) (g e : ℕ) (hg : g = s.p) (he : e = s.d)
    (N : Network (Fin g) (List Bool) (List Bool))
    (hN : (gridF P).toP.Presents (gctx pad s (!s.thin && colSide P s lam y) I y) N 0 0)
    (hS : N.Sized (P.m * (g * e ^ 2 * lam)) (e * B + e ^ 2 * P.bits s.h lam))
    (hU : N.U = totalG P s.p s.d (!s.thin && colSide P s lam y) s.h lam y)
    (hM : ∀ a b, a ≠ b → N.c a b ≤ e ^ 2 * (P.m * lam)) :
    ∃ J, childG P pad s I y = some J ∧ zval s.K J = N.value ∧ WFe s.K (lamNextG P s lam) (bNextG P s lam B) J := by
  subst hg he
  obtain ⟨J, h1, h2, h3⟩ := grouping_general _ (gridF P) _ s.K s.p (zetaOf s) N _ _ (lamNextG P s lam) pad hL.two_le hL.two_le_p (zetaOf_mem hL.D_ge).1
    (zetaOf_mem hL.D_ge).2 hN hS (cases_ii hL N hM) (Lof_le_lamNext hL N.U (hU ▸ hL.ubar y hy hc)) (Nat.le_add_left 1 _) hb.col hb.st hb.lab hb.tab
  refine ⟨J, ?_, h2, wfe_mono h3 (min_le_right _ _)⟩
  unfold childG
  rw [hlam]
  exact h1

/-! ### A term that is evaluated at once -/

/-- One term of the sum over ι (a pattern, numbered y) whose column network is evaluated by
enumeration: the result is the value of the network, and it is small. -/
theorem enum_spec2 (hE : StEnum) (P : PiecesF) (pad : U) (s : Step) (lam B : ℕ) (I : PInst) (y : ℕ) (hL : LevelOK2 P s lam) (hlam : I.1.length = lam)
    (hb : BudG P pad.length s lam) (hy : y < nPat P s lam) (hc : (s.thin && colSide P s lam y) = true)
    (N : Network (Fin s.d) (List Bool) (List Bool)) (hN : (gridF P).toP.Presents (gctx pad s true I y) N 0 0)
    (hS : N.Sized (P.m * (s.d * s.p ^ 2 * lam)) (s.p * B + s.p ^ 2 * P.bits s.h lam))
    (hU : N.U = totalG P s.p s.d true s.h lam y) :
    enumF pad s.d (gridF P) (gctx pad s true I y) = N.value ∧ |N.value| ≤ 2 ^ (Nof s lam + s.d ^ 2 * (s.p * B + s.p ^ 2 * P.bits s.h lam)) := by
  have ht : s.thin = true := by
    cases h : s.thin with
    | false => rw [h] at hc; simp at hc
    | true => rfl
  have hn : ∀ a, (gridF P).n (gctx pad s true I y) a = s.p ^ 2 * s.d * lam := by
    intro a
    change nMemb s.p s.d true * (s.p * s.d) * I.1.length = _
    rw [hlam, nMemb, if_pos rfl]
    ring
  have hst : ∀ a < s.d, 2 ^ (gridF P).n (gctx pad s true I y) a ≤ pad.length := fun a _ => by rw [hn]; exact hb.enumSt ht
  -- the number of label bits, read off with a pad that is long enough for everything
  have hbits : 2 * enumBits s.d (gridF P) (gctx pad s true I y) = N.U :=
    (hE _ (List.replicate (2 ^ enumBits s.d (gridF P) (gctx pad s true I y) + 2 ^ (s.p ^ 2 * s.d * lam)) ()) s.d (gridF P) _ N hN
      (by rw [List.length_replicate]; exact Nat.le_add_right _ _) (fun a _ => by rw [hn, List.length_replicate]; exact Nat.le_add_left _ _)).2
  have hle : enumBits s.d (gridF P) (gctx pad s true I y) ≤ ebarG s lam := by
    have := hL.ebar y hy hc
    omega
  refine ⟨(hE _ pad s.d (gridF P) _ N hN ((Nat.pow_le_pow_right (by norm_num) hle).trans (hb.enumLab ht)) hst).1, ?_⟩
  have h1 := abs_value_le N (n := s.p ^ 2 * s.d * lam) hS fun a => by
    rw [hN.S_eq a, card_words]
    exact (Nat.pow_le_pow_right (by norm_num) (hn a).le)
  rw [Fintype.card_fin] at h1
  refine h1.trans (le_of_eq ?_)
  congr 1
  unfold Nof
  ring

/-! ### The level -/

/-- One level: the factor d^|R| times Z is the sum of the terms evaluated at once and of the values
of the new instances; these are well formed; there are few; the sum is small. -/
theorem stExpandG2 (P : PiecesF) (hG : StGrid P) (hE : StEnum) : StExpandG2 P := by
  intro pad s lam B I hL hI hb
  obtain ⟨hW, hlam⟩ := hI
  subst hlam
  obtain ⟨Zt, hZ, hT⟩ := hG pad s.1.2.1 s.1.2.2 s.2.1.2 I.1 I.2 B hW.lam_pos hL.spec hb.pieces (Table.stT3c _ _ _ _ hW)
  change (P.d s.h I.1.length : ℤ) ^ nRectG s.p s.d * zval (s.p * s.d) I = ∑ y ∈ range (nPat P s I.1.length), Zt y at hZ
  change ∀ y < nPat P s I.1.length, ∀ tr : Bool, ∃ N : Network (Fin (nParts s.p s.d tr)) (List Bool) (List Bool),
    (gridF P).toP.Presents (gctx pad s tr I y) N 0 0 ∧ N.value = Zt y ∧
    N.Sized (P.m * (nParts s.p s.d tr * nMemb s.p s.d tr ^ 2 * I.1.length)) (nMemb s.p s.d tr * B + nMemb s.p s.d tr ^ 2 * P.bits s.h I.1.length) ∧
    N.U = totalG P s.p s.d tr s.h I.1.length y ∧ ∀ a b, a ≠ b → N.c a b ≤ nMemb s.p s.d tr ^ 2 * (P.m * I.1.length) at hT
  have hen : ∀ y < nPat P s I.1.length, (s.thin && colSide P s I.1.length y) = true →
      enumF pad s.d (gridF P) (gctx pad s true I y) = Zt y ∧
        |Zt y| ≤ 2 ^ (Nof s I.1.length + s.d ^ 2 * (s.p * B + s.p ^ 2 * P.bits s.h I.1.length)) := by
    intro y hy hc
    obtain ⟨N, h1, h2, h3, h4, _⟩ := hT y hy true
    rw [← h2]
    exact enum_spec2 hE P pad s I.1.length B I y hL rfl hb hy hc N h1 h3 h4
  have hch : ∀ y < nPat P s I.1.length, (s.thin && colSide P s I.1.length y) = false →
      ∃ J, childG P pad s I y = some J ∧ zval s.K J = Zt y ∧ WFe s.K (lamNextG P s I.1.length) (bNextG P s I.1.length B) J := by
    intro y hy hc
    obtain ⟨N, h1, h2, h3, h4, h5⟩ := hT y hy (!s.thin && colSide P s I.1.length y)
    rw [← h2]
    obtain ⟨e1, e2⟩ := parts_eq s hL.square (colSide P s I.1.length y)
    exact child_spec2 P pad s I.1.length B I y hL rfl hb hy hc _ _ e1 e2 N h1 h3 h4 h5
  obtain ⟨f1, f2, f3⟩ := filterMap_spec
    (f := fun y => if (s.thin && colSide P s I.1.length y) = true then none else childG P pad s I y) (z := zval s.K)
    (v := fun y => if (s.thin && colSide P s I.1.length y) = true then 0 else Zt y)
    (Q := WFe s.K (lamNextG P s I.1.length) (bNextG P s I.1.length B)) (List.range (nPat P s I.1.length)) fun y hy => by
      cases hc : (s.thin && colSide P s I.1.length y) with
      | true => exact Or.inl ⟨by simp, by simp⟩
      | false => exact Or.inr (by simpa using hch y (List.mem_range.1 hy) hc)
  unfold expandG
  simp only
  rw [rng_eq hb.pat, sumF_eq hb.pat]
  refine ⟨?_, f2, by rwa [List.length_range] at f3, ?_⟩
  · rw [f1, sum_map_range, hZ, ← sum_add_distrib]
    refine sum_congr rfl fun y hy => ?_
    split_ifs with hc
    · rw [(hen y (mem_range.1 hy) hc).1, add_zero]
    · rw [zero_add]
  · have key : |∑ y ∈ range (nPat P s I.1.length),
        if (s.thin && colSide P s I.1.length y) = true then enumF pad s.d (gridF P) (gctx pad s true I y) else 0| ≤
        (2 : ℤ) ^ (Nat.size (nPat P s I.1.length) + Nof s I.1.length + s.d ^ 2 * (s.p * B + s.p ^ 2 * P.bits s.h I.1.length + 1)) := by
      calc _ ≤ ∑ y ∈ range (nPat P s I.1.length),
            |if (s.thin && colSide P s I.1.length y) = true then enumF pad s.d (gridF P) (gctx pad s true I y) else 0| :=
            abs_sum_le_sum_abs _ _
        _ ≤ ∑ _y ∈ range (nPat P s I.1.length), (2 : ℤ) ^ (Nof s I.1.length + s.d ^ 2 * (s.p * B + s.p ^ 2 * P.bits s.h I.1.length)) := by
            refine sum_le_sum fun y hy => ?_
            split_ifs with hc
            · rw [(hen y (mem_range.1 hy) hc).1]; exact (hen y (mem_range.1 hy) hc).2
            · rw [abs_zero]; positivity
        _ = (nPat P s I.1.length : ℤ) * 2 ^ (Nof s I.1.length + s.d ^ 2 * (s.p * B + s.p ^ 2 * P.bits s.h I.1.length)) := by
            rw [sum_const, card_range, nsmul_eq_mul]
        _ ≤ 2 ^ Nat.size (nPat P s I.1.length) * 2 ^ (Nof s I.1.length + s.d ^ 2 * (s.p * B + s.p ^ 2 * P.bits s.h I.1.length)) :=
            mul_le_mul_of_nonneg_right (by exact_mod_cast (Nat.lt_size_self _).le) (by positivity)
        _ = 2 ^ (Nat.size (nPat P s I.1.length) + (Nof s I.1.length + s.d ^ 2 * (s.p * B + s.p ^ 2 * P.bits s.h I.1.length))) := (pow_add _ _ _).symm
        _ ≤ _ := pow_le_pow_right₀ (by norm_num) (by
            have := Nat.mul_le_mul_left (s.d ^ 2) (Nat.le_add_right (s.p * B + s.p ^ 2 * P.bits s.h I.1.length) 1)
            omega)
    rw [Int.abs_eq_natAbs] at key
    exact_mod_cast key

end GeneralPieces.Level
