/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ClauseBound.ParityChecks.ProgDefs
public import ClauseBound.ParityChecks.Run
import ClauseBound.ParityChecks.RunF
import all PaddedDescent.F.Eval

/-! # The count for one sparse formula is right

`stCountOL : StCountOL`, from the interface statements on one evaluation (`StEvW`), on the form of
the layers of a state (`StShape`) and on the three sums over marks (`StBridgeB`, `StBridgeA`,
`StBridgeF`), and from `ParityChecks.ChoiceByPotential`, on choosing the checks clause by clause by
a potential (Step 2 of Appendix D uses Lemma 13 instead), through the theorem on the run of the
choice of the checks (`run_ok`).
1. No cut-off of the program is active, so the program's checks are those of the run with the two
   functions `orcA`, `orcB` (`RunF.runF_eq`).
2. The two functions are right modulo 2^β in every state that satisfies the bounds for states that
   are tried (`orcOK`): by `StShape` and `StEvW` the evaluation is the sum `truncW`, which is `sumA`
   or
   `sumB` for the list of checks filled up with empty checks to the length r; by `StBridgeA`,
   `StBridgeB` that sum is, modulo 2^(β+r), 2^r times the value that `orcA`, respectively `orcB` at
   a number i' ≤ i₀, must have; the division by 2^r gives this value modulo 2^β.
3. So the checks of the run are good and satisfy the bounds (`run_ok`). If m ≤ nb there are no
   checks, and the empty list of checks is good because no assignment violates more than nb clauses.
4. The last evaluation is `sumF3`, which is 2^r times the number of satisfying assignments modulo
   2^(β+r) (`StBridgeF`); that number is at most 2^n and β ≥ n + 2. -/

public section

namespace ClauseBound.ParityChecks.Count

open Finset Groundwork Groundwork.Prog PaddedDescent.F PaddedDescent.F.Mark PaddedDescent.F.Eval ClauseBound.Alg ClauseBound.TopN ClauseBound.TopN.EvalW _root_.ParityChecks

/-- The parameters (m, nb, r, i₀, β) with m the number of clauses of ψ. -/
abbrev mkQ (ψ : Fml) (nb r i₀ β : ℕ) : Par := ⟨ψ.length, nb, r, i₀, β⟩

/-! ### Lists of checks -/

/-- Empty checks at the end do not change the entries of a list of checks. -/
theorem getD_pad (Lam : List Chk) (t j : ℕ) : (Lam ++ List.replicate t []).getD j [] = Lam.getD j [] := by
  rcases Nat.lt_or_ge j Lam.length with h | h
  · rw [List.getD_append _ _ _ _ h]
  · rw [List.getD_append_right _ _ _ _ h, List.getD_eq_default Lam _ h]
    rcases Nat.lt_or_ge (j - Lam.length) t with h' | h'
    · rw [List.getD_eq_getElem _ _ (by rw [List.length_replicate]; exact h'), List.getElem_replicate]
    · rw [List.getD_eq_default _ _ (by rw [List.length_replicate]; exact h')]

/-- Empty checks at the end do not change the checks as sets. -/
theorem Lof_pad (ψ : Fml) (Lam : List Chk) (t : ℕ) : Lof ψ (Lam ++ List.replicate t []) = lam ψ.length Lam := by
  funext j
  unfold Lof lam
  rw [getD_pad]

/-- Empty checks at the end do not change the incidences. -/
theorem incL_pad (n : ℕ) (ψ : Fml) (Lam : List Chk) (t j : ℕ) : incL n ψ (Lam ++ List.replicate t []) j = incL n ψ Lam j := by
  unfold incL
  simp only [getD_pad]

/-- A list of at most r checks, filled up with empty checks, is a list of r checks. -/
theorem wfC_pad {ψ : Fml} {r : ℕ} {Lam : List Chk} (hl : Lam.length ≤ r) (h : ∀ L ∈ Lam, ChkOK ψ.length L) :
    WfC ψ r (Lam ++ List.replicate (r - Lam.length) []) := by
  refine ⟨by rw [List.length_append, List.length_replicate]; omega, fun L hL => ?_⟩
  rcases List.mem_append.1 hL with h1 | h1
  · exact h L h1
  · rw [List.eq_of_mem_replicate h1]
    exact ⟨List.nodup_nil, fun e he => absurd he List.not_mem_nil⟩

/-- Without the current check every check is a subset of what it was. -/
theorem lam_subset (m : ℕ) (Ls : List Chk) (cur : Chk) (j : ℕ) : lam m Ls j ⊆ lam m (Ls ++ [cur]) j := by
  unfold lam
  by_cases hj : j = Ls.length
  · rw [hj, List.getD_eq_default Ls _ le_rfl]
    intro x hx
    simp at hx
  · rw [Run.getD_append_ne _ _ hj]

/-- The bounds for states that are tried pass to smaller checks. -/
theorem tent_mono {q : Par} {Λ Λ' : ℕ → Finset (Fin q.m)} (h : ∀ j, Λ' j ⊆ Λ j) (hT : Tent q Λ) : Tent q Λ' where
  inc := by
    refine lt_of_le_of_lt ?_ hT.inc
    exact_mod_cast Finset.sum_le_sum fun j _ => Finset.card_le_card (h j)
  row j' hj' := lt_of_le_of_lt (pow_le_pow_right₀ (by norm_num) (Finset.card_le_card (h j'))) (hT.row j' hj')
  col x := by
    refine lt_of_le_of_lt (pow_le_pow_right₀ (by norm_num) (Finset.card_le_card ?_)) (hT.col x)
    intro j' hj'
    rw [Finset.mem_filter] at hj' ⊢
    exact ⟨hj'.1, h j' hj'.2⟩

/-- Two numbers that are at most c, as a list. -/
theorem getD2 {a b c : ℕ} (ha : a ≤ c) (hb : b ≤ c) : ∀ l < 2, [a, b].getD l 0 ≤ c := by
  intro l hl
  interval_cases l
  · exact ha
  · exact hb

/-- Three numbers that are at most c, as a list. -/
theorem getD3 {a b d c : ℕ} (ha : a ≤ c) (hb : b ≤ c) (hd : d ≤ c) : ∀ l < 3, [a, b, d].getD l 0 ≤ c := by
  intro l hl
  interval_cases l
  · exact ha
  · exact hb
  · exact hd

/-! ### Residues -/

/-- If a ≡ 2^r·N modulo 2^(β−1+r+1), β ≥ n + 2 and 0 ≤ N ≤ 2^n, then N is the remainder of a/2^r
modulo 2^(n+1). -/
theorem toNat_eq {a : ℤ} {N n r β : ℕ} (h : a ≡ 2 ^ r * (N : ℤ) [ZMOD 2 ^ (β - 1 + r + 1)]) (hβ : n + 2 ≤ β) (hN : N ≤ 2 ^ n) :
    ((a / 2 ^ r) % 2 ^ (n + 1)).toNat = N := by
  have e : β - 1 + r + 1 = β + r := by omega
  rw [e] at h
  have h1 := (div_congr h).of_dvd (pow_dvd_pow (2 : ℤ) (by omega : n + 1 ≤ β))
  rw [emod_eq (Int.natCast_nonneg N) (by exact_mod_cast hN) h1, Int.toNat_natCast]

/-- At most 2^n assignments satisfy ψ. -/
theorem nSat_le (n : ℕ) (ψ : Fml) : nSat n ψ ≤ 2 ^ n := by
  unfold nSat
  refine (Finset.card_filter_le _ _).trans ?_
  simp

/-! ### The evaluations -/

section
variable (hE : StEvW) (hSh : StShape) {Idx : Type} [Enc Idx] (S : Solver Idx) (ok : Idx → Prop) (hC : S.Correct ok) (k : ℕ) (pad : U) (i : Idx) (n Δ : ℕ) (ψ : Fml)
  (nb r i₀ β : ℕ) (hok : ok i) (hK : 2 ≤ S.K i) (hW : WfL k n [ψ]) (hocc : ∀ v, (occ ψ v).length ≤ Δ) (hmΔ : ψ.length ≤ Δ * n) (hnb : 2 ≤ nb)
  (hLD : n < 2 * (nb * LD Δ)) (hr : r ≤ 6 * n) (hcap : β - 1 + r ≤ 11 * n) (hFit : FitsOL S k i n Δ pad.length)

include hE hSh hC hok hK hW hocc hmΔ hnb hLD hr hcap hFit

/-- An evaluation on the three layers of a state that satisfies the bounds for states that are tried
is exact. -/
theorem ev3 (Lam : List Chk) (j e : ℕ) (hj : j ≤ r) (hLam : ∀ L ∈ Lam, ChkOK ψ.length L) (hT : Tent (mkQ ψ nb r i₀ β) (lam ψ.length Lam))
    (ws : List ℤ) (lo hi : List ℕ) (hhi : ∀ l < 3, hi.getD l 0 ≤ β - 1 + r) :
    evW S k pad i n Δ (mkQ ψ nb r i₀ β) ws lo hi [ψ, incL n ψ Lam j, ψ.drop e] = truncW (n + r) ws lo hi [ψ, incL n ψ Lam j, ψ.drop e] := by
  obtain ⟨w1, w2, w3⟩ := hSh k n Δ (mkQ ψ nb r i₀ β) ψ Lam j e rfl hnb hmΔ hr hLD hW hocc hj hLam hT
  refine hE Idx S ok hC k pad i n Δ (mkQ ψ nb r i₀ β) ws lo hi _ hok hK hr hcap (by simp) w1 w2 w3 hhi ?_ hFit.net
  refine (nProf_le _ ?_ (by simp)).trans hFit.prof
  rw [length_cls]
  exact w3.trans (Nat.mul_le_mul_left _ (by change n + r + 1 ≤ _; omega))

/-- The same on the first two layers. -/
theorem ev2 (Lam : List Chk) (j : ℕ) (hj : j ≤ r) (hLam : ∀ L ∈ Lam, ChkOK ψ.length L) (hT : Tent (mkQ ψ nb r i₀ β) (lam ψ.length Lam))
    (ws : List ℤ) (lo hi : List ℕ) (hhi : ∀ l < 2, hi.getD l 0 ≤ β - 1 + r) :
    evW S k pad i n Δ (mkQ ψ nb r i₀ β) ws lo hi [ψ, incL n ψ Lam j] = truncW (n + r) ws lo hi [ψ, incL n ψ Lam j] := by
  obtain ⟨w1, w2, w3⟩ := hSh k n Δ (mkQ ψ nb r i₀ β) ψ Lam j ψ.length rfl hnb hmΔ hr hLD hW hocc hj hLam hT
  have e0 : [ψ, incL n ψ Lam j, ψ.drop ψ.length].flatten = [ψ, incL n ψ Lam j].flatten := by simp
  rw [e0] at w2 w3
  refine hE Idx S ok hC k pad i n Δ (mkQ ψ nb r i₀ β) ws lo hi _ hok hK hr hcap (by simp)
    (fun L hL => w1 L (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hL ⊢; tauto)) w2 w3 hhi ?_ hFit.net
  refine (nProf_le _ ?_ (by simp)).trans hFit.prof
  rw [length_cls]
  exact w3.trans (Nat.mul_le_mul_left _ (by change n + r + 1 ≤ _; omega))

/-- The two functions that the choice of the checks asks are right modulo 2^β in every state that
satisfies the bounds for states that are tried. -/
theorem orcOK (hB : StBridgeB) (hA : StBridgeA) (hβ : 1 ≤ β) (hnbc : nb + 1 ≤ β - 1 + r) (hi₀ : i₀ ≤ β - 1 + r) :
    OrcOK (mkQ ψ nb r i₀ β) (Vof (n := n) ψ) (orcA S k pad i n Δ (mkQ ψ nb r i₀ β) ψ) (orcB S k pad i n Δ (mkQ ψ nb r i₀ β) ψ) := by
  intro Ls cur e hlt hLs hcur he hT
  have hlt' : Ls.length < r := hlt
  have hψ : ∀ C ∈ ψ, ∀ l ∈ C, l.1 < n := fun C hC' => (hW ψ (by simp) C hC').2.2
  have hall : ∀ L ∈ Ls ++ [cur], ChkOK ψ.length L := Num.all_ok (q := mkQ ψ nb r i₀ β) hLs hcur he
  have hlen : (Ls ++ [cur]).length ≤ r := by rw [List.length_append, List.length_singleton]; omega
  have hWf := wfC_pad hlen hall
  have eM : β - 1 + r + 1 = β + r := by omega
  constructor
  · have h1 := ev2 hE hSh S ok hC k pad i n Δ ψ nb r i₀ β hok hK hW hocc hmΔ hnb hLD hr hcap hFit Ls Ls.length hlt'.le hLs
      (tent_mono (lam_subset ψ.length Ls cur) hT) [1, -2] [nb + 1, 0] [nb + 1, β - 1 + r]
      (getD2 hnbc le_rfl)
    have h2 := hA n r nb (β - 1 + r) Ls.length ψ _ hψ hWf hlt'.le
    have e1 : ((Ls ++ [cur]) ++ List.replicate (r - (Ls ++ [cur]).length) []).take Ls.length = Ls := by
      rw [List.append_assoc, List.take_left']
      rfl
    unfold sumA at h2
    rw [e1, Lof_pad, eM] at h2
    change evW S k pad i n Δ (mkQ ψ nb r i₀ β) [1, -2] [nb + 1, 0] [nb + 1, β - 1 + r] [ψ, incL n ψ (Ls.take Ls.length) Ls.length] / 2 ^ r ≡ _ [ZMOD 2 ^ β]
    rw [List.take_length, h1]
    exact div_congr h2
  · intro i' hi'
    have hi'' : i' ≤ i₀ := hi'
    have h1 := ev3 hE hSh S ok hC k pad i n Δ ψ nb r i₀ β hok hK hW hocc hmΔ hnb hLD hr hcap hFit (Ls ++ [cur]) Ls.length e hlt'.le hall hT
      [1, -2, 1] [nb + 1, 0, i'] [nb + 1, β - 1 + r, i'] (getD3 hnbc le_rfl (hi''.trans hi₀))
    have h2 := hB n r nb (β - 1 + r) i' Ls.length e ψ _ hψ hWf hlt'
    unfold sumB at h2
    rw [incL_pad, Lof_pad, eM] at h2
    change evW S k pad i n Δ (mkQ ψ nb r i₀ β) [1, -2, 1] [nb + 1, 0, i'] [nb + 1, β - 1 + r, i'] [ψ, incL n ψ (Ls ++ [cur]) Ls.length, ψ.drop e] / 2 ^ r ≡ _ [ZMOD 2 ^ β]
    rw [h1]
    exact div_congr h2

/-- The count is right, for parameters that satisfy what the choice of the checks needs, or without
checks if there are at most nb clauses. -/
theorem count_core (hB : StBridgeB) (hA : StBridgeA) (hF : StBridgeF) (H2 : ChoiceByPotential) (ε : ℚ) (hβ : n + 2 ≤ β) (hnbn : nb ≤ n)
    (hcase : (r = 0 ∧ ψ.length ≤ nb) ∨ (Hyp (mkQ ψ nb r i₀ β) (2 ^ n) ε ∧ i₀ ≤ β - 1 + r)) :
    countOL S k pad i n Δ (mkQ ψ nb r i₀ β) ψ = nSat n ψ := by
  have hψ : ∀ C ∈ ψ, ∀ l ∈ C, l.1 < n := fun C hC' => (hW ψ (by simp) C hC').2.2
  have hRF := RunF.runF_eq S k pad i n Δ (mkQ ψ nb r i₀ β) ψ hFit.lists hr hmΔ
  obtain ⟨R, hR, hlen, hchk, hgood, htent⟩ : ∃ R : List Chk, runF S k pad i n Δ (mkQ ψ nb r i₀ β) ψ = R ∧ R.length = r ∧ (∀ L ∈ R, ChkOK ψ.length L) ∧
      Good (Vof (n := n) ψ) nb r (lam ψ.length R) ∧ Tent (mkQ ψ nb r i₀ β) (lam ψ.length R) := by
    rcases hcase with ⟨hr0, hm⟩ | ⟨hH, hi₀⟩
    · subst hr0
      refine ⟨[], ?_, rfl, fun L hL => absurd hL List.not_mem_nil, fun ξ hξ => ?_, ?_⟩
      · rw [hRF]
        rfl
      · exfalso
        have h1 : #(Vof (n := n) ψ ξ) ≤ ψ.length := (Finset.card_le_univ _).trans (by simp)
        omega
      · refine ⟨by simp, fun j' hj' => absurd hj' (Nat.not_lt_zero _), fun x => ?_⟩
        have hx : (1 : ℚ) ≤ (ψ.length : ℚ) := by exact_mod_cast (Nat.lt_of_le_of_lt (Nat.zero_le _) x.2 : 0 < ψ.length)
        simp only [Finset.range_zero, Finset.filter_empty, Finset.card_empty, pow_zero, mul_one]
        linarith
    · have hcard : Fintype.card (Fin n → Bool) = 2 ^ n := by simp
      rw [← hcard] at hH
      have ho := orcOK hE hSh S ok hC k pad i n Δ ψ nb r i₀ β hok hK hW hocc hmΔ hnb hLD hr hcap hFit hB hA (by omega) (by omega) hi₀
      obtain ⟨g1, g2, g3, g4, g5, g6⟩ := run_ok (mkQ ψ nb r i₀ β) (Vof (n := n) ψ) _ _ H2 hH ho
      exact ⟨_, hRF, g1, g2, g3, Run.tent_out ⟨g4, g5, g6⟩⟩
  have h1 := ev2 hE hSh S ok hC k pad i n Δ ψ nb r i₀ β hok hK hW hocc hmΔ hnb hLD hr hcap hFit R r le_rfl hchk htent [-1, -2] [0, 0] [nb, β - 1 + r]
    (getD2 (by omega) le_rfl)
  have h2 := hF n r nb (β - 1 + r) ψ R hψ ⟨hlen, hchk⟩ hgood
  have e1 : R.take r = R := by rw [← hlen, List.take_length]
  unfold sumF3 at h2
  rw [e1] at h2
  change ((evW S k pad i n Δ (mkQ ψ nb r i₀ β) [-1, -2] [0, 0] [nb, β - 1 + r]
    [ψ, incL n ψ ((runF S k pad i n Δ (mkQ ψ nb r i₀ β) ψ).take r) r] / 2 ^ r) % 2 ^ (n + 1)).toNat = _
  rw [hR, e1, h1]
  exact toNat_eq h2 hβ (nSat_le n ψ)

end

/-! ### The parameters of the program -/

/-- β₁ ≤ m. -/
theorem beta1_le (m i₀ : ℕ) : beta1 m i₀ ≤ m := by
  unfold beta1
  refine Finset.sup_le fun i _ => ?_
  exact Nat.clog_le_of_le_pow (Nat.choose_le_two_pow m i)

/-- β₀ = 0 if m ≤ nb. -/
theorem beta0_eq_zero {m nb : ℕ} (h : m ≤ nb) : beta0 m nb = 0 := by
  unfold beta0
  rw [Nat.choose_eq_zero_of_lt (by omega)]
  simp

/-- The count is right. -/
theorem stCountOL (hE : StEvW) (hSh : StShape) (hB : StBridgeB) (hA : StBridgeA) (hF : StBridgeF) (H2 : ChoiceByPotential) : StCountOL := by
  intro Idx _ S ok hC k pad i n Δ ψ ε hok hK hW hocc hmΔ hnb hLD hH hFit
  have hnbn : nbOf n Δ ≤ n := Nat.div_le_self _ _
  by_cases hm : ψ.length ≤ nbOf n Δ
  · have e : parQ n Δ ψ.length = mkQ ψ (nbOf n Δ) 0 (i0Of n) (n + beta0 ψ.length (nbOf n Δ) + beta1 ψ.length (i0Of n) + 2) := by
      unfold parQ
      rw [if_pos hm]
      rfl
    rw [e]
    have h0 := beta0_eq_zero hm
    have h1 := beta1_le ψ.length (i0Of n)
    exact count_core hE hSh S ok hC k pad i n Δ ψ _ 0 _ _ hok hK hW hocc hmΔ hnb hLD (Nat.zero_le _) (by omega) hFit hB hA hF H2 ε (by omega) hnbn
      (Or.inl ⟨rfl, hm⟩)
  · obtain ⟨g1, g2, g3, g4⟩ := hH (not_le.1 hm)
    have e : parQ n Δ ψ.length = mkQ ψ (nbOf n Δ) (rOf n (beta0 ψ.length (nbOf n Δ))) (i0Of n)
        (n + beta0 ψ.length (nbOf n Δ) + beta1 ψ.length (i0Of n) + 2) := by
      unfold parQ
      rw [if_neg hm]
      rfl
    rw [e]
    have g2' : rOf n (beta0 ψ.length (nbOf n Δ)) ≤ 6 * n := g2
    have g3' : n + beta0 ψ.length (nbOf n Δ) + beta1 ψ.length (i0Of n) + 2 ≤ 5 * n := g3
    exact count_core hE hSh S ok hC k pad i n Δ ψ _ _ _ _ hok hK hW hocc hmΔ hnb hLD g2' (by omega) hFit hB hA hF H2 ε (by omega) hnbn (Or.inr ⟨g1, g4⟩)

end ClauseBound.ParityChecks.Count
