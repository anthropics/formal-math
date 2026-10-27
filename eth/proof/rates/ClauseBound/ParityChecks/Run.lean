/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ClauseBound.ParityChecks.Num
public import ClauseBound.ParityChecks.Congr

/-! # The choice of the checks as a computation: the run

The run decides the m·r pairs (check, clause) one after the other; each time it takes the option
with the smaller numerator of the truncated potential. This file proves that it ends with good
checks that satisfy the three bounds (`run_ok`).

The invariant: after t decisions the potential is at most 1/2 + t·(2δ), where δ bounds the error of
the truncated potential; by the hypothesis on the parameters this stays below 3/4. One decision:
both
options are states that satisfy the bounds for states that are tried, because the state reached has
a potential below 1 and they have at most one pair more; so the two functions give the right
integers, the numerators over the common denominator are the truncated potentials, and the option
taken has a potential of at most the smaller potential plus 2δ, which is at most the old potential
plus 2δ, because the old potential is a mean of the two. From one check to the next the potential
does not grow. -/

public section

namespace ClauseBound.ParityChecks

open Finset _root_.ParityChecks

variable {X : Type} [Fintype X] (q : Par) (V : X → Finset (Fin q.m)) (orcA : List Chk → ℤ) (orcB : List Chk → Chk → ℕ → ℕ → ℤ)

/-- The two functions are right, modulo 2^β, in every state that satisfies the bounds for states
that are tried. -/
@[expose] def OrcOK : Prop := ∀ (Ls : List Chk) (cur : Chk) (e : ℕ), Ls.length < q.r → (∀ L ∈ Ls, ChkOK q.m L) → ChkOK e cur → e ≤ q.m →
  Tent q (lam q.m (Ls ++ [cur])) →
    orcA Ls ≡ Aint V q.nb Ls.length (lam q.m (Ls ++ [cur])) [ZMOD 2 ^ q.β] ∧
    ∀ i ≤ q.i₀, orcB Ls cur e i ≡ Bint V q.nb i Ls.length (lam q.m (Ls ++ [cur])) (Dset q.m e) [ZMOD 2 ^ q.β]

namespace Run

/-! ### Lists and sets -/

theorem getD_append_self (Ls : List Chk) (c : Chk) : (Ls ++ [c]).getD Ls.length [] = c := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_append_ne (Ls : List Chk) (c : Chk) {j : ℕ} (hj : j ≠ Ls.length) : (Ls ++ [c]).getD j [] = Ls.getD j [] := by
  rcases Nat.lt_or_gt_of_ne hj with h | h
  · simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem chkOK_mono {e e' : ℕ} (h : e ≤ e') {L : Chk} (hL : ChkOK e L) : ChkOK e' L := ⟨hL.1, fun x hx => (hL.2 x hx).trans_le h⟩

theorem chkOK_nil (e : ℕ) : ChkOK e [] := ⟨List.nodup_nil, fun _ hx => absurd hx (List.not_mem_nil)⟩

theorem chkOK_snoc {e : ℕ} {L : Chk} (hL : ChkOK e L) : ChkOK (e + 1) (L ++ [e]) := by
  refine ⟨List.Nodup.append hL.1 (List.nodup_singleton e) ?_, fun x hx => ?_⟩
  · intro a ha hb
    have h1 := hL.2 a ha
    have h2 : a = e := by simpa using hb
    omega
  · rcases List.mem_append.1 hx with h | h
    · exact (hL.2 x h).trans (Nat.lt_succ_self e)
    · have h2 : x = e := by simpa using h
      omega

variable {q}

theorem Dset_zero : Dset q.m 0 = univ := by
  ext x; simp [Dset]

theorem Dset_self : Dset q.m q.m = ∅ := by
  ext x; simp [Dset]

theorem mem_Dset {e : ℕ} (he : e < q.m) : (⟨e, he⟩ : Fin q.m) ∈ Dset q.m e := by
  simp [Dset]

theorem Dset_succ {e : ℕ} (he : e < q.m) : Dset q.m (e + 1) = (Dset q.m e).erase ⟨e, he⟩ := by
  ext x
  simp only [Dset, mem_filter, mem_univ, true_and, mem_erase, ne_eq, Fin.ext_iff]
  omega

theorem lam_append_nil (Ls : List Chk) : lam q.m (Ls ++ [[]]) = lam q.m Ls := by
  funext j
  unfold lam
  by_cases hj : j = Ls.length
  · rw [hj, getD_append_self, List.getD_eq_default _ _ le_rfl]
  · rw [getD_append_ne _ _ hj]

theorem lam_start : lam q.m ([] ++ [[]]) = fun _ => ∅ := by
  funext j
  rw [lam_append_nil]
  simp [lam]

theorem lam_putIn (Ls : List Chk) (cur : Chk) {e : ℕ} (he : e < q.m) :
    lam q.m (Ls ++ [cur ++ [e]]) = putIn Ls.length (lam q.m (Ls ++ [cur])) ⟨e, he⟩ := by
  funext j
  unfold putIn lam
  by_cases hj : j = Ls.length
  · rw [hj, Function.update_self, getD_append_self, getD_append_self]
    ext x
    simp only [mem_filter, mem_univ, true_and, List.mem_append, List.mem_singleton, mem_insert, Fin.ext_iff]
    tauto
  · rw [Function.update_of_ne hj, getD_append_ne _ _ hj, getD_append_ne _ _ hj]

/-! ### The bounds for states that are tried -/

/-- The three bounds that a potential below 1 gives. -/
structure Bd (q : Par) (Λ : ℕ → Finset (Fin q.m)) : Prop where
  inc : ((∑ j' ∈ range q.r, #(Λ j') : ℕ) : ℚ) < 8 * pr q.nb * q.m * q.r
  row : ∀ j' < q.r, (2 : ℚ) ^ #(Λ j') < 8 * q.r * (1 + pr q.nb) ^ q.m
  col : ∀ x : Fin q.m, (2 : ℚ) ^ #{j' ∈ range q.r | x ∈ Λ j'} < 8 * q.m * (1 + pr q.nb) ^ q.r

theorem lt_two_mul {a b : ℚ} (ha : 0 < a) (h : a < b) : a < 2 * b := by linarith

theorem tent_out {Λ : ℕ → Finset (Fin q.m)} (h : Bd q Λ) : Tent q Λ where
  inc := h.inc.trans (lt_add_one _)
  row j' hj' := lt_two_mul (by positivity) (h.row j' hj')
  col x := lt_two_mul (by positivity) (h.col x)

theorem card_putIn_le (Λ : ℕ → Finset (Fin q.m)) (j : ℕ) (x : Fin q.m) (j' : ℕ) : #(putIn j Λ x j') ≤ #(Λ j') + if j' = j then 1 else 0 := by
  unfold putIn
  by_cases h : j' = j
  · rw [h, Function.update_self, if_pos rfl]
    exact card_insert_le _ _
  · rw [Function.update_of_ne h, if_neg h]
    exact le_rfl

theorem tent_in {Λ : ℕ → Finset (Fin q.m)} (h : Bd q Λ) (j : ℕ) (x : Fin q.m) : Tent q (putIn j Λ x) where
  inc := by
    have h1 : ∑ j' ∈ range q.r, #(putIn j Λ x j') ≤ ∑ j' ∈ range q.r, #(Λ j') + 1 := by
      refine (sum_le_sum fun j' _ => card_putIn_le Λ j x j').trans ?_
      rw [sum_add_distrib, sum_ite_eq']
      split_ifs <;> omega
    have h2 : ((∑ j' ∈ range q.r, #(putIn j Λ x j') : ℕ) : ℚ) ≤ ((∑ j' ∈ range q.r, #(Λ j') : ℕ) : ℚ) + 1 := by exact_mod_cast h1
    have := h.inc
    linarith
  row j' hj' := by
    have h1 : (2 : ℚ) ^ #(putIn j Λ x j') ≤ 2 ^ (#(Λ j') + 1) :=
      pow_le_pow_right₀ (by norm_num) ((card_putIn_le Λ j x j').trans (by split_ifs <;> omega))
    have := h.row j' hj'
    rw [pow_succ] at h1
    linarith
  col y := by
    have h0 : #{j' ∈ range q.r | y ∈ putIn j Λ x j'} ≤ #{j' ∈ range q.r | y ∈ Λ j'} + 1 := by
      refine (card_le_card (t := insert j {j' ∈ range q.r | y ∈ Λ j'}) fun j' hj' => ?_).trans (card_insert_le _ _)
      obtain ⟨h1, h2⟩ := mem_filter.1 hj'
      by_cases hjj : j' = j
      · exact mem_insert.2 (Or.inl hjj)
      · rw [putIn, Function.update_of_ne hjj] at h2
        exact mem_insert.2 (Or.inr (mem_filter.2 ⟨h1, h2⟩))
    have h1 : (2 : ℚ) ^ #{j' ∈ range q.r | y ∈ putIn j Λ x j'} ≤ 2 ^ (#{j' ∈ range q.r | y ∈ Λ j'} + 1) :=
      pow_le_pow_right₀ (by norm_num) h0
    have := h.col y
    rw [pow_succ] at h1
    linarith

/-! ### The potential of a state of the run -/

section Pot
variable (q)

/-- The potential of the state (Ls, cur, e). -/
def UU (Ls : List Chk) (cur : Chk) (e : ℕ) : ℚ := Ups V q.nb q.r Ls.length (lam q.m (Ls ++ [cur])) (Dset q.m e)

/-- The truncated potential of the state (Ls, cur, e). -/
def tUU (Ls : List Chk) (cur : Chk) (e : ℕ) : ℚ :=
  tUpar V q.nb q.r q.i₀ Ls.length (lam q.m (Ls ++ [cur])) (Dset q.m e) + Uinc q.nb q.r Ls.length (lam q.m (Ls ++ [cur])) (Dset q.m e)
    + Urow q.nb q.r Ls.length (lam q.m (Ls ++ [cur])) (Dset q.m e) + Ucol q.nb q.r Ls.length (lam q.m (Ls ++ [cur])) (Dset q.m e)

/-- The bound on Σ_ξ ω(ξ). -/
def NN (X : Type) [Fintype X] (q : Par) : ℚ := ((Fintype.card X * q.m.choose (q.nb + 1) : ℕ) : ℚ)

end Pot

theorem NN_nonneg : 0 ≤ NN X q := Nat.cast_nonneg _

variable {V} {orcA orcB} {ε : ℚ}

theorem eps_nonneg (hq : Hyp q (Fintype.card X) ε) : 0 ≤ ε := (abs_nonneg _).trans (hq.series 0 (Nat.zero_le _))

/-- The truncated potential differs from the potential by at most δ = ε·N/2. -/
theorem abs_tUU_sub (H2 : ChoiceByPotential) (hq : Hyp q (Fintype.card X) ε) (Ls : List Chk) (cur : Chk) (e : ℕ) :
    |tUU q V Ls cur e - UU q V Ls cur e| ≤ 1 / 2 * ε * NN X q := by
  have h := H2.approx X (Fin q.m) V q.nb q.r q.i₀ Ls.length (lam q.m (Ls ++ [cur])) (Dset q.m e) ε
  simp only [Fintype.card_fin] at h
  have h1 := h hq.series
  have e1 : tUU q V Ls cur e - UU q V Ls cur e =
      tUpar V q.nb q.r q.i₀ Ls.length (lam q.m (Ls ++ [cur])) (Dset q.m e) - Upar V q.nb q.r Ls.length (lam q.m (Ls ++ [cur])) (Dset q.m e) := by
    unfold tUU UU Ups
    ring
  rw [e1]
  exact h1

/-- A potential below 1 gives the three bounds. -/
theorem bd_of_lt_one (H2 : ChoiceByPotential) (hq : Hyp q (Fintype.card X) ε) {Ls : List Chk} {cur : Chk} {e : ℕ} (hj : Ls.length < q.r) (hc : ChkOK e cur)
    (hU : UU q V Ls cur e < 1) : Bd q (lam q.m (Ls ++ [cur])) := by
  have h := H2.structure_ X (Fin q.m) V q.nb q.r Ls.length (lam q.m (Ls ++ [cur])) (Dset q.m e) hq.nb_two
  simp only [Fintype.card_fin] at h
  obtain ⟨h1, h2, h3⟩ := h hq.m_pos (isState q hj hc) hU
  exact ⟨h1, h2, h3⟩

/-- The numerator uses the B_i with i ≤ i₀ only. -/
theorem num_congr (A : ℤ) {B B' : ℕ → ℤ} (h : ∀ i ≤ q.i₀, B i = B' i) (Ls : List Chk) (cur : Chk) (e : ℕ) : q.num A B Ls cur e = q.num A B' Ls cur e := by
  have h1 : q.numP A B = q.numP A B' := by
    unfold Par.numP
    congr 2
    exact List.map_congr_left fun i hi => by rw [h i (Nat.lt_succ_iff.1 (List.mem_range.1 hi))]
  unfold Par.num
  rw [h1]

/-- In a state that satisfies the bounds for states that are tried, the numerator that the run
computes, over the denominator, is the truncated potential. -/
theorem numO_div_den (H2 : ChoiceByPotential) (hq : Hyp q (Fintype.card X) ε) (ho : OrcOK q V orcA orcB) {Ls : List Chk} {cur : Chk} {e : ℕ} (hj : Ls.length < q.r)
    (hL : ∀ L ∈ Ls, ChkOK q.m L) (hc : ChkOK e cur) (he : e ≤ q.m) (hT : Tent q (lam q.m (Ls ++ [cur]))) :
    (q.numO orcA orcB Ls cur e : ℚ) / q.den Ls.length = tUU q V Ls cur e := by
  obtain ⟨hA, hB⟩ := ho Ls cur e hj hL hc he hT
  have hβ : 1 ≤ q.β := by have := hq.β_pos; omega
  have hpow : (2 : ℤ) ^ (q.β - 2) < 2 ^ (q.β - 1) := pow_lt_pow_right₀ (by norm_num) (by have := hq.β_pos; omega)
  have habs := fun i => H2.abs_le X (Fin q.m) V q.nb i Ls.length (lam q.m (Ls ++ [cur])) (Dset q.m e)
  simp only [Fintype.card_fin] at habs
  have hA' : bal q.β (orcA Ls) = Aint V q.nb Ls.length (lam q.m (Ls ++ [cur])) := by
    refine bal_eq hβ (lt_of_le_of_lt ((habs 0).1.trans ?_) hpow) hA
    have := hq.small 0 (Nat.zero_le _)
    rw [Nat.choose_zero_right, Nat.mul_one] at this
    exact_mod_cast this
  have hB' : ∀ i ≤ q.i₀, bal q.β (orcB Ls cur e i) = Bint V q.nb i Ls.length (lam q.m (Ls ++ [cur])) (Dset q.m e) := fun i hi => by
    refine bal_eq hβ (lt_of_le_of_lt ((habs i).2.trans ?_) hpow) (hB i hi)
    exact_mod_cast hq.small i hi
  unfold Par.numO
  rw [hA', num_congr _ hB']
  exact num_div_den q V (by have := hq.nb_two; omega) hq.m_pos hj hL hc he

/-! ### One decision -/

/-- What is known of a state that the run has reached, after t decisions. -/
structure Inv (q : Par) (V : X → Finset (Fin q.m)) (ε : ℚ) (Ls : List Chk) (cur : Chk) (e : ℕ) : Prop where
  lt : Ls.length < q.r
  done : ∀ L ∈ Ls, ChkOK q.m L
  okc : ChkOK e cur
  le : e ≤ q.m
  pot : UU q V Ls cur e ≤ 1 / 2 + ((Ls.length * q.m + e : ℕ) : ℚ) * (ε * NN X q)

/-- In a state that the run has reached the potential is below 1 (the proof gives below 3/4). -/
theorem Inv.lt_one (hq : Hyp q (Fintype.card X) ε) {Ls : List Chk} {cur : Chk} {e : ℕ} (h : Inv q V ε Ls cur e) : UU q V Ls cur e < 1 := by
  have h1 : Ls.length * q.m + e ≤ q.m * q.r := by
    have h2 : (Ls.length + 1) * q.m ≤ q.r * q.m := Nat.mul_le_mul_right _ h.lt
    have := h.le
    nlinarith
  have h3 : ((Ls.length * q.m + e : ℕ) : ℚ) ≤ (q.m : ℚ) * q.r := by exact_mod_cast h1
  have h4 : 0 ≤ ε * NN X q := mul_nonneg (eps_nonneg hq) NN_nonneg
  have h5 := mul_le_mul_of_nonneg_right h3 h4
  have h6 : ε * NN X q * ((q.m : ℚ) * q.r) < 1 / 4 := hq.drift
  have := h.pot
  linarith

/-- Both options of a decision satisfy the bounds for states that are tried. -/
theorem Inv.tent (H2 : ChoiceByPotential) (hq : Hyp q (Fintype.card X) ε) {Ls : List Chk} {cur : Chk} {e : ℕ} (h : Inv q V ε Ls cur e) (he : e < q.m) :
    Tent q (lam q.m (Ls ++ [cur ++ [e]])) ∧ Tent q (lam q.m (Ls ++ [cur])) := by
  have hb := bd_of_lt_one H2 hq h.lt h.okc (h.lt_one hq)
  rw [lam_putIn Ls cur he]
  exact ⟨tent_in hb _ _, tent_out hb⟩

/-- One decision keeps the invariant. -/
theorem Inv.step (H2 : ChoiceByPotential) (hq : Hyp q (Fintype.card X) ε) (ho : OrcOK q V orcA orcB) {Ls : List Chk} {cur : Chk} {e : ℕ} (h : Inv q V ε Ls cur e)
    (he : e < q.m) : Inv q V ε Ls (q.decide1 orcA orcB Ls cur e) (e + 1) := by
  obtain ⟨hTi, hTo⟩ := h.tent H2 hq he
  have hci : ChkOK (e + 1) (cur ++ [e]) := chkOK_snoc h.okc
  have hco : ChkOK (e + 1) cur := chkOK_mono (Nat.le_succ e) h.okc
  have hni := numO_div_den H2 hq ho h.lt h.done hci he hTi
  have hno := numO_div_den H2 hq ho h.lt h.done hco he hTo
  have hden : (0 : ℚ) < q.den Ls.length := by
    exact_mod_cast den_pos q (by have := hq.nb_two; omega) hq.m_pos hq.r_pos Ls.length
  -- the old potential is a mean of the two new ones
  have hmart : pr q.nb * UU q V Ls (cur ++ [e]) (e + 1) + (1 - pr q.nb) * UU q V Ls cur (e + 1) = UU q V Ls cur e := by
    have := H2.martingale X (Fin q.m) V q.nb q.r Ls.length (lam q.m (Ls ++ [cur])) (Dset q.m e) ⟨e, he⟩ hq.nb_two (isState q h.lt h.okc) (mem_Dset he)
    unfold UU
    rw [lam_putIn Ls cur he, Dset_succ he]
    exact this
  have hp0 : 0 < pr q.nb := by
    unfold pr
    have : (0 : ℚ) < q.nb := by exact_mod_cast (by have := hq.nb_two; omega : 0 < q.nb)
    positivity
  have hp1 : pr q.nb ≤ 1 / 2 := by
    unfold pr
    have : (2 : ℚ) ≤ q.nb := by exact_mod_cast hq.nb_two
    exact one_div_le_one_div_of_le (by norm_num) this
  have hai := abs_le.1 (abs_tUU_sub (V := V) H2 hq Ls (cur ++ [e]) (e + 1))
  have hao := abs_le.1 (abs_tUU_sub (V := V) H2 hq Ls cur (e + 1))
  have hpot := h.pot
  have hcast : ((Ls.length * q.m + (e + 1) : ℕ) : ℚ) = ((Ls.length * q.m + e : ℕ) : ℚ) + 1 := by push_cast; ring
  have key : ∀ c : Chk, ChkOK (e + 1) c → tUU q V Ls c (e + 1) ≤ tUU q V Ls (cur ++ [e]) (e + 1) → tUU q V Ls c (e + 1) ≤ tUU q V Ls cur (e + 1) →
      |tUU q V Ls c (e + 1) - UU q V Ls c (e + 1)| ≤ 1 / 2 * ε * NN X q → Inv q V ε Ls c (e + 1) := by
    intro c hc h1 h2 h3
    refine ⟨h.lt, h.done, hc, he, ?_⟩
    rw [hcast]
    have h3' := abs_le.1 h3
    have hmin : UU q V Ls (cur ++ [e]) (e + 1) ≤ UU q V Ls cur e ∨ UU q V Ls cur (e + 1) ≤ UU q V Ls cur e := by
      by_contra hcon
      push Not at hcon
      nlinarith [hcon.1, hcon.2]
    rcases hmin with hm | hm <;> linarith [h3'.1, h3'.2, hai.1, hai.2, hao.1, hao.2]
  unfold Par.decide1
  split_ifs with hle
  · refine key _ hci le_rfl ?_ (abs_tUU_sub H2 hq _ _ _)
    rw [← hni, ← hno]
    exact div_le_div_of_nonneg_right (by exact_mod_cast hle) hden.le
  · refine key _ hco ?_ le_rfl (abs_tUU_sub H2 hq _ _ _)
    rw [← hni, ← hno]
    exact div_le_div_of_nonneg_right (by exact_mod_cast (not_le.1 hle).le) hden.le

/-! ### One check, all checks -/

theorem runTo_succ (Ls : List Chk) (e : ℕ) : q.runTo orcA orcB Ls (e + 1) = q.decide1 orcA orcB Ls (q.runTo orcA orcB Ls e) e := by
  unfold Par.runTo
  rw [List.range_succ, List.foldl_append]
  rfl

theorem runChecks_succ (j : ℕ) :
    q.runChecks orcA orcB (j + 1) = q.runChecks orcA orcB j ++ [q.runTo orcA orcB (q.runChecks orcA orcB j) q.m] := by
  unfold Par.runChecks
  rw [List.range_succ, List.foldl_append]
  rfl

/-- The decisions for one check keep the invariant. -/
theorem inv_runTo (H2 : ChoiceByPotential) (hq : Hyp q (Fintype.card X) ε) (ho : OrcOK q V orcA orcB) {Ls : List Chk} (h : Inv q V ε Ls [] 0) :
    ∀ e ≤ q.m, Inv q V ε Ls (q.runTo orcA orcB Ls e) e := by
  intro e
  induction e with
  | zero => exact fun _ => h
  | succ e ih =>
    intro he
    rw [runTo_succ]
    exact (ih (by omega)).step H2 hq ho he

/-- At the beginning of every check the invariant holds. -/
theorem inv_runChecks (H2 : ChoiceByPotential) (hq : Hyp q (Fintype.card X) ε) (ho : OrcOK q V orcA orcB) :
    ∀ j < q.r, (q.runChecks orcA orcB j).length = j ∧ Inv q V ε (q.runChecks orcA orcB j) [] 0 := by
  intro j
  induction j with
  | zero =>
    intro hr
    refine ⟨rfl, hr, fun L hL => absurd hL (List.not_mem_nil), chkOK_nil 0, Nat.zero_le _, ?_⟩
    have h := H2.start X (Fin q.m) V q.nb q.r hq.nb_two hq.r_pos
    simp only [Fintype.card_fin] at h
    have h1 := h hq.m_pos hq.start
    have e1 : UU q V (q.runChecks orcA orcB 0) [] 0 = Ups V q.nb q.r 0 (fun _ => ∅) univ := by
      change Ups V q.nb q.r 0 (lam q.m ([] ++ [[]])) (Dset q.m 0) = _
      rw [lam_start, Dset_zero]
    rw [e1]
    have h2 : 0 ≤ (((q.runChecks orcA orcB 0).length * q.m + 0 : ℕ) : ℚ) * (ε * NN X q) :=
      mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (eps_nonneg hq) NN_nonneg)
    linarith
  | succ j ih =>
    intro hj
    obtain ⟨hlen, hinv⟩ := ih (by omega)
    have hend := inv_runTo H2 hq ho hinv q.m le_rfl
    have hlen' : (q.runChecks orcA orcB (j + 1)).length = j + 1 := by rw [runChecks_succ, List.length_append, hlen]; rfl
    refine ⟨hlen', by rw [hlen']; exact hj, fun L hL => ?_, chkOK_nil 0, Nat.zero_le _, ?_⟩
    · rw [runChecks_succ] at hL
      rcases List.mem_append.1 hL with h | h
      · exact hinv.done L h
      · rw [List.mem_singleton.1 h]; exact hend.okc
    · have hb := H2.boundary X (Fin q.m) V q.nb q.r (q.runChecks orcA orcB j).length
        (lam q.m (q.runChecks orcA orcB j ++ [q.runTo orcA orcB (q.runChecks orcA orcB j) q.m])) hq.nb_two
        (by have := isState q hend.lt hend.okc; rwa [Dset_self] at this) (by rw [hlen]; exact hj)
      have e1 : UU q V (q.runChecks orcA orcB (j + 1)) [] 0 = Ups V q.nb q.r ((q.runChecks orcA orcB j).length + 1)
          (lam q.m (q.runChecks orcA orcB j ++ [q.runTo orcA orcB (q.runChecks orcA orcB j) q.m])) univ := by
        unfold UU
        rw [lam_append_nil, Dset_zero, hlen', hlen, runChecks_succ]
      have e2 : UU q V (q.runChecks orcA orcB j) (q.runTo orcA orcB (q.runChecks orcA orcB j) q.m) q.m = Ups V q.nb q.r (q.runChecks orcA orcB j).length
          (lam q.m (q.runChecks orcA orcB j ++ [q.runTo orcA orcB (q.runChecks orcA orcB j) q.m])) ∅ := by
        unfold UU
        rw [Dset_self]
      have hp := hend.pot
      rw [e2] at hp
      rw [e1, hlen']
      have hc : (((j + 1) * q.m + 0 : ℕ) : ℚ) = (((q.runChecks orcA orcB j).length * q.m + q.m : ℕ) : ℚ) := by rw [hlen]; push_cast; ring
      rw [hc]
      exact hb.trans hp

end Run

open Run

/-- The result of the run: r checks, each a list of clauses without repetition; they are good; and
the three bounds hold. -/
theorem run_ok (H2 : ChoiceByPotential) {ε : ℚ} (hq : Hyp q (Fintype.card X) ε) (ho : OrcOK q V orcA orcB) :
    (q.run orcA orcB).length = q.r ∧ (∀ L ∈ q.run orcA orcB, ChkOK q.m L) ∧ Good V q.nb q.r (lam q.m (q.run orcA orcB)) ∧
      ((∑ j' ∈ range q.r, #(lam q.m (q.run orcA orcB) j') : ℕ) : ℚ) < 8 * pr q.nb * q.m * q.r ∧
      (∀ j' < q.r, (2 : ℚ) ^ #(lam q.m (q.run orcA orcB) j') < 8 * q.r * (1 + pr q.nb) ^ q.m) ∧
      ∀ x : Fin q.m, (2 : ℚ) ^ #{j' ∈ range q.r | x ∈ lam q.m (q.run orcA orcB) j'} < 8 * q.m * (1 + pr q.nb) ^ q.r := by
  have hr := hq.r_pos
  obtain ⟨hlen, hinv⟩ := inv_runChecks H2 hq ho (q.r - 1) (by omega)
  have hend := inv_runTo H2 hq ho hinv q.m le_rfl
  have erun : q.run orcA orcB = q.runChecks orcA orcB (q.r - 1) ++ [q.runTo orcA orcB (q.runChecks orcA orcB (q.r - 1)) q.m] := by
    unfold Par.run
    conv_lhs => rw [show q.r = q.r - 1 + 1 by omega]
    exact runChecks_succ _
  have hb := bd_of_lt_one H2 hq hend.lt hend.okc (hend.lt_one hq)
  rw [← erun] at hb
  refine ⟨by rw [erun, List.length_append, hlen]; simp; omega, fun L hL => ?_, ?_, hb.inc, hb.row, hb.col⟩
  · rw [erun] at hL
    rcases List.mem_append.1 hL with h | h
    · exact hinv.done L h
    · rw [List.mem_singleton.1 h]; exact hend.okc
  · have hst := isState q hend.lt hend.okc
    have hU := hend.lt_one hq
    unfold UU at hU
    rw [Dset_self, hlen, ← erun] at hst hU
    exact H2.final X (Fin q.m) V q.nb q.r _ hq.nb_two hst hU

end ClauseBound.ParityChecks
