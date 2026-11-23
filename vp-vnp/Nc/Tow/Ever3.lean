/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Tow.Ever2

/-!
# The units given at a node: the start, the laws
-/

set_option linter.unusedSectionVars false

namespace Nc.Tow

open Finset Nc.G

variable {F : Type} [CommRing F] {h b D J r m Uu AA : ℕ} {T : Tower h b D J r}
  {R : Routes T m Uu} {ch : Fin AA ↪ T.X 0} {FL : FlagLaws F T} {lhat : ℕ} {n : Fin AA → Fin AA → ℕ}
  {o : NM R FL (ch := ch) → ℕ}

section Start

/-- The batches between two base parties. -/
theorem sum_Bt (a c : Fin AA) : ∑ γ, Bt T ch lhat n a c γ = if Valid lhat n then n a c else 0 := by
  classical
  unfold Bt
  split_ifs
  · rw [← card_eq_sum_card_fiberwise (f := fun k => gam T ch a k) (t := univ) (fun _ _ => mem_coe.2 (mem_univ _)),
      card_range]
  · simp

variable (hr : 0 < r) (hb : 0 < b)
include hr hb

theorem nR_start (a c : Fin AA) (γ : T.X 0) (s : Fin (2 * m)) : nR R ch FL lhat n o (.start a c γ s) ≤
    if a = c then 0 else Bt T ch lhat n a c γ := by
  unfold nR
  split_ifs with hx hac hac
  · exact absurd hac hx.1
  · exact num_start_le hr hb a c γ s hx
  · exact le_rfl
  · exact Nat.zero_le _

open Classical in
/-- Quadruples of the start. -/
abbrev Q4 (T : Tower h b D J r) (m AA : ℕ) := Fin AA × Fin AA × T.X 0 × Fin (2 * m)

/-- The relay of a quadruple. -/
def stR (q : Q4 T m AA) : RM T m AA := .start q.1 q.2.1 q.2.2.1 q.2.2.2

variable (hgR : ∀ (x : {x : RM T m AA // okR T R ch x}) (ν : Bool), o ⟨.inl x, ν⟩ = num R ch FL lhat n o (.inl x))
include hgR

open Classical in
/-- The paths at a chamber. -/
theorem paths_at (x : T.X 0) :
    (∑ q : Q4 T m AA, ((if R.pn (ch q.1) (ch q.2.1) q.2.2.1 q.2.2.2 = x then nR R ch FL lhat n o (stR q) else 0) +
      if R.pn (ch q.1) (ch q.2.1) q.2.2.1 (q.2.2.2 + 1) = x then nR R ch FL lhat n o (stR q) else 0)) ≤
      fb (ldL R ch FL lhat n o) 0 x := by
  -- one step
  have h1 : ∀ q : Q4 T m AA, ((if R.pn (ch q.1) (ch q.2.1) q.2.2.1 q.2.2.2 = x then nR R ch FL lhat n o (stR q) else 0) +
      if R.pn (ch q.1) (ch q.2.1) q.2.2.1 (q.2.2.2 + 1) = x then nR R ch FL lhat n o (stR q) else 0) ≤
      ∑ e : T.Ed 0, if T.e0 e = x ∨ T.e1 e = x then
        (if okR T R ch (stR q) ∧ (R.path (ch q.1) (ch q.2.1) q.2.2.1)[q.2.2.2.1]? = some e then
          nR R ch FL lhat n o (stR q) else 0) else 0 := by
    rintro ⟨a, c, γ, s⟩
    by_cases hx : okR T R ch (stR (a, c, γ, s))
    · obtain ⟨e, h2, h3, h4⟩ := R.exists_edge (ch a) (ch c) γ (s := s) (by have := hx.2; simp only at this; omega)
      have h6 : (T.e0 e = x ∨ T.e1 e = x) ↔ (R.pn (ch a) (ch c) γ s = x ∨ R.pn (ch a) (ch c) γ (s + 1) = x) := by
        have h7 : ∀ y z : T.X 0, (y = x ∨ z = x) ↔ x ∈ s(y, z) := fun y z => by
          rw [Sym2.mem_iff]
          exact or_congr eq_comm eq_comm
        rw [h7, h7, h3]
      by_cases h0 : R.pn (ch a) (ch c) γ s = x
      · have h8 : ¬ R.pn (ch a) (ch c) γ (s + 1) = x := fun hc => h4 (h0.trans hc.symm)
        simp only [if_pos h0, if_neg h8, Nat.add_zero]
        refine le_trans ?_ (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ e))
        rw [if_pos (h6.2 (Or.inl h0)), if_pos ⟨hx, h2⟩]
      · simp only [if_neg h0, Nat.zero_add]
        split_ifs with h8
        · refine le_trans ?_ (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ e))
          rw [if_pos (h6.2 (Or.inr h8)), if_pos ⟨hx, h2⟩]
        · exact Nat.zero_le _
    · have h5 : nR R ch FL lhat n o (stR (a, c, γ, s)) = 0 := by
        unfold nR
        rw [dif_neg hx]
      rw [h5]
      simp
  refine (Finset.sum_le_sum fun q _ => h1 q).trans ?_
  rw [Finset.sum_comm]
  unfold fb Tower.bet
  refine Finset.sum_le_sum fun e _ => ?_
  split_ifs with he
  · rw [← Finset.sum_filter]
    have h2 : ldL R ch FL lhat n o 0 e = load R ch FL lhat n o (.edge 0 e) := by
      unfold ldL lev
      rw [dif_pos (Nat.succ_pos J)]
      rfl
    rw [h2, ← Finset.sum_attach]
    set S := univ.filter fun q : Q4 T m AA => okR T R ch (stR q) ∧
      (R.path (ch q.1) (ch q.2.1) q.2.2.1)[q.2.2.2.1]? = some e with hS
    have h3 : ∀ q : {q // q ∈ S}, nR R ch FL lhat n o (stR q.1) = alv R ch FL lhat n o
        (⟨.inl ⟨stR q.1, (mem_filter.1 q.2).2.1⟩, false⟩ : NM R FL (ch := ch)) := by
      intro q
      unfold nR
      rw [dif_pos (mem_filter.1 q.2).2.1]
      exact (alv_relay hgR ⟨stR q.1, (mem_filter.1 q.2).2.1⟩ false).symm
    rw [Finset.sum_congr rfl fun q _ => h3 q]
    refine sum_alv_le (.edge 0 e) S.attach
      (fun q => (⟨.inl ⟨stR q.1, (mem_filter.1 q.2).2.1⟩, false⟩ : NM R FL (ch := ch))) ?_ ?_
    · rintro ⟨⟨a, c, γ, s⟩, hq⟩ _ ⟨⟨a', c', γ', s'⟩, hq'⟩ _ hee
      have h4 : (Sum.inl ⟨stR (a, c, γ, s), (mem_filter.1 hq).2.1⟩ : Mv T R ch FL) =
          .inl ⟨stR (a', c', γ', s'), (mem_filter.1 hq').2.1⟩ := congrArg Sigma.fst hee
      have h5 := congrArg Subtype.val (Sum.inl_injective h4)
      simp only [stR, RM.start.injEq] at h5
      obtain ⟨e1, e2, e3, e4⟩ := h5
      subst e1 e2 e3 e4
      rfl
    · rintro ⟨⟨a, c, γ, s⟩, hq⟩ _
      have h4 := (mem_filter.1 hq).2.2
      change edgeO T ((R.path (ch a) (ch c) γ)[s.1]?) = _
      simp only at h4
      rw [h4]
      rfl
  · simp

open Classical in
/-- **The start at a chamber.** -/
theorem NR0_le (x : T.X 0) : NR0 R ch FL lhat n o (nd T 0 (Nat.zero_le _) x) ≤
    (if ∃ c, ch c = x then 2 * m * lhat else 0) + fb (ldL R ch FL lhat n o) 0 x := by
  have h0 : ∀ a c γ (s : Fin (2 * m)), (∑ q : Fin 3, if tri T R ch (.start a c γ s) q = nd T 0 (Nat.zero_le _) x then
      nR R ch FL lhat n o (.start a c γ s) else 0) =
      ((if R.pn (ch a) (ch c) γ s = x then nR R ch FL lhat n o (.start a c γ s) else 0) +
      if R.pn (ch a) (ch c) γ (s + 1) = x then nR R ch FL lhat n o (.start a c γ s) else 0) +
      if ch c = x then nR R ch FL lhat n o (.start a c γ s) else 0 := by
    intro a c γ s
    rw [Fin.sum_univ_three]
    change ((if nd T 0 (Nat.zero_le _) (R.pn (ch a) (ch c) γ s) = nd T 0 (Nat.zero_le _) x then _ else 0) +
      (if nd T 0 (Nat.zero_le _) (R.pn (ch a) (ch c) γ (s + 1)) = nd T 0 (Nat.zero_le _) x then _ else 0)) +
      (if nd T 0 (Nat.zero_le _) (ch c) = nd T 0 (Nat.zero_le _) x then _ else 0) = _
    simp only [nd_inj]
  have h1 : NR0 R ch FL lhat n o (nd T 0 (Nat.zero_le _) x) =
      (∑ a, ∑ c, ∑ γ, ∑ s : Fin (2 * m),
        ((if R.pn (ch a) (ch c) γ s = x then nR R ch FL lhat n o (.start a c γ s) else 0) +
        if R.pn (ch a) (ch c) γ (s + 1) = x then nR R ch FL lhat n o (.start a c γ s) else 0)) +
      ∑ a, ∑ c, ∑ γ, ∑ s : Fin (2 * m), if ch c = x then nR R ch FL lhat n o (.start a c γ s) else 0 := by
    unfold NR0
    simp only [h0, Finset.sum_add_distrib]
  rw [h1, Nat.add_comm]
  refine add_le_add ?_ ?_
  · -- as the end of paths
    have h2 : ∀ c, (∑ a, ∑ γ, ∑ s : Fin (2 * m), if ch c = x then nR R ch FL lhat n o (.start a c γ s) else 0) ≤
        if ch c = x then 2 * m * lhat else 0 := by
      intro c
      split_ifs with hc
      · have h3 : ∀ a, (∑ γ, ∑ s : Fin (2 * m), nR R ch FL lhat n o (.start a c γ s)) ≤
            2 * m * if a = c then 0 else (if Valid lhat n then n a c else 0) := by
          intro a
          calc (∑ γ, ∑ s : Fin (2 * m), nR R ch FL lhat n o (.start a c γ s)) ≤
              ∑ γ, ∑ _s : Fin (2 * m), (if a = c then 0 else Bt T ch lhat n a c γ) :=
                Finset.sum_le_sum fun γ _ => Finset.sum_le_sum fun s _ => nR_start hr hb a c γ s
            _ = 2 * m * ∑ γ, (if a = c then 0 else Bt T ch lhat n a c γ) := by
                simp only [Finset.sum_const, card_univ, Fintype.card_fin, smul_eq_mul]
                rw [Finset.mul_sum]
            _ = _ := by
                congr 1
                by_cases hac : a = c
                · simp [hac]
                · simp only [if_neg hac]
                  exact sum_Bt a c
        refine (Finset.sum_le_sum fun a _ => h3 a).trans ?_
        rw [← Finset.mul_sum]
        refine Nat.mul_le_mul_left _ ?_
        by_cases hv : Valid lhat n
        · refine le_trans (Finset.sum_le_sum fun a _ => ?_) (hv c)
          by_cases hac : a = c
          · simp [hac]
          · rw [if_neg hac, if_pos hv, if_neg hac]
            omega
        · simp [hv]
      · simp
    have h3 : (∑ a, ∑ c, ∑ γ, ∑ s : Fin (2 * m), if ch c = x then nR R ch FL lhat n o (.start a c γ s) else 0) =
        ∑ c, ∑ a, ∑ γ, ∑ s : Fin (2 * m), if ch c = x then nR R ch FL lhat n o (.start a c γ s) else 0 :=
      Finset.sum_comm
    rw [h3]
    refine (Finset.sum_le_sum fun c _ => h2 c).trans ?_
    split_ifs with hx
    · obtain ⟨c0, rfl⟩ := hx
      rw [Finset.sum_eq_single c0]
      · rw [if_pos rfl]
      · intro c _ hc
        rw [if_neg fun he => hc (ch.injective he)]
      · intro hn; exact absurd (mem_univ _) hn
    · refine le_of_eq (Finset.sum_eq_zero fun c _ => if_neg fun he => hx ⟨c, he⟩)
  · -- on the paths
    refine le_trans (le_of_eq ?_) (paths_at hr hb hgR x)
    simp only [Fintype.sum_prod_type]
    rfl

omit hr hb hgR in
open Classical in
theorem NR0_succ {j : ℕ} (hj : j + 1 ≤ J) (x : T.X (j + 1)) : NR0 R ch FL lhat n o (nd T (j + 1) hj x) = 0 := by
  unfold NR0
  refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun c _ => Finset.sum_eq_zero fun γ _ =>
    Finset.sum_eq_zero fun s _ => Finset.sum_eq_zero fun q _ => if_neg ?_
  fin_cases q <;> exact nd_ne (hj := Nat.zero_le J) (Nat.succ_ne_zero j).symm

omit hr hb hgR in
open Classical in
theorem NR0_none : NR0 R ch FL lhat n o none = 0 := by
  unfold NR0
  refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun c _ => Finset.sum_eq_zero fun γ _ =>
    Finset.sum_eq_zero fun s _ => Finset.sum_eq_zero fun q _ => if_neg ?_
  fin_cases q <;> exact nd_ne_none (hj := Nat.zero_le J)

end Start

section Laws

variable (R ch FL lhat n o) in
open Classical in
/-- The number of units given in law moves at a node. -/
noncomputable def NL (P : Nd T) : ℕ := ∑ l : LMv T FL, ∑ f : T.Fl,
  if nd T (l.1 + 1) l.1.2 (atv l.1.2 l.2.1 l.2.2.1 f) = P then num R ch FL lhat n o (.inr l) else 0

variable (hh : 0 < h) (hr : 0 < r) (hb : 0 < b)
  (hgL : ∀ l : LMv T FL, GoodL R ch FL o l (num R ch FL lhat n o (.inr l)) ∧
    ∀ ν, num R ch FL lhat n o (.inr l) ≤ o ⟨.inr l, ν⟩)
  (hnr : ∀ f : T.Fl, ∃ ν, T.cN ν = f ∨ T.dN ν = f)
include hr hb hgL hnr

/-- The units of a law move lie on edges at its chambers. -/
theorem num_law_le (j : Fin J) (i : Fin h) (x : T.X (j + 1)) (d : FL.Di) :
    num R ch FL lhat n o (.inr ⟨j, i, T.vx i x, d⟩) ≤ fb (ldL R ch FL lhat n o) (j + 1) x := by
  classical
  set l : LMv T FL := ⟨j, i, T.vx i x, d⟩ with hl
  obtain ⟨ν, hν⟩ := hnr (T.co i x)
  set ν' : (FL.L d).Cn := (FL.cn d).symm ν with hν'
  have h1 : alv R ch FL lhat n o ⟨.inr l, ν'⟩ = o ⟨.inr l, ν'⟩ := by
    unfold alv
    have h2 : alvN R ch FL o ⟨.inr l, ν'⟩ (num R ch FL lhat n o (.inr l)) =
        if GoodL R ch FL o l (num R ch FL lhat n o (.inr l)) then o ⟨.inr l, ν'⟩ else
          min (o ⟨.inr l, ν'⟩) (num R ch FL lhat n o (.inr l)) := rfl
    rw [h2, if_pos (hgL l).1]
  set p := (T.nr j.2 i).symm (T.vx i x, ν) with hp
  have hp2 : T.nr j.2 i p = (T.vx i x, ν) := by rw [hp, Equiv.apply_symm_apply]
  have v0 := T.nr_vx0 j.2 i p
  have v1 := T.nr_vx1 j.2 i p
  have v2 := T.nr_co j.2 i p
  rw [hp2] at v0 v1 v2
  have hend : T.e0 p.1 = x ∨ T.e1 p.1 = x := by
    have h3 : T.co i x ∈ s(T.co i (T.e0 p.1), T.co i (T.e1 p.1)) := by
      rw [v2, Sym2.mem_iff]
      rcases hν with hν | hν
      · exact Or.inl hν.symm
      · exact Or.inr hν.symm
    rw [Sym2.mem_iff] at h3
    rcases h3 with h3 | h3
    · exact Or.inl ((T.vx_co j.2 i).1 (Prod.ext v0 h3.symm))
    · exact Or.inr ((T.vx_co j.2 i).1 (Prod.ext v1 h3.symm))
  have htg : tgM R ch FL (⟨.inr l, ν'⟩ : NM R FL (ch := ch)).1 ν' = .edge j.succ p.1 := by
    change Tg.edge j.succ ((T.nr j.2 i).symm (T.vx i x, FL.cn d ν')).1 = _
    rw [hν', Equiv.apply_symm_apply]
  have h4 := sum_alv_le (lhat := lhat) (n := n) (o := o) (.edge j.succ p.1) ({()} : Finset Unit)
    (fun _ => (⟨.inr l, ν'⟩ : NM R FL (ch := ch))) (fun _ _ _ _ _ => rfl) (fun _ _ => htg)
  rw [Finset.sum_singleton, h1] at h4
  refine ((hgL l).2 ν').trans (h4.trans ?_)
  rw [lev_succ]
  unfold fb Tower.bet
  refine le_trans ?_ (Finset.single_le_sum (f := fun e : T.Ed (j + 1) => if T.e0 e = x ∨ T.e1 e = x then
    ldL R ch FL lhat n o (j + 1) e else 0) (fun _ _ => Nat.zero_le _) (mem_univ p.1))
  rw [if_pos hend]

include hh

open Classical in
/-- Law moves at a chamber. -/
theorem NL_succ {k : ℕ} (hk : k + 1 ≤ J) (x : T.X (k + 1)) : NL R ch FL lhat n o (nd T (k + 1) hk x) ≤
    Fintype.card FL.Di * fb (ldL R ch FL lhat n o) (k + 1) x := by
  have h1 : NL R ch FL lhat n o (nd T (k + 1) hk x) = ∑ j : Fin J, ∑ y : T.X (j + 1),
      if nd T (j + 1) j.2 y = nd T (k + 1) hk x then
        ∑ i, ∑ d, num R ch FL lhat n o (.inr ⟨j, i, T.vx i y, d⟩) else 0 := by
    unfold NL
    rw [Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Fintype.sum_sigma]
    have h2 : ∀ i, (∑ p : T.V (j + 1) i × FL.Di, ∑ f : T.Fl,
        if nd T (j + 1) j.2 (atv j.2 i p.1 f) = nd T (k + 1) hk x then
          num R ch FL lhat n o (.inr ⟨j, i, p.1, p.2⟩) else 0) =
        ∑ y : T.X (j + 1), if nd T (j + 1) j.2 y = nd T (k + 1) hk x then
          ∑ d, num R ch FL lhat n o (.inr ⟨j, i, T.vx i y, d⟩) else 0 := by
      intro i
      rw [← Equiv.sum_comp (Equiv.ofBijective _ (T.vx_co j.2 i)).symm, Fintype.sum_prod_type, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun ω _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun f _ => ?_
      have h3 : (Equiv.ofBijective _ (T.vx_co j.2 i)).symm (ω, f) = atv j.2 i ω f := rfl
      rw [h3, atv_vx]
      split_ifs
      · rfl
      · simp
    rw [Finset.sum_congr rfl fun i _ => h2 i, Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => ?_
    split_ifs
    · rfl
    · simp
  rw [h1, sum_level_succ (fun j y => ∑ i, ∑ d, num R ch FL lhat n o (.inr ⟨j, i, T.vx i y, d⟩)) k hk x]
  set j : Fin J := ⟨k, hk⟩ with hj
  rw [Finset.sum_eq_single (imin hh (ldL R ch FL lhat n o) k)]
  · calc _ ≤ ∑ _d : FL.Di, fb (ldL R ch FL lhat n o) (k + 1) x :=
          Finset.sum_le_sum fun d _ => num_law_le hr hb hgL hnr j _ x d
      _ = _ := by rw [Finset.sum_const, card_univ, smul_eq_mul]
  · intro i _ hi
    refine Finset.sum_eq_zero fun d _ => ?_
    refine num_inr_zero hr hb (Or.inl fun hm => hi ?_)
    exact (isMin_iff hh _ j.castSucc i).1 hm
  · intro hn; exact absurd (mem_univ _) hn

omit hr hb hgL hnr hh in
open Classical in
theorem NL_zero (x : T.X 0) : NL R ch FL lhat n o (nd T 0 (Nat.zero_le _) x) = 0 := by
  unfold NL
  exact Finset.sum_eq_zero fun l _ => Finset.sum_eq_zero fun f _ => if_neg (nd_ne (Nat.succ_ne_zero _))

omit hr hb hgL hnr hh in
open Classical in
theorem NL_none : NL R ch FL lhat n o none = 0 := by
  unfold NL
  exact Finset.sum_eq_zero fun l _ => Finset.sum_eq_zero fun f _ => if_neg nd_ne_none

end Laws

section Final

variable (hh : 0 < h) (hr : 0 < r) (hb : 0 < b)
  (hgR : ∀ (x : {x : RM T m AA // okR T R ch x}) (ν : Bool), o ⟨.inl x, ν⟩ = num R ch FL lhat n o (.inl x))
include hh hr hb hgR

open Classical in
theorem NR_zero (x : T.X 0) : NR R ch FL lhat n o (nd T 0 (Nat.zero_le _) x) ≤
    (if ∃ c, ch c = x then 2 * m * lhat else 0) + 7 * fb (ldL R ch FL lhat n o) 0 x := by
  refine (NR_le hh hr hb hgR _).trans ?_
  have h1 := NR0_le hr hb hgR x
  have h2 := sum_level (fun j y => 5 * fb (ldL R ch FL lhat n o) j y) 0 (Nat.zero_le J) x
  have h3 := sum_level_zero (fun j y => 3 * chs hh (ldL R ch FL lhat n o) j y +
    2 * fb (ldL R ch FL lhat n o) (j + 1) y) x
  rw [h2, h3, if_neg nd_ne_none.symm]
  have h4 : (∑ y : T.X J, if nd T J le_rfl y = nd T 0 (Nat.zero_le _) x then fb (ldL R ch FL lhat n o) J y else 0) ≤
      fb (ldL R ch FL lhat n o) 0 x := by
    by_cases hJ : J = 0
    · subst hJ
      simp only [nd_inj]
      rw [Finset.sum_ite_eq', if_pos (mem_univ _)]
    · rw [Finset.sum_eq_zero]
      · exact Nat.zero_le _
      · intro y _
        rw [if_neg (nd_ne hJ)]
  have h5 : (if hlt : 0 < J then 5 * fb (ldL R ch FL lhat n o) 0 x else 0) ≤ 5 * fb (ldL R ch FL lhat n o) 0 x := by
    split_ifs
    · exact le_rfl
    · exact Nat.zero_le _
  have h6 : (if hlt : 0 < J then 5 * fb (ldL R ch FL lhat n o) (⟨0, hlt⟩ : Fin J) x else 0) =
      if hlt : 0 < J then 5 * fb (ldL R ch FL lhat n o) 0 x else 0 := rfl
  omega

open Classical in
theorem NR_succ {k : ℕ} (hk : k + 1 ≤ J) (x : T.X (k + 1)) : NR R ch FL lhat n o (nd T (k + 1) hk x) ≤
    8 * fb (ldL R ch FL lhat n o) (k + 1) x + 3 * chs hh (ldL R ch FL lhat n o) k x := by
  refine (NR_le hh hr hb hgR _).trans ?_
  have h1 : NR0 R ch FL lhat n o (nd T (k + 1) hk x) = 0 := NR0_succ hk x
  have h2 := sum_level (fun j y => 5 * fb (ldL R ch FL lhat n o) j y) (k + 1) hk x
  have h3 := sum_level_succ (fun j y => 3 * chs hh (ldL R ch FL lhat n o) j y +
    2 * fb (ldL R ch FL lhat n o) (j + 1) y) k hk x
  rw [h1, h2, h3, if_neg nd_ne_none.symm]
  have h4 : (∑ y : T.X J, if nd T J le_rfl y = nd T (k + 1) hk x then fb (ldL R ch FL lhat n o) J y else 0) ≤
      fb (ldL R ch FL lhat n o) (k + 1) x := by
    by_cases hJ : J = k + 1
    · subst hJ
      simp only [nd_inj]
      rw [Finset.sum_ite_eq', if_pos (mem_univ _)]
    · rw [Finset.sum_eq_zero]
      · exact Nat.zero_le _
      · intro y _
        rw [if_neg (nd_ne hJ)]
  have h5 : (if hlt : k + 1 < J then 5 * fb (ldL R ch FL lhat n o) (⟨k + 1, hlt⟩ : Fin J) x else 0) ≤
      5 * fb (ldL R ch FL lhat n o) (k + 1) x := by
    split_ifs
    · exact le_rfl
    · exact Nat.zero_le _
  have h6 : 3 * chs hh (ldL R ch FL lhat n o) (⟨k, hk⟩ : Fin J) x + 2 * fb (ldL R ch FL lhat n o) ((⟨k, hk⟩ : Fin J) + 1) x =
      3 * chs hh (ldL R ch FL lhat n o) k x + 2 * fb (ldL R ch FL lhat n o) (k + 1) x := rfl
  omega

open Classical in
theorem NR_none : NR R ch FL lhat n o none ≤ ∑ e : T.Ed J, ldL R ch FL lhat n o J e := by
  refine (NR_le hh hr hb hgR _).trans ?_
  have h1 : NR0 R ch FL lhat n o none = 0 := NR0_none
  have h2 : (∑ j : Fin J, ∑ y : T.X j, if nd T j j.2.le y = none then 5 * fb (ldL R ch FL lhat n o) j y else 0) = 0 :=
    Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun y _ => if_neg nd_ne_none
  have h3 : (∑ j : Fin J, ∑ y : T.X (j + 1), if nd T (j + 1) j.2 y = none then
      3 * chs hh (ldL R ch FL lhat n o) j y + 2 * fb (ldL R ch FL lhat n o) (j + 1) y else 0) = 0 :=
    Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun y _ => if_neg nd_ne_none
  have h4 : (∑ y : T.X J, if nd T J le_rfl y = none then fb (ldL R ch FL lhat n o) J y else 0) = 0 :=
    Finset.sum_eq_zero fun y _ => if_neg nd_ne_none
  rw [h1, h2, h3, h4, if_pos rfl]
  omega

end Final

end Nc.Tow
