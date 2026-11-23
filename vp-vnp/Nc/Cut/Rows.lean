/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Cut.Defs

/-!
# Row data of a staircase, and strings of segments

A matrix of words with staircase support has exactly one valid sequence of row data; valid row data imply
staircase support. The string of the segments between two parties determines the segments.
-/

set_option linter.unusedSectionVars false

namespace Nc.Cut

open Finset

section Rows

variable {Γ : Type} {A : ℕ}

/-- The row data on one tape are those of a staircase, row `p`. -/
def ValidRow (ρ : Fin A → RowData A) (p : Fin A) : Prop :=
  if (ρ p).1 then (ρ p).2.1.1 = prevHi ρ p ∧ (ρ p).2.2.1 = prevHi ρ p
  else prevHi ρ p ≤ (ρ p).2.1.1 ∧ (ρ p).2.1 ≤ (ρ p).2.2

theorem ValidRow.prev_le {ρ : Fin A → RowData A} {p : Fin A} (h : ValidRow ρ p) : prevHi ρ p ≤ (ρ p).2.2.1 := by
  unfold ValidRow at h
  split_ifs at h with hc
  · exact h.2.ge
  · exact h.1.trans h.2

theorem hi_le_prevHi {ρ : Fin A → RowData A} (h : ∀ p, ValidRow ρ p) {p p' : Fin A} (hp : p < p') :
    (ρ p).2.2.1 ≤ prevHi ρ p' := by
  obtain ⟨p', hp'⟩ := p'
  have hlt : p.1 < p' := hp
  clear hp
  induction p' with
  | zero => omega
  | succ q ih =>
    have e : prevHi ρ ⟨q + 1, hp'⟩ = (ρ ⟨q, Nat.lt_of_succ_lt hp'⟩).2.2.1 := by
      rw [prevHi, dif_neg (Nat.succ_ne_zero q)]
      rfl
    rw [e]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hlt with h1 | h1
    · exact (ih (Nat.lt_of_succ_lt hp') h1).trans (h _).prev_le
    · have : p = ⟨q, Nat.lt_of_succ_lt hp'⟩ := Fin.ext h1
      rw [this]

theorem RowOk.flag {d : RowData A} {X : Fin A → List Γ} (h : RowOk d X) {b : Fin A} (hb : X b ≠ []) :
    d.1 = false := by
  by_contra hc
  rw [Bool.not_eq_false] at hc
  rw [RowOk, if_pos hc] at h
  exact hb (h b)

/-- Valid row data imply staircase support. -/
theorem stair_of_rows {ρ : Fin A → RowData A} (h : ∀ p, ValidRow ρ p) {X : Fin A → Fin A → List Γ}
    (hX : ∀ p, RowOk (ρ p) (X p)) : Stair X := by
  intro a a' b b' hb hb' hlt
  have f := (hX a).flag hb
  have f' := (hX a').flag hb'
  have r := hX a
  have r' := hX a'
  have v' := h a'
  rw [RowOk, if_neg (by simp [f])] at r
  rw [RowOk, if_neg (by simp [f'])] at r'
  rw [ValidRow, if_neg (by simp [f'])] at v'
  have h1 := (r.2.2 b hb).2
  have h2 := hi_le_prevHi h hlt
  have h3 := (r'.2.2 b' hb').1
  rw [Fin.le_def] at *
  omega

/-- The largest column that is used in a row before row `q`. -/
noncomputable def hiBefore (X : Fin A → Fin A → List Γ) (q : ℕ) : ℕ :=
  open Classical in (univ.filter fun z : Fin A × Fin A => z.1.1 < q ∧ X z.1 z.2 ≠ []).sup fun z => z.2.1

theorem le_hiBefore {X : Fin A → Fin A → List Γ} {q : ℕ} {p b : Fin A} (hp : p.1 < q) (hb : X p b ≠ []) :
    b.1 ≤ hiBefore X q := by
  classical
  exact Finset.le_sup (f := fun z : Fin A × Fin A => z.2.1) (b := (p, b))
    (Finset.mem_filter.2 ⟨Finset.mem_univ _, hp, hb⟩)

theorem hiBefore_le {X : Fin A → Fin A → List Γ} {q c : ℕ} (h : ∀ p b : Fin A, p.1 < q → X p b ≠ [] → b.1 ≤ c) :
    hiBefore X q ≤ c := by
  classical
  refine Finset.sup_le fun z hz => ?_
  have := (Finset.mem_filter.1 hz).2
  exact h _ _ this.1 this.2

theorem exists_rows {X : Fin A → Fin A → List Γ} (hX : Stair X) :
    ∃ ρ : Fin A → RowData A, (∀ p, ValidRow ρ p) ∧ ∀ p, RowOk (ρ p) (X p) := by
  classical
  have hlt : ∀ (p : Fin A) q, hiBefore X q < A := by
    intro p q
    have : hiBefore X q ≤ A - 1 := hiBefore_le fun p b _ _ => by omega
    have := p.2
    omega
  have hrow : ∀ p : Fin A, ∃ d : RowData A, RowOk d (X p) ∧ d.2.2.1 = hiBefore X (p.1 + 1) ∧
      (if d.1 then d.2.1.1 = hiBefore X p.1 ∧ d.2.2.1 = hiBefore X p.1
        else hiBefore X p.1 ≤ d.2.1.1 ∧ d.2.1 ≤ d.2.2) := by
    intro p
    by_cases he : ∀ b, X p b = []
    · refine ⟨(true, ⟨hiBefore X p.1, hlt p _⟩, ⟨hiBefore X p.1, hlt p _⟩), ?_, ?_, ?_⟩
      · simpa [RowOk] using he
      · apply le_antisymm
        · exact hiBefore_le fun p' b hp' hb => le_hiBefore (Nat.lt_succ_of_lt hp') hb
        · refine hiBefore_le fun p' b hp' hb => ?_
          rcases Nat.lt_succ_iff_lt_or_eq.1 hp' with h1 | h1
          · exact le_hiBefore h1 hb
          · have : p' = p := Fin.ext h1
            subst this
            exact absurd (he b) hb
      · simp
    · push Not at he
      obtain ⟨b0, hb0⟩ := he
      have hne : (univ.filter fun b => X p b ≠ []).Nonempty := ⟨b0, by simpa using hb0⟩
      have hmin := Finset.min'_mem _ hne
      have hmax := Finset.max'_mem _ hne
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmin hmax
      refine ⟨(false, Finset.min' _ hne, Finset.max' _ hne), ?_, ?_, ?_⟩
      · simp only [RowOk, Bool.false_eq_true, if_false]
        refine ⟨hmin, hmax, fun b hb => ⟨Finset.min'_le _ _ (by simpa using hb), Finset.le_max' _ _ (by simpa using hb)⟩⟩
      · apply le_antisymm
        · exact le_hiBefore (Nat.lt_succ_self _) hmax
        · refine hiBefore_le fun p' b hp' hb => ?_
          rcases Nat.lt_succ_iff_lt_or_eq.1 hp' with h1 | h1
          · exact hX p' p b _ hb hmax h1
          · have : p' = p := Fin.ext h1
            subst this
            have hm : b ∈ univ.filter fun b => X p' b ≠ [] := by simpa using hb
            exact Finset.le_max' _ _ hm
      · simp only [Bool.false_eq_true, if_false]
        exact ⟨hiBefore_le fun p' b hp' hb => hX p' p b _ hb hmin hp', Finset.min'_le _ _ (by simpa using hmax)⟩
  choose ρ h1 h2 h3 using hrow
  have hprev : ∀ p, prevHi ρ p = hiBefore X p.1 := by
    intro p
    rw [prevHi]
    split_ifs with h
    · rw [h]
      symm
      apply Nat.le_zero.1
      exact hiBefore_le fun p' b hp' _ => by omega
    · rw [h2]
      congr 1
      show p.1 - 1 + 1 = p.1
      omega
  refine ⟨ρ, fun p => ?_, h1⟩
  rw [ValidRow, hprev]
  exact h3 p

theorem rows_unique {X : Fin A → Fin A → List Γ} {ρ ρ' : Fin A → RowData A} (h : ∀ p, ValidRow ρ p)
    (h' : ∀ p, ValidRow ρ' p) (hX : ∀ p, RowOk (ρ p) (X p)) (hX' : ∀ p, RowOk (ρ' p) (X p)) : ρ = ρ' := by
  have key : ∀ (q : ℕ) (hq : q < A), ρ ⟨q, hq⟩ = ρ' ⟨q, hq⟩ := by
    intro q
    induction q with
    | zero =>
      intro hq
      exact row_eq h h' hX hX' rfl
    | succ q ih =>
      intro hq
      apply row_eq h h' hX hX'
      rw [prevHi, prevHi, dif_neg (Nat.succ_ne_zero q), dif_neg (Nat.succ_ne_zero q)]
      have := ih (Nat.lt_of_succ_lt hq)
      show (ρ ⟨q, _⟩).2.2.1 = (ρ' ⟨q, _⟩).2.2.1
      rw [this]
  exact funext fun p => key p.1 p.2
where
  row_eq {X : Fin A → Fin A → List Γ} {ρ ρ' : Fin A → RowData A} (h : ∀ p, ValidRow ρ p)
      (h' : ∀ p, ValidRow ρ' p) (hX : ∀ p, RowOk (ρ p) (X p)) (hX' : ∀ p, RowOk (ρ' p) (X p)) {p : Fin A}
      (hp : prevHi ρ p = prevHi ρ' p) : ρ p = ρ' p := by
    have v := h p
    have v' := h' p
    have r := hX p
    have r' := hX' p
    rw [ValidRow] at v v'
    by_cases he : ∀ b, X p b = []
    · have f : (ρ p).1 = true := by
        by_contra hc
        rw [RowOk, if_neg hc] at r
        exact r.1 (he _)
      have f' : (ρ' p).1 = true := by
        by_contra hc
        rw [RowOk, if_neg hc] at r'
        exact r'.1 (he _)
      rw [if_pos f] at v
      rw [if_pos f'] at v'
      refine Prod.ext (f.trans f'.symm) (Prod.ext (Fin.ext ?_) (Fin.ext ?_))
      · rw [v.1, v'.1, hp]
      · rw [v.2, v'.2, hp]
    · push Not at he
      obtain ⟨b, hb⟩ := he
      have f := r.flag hb
      have f' := r'.flag hb
      rw [RowOk, if_neg (by simp [f])] at r
      rw [RowOk, if_neg (by simp [f'])] at r'
      refine Prod.ext (f.trans f'.symm) (Prod.ext ?_ ?_)
      · exact le_antisymm (r.2.2 _ r'.1).1 (r'.2.2 _ r.1).1
      · exact le_antisymm (r'.2.2 _ r.2.1).2 (r.2.2 _ r'.2.1).2

end Rows

section Strings

variable {Γ S : Type} [Fintype S] [DecidableEq S]

theorem flatMap_sep_inj {σ : Type} (l : List σ) {X X' : σ → List Γ}
    (h : (l.flatMap fun s => (X s).map some ++ [none]) = l.flatMap fun s => (X' s).map some ++ [none]) :
    ∀ s ∈ l, X s = X' s := by
  have sep : ∀ (w w' : List Γ) (r r' : List (Option Γ)), w.map some ++ (none :: r) = w'.map some ++ (none :: r') →
      w = w' ∧ r = r' := by
    intro w
    induction w with
    | nil =>
      intro w' r r' h
      cases w' with
      | nil => simpa using h
      | cons a w' => simp at h
    | cons a w ih =>
      intro w' r r' h
      cases w' with
      | nil => simp at h
      | cons a' w' =>
        simp only [List.map_cons, List.cons_append, List.cons.injEq, Option.some.injEq] at h
        obtain ⟨e1, e2⟩ := ih w' r r' h.2
        exact ⟨by rw [h.1, e1], e2⟩
  induction l with
  | nil => simp
  | cons s l ih =>
    simp only [List.flatMap_cons, List.append_assoc, List.singleton_append] at h
    obtain ⟨e1, e2⟩ := sep _ _ _ _ h
    intro s' hs'
    rcases List.mem_cons.1 hs' with rfl | hs'
    · exact e1
    · exact ih e2 s' hs'

theorem joinSeg_inj {X X' : Option S → List Γ} (h : joinSeg X = joinSeg X') : X = X' :=
  funext fun s => flatMap_sep_inj _ h s (Finset.mem_toList.2 (Finset.mem_univ s))

theorem length_joinSeg (X : Option S → List Γ) :
    (joinSeg X).length = ∑ s, (X s).length + (Fintype.card S + 1) := by
  have : ∀ l : List (Option S), (l.flatMap fun s => (X s).map some ++ [none]).length =
      (l.map fun s => (X s).length).sum + l.length := by
    intro l
    induction l with
    | nil => simp
    | cons s l ih =>
      simp only [List.flatMap_cons, List.length_append, ih, List.length_map, List.length_nil,
        List.map_cons, List.sum_cons, List.length_cons]
      omega
  rw [joinSeg, this, Finset.length_toList, Finset.card_univ, Fintype.card_option]
  congr 1
  exact Finset.sum_map_toList _ _

variable {c : ℕ} {cb : Option Γ → Fin c → Bool}

theorem strOf_inj (hcb : Function.Injective cb) (hc : 0 < c) {X X' : Option S → List Γ}
    (h : strOf cb X = strOf cb X') : X = X' :=
  joinSeg_inj (bitsOf_inj hcb hc h)

theorem length_strOf (X : Option S → List Γ) :
    (strOf cb X).length = (∑ s, (X s).length + (Fintype.card S + 1)) * c := by
  rw [strOf, length_bitsOf, length_joinSeg]

end Strings

end Nc.Cut
