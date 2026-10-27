/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import CircuitLowerBound.Tab.Frame
import Mathlib.Tactic

/-! # The circuit lower bound for E^NP (Section 7): the conditions on the rows are the shifts of a table

`table N` lists, with atoms as kinds, a 3-literal clause for each condition of `Spec`; all its
shifts hold iff the conditions do (`spec_of_table`, `table_of_spec`). `stSpecTab` numbers the atoms. -/

public section

namespace CircuitLowerBound.Tab

open ENP Turing

variable (N : TM2ComputableAux Bool Bool)

/-- A literal with an atom as its kind. -/
abbrev YLit : Type := Atom N × ℕ × ℕ × ℕ × Bool

/-- A clause of three such literals. -/
abbrev YCl : Type := YLit N × YLit N × YLit N

variable {N}

/-- The literal holds in the shift by (t, q). -/
def holdsY (α : Atom N → ℕ → ℕ → Bool) (b P t q : ℕ) (l : YLit N) : Prop := α l.1 (tval b t l.2.1) (qval P q l.2.2.1 + l.2.2.2.1) = l.2.2.2.2

/-- The clause holds in all shifts. -/
def HoldsC (α : Atom N → ℕ → ℕ → Bool) (b Q P : ℕ) (c : YCl N) : Prop :=
  ∀ t < 2 ^ b, ∀ q < 2 ^ Q, holdsY α b P t q c.1 ∨ holdsY α b P t q c.2.1 ∨ holdsY α b P t q c.2.2

def c1 (l : YLit N) : YCl N := (l, l, l)
def c2 (l l' : YLit N) : YCl N := (l, l', l')
/-- A clause that always holds. -/
def taut : YCl N := ((.u, 0, 0, 0, false), (.u, 0, 0, 0, true), (.u, 0, 0, 0, true))

theorem tval0 (b t : ℕ) : tval b t 0 = 0 := by simp [tval]
theorem tval1 (b t : ℕ) : tval b t 1 = t := by simp [tval]
theorem tval2 (b t : ℕ) : tval b t 2 = t + 1 := by simp [tval]
theorem tval3 (b t : ℕ) : tval b t 3 = 2 ^ b := by simp [tval]
theorem qval0 (P q : ℕ) : qval P q 0 = 0 := by simp [qval]
theorem qval1 (P q : ℕ) : qval P q 1 = q := by simp [qval]
theorem qval2 (P q : ℕ) : qval P q 2 = P := by simp [qval]

theorem holdsC_taut (α : Atom N → ℕ → ℕ → Bool) (b Q P : ℕ) : HoldsC α b Q P taut := by
  intro t _ q _
  simp only [taut, holdsY]
  cases α .u (tval b t 0) (qval P q 0 + 0) <;> simp

/-- The elements of a finite type as a list. -/
noncomputable def en (ι : Type) [Finite ι] : List ι := (@Finset.univ ι (Fintype.ofFinite ι)).toList

theorem mem_en {ι : Type} [Finite ι] (i : ι) : i ∈ en ι := by simp [en]

/-- A family of clauses over a finite type as a list. -/
noncomputable def fam {ι : Type} [Finite ι] (f : ι → YCl N) : List (YCl N) := (en ι).map f

theorem forall_fam {ι : Type} [Finite ι] {f : ι → YCl N} {p : YCl N → Prop} : (∀ c ∈ fam f, p c) ↔ ∀ i, p (f i) := by
  simp [fam, mem_en]

theorem forall_flatten {β : Type} {p : β → Prop} {Ls : List (List β)} : (∀ c ∈ Ls.flatten, p c) ↔ ∀ l ∈ Ls, ∀ c ∈ l, p c := by
  simp only [List.mem_flatten]
  exact ⟨fun h l hl c hc => h c ⟨l, hl, hc⟩, fun h c ⟨l, hl, hc⟩ => h l hl c hc⟩

variable (N) [Finite (Case N)] [∀ k, Finite (N.tm.Γ k)]

open Classical in
/-- The table, with atoms as kinds. -/
noncomputable def table : List (YCl N) := List.flatten [
  [c1 (.pre (Fin.last _), 1, 0, 0, true)],
  [c1 (.pre 0, 1, 0, 0, false)],
  fam fun i : Fin (nc N) => ((.pre i.succ, 1, 0, 0, false), (.pre i.castSucc, 1, 0, 0, true), (.cs ((ec N).symm i), 1, 0, 0, true)),
  fam fun γ : Case N => c2 (.cs γ, 1, 0, 0, false) (.lab γ.1, 1, 0, 0, true),
  fam fun γ : Case N => c2 (.cs γ, 1, 0, 0, false) (.var γ.2.1, 1, 0, 0, true),
  fam fun p : Case N × N.tm.K × Fin (dep N) => c2 (.cs p.1, 1, 0, 0, false) (.cell p.2.1 (p.1.2.2 p.2.1 p.2.2), 1, 0, p.2.2, true),
  fam fun p : Case N × Option N.tm.Λ => c2 (.cs p.1, 1, 0, 0, false) (.lab p.2, 2, 0, 0, decide (p.2 = (nxt N p.1).l)),
  fam fun p : Case N × N.tm.σ => c2 (.cs p.1, 1, 0, 0, false) (.var p.2, 2, 0, 0, decide (p.2 = (nxt N p.1).var)),
  fam fun p : Case N × N.tm.K × Fin (2 * dep N + 1) =>
    c2 (.cs p.1, 1, 0, 0, false) (.len p.2.1 p.2.2, 1, 0, 0, decide ((p.2.2 : ℕ) = ((nxt N p.1).stk p.2.1).length)),
  fam fun p : Case N × (Σ k, Option (N.tm.Γ k)) × Fin (2 * dep N) =>
    if (p.2.2 : ℕ) < ((nxt N p.1).stk p.2.1.1).length then
      c2 (.cs p.1, 1, 0, 0, false) (.cell p.2.1.1 p.2.1.2, 2, 0, p.2.2, decide (p.2.1.2 = ((nxt N p.1).stk p.2.1.1)[(p.2.2 : ℕ)]?))
    else taut,
  fam fun p : (Σ k, Option (N.tm.Γ k)) × Fin (2 * dep N + 1) =>
    ((.len p.1.1 p.2, 1, 0, 0, false), (.cell p.1.1 p.1.2, 2, 1, p.2, false), (.cell p.1.1 p.1.2, 1, 1, dep N, true)),
  fam fun p : (Σ k, Option (N.tm.Γ k)) × Fin (2 * dep N + 1) =>
    ((.len p.1.1 p.2, 1, 0, 0, false), (.cell p.1.1 p.1.2, 2, 1, p.2, true), (.cell p.1.1 p.1.2, 1, 1, dep N, false)),
  fam fun x : Option N.tm.Λ => c1 (.lab x, 0, 0, 0, decide (x = some N.tm.main)),
  fam fun x : N.tm.σ => c1 (.var x, 0, 0, 0, decide (x = N.tm.initialState)),
  fam fun p : Σ k, Option (N.tm.Γ k) => if p.1 ≠ N.tm.k₀ then c1 (.cell p.1 p.2, 0, 1, 0, decide (p.2 = none)) else taut,
  [((.cell N.tm.k₀ none, 0, 1, 0, true), (.cell N.tm.k₀ (some (N.inputAlphabet.symm false)), 0, 1, 0, true), (.cell N.tm.k₀ (some (N.inputAlphabet.symm true)), 0, 1, 0, true))],
  fam fun p : Option (N.tm.Γ N.tm.k₀) × Option (N.tm.Γ N.tm.k₀) =>
    if p.1 ≠ p.2 then c2 (.cell N.tm.k₀ p.1, 0, 1, 0, false) (.cell N.tm.k₀ p.2, 0, 1, 0, false) else taut,
  [c2 (.cell N.tm.k₀ none, 0, 1, 0, false) (.cell N.tm.k₀ none, 0, 1, 1, true)],
  [c2 (.u, 0, 1, 1, false) (.u, 0, 1, 0, true)],
  [c1 (.u, 0, 2, 0, true)],
  [c1 (.u, 0, 2, 1, false)],
  [c2 (.u, 0, 1, 1, false) (.cell N.tm.k₀ (some (N.inputAlphabet.symm true)), 0, 1, 0, true)],
  [c1 (.cell N.tm.k₀ (some (N.inputAlphabet.symm false)), 0, 2, 0, true)],
  [c1 (.lab none, 3, 0, 0, true)],
  [c1 (.var N.tm.initialState, 3, 0, 0, true)],
  [c1 (.cell N.tm.k₁ (some (N.outputAlphabet.symm true)), 3, 0, 0, true)],
  [c1 (.cell N.tm.k₁ none, 3, 0, 1, true)],
  fam fun k : N.tm.K => if k ≠ N.tm.k₁ then c1 (.cell k none, 3, 0, 0, true) else taut]

variable {N}

theorem bool_imp {x : Bool} {p : Prop} : (x = false ∨ p ∨ p) ↔ (x = true → p) := by cases x <;> simp

theorem bool_dec {y : Bool} {p : Prop} [Decidable p] : y = decide p ↔ (y = true ↔ p) := by
  by_cases hp : p <;> cases y <;> simp [hp]

theorem bool_copy {x y z : Bool} : ((x = false ∨ y = false ∨ z = true) ∧ (x = false ∨ y = true ∨ z = false)) ↔ (x = true → y = z) := by
  cases x <;> cases y <;> cases z <;> simp

theorem or_self3 {p : Prop} : (p ∨ p ∨ p) ↔ p := by tauto

/-- If all shifts of the clauses of the table hold, the conditions hold. -/
theorem spec_of_table {α : Atom N → ℕ → ℕ → Bool} {b Q P : ℕ} (H : ∀ c ∈ table N, HoldsC α b Q P c) : Spec N α b Q P := by
  classical
  have hQ : 0 < 2 ^ Q := by positivity
  have hb : 0 < 2 ^ b := by positivity
  simp only [table, forall_flatten, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, forall_fam] at H
  revert H
  · rintro ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24, a25, a26, a27, a28⟩
    simp only [HoldsC, holdsY, c1, c2, tval0, tval1, tval2, tval3, qval0, qval1, qval2, Nat.zero_add, Nat.add_zero, bool_imp, bool_dec, or_self3]
      at a1 a2 a3 a4 a5 a6 a7 a8 a9 a11 a12 a13 a14 a16 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27
    exact
      { preTop := fun t ht => a1 t ht 0 hQ
        preBot := fun t ht => a2 t ht 0 hQ
        preStep := fun t ht i => a3 i t ht 0 hQ
        csLab := fun t ht γ => a4 γ t ht 0 hQ
        csVar := fun t ht γ => a5 γ t ht 0 hQ
        csCell := fun t ht γ k j => a6 (γ, k, j) t ht 0 hQ
        nxLab := fun t ht γ x => a7 (γ, x) t ht 0 hQ
        nxVar := fun t ht γ x => a8 (γ, x) t ht 0 hQ
        nxLen := fun t ht γ k n => a9 (γ, k, n) t ht 0 hQ
        nxCell := fun t ht γ k x j hj => by
          have hj2 : j < 2 * dep N := lt_of_lt_of_le hj (length_nxt_le N γ k)
          have := a10 (γ, ⟨k, x⟩, ⟨j, hj2⟩)
          rw [if_pos hj] at this
          simpa only [HoldsC, holdsY, c2, tval1, tval2, qval0, Nat.zero_add, bool_imp, bool_dec] using this t ht 0 hQ
        copy := fun t ht q hq k n x => bool_copy.1 ⟨a11 (⟨k, x⟩, n) t ht q hq, a12 (⟨k, x⟩, n) t ht q hq⟩
        iLab := fun x => a13 x 0 hb 0 hQ
        iVar := fun x => a14 x 0 hb 0 hQ
        iCell := fun q hq k hk x => by
          have := a15 ⟨k, x⟩
          rw [if_pos hk] at this
          simpa only [HoldsC, holdsY, c1, tval0, qval1, Nat.add_zero, or_self3, bool_dec] using this 0 hb q hq
        iSome := fun q hq => a16 0 hb q hq
        iMost := fun q hq x x' hne => by
          have := a17 (x, x')
          rw [if_pos hne] at this
          have := this 0 hb q hq
          simp only [holdsY, c2, tval0, qval1, Nat.add_zero] at this
          tauto
        iBlank := fun q hq => a18 0 hb q hq
        uStep := fun q hq => a19 0 hb q hq
        uP := a20 0 hb 0 hQ
        uP1 := a21 0 hb 0 hQ
        uOne := fun q hq => a22 0 hb q hq
        cellP := a23 0 hb 0 hQ
        fLab := a24 0 hb 0 hQ
        fVar := a25 0 hb 0 hQ
        fOut0 := a26 0 hb 0 hQ
        fOut1 := a27 0 hb 0 hQ
        fOther := fun k hk => by
          have := a28 k
          rw [if_pos hk] at this
          simpa only [HoldsC, holdsY, c1, tval3, qval0, Nat.add_zero, or_self3] using this 0 hb 0 hQ }

/-- If the conditions hold, all shifts of the clauses of the table hold. -/
theorem table_of_spec {α : Atom N → ℕ → ℕ → Bool} {b Q P : ℕ} (h : Spec N α b Q P) : ∀ c ∈ table N, HoldsC α b Q P c := by
  classical
  simp only [table, forall_flatten, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, forall_fam]
  · simp only [HoldsC, holdsY, c1, c2, tval0, tval1, tval2, tval3, qval0, qval1, qval2, Nat.zero_add, Nat.add_zero, bool_imp, bool_dec, or_self3]
    refine ⟨fun t ht _ _ => h.preTop t ht, fun t ht _ _ => h.preBot t ht, fun i t ht _ _ => h.preStep t ht i, fun γ t ht _ _ => h.csLab t ht γ,
      fun γ t ht _ _ => h.csVar t ht γ, fun p t ht _ _ => h.csCell t ht p.1 p.2.1 p.2.2, fun p t ht _ _ => h.nxLab t ht p.1 p.2,
      fun p t ht _ _ => h.nxVar t ht p.1 p.2, fun p t ht _ _ => h.nxLen t ht p.1 p.2.1 p.2.2, fun p => ?_, fun p t ht q hq => ?_, fun p t ht q hq => ?_,
      fun x _ _ _ _ => h.iLab x, fun x _ _ _ _ => h.iVar x, fun p => ?_, fun _ _ q hq => h.iSome q hq, fun p => ?_, fun _ _ q hq => h.iBlank q hq,
      fun _ _ q hq => h.uStep q hq, fun _ _ _ _ => h.uP, fun _ _ _ _ => h.uP1, fun _ _ q hq => h.uOne q hq, fun _ _ _ _ => h.cellP,
      fun _ _ _ _ => h.fLab, fun _ _ _ _ => h.fVar, fun _ _ _ _ => h.fOut0, fun _ _ _ _ => h.fOut1, fun k => ?_⟩
    · split_ifs with hj
      · intro t ht q _
        simp only [tval1, tval2, qval0, Nat.zero_add, bool_imp, bool_dec]
        exact h.nxCell t ht p.1 p.2.1.1 p.2.1.2 p.2.2 hj
      · exact holdsC_taut α b Q P
    · exact (bool_copy.2 (h.copy t ht q hq p.1.1 p.2 p.1.2)).1
    · exact (bool_copy.2 (h.copy t ht q hq p.1.1 p.2 p.1.2)).2
    · split_ifs with hk
      · intro t _ q hq
        simp only [tval0, qval1, Nat.add_zero, or_self3, bool_dec]
        exact h.iCell q hq p.1 hk p.2
      · exact holdsC_taut α b Q P
    · split_ifs with hne
      · intro t _ q hq
        simp only [tval0, qval1, Nat.add_zero]
        have := h.iMost q hq p.1 p.2 hne
        tauto
      · exact holdsC_taut α b Q P
    · split_ifs with hk
      · intro t _ q _
        simp only [tval3, qval0, Nat.add_zero, or_self3]
        exact h.fOther k hk
      · exact holdsC_taut α b Q P

/-- The numbers added to positions are at most 2d. -/
theorem table_dq : ∀ c ∈ table N, c.1.2.2.2.1 ≤ 2 * dep N ∧ c.2.1.2.2.2.1 ≤ 2 * dep N ∧ c.2.2.2.2.2.1 ≤ 2 * dep N := by
  classical
  have hd := one_le_dep N
  simp only [table, forall_flatten, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, forall_fam]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  case refine_6 => intro p; have := p.2.2.isLt; simp only [c2]; omega
  case refine_10 => intro p; have := p.2.2.isLt; split_ifs <;> simp only [c2, taut] <;> omega
  case refine_11 => intro p; have := p.2.isLt; omega
  case refine_12 => intro p; have := p.2.isLt; omega
  all_goals (intros; (try split_ifs) <;> (try simp only [c1, c2, taut]) <;> omega)

instance : Finite (Atom N) := by
  let f : Atom N → Option N.tm.Λ ⊕ N.tm.σ ⊕ (N.tm.K × Fin (2 * dep N + 1)) ⊕ (Σ k, Option (N.tm.Γ k)) ⊕ Case N ⊕ Fin (nc N + 1) ⊕ Unit := fun a =>
    match a with
    | .lab l => .inl l
    | .var v => .inr (.inl v)
    | .len k n => .inr (.inr (.inl (k, n)))
    | .cell k x => .inr (.inr (.inr (.inl ⟨k, x⟩)))
    | .cs γ => .inr (.inr (.inr (.inr (.inl γ))))
    | .pre i => .inr (.inr (.inr (.inr (.inr (.inl i)))))
    | .u => .inr (.inr (.inr (.inr (.inr (.inr ())))))
  refine Finite.of_injective f fun a a' h => ?_
  cases a <;> cases a' <;> simp only [f, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, Prod.mk.injEq, Sigma.mk.injEq] at h
  · rw [h]
  · rw [h]
  · rw [h.1, h.2]
  · obtain ⟨rfl, h⟩ := h; rw [eq_of_heq h]
  · rw [h]
  · rw [h]
  · rfl

/-- The number of an atom: at least 1. -/
noncomputable def num (a : Atom N) : ℕ := (Finite.equivFin (Atom N) a : ℕ) + 1

theorem num_injective : Function.Injective (num (N := N)) := fun a a' h =>
  (Finite.equivFin (Atom N)).injective (Fin.ext (by simpa [num] using h))

/-- A literal with the number of its atom as kind. -/
noncomputable def nl (l : YLit N) : TLit := (num l.1, l.2)

variable (N) in
/-- The table with numbers as kinds. -/
noncomputable def codeTab : MCode := (Nat.size (Nat.card (Atom N) + 1), lamOf N, (table N).map fun c => (nl c.1, nl c.2.1, nl c.2.2))

end CircuitLowerBound.Tab

namespace CircuitLowerBound

open Tab Turing

/-- The conditions are the shifts of a table. -/
theorem stSpecTab : StSpecTab := by
  intro N _ hfin
  have : ∀ k, Finite (N.tm.Γ k) := hfin
  refine ⟨codeTab N, ?_, rfl, fun b Q P => ?_⟩
  · intro c hc l hl
    obtain ⟨c', hc', rfl⟩ := List.mem_map.1 hc
    have hdq := table_dq c' hc'
    have hlam : 2 * dep N + 2 < 2 ^ lamOf N := Nat.lt_size_self _
    have hnum : ∀ a : Atom N, 1 ≤ num a ∧ num a < 2 ^ kb (codeTab N) := fun a =>
      ⟨by simp [num], lt_trans (by have := (Finite.equivFin (Atom N) a).isLt; simp only [num]; omega) (Nat.lt_size_self _)⟩
    have hl' : lam (codeTab N) = lamOf N := rfl
    simp only [lits, List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl | rfl
    · exact ⟨(hnum _).1, (hnum _).2, by rw [hl']; simp only [nl]; omega⟩
    · exact ⟨(hnum _).1, (hnum _).2, by rw [hl']; simp only [nl]; omega⟩
    · exact ⟨(hnum _).1, (hnum _).2, by rw [hl']; simp only [nl]; omega⟩
  · have key : ∀ (β : ℕ → ℕ → ℕ → Bool) (α : Atom N → ℕ → ℕ → Bool), (∀ a t q, β (num a) t q = α a t q) →
        ((∀ c ∈ tab (codeTab N), ∀ t < 2 ^ b, ∀ q < 2 ^ Q, ∃ l ∈ lits c, holdsT β b P t q l) ↔ ∀ c ∈ table N, HoldsC α b Q P c) := by
      intro β α h
      simp only [tab, codeTab, List.forall_mem_map, lits, List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left, holdsT, nl, h]
      rfl
    constructor
    · rintro ⟨β, hβ⟩
      exact ⟨fun a t q => β (num a) t q, spec_of_table ((key β _ fun _ _ _ => rfl).1 hβ)⟩
    · rintro ⟨α, hα⟩
      classical
      refine ⟨fun k t q => if h : ∃ a, num a = k then α h.choose t q else false, (key _ α fun a t q => ?_).2 (table_of_spec hα)⟩
      have h : ∃ a', num a' = num a := ⟨a, rfl⟩
      rw [dif_pos h, num_injective h.choose_spec]

end CircuitLowerBound
