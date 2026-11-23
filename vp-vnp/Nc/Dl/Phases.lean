/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Dl.Tab

/-!
# The phases of the dealing program
-/

set_option linter.unusedSectionVars false

namespace Nc.Dl

open NS1 NS1.Tree Finset Nc.G Nc.Cut

theorem sum_execAll_append {B : Type} [CommRing B] (m : ℕ) (a b : List DStep) (σ : List Bool → Tree)
    (Φ : (List Bool → Tree) → B) :
    ((execAll m (a ++ b) σ).map Φ).sum = ((execAll m a σ).map fun σ' => ((execAll m b σ').map Φ).sum).sum := by
  rw [execAll_append, sum_flatMap_map]

/-- The sum over all functions with values in lists. -/
theorem sum_funs_univ {A : Type} [CommRing A] {ι α : Type} [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α]
    (opts : ι → List α) (hopts : ∀ i, (opts i).Nodup) (f0 : ι → α) (Φ : (ι → α) → A) :
    ((funs opts f0 (univ : Finset ι).toList).map Φ).sum = ∑ f : ι → α, if ∀ i, f i ∈ opts i then Φ f else 0 := by
  rw [sum_funs opts hopts _ (Finset.nodup_toList _)]
  refine Finset.sum_congr rfl fun f _ => ?_
  congr 1
  simp

variable {B : Type} [CommRing B] {A : Type} [CommRing A] {S Q : Type} [Fintype S] [DecidableEq S] [Fintype Q] [DecidableEq Q]
  {K A' E U0 U1 ub mm D pS : ℕ} {M : Sys A (K + K + A') E} {P : G.Plan M U0 U1}
  {grp : NN K U0 → (M.N → Fin U1) → Fin (K + K + A') → Fin mm} (C : Codes S M U0 U1 D pS) {m : ℕ}

open Codes

section Generic

variable {ι α : Type} [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α]

/-- A step that chooses an option from a fixed list. -/
noncomputable def pickS (opts : List α) (o : α → List (NmT S M U0 U1 pS × Tree)) : DStep :=
  .pick (C.nm .zero) (.cons (listT (opts.map fun a => optT C.nm (o a))) .nil)

theorem exec_pickS {st : NmT S M U0 U1 pS → Tree} (hz : st .zero = .nil) (opts : List α)
    (o : α → List (NmT S M U0 U1 pS × Tree)) :
    (pickS C opts o).exec m (byPath C.nm st) = opts.map fun a => byPath C.nm (upds st (o a)) := by
  rw [pickS, exec_pick C.nm_inj (opts := opts.map o), List.map_map]
  · rfl
  · rw [hz]
    simp [path, tget, Function.comp_def]

theorem upds_of_not {ν : Type} [DecidableEq ν] {st : ν → Tree} {o : List (ν × Tree)} {x : ν} (h : ∀ a ∈ o, a.1 ≠ x) :
    upds st o x = st x := by
  unfold upds
  induction o generalizing st with
  | nil => rfl
  | cons a o ih =>
    rw [List.foldl_cons, ih fun b hb => h b (List.mem_cons_of_mem _ hb),
      Function.update_of_ne (h a List.mem_cons_self).symm]

/-- **A phase of choices.** `v f x`: the value of the name `x` for the choices `f`. -/
theorem phase_picks {st : NmT S M U0 U1 pS → Tree} (hz : st .zero = .nil) (opts : ι → List α)
    (hopts : ∀ i, (opts i).Nodup) (o : ι → α → List (NmT S M U0 U1 pS × Tree))
    (own : NmT S M U0 U1 pS → Option ι) (v : (ι → α) → NmT S M U0 U1 pS → Tree)
    (ho : ∀ (f : ι → α) i, ∀ a ∈ o i (f i), own a.1 = some i ∧ a.2 = v f a.1)
    (hall : ∀ (f : ι → α) i x, own x = some i → ∃ a ∈ o i (f i), a.1 = x) (hz' : own .zero = none) (f0 : ι → α)
    (Φ : (List Bool → Tree) → B) :
    ((execAll m ((univ : Finset ι).toList.map fun i => pickS C (opts i) (o i)) (byPath C.nm st)).map Φ).sum =
      ∑ f : ι → α, if ∀ i, f i ∈ opts i then
        Φ (byPath C.nm fun x => if (own x).isSome then v f x else st x) else 0 := by
  have hzero : ∀ (st : NmT S M U0 U1 pS → Tree) i a, st .zero = .nil → upds st (o i a) .zero = .nil := by
    intro st i a hst
    rw [upds_of_not, hst]
    intro b hb h0
    have := (ho (Function.update f0 i a) i b (by rw [Function.update_self]; exact hb)).1
    rw [h0, hz'] at this
    simp at this
  rw [execAll_choices (opts := opts) (L := byPath C.nm) (ov := fun i a st => upds st (o i a))
    (good := fun st => st .zero = .nil) (fun i st hst => exec_pickS C hst (opts i) (o i))
    (fun i st a _ hst => hzero st i a hst) (Finset.nodup_toList _) hz f0, sum_funs_univ opts hopts]
  refine Finset.sum_congr rfl fun f _ => ?_
  have hf := foldl_upds (own := own) (o := fun i => o i (f i)) (v := v f) (ho f) (hall f) (univ : Finset ι).toList st
  rw [hf]
  congr 2
  congr 1
  funext x
  cases h : own x with
  | none => simp
  | some i => simp

/-- **A phase of deterministic steps**, each writing one name. -/
theorem phase_det {st : NmT S M U0 U1 pS → Tree} {step : ι → DStep} (g : ι → NmT S M U0 U1 pS)
    (hg : Function.Injective g) (v : ι → Tree) (base : (NmT S M U0 U1 pS → Tree) → Prop) (hst0 : base st)
    (hstep : ∀ i st, base st → (step i).exec m (byPath C.nm st) = [byPath C.nm (Function.update st (g i) (v i))])
    (hbase : ∀ i st, base st → base (Function.update st (g i) (v i))) (s : List ι) (hall : ∀ i, i ∈ s) :
    execAll m (s.map step) (byPath C.nm st) = [byPath C.nm fun x =>
      open Classical in if h : ∃ i, g i = x then v h.choose else st x] := by
  classical
  rw [execAll_det (L := byPath C.nm) (ov := fun i st => Function.update st (g i) (v i)) (good := fun _ st => base st)
    (fun i _ st hst => ⟨hstep i st hst, hbase i st hst⟩) hst0]
  have hf := foldl_upds (own := fun x => if h : ∃ i, g i = x then some h.choose else none)
    (o := fun i => [(g i, v i)]) (v := fun x => if h : ∃ i, g i = x then v h.choose else .nil) (by
      intro i a ha
      rw [List.mem_singleton] at ha
      subst ha
      have h : ∃ j, g j = g i := ⟨i, rfl⟩
      rw [dif_pos h, dif_pos h, hg h.choose_spec]
      exact ⟨rfl, rfl⟩) (by
      intro i x hx
      by_cases h : ∃ i, g i = x
      · rw [dif_pos h] at hx
        refine ⟨_, List.mem_singleton_self _, ?_⟩
        rw [← Option.some.inj hx]
        exact h.choose_spec
      · rw [dif_neg h] at hx
        simp at hx) s st
  have e : (s.foldl (fun st i => Function.update st (g i) (v i)) st) = s.foldl (fun st i => upds st [(g i, v i)]) st := rfl
  rw [e, hf]
  congr 2
  funext x
  by_cases h : ∃ i, g i = x
  · rw [dif_pos h, dif_pos h]
    simp [hall, h]
  · simp only [dif_neg h]

end Generic

end Nc.Dl
