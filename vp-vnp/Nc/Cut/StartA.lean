/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Cut.Rows

/-!
# Start, I: segments

For given states between the blocks, the sum over what the blocks emit is a sum over the common segments of the
parties on all tapes, with staircase support.
-/

set_option linter.unusedSectionVars false

namespace Nc.Cut

open Finset

section Cat

variable {Γ : Type}

theorem cat_add {K K' : ℕ} (X : Fin (K + K') → List Γ) :
    cat X = (cat fun κ : Fin K => X (Fin.castAdd K' κ)) ++ cat fun κ : Fin K' => X (Fin.natAdd K κ) := by
  simp only [cat]
  rw [List.ofFn_add, List.flatten_append]
  rfl

theorem length_le_cat {K : ℕ} (X : Fin K → List Γ) (b : Fin K) : (X b).length ≤ (cat X).length := by
  rw [cat, List.length_flatten]
  refine List.single_le_sum (fun _ _ => Nat.zero_le _) _ ?_
  rw [List.mem_map]
  exact ⟨X b, List.mem_ofFn.2 ⟨b, rfl⟩, rfl⟩

theorem cat_nil_of {K : ℕ} {X : Fin K → List Γ} (h : ∀ b, X b = []) : cat X = [] := cat_eq_nil.2 h

theorem cat_parts {K : ℕ} (ℓ : ℕ) (u : List Γ) : cat (parts ℓ u : Fin K → List Γ) = u.take (K * ℓ) := by
  induction K generalizing u with
  | zero => simp [cat]
  | succ K ih =>
    rw [cat_succ]
    have e1 : (fun i : Fin K => (parts ℓ u : Fin (K + 1) → List Γ) i.succ) = parts ℓ (u.drop ℓ) := by
      funext i
      simp only [parts, Fin.val_succ, List.drop_drop]
      congr 2
      ring
    rw [e1, ih]
    simp only [parts, Fin.val_zero, Nat.zero_mul, List.drop_zero]
    rw [← List.take_add]
    congr 1
    ring

theorem length_parts_le {K : ℕ} (ℓ : ℕ) (u : List Γ) (κ : Fin K) : (parts ℓ u κ).length ≤ ℓ := by
  simp [parts]

end Cat

variable {F : Type} [CommRing F] {Γ S Q : Type} [Fintype Γ] [DecidableEq Γ] [Fintype S] [DecidableEq S]
  [Fintype Q] [DecidableEq Q] {K : ℕ} (mu : Letter S Unit Γ → Matrix Q Q F) (T : ℕ)

/-- A block emits at most `T` letters in all. -/
theorem blockW_sum_le {J : Type} [Fintype J] [DecidableEq J] {mu : Letter S J Γ → Matrix Q Q F} {T : ℕ} {q q' : Q}
    {v : Ch S J → List Γ} (h : blockW mu T q q' v ≠ 0) : ∑ z, (v z).length ≤ T := by
  obtain ⟨o, -, ho⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  split_ifs at ho with he
  · have h1 := sum_length_proj (List.ofFn o).reduceOption
    have h2 := List.reduceOption_length_le (List.ofFn o)
    rw [← he]
    calc ∑ z, (emit (List.ofFn o) z).length = (List.ofFn o).reduceOption.length := h1
      _ ≤ T := by simpa using h2
  · exact absurd rfl ho

section Party

variable {T} {q : Fin (K + 1) → Q} {x : Fin K → List Γ} {R C : Option S → Fin (K + K) → List Γ}

open Classical in
theorem partyW_block (κ : Fin K) : partyW mu T q x (Fin.castAdd K κ) R C =
    if ∀ b, R none b = [] then blockW mu T (q κ.castSucc) (q κ.succ) (vec R C) else 0 := by
  rw [partyW, Fin.addCases_left]

open Classical in
theorem partyW_input (κ : Fin K) : partyW mu T q x (Fin.natAdd K κ) R C =
    if (∀ s b, R (some s) b = []) ∧ (∀ s b, C s b = []) ∧ cat (R none) = x κ then 1 else 0 := by
  rw [partyW, Fin.addCases_right]

variable {mu}

/-- A party writes at most `T` letters in all. -/
theorem partyW_sum_le (hx : ∀ κ, (x κ).length ≤ T) {p : Fin (K + K)} (h : partyW mu T q x p R C ≠ 0) :
    ∑ s, (cat (R s)).length ≤ T := by
  classical
  refine Fin.addCases (motive := fun p => partyW mu T q x p R C ≠ 0 → ∑ s, (cat (R s)).length ≤ T) ?_ ?_ p h
  · intro κ h
    rw [partyW_block] at h
    split_ifs at h with hc
    swap
    · exact absurd rfl h
    refine le_trans ?_ (blockW_sum_le h)
    rw [Fintype.sum_option, cat_nil_of hc, List.length_nil, zero_add]
    have : ∑ s, (cat (R (some s))).length = ∑ s : S, ((vec R C (.tp s false)).length) := by
      simp [vec]
    rw [this]
    rw [← Finset.sum_image (f := fun z : Ch S Unit => (vec R C z).length) (s := univ) (g := fun s : S => .tp s false)]
    · exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    · intro s _ s' _ e
      simpa using e
  · intro κ h
    rw [partyW_input] at h
    split_ifs at h with hc
    swap
    · exact absurd rfl h
    rw [Fintype.sum_option, hc.2.2]
    have : ∑ s, (cat (R (some s))).length = 0 := by
      refine Finset.sum_eq_zero fun s _ => ?_
      rw [cat_nil_of (hc.1 s), List.length_nil]
    rw [this]
    exact hx κ

end Party

/-- The product of the weights of the parties. -/
noncomputable def segW (q : Fin (K + 1) → Q) (x : Fin K → List Γ)
    (X : Option S → Fin (K + K) → Fin (K + K) → List Γ) : F :=
  ∏ p, partyW mu T q x p (fun s b => X s p b) (fun s b => X s b p)

/-- Segments of at most `T` letters. -/
noncomputable def segs (Γ S : Type) [Fintype Γ] [Fintype S] [DecidableEq S] (K T : ℕ) :
    Finset (Option S → Fin (K + K) → Fin (K + K) → List Γ) :=
  Fintype.piFinset fun _ => Fintype.piFinset fun _ => Fintype.piFinset fun _ => wordsLe Γ T

theorem mem_segs {K T : ℕ} {X : Option S → Fin (K + K) → Fin (K + K) → List Γ} :
    X ∈ segs Γ S K T ↔ ∀ s a b, (X s a b).length ≤ T := by
  simp [segs, mem_wordsLe]

variable {mu T}

/-- What the non-vanishing of the product of the weights means. -/
theorem segW_ne_zero {q : Fin (K + 1) → Q} {x : Fin K → List Γ}
    {X : Option S → Fin (K + K) → Fin (K + K) → List Γ} (h : segW mu T q x X ≠ 0) :
    (∀ κ b, X none (Fin.castAdd K κ) b = []) ∧
    (∀ s κ b, X (some s) (Fin.natAdd K κ) b = []) ∧ (∀ s κ b, X s b (Fin.natAdd K κ) = []) ∧
    (∀ κ, cat (X none (Fin.natAdd K κ)) = x κ) ∧
    segW mu T q x X = ∏ κ : Fin K, blockW mu T (q κ.castSucc) (q κ.succ)
      (vec (fun s b => X s (Fin.castAdd K κ) b) fun s b => X s b (Fin.castAdd K κ)) := by
  classical
  have h0 : ∀ p, partyW mu T q x p (fun s b => X s p b) (fun s b => X s b p) ≠ 0 := fun p hp =>
    h (Finset.prod_eq_zero (Finset.mem_univ p) hp)
  have h1 : ∀ κ b, X none (Fin.castAdd K κ) b = [] := by
    intro κ
    have := h0 (Fin.castAdd K κ)
    rw [partyW_block] at this
    by_contra hc
    rw [if_neg hc] at this
    exact this rfl
  have h2 : ∀ κ, (∀ s b, X (some s) (Fin.natAdd K κ) b = []) ∧ (∀ s b, X s b (Fin.natAdd K κ) = []) ∧
      cat (X none (Fin.natAdd K κ)) = x κ := by
    intro κ
    have := h0 (Fin.natAdd K κ)
    rw [partyW_input] at this
    by_contra hc
    rw [if_neg hc] at this
    exact this rfl
  refine ⟨h1, fun s κ => (h2 κ).1 s, fun s κ => (h2 κ).2.1 s, fun κ => (h2 κ).2.2, ?_⟩
  rw [segW, Fin.prod_univ_add]
  have e1 : (∏ κ : Fin K, partyW mu T q x (Fin.natAdd K κ) (fun s b => X s (Fin.natAdd K κ) b)
      fun s b => X s b (Fin.natAdd K κ)) = 1 := by
    refine Finset.prod_eq_one fun κ _ => ?_
    rw [partyW_input, if_pos (h2 κ)]
  rw [e1, mul_one]
  refine Finset.prod_congr rfl fun κ _ => ?_
  rw [partyW_block, if_pos (h1 κ)]

open Classical in
/-- **Segments.** -/
theorem sum_segs (q : Fin (K + 1) → Q) {x : Fin K → List Γ} (hx : ∀ κ, (x κ).length ≤ T) (u : Unit → List Γ)
    (hu : cat x = u ()) :
    (∑ v ∈ Fintype.piFinset fun _ : Fin K => Fintype.piFinset fun _ : Ch S Unit => wordsLe Γ T,
      if (∀ s, cat (fun k => v k (.tp s false)) = cat fun k => v k (.tp s true)) ∧
        ∀ j, cat (fun k => v k (.inp j)) = u j then
      ∏ k, blockW mu T (q k.castSucc) (q k.succ) (v k) else 0) =
    ∑ X ∈ segs Γ S K T, if ∀ s, Stair (X s) then segW mu T q x X else 0 := by
  symm
  refine Finset.sum_bij_ne_zero (fun X _ _ => fun κ =>
    vec (fun s b => X s (Fin.castAdd K κ) b) fun s b => X s b (Fin.castAdd K κ)) ?_ ?_ ?_ ?_
  · intro X _ hne
    have hst : ∀ s, Stair (X s) := by
      by_contra hc
      rw [if_neg hc] at hne
      exact hne rfl
    rw [if_pos hst] at hne
    obtain ⟨-, -, -, -, e⟩ := segW_ne_zero hne
    rw [e] at hne
    rw [Fintype.mem_piFinset]
    intro κ
    rw [Fintype.mem_piFinset]
    exact blockW_ne_zero fun h0 => hne (Finset.prod_eq_zero (Finset.mem_univ κ) h0)
  · intro X _ hX X' _ hX' heq
    have hst : ∀ s, Stair (X s) := by
      by_contra hc
      rw [if_neg hc] at hX
      exact hX rfl
    have hst' : ∀ s, Stair (X' s) := by
      by_contra hc
      rw [if_neg hc] at hX'
      exact hX' rfl
    rw [if_pos hst] at hX
    rw [if_pos hst'] at hX'
    obtain ⟨a1, a2, a3, a4, -⟩ := segW_ne_zero hX
    obtain ⟨b1, b2, b3, b4, -⟩ := segW_ne_zero hX'
    funext s
    have hrow : ∀ p, cat (X s p) = cat (X' s p) := by
      intro p
      refine Fin.addCases (fun κ => ?_) (fun κ => ?_) p
      · cases s with
        | none => rw [cat_nil_of (a1 κ), cat_nil_of (b1 κ)]
        | some s => exact congrFun (congrFun heq κ) (.tp s false)
      · cases s with
        | none => rw [a4, b4]
        | some s => rw [cat_nil_of (a2 s κ), cat_nil_of (b2 s κ)]
    have hcol : ∀ p, cat (fun a => X s a p) = cat fun a => X' s a p := by
      intro p
      refine Fin.addCases (fun κ => ?_) (fun κ => ?_) p
      · cases s with
        | none => exact congrFun (congrFun heq κ) (.inp ())
        | some s => exact congrFun (congrFun heq κ) (.tp s true)
      · rw [cat_nil_of (a3 s κ), cat_nil_of (b3 s κ)]
    have r1 : IsRef (fun p => cat (X s p)) (fun p => cat fun a => X s a p) (X s) :=
      ⟨hst s, fun _ => rfl, fun _ => rfl⟩
    have r2 : IsRef (fun p => cat (X s p)) (fun p => cat fun a => X s a p) (X' s) :=
      ⟨hst' s, fun p => (hrow p).symm, fun p => (hcol p).symm⟩
    exact r1.unique r2
  · intro v hv hne
    have hm : (∀ s, cat (fun k => v k (.tp s false)) = cat fun k => v k (.tp s true)) ∧
        ∀ j, cat (fun k => v k (.inp j)) = u j := by
      by_contra hc
      rw [if_neg hc] at hne
      exact hne rfl
    rw [if_pos hm] at hne
    have hvT : ∀ κ z, (v κ z).length ≤ T := by
      intro κ z
      have := Fintype.mem_piFinset.1 (Fintype.mem_piFinset.1 hv κ) z
      exact mem_wordsLe.1 this
    -- what the parties write and read
    let W : Option S → Fin (K + K) → List Γ := fun s => match s with
      | none => Fin.addCases (motive := fun _ => List Γ) (fun _ => []) x
      | some s => Fin.addCases (motive := fun _ => List Γ) (fun κ => v κ (.tp s false)) fun _ => []
    let Rd : Option S → Fin (K + K) → List Γ := fun s => match s with
      | none => Fin.addCases (motive := fun _ => List Γ) (fun κ => v κ (.inp ())) fun _ => []
      | some s => Fin.addCases (motive := fun _ => List Γ) (fun κ => v κ (.tp s true)) fun _ => []
    have hW1 : ∀ κ, W none (Fin.castAdd K κ) = [] := fun κ => by simp only [W, Fin.addCases_left]
    have hW2 : ∀ κ, W none (Fin.natAdd K κ) = x κ := fun κ => by simp only [W, Fin.addCases_right]
    have hW3 : ∀ s κ, W (some s) (Fin.castAdd K κ) = v κ (.tp s false) := fun s κ => by
      simp only [W, Fin.addCases_left]
    have hW4 : ∀ s κ, W (some s) (Fin.natAdd K κ) = [] := fun s κ => by simp only [W, Fin.addCases_right]
    have hR1 : ∀ κ, Rd none (Fin.castAdd K κ) = v κ (.inp ()) := fun κ => by simp only [Rd, Fin.addCases_left]
    have hR2 : ∀ s κ, Rd s (Fin.natAdd K κ) = [] := by
      intro s κ
      cases s <;> simp only [Rd, Fin.addCases_right]
    have hR3 : ∀ s κ, Rd (some s) (Fin.castAdd K κ) = v κ (.tp s true) := fun s κ => by
      simp only [Rd, Fin.addCases_left]
    have hcat : ∀ s, cat (W s) = cat (Rd s) := by
      intro s
      rw [cat_add, cat_add]
      cases s with
      | none =>
        simp only [hW1, hW2, hR1, hR2]
        rw [cat_nil_of fun _ => rfl, hm.2 (), ← hu]
        simp
      | some s =>
        simp only [hW3, hW4, hR3, hR2]
        rw [hm.1 s]
    choose X hX using fun s => IsRef.exists (hcat s)
    have row : ∀ s p, cat (X s p) = W s p := fun s p => (hX s).row p
    have col : ∀ s p, cat (fun a => X s a p) = Rd s p := fun s p => (hX s).col p
    have c1 : ∀ κ b, X none (Fin.castAdd K κ) b = [] := fun κ => cat_eq_nil.1 ((row _ _).trans (hW1 κ))
    have c2 : ∀ s κ b, X (some s) (Fin.natAdd K κ) b = [] := fun s κ => cat_eq_nil.1 ((row _ _).trans (hW4 s κ))
    have c3 : ∀ s κ b, X s b (Fin.natAdd K κ) = [] := fun s κ => cat_eq_nil.1 ((col _ _).trans (hR2 s κ))
    have c4 : ∀ κ, cat (X none (Fin.natAdd K κ)) = x κ := fun κ => (row _ _).trans (hW2 κ)
    have hvec : ∀ κ, vec (fun s b => X s (Fin.castAdd K κ) b) (fun s b => X s b (Fin.castAdd K κ)) = v κ := by
      intro κ
      funext z
      cases z with
      | tp s b =>
        cases b with
        | false => exact (row (some s) _).trans (hW3 s κ)
        | true => exact (col (some s) _).trans (hR3 s κ)
      | inp j => exact (col none _).trans (hR1 κ)
    have hWX : segW mu T q x X = ∏ k, blockW mu T (q k.castSucc) (q k.succ) (v k) := by
      rw [segW, Fin.prod_univ_add]
      have e1 : (∏ κ : Fin K, partyW mu T q x (Fin.natAdd K κ) (fun s b => X s (Fin.natAdd K κ) b)
          fun s b => X s b (Fin.natAdd K κ)) = 1 := by
        refine Finset.prod_eq_one fun κ _ => ?_
        rw [partyW_input, if_pos ⟨fun s => c2 s κ, fun s => c3 s κ, c4 κ⟩]
      rw [e1, mul_one]
      refine Finset.prod_congr rfl fun κ _ => ?_
      rw [partyW_block, if_pos (c1 κ), hvec]
    refine ⟨X, ?_, ?_, ?_⟩
    · rw [mem_segs]
      intro s a b
      refine (length_le_cat (X s a) b).trans ?_
      rw [row]
      refine Fin.addCases (fun κ => ?_) (fun κ => ?_) a
      · cases s with
        | none => rw [hW1]; exact Nat.zero_le _
        | some s => rw [hW3]; exact hvT _ _
      · cases s with
        | none => rw [hW2]; exact hx κ
        | some s => rw [hW4]; exact Nat.zero_le _
    · rw [if_pos fun s => (hX s).stair, hWX]
      exact hne
    · funext κ
      exact hvec κ
  · intro X _ hne
    have hst : ∀ s, Stair (X s) := by
      by_contra hc
      rw [if_neg hc] at hne
      exact hne rfl
    rw [if_pos hst] at hne ⊢
    obtain ⟨a1, a2, a3, a4, e⟩ := segW_ne_zero hne
    rw [if_pos, e]
    have hcat : ∀ s, cat (fun p => cat (X s p)) = cat fun p => cat fun a => X s a p := fun s =>
      IsRef.cat_eq ⟨hst s, fun _ => rfl, fun _ => rfl⟩
    constructor
    · intro s
      have := hcat (some s)
      rw [cat_add, cat_add] at this
      simp only [fun κ => cat_nil_of (a2 s κ), fun κ => cat_nil_of (a3 (some s) κ)] at this
      exact List.append_cancel_right this
    · intro j
      have := hcat none
      rw [cat_add, cat_add] at this
      simp only [fun κ => cat_nil_of (a1 κ), fun κ => cat_nil_of (a3 none κ), a4] at this
      rw [cat_nil_of (K := K) (X := fun _ => ([] : List Γ)) fun _ => rfl, List.nil_append, List.append_nil] at this
      rw [hu] at this
      exact this.symm

end Nc.Cut
