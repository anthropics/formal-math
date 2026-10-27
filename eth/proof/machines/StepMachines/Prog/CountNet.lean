/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import StepMachines.Prog.Spec
public import StepMachines.Math.SatNet

/-! The network of a k-CNF, as in Section 6 (the network of Φ), on words. The clauses are cut into g
clusters of μ
clauses, a state of a cluster has one bit for each literal slot, and a link (an equality test of the
paper) joins consecutive
occurrences of a variable. The file has plain list functions for the weights, factors and
capacities, and their agreement
with the network `SatNet.net`. State word: bit c*k+j is the slot (c,j). Label word: one bit for each
link, in reading
order. -/

namespace Groundwork.Prog

open Finset SatNet

/-- A formula as data: a literal is (variable, the value that makes it true). -/
public abbrev Fml : Type := List (List (ℕ × Bool))

namespace Count

/-! ### The plain functions -/

/-- The number of clauses of a cluster. -/
@[expose] public def mu (g : ℕ) (φ : Fml) : ℕ := (φ.length + g - 1) / g

/-- The literal at place i % k of clause i / k. -/
@[expose] public def litAt (k : ℕ) (φ : Fml) (i : ℕ) : Option (ℕ × Bool) :=
  ((φ.getD (i / k) []).map some).getD (i % k) none

/-- The variable at slot i. -/
@[expose] public def varAt (k : ℕ) (φ : Fml) (i : ℕ) : Option ℕ := (litAt k φ i).map Prod.fst

/-- The slots of the clauses of φ: 0, …, m*k - 1. -/
@[expose] public def slotsOf (k : ℕ) (φ : Fml) : List ℕ := List.range (φ.flatMap fun _ => List.replicate k ()).length

/-- Slot i' is the next occurrence of the variable at slot i. -/
@[expose] public def linkB (k : ℕ) (φ : Fml) (i i' : ℕ) : Bool :=
  decide (i < i') && (varAt k φ i).isSome && (varAt k φ i == varAt k φ i') &&
    (slotsOf k φ).all fun t => !(decide (i < t) && decide (t < i') && (varAt k φ t == varAt k φ i))

/-- The slots of a cluster: 0, …, μ*k - 1. -/
@[expose] public def locals (g k : ℕ) (φ : Fml) : List ℕ := (slotsOf k φ).take (mu g φ * k)

/-- The clauses of a cluster: 0, …, μ - 1. -/
@[expose] public def rows (g : ℕ) (φ : Fml) : List ℕ := (List.range φ.length).take (mu g φ)

/-- The links from cluster a to cluster b, as pairs of slots of the clusters, in reading order. -/
@[expose] public def links (g k : ℕ) (φ : Fml) (a b : ℕ) : List (ℕ × ℕ) :=
  (locals g k φ ×ˢ locals g k φ).filter fun p => linkB k φ (a * (mu g φ * k) + p.1) (b * (mu g φ * k) + p.2)

/-- The capacity of two clusters: the number of links between them, one label bit each. -/
@[expose] public def capF (g k : ℕ) (φ : Fml) (a b : ℕ) : ℕ := (links g k φ (min a b) (max a b)).length

/-- The weight of cluster a at the state word z, for x = (φ, (a, z)): 1 if the slots without a
literal carry false,
every clause of the cluster has a true literal and the links inside the cluster join equal bits,
else 0. -/
@[expose] public def wF (g k : ℕ) (x : Fml × WQ) : ℤ :=
  if ((locals g k x.1).all fun r => (litAt k x.1 (x.2.1 * (mu g x.1 * k) + r)).isSome || !(x.2.2.getD r false)) &&
      ((rows g x.1).all fun c => !(decide (x.2.1 * mu g x.1 + c < x.1.length)) ||
        (List.range k).any fun j =>
          (litAt k x.1 ((x.2.1 * mu g x.1 + c) * k + j)).map Prod.snd == some (x.2.2.getD (c * k + j) false)) &&
      ((links g k x.1 x.2.1 x.2.1).all fun p => x.2.2.getD p.1 false == x.2.2.getD p.2 false)
  then 1 else 0

/-- The factor of clusters a, b on the side of a, at the state word z and the label word θ,
for x = (φ, ((a, b), (z, θ))): 1 if every link of the two clusters has, at its end in a, the bit
that θ gives it, else 0. -/
@[expose] public def fF (g k : ℕ) (x : Fml × FQ) : ℤ :=
  if x.2.1.1 < x.2.1.2 then
    (if ((links g k x.1 x.2.1.1 x.2.1.2).zip x.2.2.2).all fun p => x.2.2.1.getD p.1.1 false == p.2 then 1 else 0)
  else (if ((links g k x.1 x.2.1.2 x.2.1.1).zip x.2.2.2).all fun p => x.2.2.1.getD p.1.2 false == p.2 then 1 else 0)

/-- The cluster network on words. -/
@[expose] public def wordNet (g k : ℕ) (φ : Fml) : Network (Fin g) (List Bool) (List Bool) where
  S _ := words (mu g φ * k)
  W a z := wF g k (φ, (a.val, z))
  Θ a b := words (capF g k φ a.val b.val)
  f a b z θ := fF g k (φ, ((a.val, b.val), (z, θ)))
  c a b := capF g k φ a.val b.val

/-! ### Ranges -/

theorem slotsOf_eq (k : ℕ) (φ : Fml) : slotsOf k φ = List.range (φ.length * k) := by
  unfold slotsOf
  congr 1
  induction φ with
  | nil => simp
  | cons C φ ih => simp only [List.flatMap_cons, List.length_append, List.length_replicate, ih, List.length_cons]; ring

public theorem mu_le {g : ℕ} (hg : 0 < g) (φ : Fml) : mu g φ ≤ φ.length := by
  unfold mu
  rw [Nat.div_le_iff_le_mul_add_pred hg]
  have : φ.length ≤ g * φ.length := Nat.le_mul_of_pos_left _ hg
  omega

theorem locals_eq {g : ℕ} (hg : 0 < g) (k : ℕ) (φ : Fml) : locals g k φ = List.range (mu g φ * k) := by
  rw [locals, slotsOf_eq, List.take_range, min_eq_left (Nat.mul_le_mul_right k (mu_le hg φ))]

theorem rows_eq {g : ℕ} (hg : 0 < g) (φ : Fml) : rows g φ = List.range (mu g φ) := by
  rw [rows, List.take_range, min_eq_left (mu_le hg φ)]

/-! ### Slots as numbers -/

variable {g μ k : ℕ} {φ : Fml}

/-- The place of a slot in its cluster. -/
@[expose] public def loc (s : Sl μ k) : ℕ := s.1.val * k + s.2.val

theorem loc_lt (s : Sl μ k) : loc s < μ * k := by
  have h1 : (s.1.val + 1) * k ≤ μ * k := Nat.mul_le_mul_right k s.1.2
  have := s.2.2
  rw [Nat.succ_mul] at h1
  unfold loc
  omega

theorem exists_loc {r : ℕ} (h : r < μ * k) : ∃ s : Sl μ k, loc s = r := by
  have hk : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · subst h0; simp at h
    · exact h0
  exact ⟨(⟨r / k, Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm])⟩, ⟨r % k, Nat.mod_lt _ hk⟩), Nat.div_add_mod' r k⟩

theorem idx_eq (a : Fin g) (s : Sl μ k) : idx (a, s) = a.val * (μ * k) + loc s := by
  simp only [idx, loc]; ring

theorem litAt_idx (p : Slot g μ k) : litAt k φ (idx p) = lit φ p := by
  have hj := p.2.2.2
  have h1 : idx p / k = p.1.val * μ + p.2.1.val := by
    rw [idx, Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hj, Nat.zero_add]
  have h2 : idx p % k = p.2.2.val := by
    rw [idx, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]
  rw [litAt, h1, h2, lit]
  cases h : φ[p.1.val * μ + p.2.1.val]? with
  | none => simp [List.getD_eq_getElem?_getD, h]
  | some C =>
    simp only [List.getD_eq_getElem?_getD, h, Option.getD_some, List.getElem?_map, Option.bind_some]
    cases C[p.2.2.val]? <;> rfl

theorem varAt_idx (p : Slot g μ k) : varAt k φ (idx p) = lab φ p := by
  rw [varAt, litAt_idx, lab]

theorem varAt_eq_none (h0 : 0 < k) {i : ℕ} (h : φ.length * k ≤ i) : varAt k φ i = none := by
  have : φ.length ≤ i / k := (Nat.le_div_iff_mul_le h0).2 h
  simp [varAt, litAt, List.getD_eq_getElem?_getD, List.getElem?_eq_none this]

theorem exists_idx {i : ℕ} (h : i < g * μ * k) : ∃ p : Slot g μ k, idx p = i := by
  rw [Nat.mul_assoc] at h
  have hn : 0 < μ * k := by
    rcases Nat.eq_zero_or_pos (μ * k) with h0 | h0
    · rw [h0] at h; simp at h
    · exact h0
  obtain ⟨s, hs⟩ := exists_loc (μ := μ) (k := k) (Nat.mod_lt i hn)
  refine ⟨(⟨i / (μ * k), Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm])⟩, s), ?_⟩
  rw [idx_eq, hs]
  exact Nat.div_add_mod' i (μ * k)

theorem linkB_iff (hm : φ.length ≤ g * μ) (p q : Slot g μ k) : linkB k φ (idx p) (idx q) = true ↔ Link φ p q := by
  simp only [linkB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, slotsOf_eq, List.mem_range, Bool.not_eq_true',
    Bool.and_eq_false_iff, decide_eq_false_iff_not, beq_iff_eq, beq_eq_false_iff_ne, varAt_idx, Option.isSome_iff_ne_none]
  constructor
  · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
    refine ⟨h1, h2, h3, fun r hr1 hr2 hr3 => ?_⟩
    by_cases ht : idx r < φ.length * k
    · rcases h4 _ ht with (h | h) | h
      · exact h hr1
      · exact h hr2
      · rw [varAt_idx] at h; exact h hr3
    · rw [← varAt_idx, varAt_eq_none (Nat.zero_lt_of_lt p.2.2.2) (not_lt.1 ht)] at hr3
      exact h2 hr3.symm
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨⟨⟨h1, h2⟩, h3⟩, fun t ht => ?_⟩
    obtain ⟨r, rfl⟩ := exists_idx (g := g) (μ := μ) (lt_of_lt_of_le ht (Nat.mul_le_mul_right k hm))
    by_cases hr1 : idx p < idx r
    · by_cases hr2 : idx r < idx q
      · right; rw [varAt_idx]; exact h4 r hr1 hr2
      · left; right; exact hr2
    · left; left; exact hr1

/-! ### States -/

/-- The state that a word writes. -/
@[expose] public def bits (z : List Bool) : Sl μ k → Bool := fun s => z.getD (loc s) false

theorem bijOn_bits : Set.BijOn (bits (μ := μ) (k := k)) (words (μ * k)) (univ : Finset (Sl μ k → Bool)) := by
  refine ⟨fun _ _ => by simp, fun z hz z' hz' h => ?_, fun f _ => ?_⟩
  · have hl : z.length = μ * k := mem_words.1 hz
    have hl' : z'.length = μ * k := mem_words.1 hz'
    refine List.ext_getElem (hl.trans hl'.symm) fun r h1 h2 => ?_
    obtain ⟨s, rfl⟩ := exists_loc (μ := μ) (k := k) (hl ▸ h1)
    have := congrFun h s
    simpa [bits, List.getD_eq_getElem?_getD, h1, h2] using this
  · classical
    refine ⟨(List.range (μ * k)).map fun r => if h : r < μ * k then f (exists_loc h).choose else false,
      mem_words.2 (by simp), funext fun s => ?_⟩
    have hs := loc_lt s
    have hinj : (exists_loc hs).choose = s := by
      have h := (exists_loc hs).choose_spec
      generalize (exists_loc hs).choose = s' at h
      obtain ⟨h1, h2⟩ := SatNet.mul_add_inj' s'.2.2 s.2.2 h
      exact Prod.ext (Fin.ext h1) (Fin.ext h2)
    simp [bits, List.getD_eq_getElem?_getD, hs, hinj]

/-! ### Links -/

theorem mem_links (hg : 0 < g) (a b : ℕ) (p : ℕ × ℕ) : p ∈ links g k φ a b ↔
    p.1 < mu g φ * k ∧ p.2 < mu g φ * k ∧ linkB k φ (a * (mu g φ * k) + p.1) (b * (mu g φ * k) + p.2) = true := by
  obtain ⟨r, r'⟩ := p
  simp only [links, locals_eq hg, List.mem_filter, SProd.sprod, List.pair_mem_product, List.mem_range, and_assoc]

theorem nodup_links (hg : 0 < g) (a b : ℕ) : (links g k φ a b).Nodup := by
  rw [links, locals_eq hg]
  exact (List.nodup_range.product List.nodup_range).filter _

/-- A condition on all links of two clusters, read on slots. -/
theorem all_links_iff (hg : 0 < g) (hm : φ.length ≤ g * mu g φ) (a b : Fin g) (P : ℕ → ℕ → Bool) :
    ((links g k φ a.val b.val).all fun p => P p.1 p.2) = true ↔
      ∀ s s' : Sl (mu g φ) k, Link φ (a, s) (b, s') → P (loc s) (loc s') = true := by
  simp only [List.all_eq_true, mem_links hg]
  constructor
  · intro h s s' hl
    refine h (loc s, loc s') ⟨loc_lt s, loc_lt s', ?_⟩
    rw [← idx_eq, ← idx_eq]
    exact (linkB_iff hm _ _).2 hl
  · rintro h ⟨r, r'⟩ ⟨h1, h2, h3⟩
    obtain ⟨s, rfl⟩ := exists_loc h1
    obtain ⟨s', rfl⟩ := exists_loc h2
    simp only [← idx_eq] at h3
    exact h s s' ((linkB_iff hm _ _).1 h3)

theorem boole_congr {P Q : Prop} {_ : Decidable P} {_ : Decidable Q} (h : P ↔ Q) :
    (if P then (1 : ℤ) else 0) = if Q then 1 else 0 := by
  by_cases hp : P
  · rw [if_pos hp, if_pos (h.1 hp)]
  · rw [if_neg hp, if_neg fun hq => hp (h.2 hq)]

/-- The plain weight is the weight of the network. -/
theorem wF_eq (hg : 0 < g) (hm : φ.length ≤ g * mu g φ) (a : Fin g) (z : List Bool) :
    wF g k (φ, (a.val, z)) = weight φ a (bits (μ := mu g φ) (k := k) z) := by
  unfold wF weight
  refine boole_congr ?_
  simp only [Bool.and_eq_true, and_assoc]
  refine and_congr ?_ (and_congr ?_ ?_)
  · simp only [List.all_eq_true, locals_eq hg, List.mem_range, Bool.or_eq_true, Bool.not_eq_true']
    constructor
    · intro h s hs
      rcases h _ (loc_lt s) with h' | h'
      · rw [← idx_eq, litAt_idx, hs] at h'; simp at h'
      · exact h'
    · intro h r hr
      obtain ⟨s, rfl⟩ := exists_loc hr
      rw [← idx_eq, litAt_idx]
      cases hs : lit φ (a, s) with
      | none => right; exact h s hs
      | some l => left; rfl
  · simp only [List.all_eq_true, rows_eq hg, List.mem_range, Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
      List.any_eq_true, beq_iff_eq]
    constructor
    · intro h c hc
      rcases h _ c.2 with h' | ⟨j, hj, h'⟩
      · exact absurd hc h'
      · refine ⟨⟨j, hj⟩, ?_⟩
        rw [← litAt_idx]
        exact h'
    · intro h c hc
      by_cases hlt : a.val * mu g φ + c < φ.length
      · obtain ⟨j, hj⟩ := h ⟨c, hc⟩ hlt
        rw [← litAt_idx] at hj
        exact Or.inr ⟨j.val, j.2, hj⟩
      · exact Or.inl hlt
  · rw [all_links_iff hg hm a a fun r r' => z.getD r false == z.getD r' false]
    simp only [beq_iff_eq, bits]

/-! ### Labels -/

theorem zip_all_iff {α : Type} (u : α → Bool) : ∀ (L : List α) (θ : List Bool), θ.length = L.length →
    (((L.zip θ).all fun p => u p.1 == p.2) = true ↔ θ = L.map u)
  | [], [], _ => by simp
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | x :: L, t :: θ, h => by
    have ih := zip_all_iff u L θ (by simpa using h)
    simp only [List.zip_cons_cons, List.all_cons, Bool.and_eq_true, beq_iff_eq, ih, List.map_cons, List.cons.injEq]
    exact and_congr_left fun _ => eq_comm

/-- One bit a link: the sum over the label words restores the equalities. -/
theorem sum_words_zip {α : Type} (L : List α) (u v : α → Bool) :
    ∑ θ ∈ words L.length, (if ((L.zip θ).all fun p => u p.1 == p.2) then (1 : ℤ) else 0) *
      (if ((L.zip θ).all fun p => v p.1 == p.2) then 1 else 0) = if (L.all fun p => u p == v p) then 1 else 0 := by
  rw [Finset.sum_eq_single (L.map u)]
  · rw [if_pos ((zip_all_iff u L _ (by simp)).2 rfl), one_mul]
    refine boole_congr ?_
    rw [zip_all_iff v L _ (by simp)]
    simp only [List.all_eq_true, beq_iff_eq, List.map_inj_left]
  · intro θ hθ hne
    rw [if_neg, zero_mul]
    exact fun h => hne ((zip_all_iff u L θ (mem_words.1 hθ)).1 h)
  · intro h
    exact absurd (mem_words.2 (by simp)) h

/-- The interaction of clusters a < b on words. -/
theorem wordNet_Ψ_lt {a b : Fin g} (h : a < b) (z z' : List Bool) : (wordNet g k φ).Ψ a b z z' =
    if ((links g k φ a.val b.val).all fun p => z.getD p.1 false == z'.getD p.2 false) then 1 else 0 := by
  have h' : a.val < b.val := h
  have hn : ¬ b.val < a.val := by omega
  simp only [Network.Ψ, Network.lab, wordNet, fF, min_eq_left h.le, max_eq_right h.le, capF, min_eq_left h'.le,
    max_eq_right h'.le, if_pos h', if_neg hn]
  exact sum_words_zip (links g k φ a.val b.val) (fun p => z.getD p.1 false) (fun p => z'.getD p.2 false)

theorem wordNet_Ψ_eq (hg : 0 < g) (hm : φ.length ≤ g * mu g φ) {a b : Fin g} (h : a < b) (z z' : List Bool) :
    (wordNet g k φ).Ψ a b z z' = (net φ g (mu g φ) k).Ψ a b (bits z) (bits z') := by
  rw [wordNet_Ψ_lt h, SatNet.Ψ_of_lt h]
  refine boole_congr ?_
  rw [all_links_iff hg hm a b fun r r' => z.getD r false == z'.getD r' false]
  simp only [beq_iff_eq, bits]

/-- The number of links is the capacity of the network. -/
theorem length_links (hg : 0 < g) (hm : φ.length ≤ g * mu g φ) (a b : Fin g) :
    (links g k φ a.val b.val).length = #{s : Sl (mu g φ) k | Out φ a b s} := by
  classical
  rw [← List.toFinset_card_of_nodup (nodup_links hg _ _)]
  set A : Finset (Sl (mu g φ) k × Sl (mu g φ) k) := {q | Link φ (a, q.1) (b, q.2)} with hA
  have h1 : ({s : Sl (mu g φ) k | Out φ a b s} : Finset _) = A.image Prod.fst := by
    ext s
    simp only [mem_filter, mem_univ, true_and, mem_image, hA, Prod.exists, exists_and_right, exists_eq_right, Out]
  have h2 : (links g k φ a.val b.val).toFinset = A.image fun q => (loc q.1, loc q.2) := by
    ext ⟨r, r'⟩
    simp only [List.mem_toFinset, mem_links hg, mem_image, hA, mem_filter, mem_univ, true_and, Prod.mk.injEq]
    constructor
    · rintro ⟨hr, hr', hl⟩
      obtain ⟨s, rfl⟩ := exists_loc hr
      obtain ⟨s', rfl⟩ := exists_loc hr'
      rw [← idx_eq, ← idx_eq] at hl
      exact ⟨(s, s'), (linkB_iff hm _ _).1 hl, rfl, rfl⟩
    · rintro ⟨⟨s, s'⟩, hl, rfl, rfl⟩
      refine ⟨loc_lt s, loc_lt s', ?_⟩
      rw [← idx_eq, ← idx_eq]
      exact (linkB_iff hm _ _).2 hl
  have loc_inj : ∀ s s' : Sl (mu g φ) k, loc s = loc s' → s = s' := fun s s' h => by
    obtain ⟨e1, e2⟩ := SatNet.mul_add_inj' s.2.2 s'.2.2 h
    exact Prod.ext (Fin.ext e1) (Fin.ext e2)
  rw [h1, h2, Finset.card_image_of_injOn, Finset.card_image_of_injOn]
  · rintro ⟨s, s'⟩ hq ⟨t, t'⟩ hq' (e : s = t)
    subst e
    have hl : Link φ (a, s) (b, s') := by simpa [hA] using hq
    have hl' : Link φ (a, s) (b, t') := by simpa [hA] using hq'
    have := hl.succ_unique idx_injective hl'
    simp only [Prod.mk.injEq, true_and] at this
    rw [this]
  · rintro ⟨s, s'⟩ _ ⟨t, t'⟩ _ e
    simp only [Prod.mk.injEq] at e
    rw [loc_inj _ _ e.1, loc_inj _ _ e.2]

theorem wordNet_c (hg : 0 < g) (hm : φ.length ≤ g * mu g φ) (a b : Fin g) :
    (wordNet g k φ).c a b = (net φ g (mu g φ) k).c a b := by
  have h := length_links (k := k) hg hm (min a b) (max a b)
  simp only [wordNet, capF, net]
  rw [← h]
  rcases le_total a b with hab | hab
  · have : a.val ≤ b.val := hab
    rw [min_eq_left hab, max_eq_right hab, min_eq_left this, max_eq_right this]
  · have : b.val ≤ a.val := hab
    rw [min_eq_right hab, max_eq_left hab, min_eq_right this, max_eq_left this]

/-! ### The value and the size -/

/-- Two networks that agree along a bijection of their states have the same value. -/
theorem value_congr {J σ τ σ' τ' : Type} [Fintype J] [LinearOrder J] (N : Network J σ τ) (N' : Network J σ' τ')
    (es : σ' → σ) (hS : ∀ a, Set.BijOn es (N'.S a) (N.S a)) (hW : ∀ a z, N'.W a z = N.W a (es z))
    (hΨ : ∀ a b, a < b → ∀ z z', N'.Ψ a b z z' = N.Ψ a b (es z) (es z')) : N'.value = N.value := by
  unfold Network.value
  refine Finset.sum_nbij (fun z a => es (z a)) ?_ ?_ ?_ ?_
  · intro z hz
    rw [Fintype.mem_piFinset] at *
    exact fun a => (hS a).mapsTo (hz a)
  · intro z hz z' hz' h
    funext a
    exact (hS a).injOn (Fintype.mem_piFinset.1 (Finset.mem_coe.1 hz) a) (Fintype.mem_piFinset.1 (Finset.mem_coe.1 hz') a)
      (congrFun h a)
  · intro y hy
    have : ∀ a, ∃ x ∈ N'.S a, es x = y a := fun a => (hS a).surjOn (Fintype.mem_piFinset.1 (Finset.mem_coe.1 hy) a)
    choose x hx hxy using this
    exact ⟨x, Finset.mem_coe.2 (Fintype.mem_piFinset.2 hx), funext hxy⟩
  · intro z _
    congr 1
    · exact Finset.prod_congr rfl fun a _ => hW a _
    · exact Finset.prod_congr rfl fun p hp => hΨ _ _ (Finset.mem_filter.1 hp).2 _ _

public theorem le_mul_mu {g : ℕ} (hg : 0 < g) (φ : Fml) : φ.length ≤ g * mu g φ := SatNet.le_mul_ceil _ hg

/-- The network on words has the value of `SatNet.net`, the network of a formula as in Section 6. -/
public theorem value_wordNet (hg : 0 < g) : (wordNet g k φ).value = (net φ g (mu g φ) k).value :=
  value_congr _ _ bits (fun _ => bijOn_bits) (fun a z => wF_eq hg (le_mul_mu hg φ) a z)
    fun _ _ h z z' => wordNet_Ψ_eq hg (le_mul_mu hg φ) h z z'

/-- The network on words has the same U, the sum of the capacities over ordered pairs of clusters,
as `SatNet.net`. -/
public theorem U_wordNet (hg : 0 < g) : (wordNet g k φ).U = (net φ g (mu g φ) k).U := by
  unfold Network.U
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => wordNet_c hg (le_mul_mu hg φ) a b

theorem abs_boole_le (p : Prop) [Decidable p] : |if p then (1 : ℤ) else 0| ≤ 1 := by
  split_ifs <;> simp

public theorem lab_wordNet (a b : Fin g) : (wordNet g k φ).lab a b = words (capF g k φ a.val b.val) := by
  simp only [Network.lab, wordNet, capF]
  rcases le_total a b with hab | hab
  · have : a.val ≤ b.val := hab
    simp [min_eq_left hab, max_eq_right hab, min_eq_left this, max_eq_right this]
  · have : b.val ≤ a.val := hab
    simp [min_eq_right hab, max_eq_left hab, min_eq_right this, max_eq_left this, min_eq_left this, max_eq_right this]

/-- The network on words has size 2kμ: every node has at most 2^(2kμ) states and at most 2kμ label
bits.
Its weights, factors and interactions are 0 or 1, so the bound 2^B on their absolute values holds
for every B. -/
public theorem sized_wordNet (hg : 0 < g) (B : ℕ) : (wordNet g k φ).Sized (2 * k * mu g φ) B where
  card_S a := by
    simp only [wordNet, card_words]
    exact Nat.pow_le_pow_right (by norm_num) (by rw [Nat.mul_assoc, Nat.mul_comm k]; omega)
  abs_W a z := by
    simp only [wordNet, wF]
    exact (abs_boole_le _).trans (one_le_pow₀ (by norm_num))
  c_symm a b := by simp only [wordNet, capF, min_comm, max_comm]
  sum_c a := by
    rw [Finset.sum_congr rfl fun b _ => wordNet_c hg (le_mul_mu hg φ) a b]
    exact (sized_net (φ := φ) (g := g) (μ := mu g φ) (k := k) B).sum_c a
  card_lab a b _ := by
    rw [lab_wordNet, card_words]
    rfl
  abs_f a b z θ := by
    have h1 : (1 : ℤ) ≤ 2 ^ B := one_le_pow₀ (by norm_num)
    simp only [wordNet, fF]
    split_ifs <;> simp [h1]
  abs_Ψ a b z z' hab := by
    rcases lt_or_gt_of_ne hab with h | h
    · rw [wordNet_Ψ_lt h]; exact (abs_boole_le _).trans (one_le_pow₀ (by norm_num))
    · rw [Network.Ψ_comm, wordNet_Ψ_lt h]; exact (abs_boole_le _).trans (one_le_pow₀ (by norm_num))

end Count

end Groundwork.Prog
