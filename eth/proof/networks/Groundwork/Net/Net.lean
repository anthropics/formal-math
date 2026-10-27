/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Groundwork.Net.Defs
public import Groundwork.Net.Calculus

/-! Theorems on the definitions of Groundwork.Net.Defs: an instance
padded to a larger alphabet has the value of the instance's network, the half-edge form of Z,
merging keeps the value and
multiplies the size by the class size, and the instance made from a network has the network's value;
also bounds on the sizes and
values of a merged network and of the instance made from a network. -/

namespace Groundwork

open Finset

variable {J J' σ τ A A' : Type*}

/-- A product over ordered pairs of distinct nodes, regrouped by unordered pairs. -/
public theorem prod_erase_eq_pairs [Fintype J] [LinearOrder J] (G : J → J → ℤ) :
    ∏ a, ∏ b ∈ univ.erase a, G a b = ∏ p ∈ pairs J, G p.1 p.2 * G p.2 p.1 := by
  rw [← Finset.prod_finset_product' (univ.filter fun p : J × J => p.1 ≠ p.2) univ (fun a => univ.erase a)
    (by intro p; simp [eq_comm])]
  rw [Finset.prod_mul_distrib]
  have h1 : ∏ p ∈ pairs J, G p.2 p.1 = ∏ p ∈ univ.filter (fun p : J × J => p.2 < p.1), G p.1 p.2 :=
    Finset.prod_nbij' Prod.swap Prod.swap (by intro p; simp [pairs]) (by intro p; simp [pairs]) (by intro p; simp)
      (by intro p; simp) (by intro p; simp)
  rw [h1, pairs, ← Finset.prod_union]
  · congr 1; ext p; simp [lt_or_lt_iff_ne]
  · rw [Finset.disjoint_left]; intro p; simp; grind

/-- Products of nonnegative factors are monotone. -/
public theorem prod_le_prod_of_nonneg {ι R : Type*} [CommSemiring R] [PartialOrder R] [IsOrderedRing R] (s : Finset ι)
    (f g : ι → R) (h0 : ∀ i ∈ s, 0 ≤ f i) (h1 : ∀ i ∈ s, f i ≤ g i) : ∏ i ∈ s, f i ≤ ∏ i ∈ s, g i := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
    simp only [Finset.prod_cons, Finset.forall_mem_cons] at *
    exact mul_le_mul h1.1 (ih h0.2 h1.2) (Finset.prod_nonneg h0.2) (h0.1.trans h1.1)

/-- A product of at most k integers of absolute value at most 2^B has absolute value at most
2^(B·k). -/
public theorem abs_prod_le_two_pow {ι : Type*} (s : Finset ι) (f : ι → ℤ) {B k : ℕ} (h : ∀ i ∈ s, |f i| ≤ 2 ^ B)
    (hk : #s ≤ k) : |∏ i ∈ s, f i| ≤ 2 ^ (B * k) := by
  rw [Finset.abs_prod]
  calc ∏ i ∈ s, |f i| ≤ ∏ _i ∈ s, (2 : ℤ) ^ B := prod_le_prod_of_nonneg _ _ _ (fun _ _ => abs_nonneg _) h
    _ = 2 ^ (B * #s) := by rw [Finset.prod_const, pow_mul]
    _ ≤ 2 ^ (B * k) := pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_left _ hk)

/-- If every class has at most m members, there are at most m² ordered pairs from one class to
another. -/
public theorem card_class_pairs_le [Fintype J] [DecidableEq J'] (χ : J → J') {m : ℕ} (hm : ∀ G, #{a | χ a = G} ≤ m)
    (G G' : J') : #{p : J × J | χ p.1 = G ∧ χ p.2 = G'} ≤ m * m := by
  have h : (univ.filter fun p : J × J => χ p.1 = G ∧ χ p.2 = G') =
      (univ.filter fun a => χ a = G) ×ˢ (univ.filter fun b => χ b = G') := by
    ext p; simp
  rw [h, Finset.card_product]
  exact Nat.mul_le_mul (hm G) (hm G')

/-- Both orders of a pair a < b have the name (a, b). -/
public theorem pr_of_lt [LinearOrder J] {a b : J} (h : a < b) : pr a b = (a, b) ∧ pr b a = (a, b) := by
  simp [pr, h.le]

namespace Network

/-- The label set of a pair does not depend on the order of the two nodes. -/
public theorem lab_comm [LinearOrder J] (N : Network J σ τ) (a b : J) : N.lab a b = N.lab b a := by
  simp [lab, min_comm, max_comm]

/-- The interaction of a pair, read from the other side. -/
public theorem Ψ_comm [LinearOrder J] (N : Network J σ τ) (a b : J) (z z' : σ) : N.Ψ a b z z' = N.Ψ b a z' z := by
  unfold Ψ
  rw [lab_comm]
  exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

/-- The instance made from a network has the network's value, for every way (D, dec) of naming its
labels by elements of A. -/
public theorem Z_toInst [Fintype J] [LinearOrder J] [Fintype A] [DecidableEq A] (N : Network J σ τ)
    (D : J → J → Finset A) (dec : J → J → A → τ) (h : ∀ a b, a < b → Set.BijOn (dec a b) (D a b) (N.Θ a b)) (d : A) :
    (N.toInst D dec).Z d = N.value := by
  unfold Inst.Z value toInst
  simp only [Finset.prod_univ_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun z _ => ?_
  simp only [Finset.prod_mul_distrib, ← Finset.mul_sum]
  congr 1
  have key : ∀ Λ : J × J → A,
      ∏ a, ∏ b ∈ univ.erase a, (if star Λ a b ∈ D (min a b) (max a b) then
        N.f a b (z a) (dec (min a b) (max a b) (star Λ a b)) else 0) =
      ∏ p : J × J with p.1 < p.2, (if Λ p ∈ D p.1 p.2 then N.f p.1 p.2 (z p.1) (dec p.1 p.2 (Λ p)) else 0) *
        (if Λ p ∈ D p.1 p.2 then N.f p.2 p.1 (z p.2) (dec p.1 p.2 (Λ p)) else 0) := by
    intro Λ
    rw [prod_erase_eq_pairs]
    refine Finset.prod_congr rfl fun p hp => ?_
    have hp' : p.1 < p.2 := by simpa [pairs] using hp
    simp [star, pr_of_lt hp', hp'.le]
  simp only [key]
  rw [labellings, sum_tuples_prod (fun p : J × J => p.1 < p.2) (fun _ => univ) d
    (fun p x => (if x ∈ D p.1 p.2 then N.f p.1 p.2 (z p.1) (dec p.1 p.2 x) else 0) *
        (if x ∈ D p.1 p.2 then N.f p.2 p.1 (z p.2) (dec p.1 p.2 x) else 0))]
  refine Finset.prod_congr rfl fun p hp => ?_
  have hp' : p.1 < p.2 := by simpa [pairs] using hp
  rw [sum_renamed (D p.1 p.2) (dec p.1 p.2) (N.Θ p.1 p.2) (h _ _ hp')]
  simp [Ψ, lab, hp'.le]

end Network

/-! ### Half-edges and padding -/

/-- An instance as a network: a state of v is a vector of half-edges with source v; the edge {v,w}
asks that the two
half-edges agree. The capacities are set to 0: no statement on sizes is made of this network. -/
@[expose] public def Inst.net [Fintype J] [DecidableEq J] [Fintype A] [DecidableEq A] (R : Inst J A) (d : A) :
    Network J (J → A) A where
  S v := tuples (fun w => w ≠ v) (fun _ => univ) d
  W := R
  Θ _ _ := univ
  f _ w z θ := if z w = θ then 1 else 0
  c _ _ := 0

/-- An instance, made into a network and back into an instance over a larger alphabet, is the padded
instance. -/
public theorem Inst.toInst_net [Fintype J] [LinearOrder J] [Fintype A] [DecidableEq A] [DecidableEq A'] (R : Inst J A) (d : A)
    (D : Finset A') (dec : A' → A) : (R.net d).toInst (fun _ _ => D) (fun _ _ => dec) = R.pad d D dec := by
  funext v θ
  unfold Network.toInst Inst.pad Inst.net
  simp only
  split_ifs with hall
  · rw [Finset.sum_eq_single (fun w => if w = v then d else dec (θ w))]
    · rw [Finset.prod_eq_one, mul_one]
      intro b hb
      have hb' : b ≠ v := by simpa using hb
      simp [hall b hb', hb']
    · intro z hz hne
      have hz' := (mem_tuples _ _ _ _).1 hz
      obtain ⟨b, hb⟩ : ∃ b, z b ≠ (if b = v then d else dec (θ b)) := by
        by_contra hcon
        exact hne (funext fun b => by_contra fun hb => hcon ⟨b, hb⟩)
      have hbv : b ≠ v := by
        rintro rfl
        exact hb (by simpa using (hz' b).2 (by simp))
      rw [Finset.prod_eq_zero (i := b) (by simp [hbv]), mul_zero]
      simp only [hbv, ite_false] at hb
      simp [hall b hbv, hb]
    · intro hn
      exact absurd ((mem_tuples _ _ _ _).2 fun w => ⟨fun _ => mem_univ _, fun hw => by simp at hw; simp [hw]⟩) hn
  · obtain ⟨w, hw, hwD⟩ : ∃ w, w ≠ v ∧ θ w ∉ D := by
      by_contra hcon
      exact hall fun w hw => by_contra fun hD => hcon ⟨w, hw, hD⟩
    refine Finset.sum_eq_zero fun z _ => ?_
    rw [Finset.prod_eq_zero (i := w) (by simp [hw]), mul_zero]
    simp [hwD]

/-- The padded instance has the value of the network of the instance. -/
public theorem Inst.Z_pad_eq_value [Fintype J] [LinearOrder J] [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A']
    (R : Inst J A) (d : A) (d' : A') (D : Finset A') (dec : A' → A) (h : Set.BijOn dec D Set.univ) :
    (R.pad d D dec).Z d' = (R.net d).value := by
  rw [← Inst.toInst_net]
  exact Network.Z_toInst _ _ _ (fun _ _ _ => by simpa [Inst.net] using h) d'

/-- An instance has the value of its network. -/
public theorem Inst.Z_eq_value [Fintype J] [LinearOrder J] [Fintype A] [DecidableEq A] (R : Inst J A) (d : A) :
    R.Z d = (R.net d).value := by
  rw [← Inst.Z_pad_eq_value R d d univ id (by simp)]
  unfold Inst.Z Inst.pad
  refine Finset.sum_congr rfl fun Λ hΛ => Finset.prod_congr rfl fun v _ => ?_
  have hv : Λ (v, v) = d := ((mem_tuples _ _ _ _).1 hΛ (v, v)).2 (by simp)
  simp only [mem_univ, implies_true, ite_true, id]
  congr 1
  funext w
  split_ifs with hw
  · subst hw; simp [star, pr, hv]
  · rfl

/-- Half-edges: every edge is cut into two half-edges that must agree.
Z(R) = Σ_ℓ ∏_w R_w(ℓ(w,·)) ∏_{w<w'} [ℓ(w,w') = ℓ(w',w)], with ℓ(w,w) = d. -/
public theorem Inst.Z_eq_halfEdges [Fintype J] [LinearOrder J] [Fintype A] [DecidableEq A] (R : Inst J A) (d : A) :
    R.Z d = ∑ ℓ ∈ Fintype.piFinset fun w : J => tuples (fun w' => w' ≠ w) (fun _ => (univ : Finset A)) d,
      (∏ w, R w (ℓ w)) * ∏ p ∈ pairs J, if ℓ p.1 p.2 = ℓ p.2 p.1 then 1 else 0 := by
  rw [Inst.Z_eq_value]
  unfold Network.value
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  congr 1
  refine Finset.prod_congr rfl fun p _ => ?_
  simp [Network.Ψ, Network.lab, Inst.net]

/-! ### Merging -/

namespace Network

/-- The interaction of two classes G < G' is the product of the interactions of their members. -/
public theorem merge_Ψ_lt [Fintype J] [LinearOrder J] [LinearOrder J'] (N : Network J σ τ) (χ : J → J') (s₀ : σ) (t₀ : τ)
    {G G' : J'} (h : G < G') (z z' : J → σ) :
    (N.merge χ s₀ t₀).Ψ G G' z z' = ∏ p : J × J with χ p.1 = G ∧ χ p.2 = G', N.Ψ p.1 p.2 (z p.1) (z' p.2) := by
  have h2 : ∀ t : J × J → τ, ∏ q : J × J with χ q.1 = G' ∧ χ q.2 = G, N.f q.1 q.2 (z' q.1) (t q.swap) =
      ∏ p : J × J with χ p.1 = G ∧ χ p.2 = G', N.f p.2 p.1 (z' p.2) (t p) := fun t =>
    Finset.prod_nbij' Prod.swap Prod.swap (by intro p; simp [and_comm]) (by intro p; simp [and_comm]) (by intro p; simp)
      (by intro p; simp) (by intro p; simp)
  simp only [Ψ, lab, merge, h.le, min_eq_left, max_eq_right, h, ite_true, h.not_gt, ite_false, h2]
  rw [← prod_factorised]

/-- The interaction of two classes is the product of the interactions of their members. -/
public theorem merge_Ψ [Fintype J] [LinearOrder J] [LinearOrder J'] (N : Network J σ τ) (χ : J → J') (s₀ : σ) (t₀ : τ)
    {G G' : J'} (h : G ≠ G') (z z' : J → σ) :
    (N.merge χ s₀ t₀).Ψ G G' z z' = ∏ p : J × J with χ p.1 = G ∧ χ p.2 = G', N.Ψ p.1 p.2 (z p.1) (z' p.2) := by
  rcases lt_or_gt_of_ne h with h | h
  · exact merge_Ψ_lt N χ s₀ t₀ h z z'
  · rw [Ψ_comm, merge_Ψ_lt N χ s₀ t₀ h z' z]
    exact Finset.prod_nbij' Prod.swap Prod.swap (by intro p; simp [and_comm]) (by intro p; simp [and_comm])
      (by intro p; simp) (by intro p; simp) (by intro p _; simp [Ψ_comm])

/-- A product of a symmetric function over unordered pairs in different classes, oriented by class
or by node. -/
public theorem prod_orient [Fintype J] [LinearOrder J] [LinearOrder J'] (χ : J → J') (F : J × J → ℤ) (hF : ∀ p, F p.swap = F p) :
    ∏ p : J × J with χ p.1 < χ p.2, F p = ∏ p ∈ pairs J with χ p.1 ≠ χ p.2, F p := by
  refine Finset.prod_nbij' (fun p => if p.1 < p.2 then p else p.swap) (fun p => if χ p.1 < χ p.2 then p else p.swap)
    ?_ ?_ ?_ ?_ ?_
  · rintro ⟨a, b⟩ h
    simp only [pairs, mem_filter, mem_univ, true_and] at h ⊢
    split_ifs with hab <;> simp only [Prod.swap_prod_mk] <;> grind
  · rintro ⟨a, b⟩ h
    simp only [pairs, mem_filter, mem_univ, true_and] at h ⊢
    split_ifs with hab <;> simp only [Prod.swap_prod_mk] <;> grind
  · rintro ⟨a, b⟩ h
    simp only [mem_filter, mem_univ, true_and] at h ⊢
    split_ifs <;> simp_all
    grind
  · rintro ⟨a, b⟩ h
    simp only [pairs, mem_filter, mem_univ, true_and] at h ⊢
    split_ifs <;> simp_all
    grind
  · rintro p _
    split_ifs
    · rfl
    · exact (hF p).symm

/-- One summand of the value of a network, regrouped by classes. -/
public theorem merge_summand [Fintype J] [LinearOrder J] [Fintype J'] [LinearOrder J'] (N : Network J σ τ) (χ : J → J')
    (s₀ : σ) (t₀ : τ) (z : J → σ) :
    (∏ a, N.W a (z a)) * ∏ p ∈ pairs J, N.Ψ p.1 p.2 (z p.1) (z p.2) =
    (∏ G, (N.merge χ s₀ t₀).W G (fun a => if χ a = G then z a else s₀)) *
      ∏ q ∈ pairs J', (N.merge χ s₀ t₀).Ψ q.1 q.2 (fun a => if χ a = q.1 then z a else s₀)
        (fun a => if χ a = q.2 then z a else s₀) := by
  set F : J × J → ℤ := fun p => N.Ψ p.1 p.2 (z p.1) (z p.2) with hFdef
  have hW : ∀ G, (N.merge χ s₀ t₀).W G (fun a => if χ a = G then z a else s₀) =
      (∏ a with χ a = G, N.W a (z a)) * ∏ p ∈ pairs J with χ p.1 = G ∧ χ p.2 = G, F p := by
    intro G
    simp only [merge]
    congr 1
    · refine Finset.prod_congr rfl fun a ha => ?_
      simp [(Finset.mem_filter.1 ha).2]
    · refine Finset.prod_congr rfl fun p hp => ?_
      obtain ⟨h1, h2⟩ := (Finset.mem_filter.1 hp).2
      simp [F, h1, h2]
  have hΨ : ∀ q ∈ pairs J', (N.merge χ s₀ t₀).Ψ q.1 q.2 (fun a => if χ a = q.1 then z a else s₀)
        (fun a => if χ a = q.2 then z a else s₀) = ∏ p : J × J with χ p.1 = q.1 ∧ χ p.2 = q.2, F p := by
    intro q hq
    have hq' : q.1 < q.2 := by simpa [pairs] using hq
    rw [merge_Ψ_lt N χ s₀ t₀ hq']
    refine Finset.prod_congr rfl fun p hp => ?_
    obtain ⟨h1, h2⟩ := (Finset.mem_filter.1 hp).2
    simp [F, h1, h2]
  rw [Finset.prod_congr rfl hΨ]
  simp only [hW, Finset.prod_mul_distrib]
  rw [Finset.prod_fiberwise univ χ (fun a => N.W a (z a))]
  have h1 : ∏ G, ∏ p ∈ pairs J with χ p.1 = G ∧ χ p.2 = G, F p = ∏ p ∈ pairs J with χ p.1 = χ p.2, F p := by
    rw [← Finset.prod_fiberwise ((pairs J).filter fun p => χ p.1 = χ p.2) (fun p => χ p.1)]
    refine Finset.prod_congr rfl fun G _ => ?_
    rw [Finset.filter_filter]
    refine Finset.prod_congr (Finset.filter_congr fun p _ => ?_) fun _ _ => rfl
    grind
  have h2 : ∏ q ∈ pairs J', ∏ p : J × J with χ p.1 = q.1 ∧ χ p.2 = q.2, F p = ∏ p : J × J with χ p.1 < χ p.2, F p := by
    rw [← Finset.prod_fiberwise_of_maps_to (s := univ.filter fun p : J × J => χ p.1 < χ p.2) (t := pairs J')
      (g := fun p => (χ p.1, χ p.2)) (by intro p; simp [pairs])]
    refine Finset.prod_congr rfl fun q hq => ?_
    have hq' : q.1 < q.2 := by simpa [pairs] using hq
    rw [Finset.filter_filter]
    refine Finset.prod_congr (Finset.filter_congr fun p _ => ?_) fun _ _ => rfl
    rw [Prod.ext_iff]
    grind
  rw [h1, h2, prod_orient χ F (fun p => N.Ψ_comm _ _ _ _), mul_assoc, Finset.prod_filter_mul_prod_filter_not]

/-- Merging keeps the value. -/
public theorem value_merge [Fintype J] [LinearOrder J] [Fintype J'] [LinearOrder J'] (N : Network J σ τ) (χ : J → J')
    (s₀ : σ) (t₀ : τ) : (N.merge χ s₀ t₀).value = N.value := by
  unfold value
  symm
  refine Finset.sum_nbij' (fun z G a => if χ a = G then z a else s₀) (fun Z a => Z (χ a) a) ?_ ?_ ?_ ?_ ?_
  · intro z hz
    rw [Fintype.mem_piFinset] at hz ⊢
    intro G
    exact (mem_tuples _ _ _ _).2 fun a => ⟨fun h => by simp [h, hz a], fun h => by simp [h]⟩
  · intro Z hZ
    rw [Fintype.mem_piFinset] at hZ ⊢
    intro a
    exact ((mem_tuples _ _ _ _).1 (hZ (χ a)) a).1 rfl
  · intro z _
    funext a
    simp
  · intro Z hZ
    rw [Fintype.mem_piFinset] at hZ
    funext G a
    by_cases h : χ a = G
    · subst h; simp
    · simp [h, ((mem_tuples _ _ _ _).1 (hZ G) a).2 h]
  · intro z _
    exact merge_summand N χ s₀ t₀ z

/-- The number of states of a class. -/
public theorem card_merge_S [Fintype J] [LinearOrder J] [LinearOrder J'] (N : Network J σ τ) (χ : J → J') (s₀ : σ) (t₀ : τ)
    (G : J') : #((N.merge χ s₀ t₀).S G) = ∏ a with χ a = G, #(N.S a) :=
  card_tuples _ _ _

/-- If every class has at most m members, the merged network has the shape of a network of size P·m. -/
public theorem merge_shaped [Fintype J] [LinearOrder J] [Fintype J'] [LinearOrder J'] (N : Network J σ τ) (χ : J → J')
    (s₀ : σ) (t₀ : τ) {P m : ℕ} (h : N.Shaped P) (hm : ∀ G, #{a | χ a = G} ≤ m) :
    (N.merge χ s₀ t₀).Shaped (P * m) := by
  have hc : ∀ G G', (N.merge χ s₀ t₀).c G G' = (N.merge χ s₀ t₀).c G' G := by
    intro G G'
    simp only [merge]
    exact Finset.sum_nbij' Prod.swap Prod.swap (by intro p; simp [and_comm]) (by intro p; simp [and_comm])
      (by intro p; simp) (by intro p; simp) (by intro p _; exact h.c_symm _ _)
  have hlab : ∀ G G', G < G' → #((N.merge χ s₀ t₀).lab G G') ≤ 2 ^ (N.merge χ s₀ t₀).c G G' := by
    intro G G' hlt
    simp only [lab, merge, min_eq_left hlt.le, max_eq_right hlt.le]
    rw [card_tuples, ← Finset.prod_pow_eq_pow_sum]
    refine prod_le_prod_of_nonneg _ _ _ (fun _ _ => Nat.zero_le _) fun p hp => ?_
    obtain ⟨h1, h2⟩ := (Finset.mem_filter.1 hp).2
    exact h.card_lab _ _ (by rintro he; rw [he, h2] at h1; exact hlt.ne' h1)
  refine ⟨?_, hc, ?_, ?_⟩
  · intro G
    rw [card_merge_S]
    calc ∏ a with χ a = G, #(N.S a) ≤ ∏ a with χ a = G, 2 ^ P :=
          prod_le_prod_of_nonneg _ _ _ (fun _ _ => Nat.zero_le _) (fun a _ => h.card_S a)
      _ = 2 ^ (P * #{a | χ a = G}) := by rw [Finset.prod_const, pow_mul]
      _ ≤ 2 ^ (P * m) := Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left _ (hm G))
  · intro G
    simp only [merge]
    calc ∑ G' ∈ univ.erase G, ∑ p : J × J with χ p.1 = G ∧ χ p.2 = G', N.c p.1 p.2
        = ∑ p : J × J with χ p.1 = G ∧ χ p.2 ≠ G, N.c p.1 p.2 := by
          rw [← Finset.sum_fiberwise_of_maps_to (s := univ.filter fun p : J × J => χ p.1 = G ∧ χ p.2 ≠ G)
            (t := univ.erase G) (g := fun p => χ p.2) (by intro p; simp)]
          refine Finset.sum_congr rfl fun G' hG' => ?_
          have hne : G' ≠ G := by simpa using hG'
          rw [Finset.filter_filter]
          refine Finset.sum_congr (Finset.filter_congr fun p _ => ?_) fun _ _ => rfl
          grind
      _ ≤ ∑ p : J × J with χ p.1 = G ∧ p.2 ≠ p.1, N.c p.1 p.2 := by
          refine Finset.sum_le_sum_of_subset fun p hp => ?_
          simp only [mem_filter, mem_univ, true_and] at hp ⊢
          grind
      _ = ∑ a with χ a = G, ∑ b ∈ univ.erase a, N.c a b :=
          Finset.sum_finset_product' _ _ _ (by intro p; simp)
      _ ≤ ∑ a with χ a = G, P := Finset.sum_le_sum fun a _ => h.sum_c a
      _ = P * #{a | χ a = G} := by simp [mul_comm]
      _ ≤ P * m := Nat.mul_le_mul_left _ (hm G)
  · intro G G' hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact hlab _ _ hlt
    · rw [lab_comm, hc]; exact hlab _ _ hlt

/-- If every class has at most m members, the merged network has size P·m and values bounded by
2^{B·(m+m²)}:
a merged weight is a product of at most m weights and at most m² interactions, a merged factor or
interaction is a
product of at most m² factors or interactions. -/
public theorem merge_sized [Fintype J] [LinearOrder J] [Fintype J'] [LinearOrder J'] (N : Network J σ τ) (χ : J → J')
    (s₀ : σ) (t₀ : τ) {P B m : ℕ} (h : N.Sized P B) (hm : ∀ G, #{a | χ a = G} ≤ m) :
    (N.merge χ s₀ t₀).Sized (P * m) (B * (m + m * m)) := by
  have hmono : (2 : ℤ) ^ (B * (m * m)) ≤ 2 ^ (B * (m + m * m)) :=
    pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_left _ (Nat.le_add_left _ _))
  refine ⟨merge_shaped N χ s₀ t₀ h.toShaped hm, ?_, ?_, ?_⟩
  · intro G z
    simp only [merge]
    rw [abs_mul, mul_add, pow_add]
    refine mul_le_mul (abs_prod_le_two_pow _ _ (fun a _ => h.abs_W a _) (hm G)) ?_ (abs_nonneg _)
      (pow_nonneg (by norm_num) _)
    refine abs_prod_le_two_pow _ _ (fun p hp => h.abs_Ψ _ _ _ _ ?_)
      ((Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ _))).trans (card_class_pairs_le χ hm G G))
    have : p.1 < p.2 := by simpa [pairs] using (Finset.mem_filter.1 hp).1
    exact this.ne
  · intro G G' z t
    simp only [merge]
    exact (abs_prod_le_two_pow _ _ (fun p _ => h.abs_f _ _ _ _) (card_class_pairs_le χ hm G G')).trans hmono
  · intro G G' z z' hne
    rw [merge_Ψ _ _ _ _ hne]
    refine (abs_prod_le_two_pow _ _ (fun p hp => h.abs_Ψ _ _ _ _ ?_) (card_class_pairs_le χ hm G G')).trans hmono
    obtain ⟨h1, h2⟩ := (Finset.mem_filter.1 hp).2
    rintro he
    rw [he, h2] at h1
    exact hne h1.symm

/-- A value of the instance is a sum of at most 2^P terms, each a product of one weight and card J −
1 factors. -/
public theorem abs_toInst_le [Fintype J] [LinearOrder J] [DecidableEq A] (N : Network J σ τ)
    (D : J → J → Finset A) (dec : J → J → A → τ) {P B : ℕ} (h : N.Sized P B) (a : J) (θ : J → A) :
    |N.toInst D dec a θ| ≤ 2 ^ (P + B * Fintype.card J) := by
  unfold toInst
  have hJ : 0 < Fintype.card J := Fintype.card_pos_iff.2 ⟨a⟩
  have hcard : #(univ.erase a) ≤ Fintype.card J - 1 := by
    rw [Finset.card_erase_of_mem (mem_univ a), Finset.card_univ]
  have hexp : B + B * (Fintype.card J - 1) = B * Fintype.card J := by
    obtain ⟨n, hn⟩ : ∃ n, Fintype.card J = n + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hJ).symm⟩
    rw [hn, Nat.add_sub_cancel]; ring
  have h1 : ∀ z, |N.W a z * ∏ b ∈ univ.erase a, if θ b ∈ D (min a b) (max a b) then
      N.f a b z (dec (min a b) (max a b) (θ b)) else 0| ≤ 2 ^ (B * Fintype.card J) := by
    intro z
    rw [abs_mul, ← hexp, pow_add]
    refine mul_le_mul (h.abs_W a z) (abs_prod_le_two_pow _ _ (fun b _ => ?_) hcard) (abs_nonneg _)
      (pow_nonneg (by norm_num) _)
    split_ifs
    · exact h.abs_f _ _ _ _
    · simp
  calc _ ≤ ∑ z ∈ N.S a, |N.W a z * ∏ b ∈ univ.erase a, if θ b ∈ D (min a b) (max a b) then
      N.f a b z (dec (min a b) (max a b) (θ b)) else 0| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ z ∈ N.S a, (2 : ℤ) ^ (B * Fintype.card J) := Finset.sum_le_sum fun z _ => h1 z
    _ = (#(N.S a) : ℤ) * 2 ^ (B * Fintype.card J) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 2 ^ P * 2 ^ (B * Fintype.card J) := by
          refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg (by norm_num) _)
          exact_mod_cast h.card_S a
    _ = 2 ^ (P + B * Fintype.card J) := (pow_add _ _ _).symm

end Network

end Groundwork
