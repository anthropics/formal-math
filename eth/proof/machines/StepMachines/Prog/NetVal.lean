/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import StepMachines.Prog.NetProg

/-! The rebalancing of a network into K classes: what the programs of StepMachines/Prog/NetProg.lean
compute. A network on g nodes is
merged along a colouring with K colours into an instance of the problem on K nodes. mergedVal is an
entry of a tensor of
that instance, the value of the instance is the value of the network, and some colouring passes the
test goodB. -/

namespace Groundwork

open Finset

/-- The instance N.toInst D dec has the value of the network N. Its labels are words: x ∈ D a b ⊆
words ℓ stands for the
label dec a b x of N, and x ↦ dec a b x carries sums over D a b to sums over the labels of N. -/
public theorem Network.ZW_toInst {J σ τ : Type*} [Fintype J] [LinearOrder J] (N : Network J σ τ) (ℓ : ℕ) (d : List Bool)
    (D : J → J → Finset (List Bool)) (dec : J → J → List Bool → τ) (hD : ∀ a b, a < b → D a b ⊆ words ℓ)
    (h : ∀ a b, a < b → ∀ F : τ → ℤ, ∑ x ∈ D a b, F (dec a b x) = ∑ θ ∈ N.Θ a b, F θ) :
    Inst.ZW ℓ d (N.toInst D dec) = N.value := by
  unfold Inst.ZW Network.value Network.toInst
  simp only [Finset.prod_univ_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun z _ => ?_
  simp only [Finset.prod_mul_distrib, ← Finset.mul_sum]
  congr 1
  have key : ∀ Λ : J × J → List Bool,
      ∏ a, ∏ b ∈ univ.erase a, (if star Λ a b ∈ D (min a b) (max a b) then
        N.f a b (z a) (dec (min a b) (max a b) (star Λ a b)) else 0) =
      ∏ p : J × J with p.1 < p.2, (if Λ p ∈ D p.1 p.2 then N.f p.1 p.2 (z p.1) (dec p.1 p.2 (Λ p)) else 0) *
        (if Λ p ∈ D p.1 p.2 then N.f p.2 p.1 (z p.2) (dec p.1 p.2 (Λ p)) else 0) := by
    intro Λ
    rw [prod_erase_eq_pairs]
    refine Finset.prod_congr rfl fun p hp => ?_
    have hp' : p.1 < p.2 := by simpa [pairs] using hp
    simp [star, pr, hp'.le]
  simp only [key]
  rw [sum_tuples_prod (fun p : J × J => p.1 < p.2) (fun _ => words ℓ) d
    (fun p x => (if x ∈ D p.1 p.2 then N.f p.1 p.2 (z p.1) (dec p.1 p.2 x) else 0) *
        (if x ∈ D p.1 p.2 then N.f p.2 p.1 (z p.2) (dec p.1 p.2 x) else 0))]
  refine Finset.prod_congr rfl fun p hp => ?_
  have hp' : p.1 < p.2 := by simpa [pairs] using hp
  have h1 : ∀ x, (if x ∈ D p.1 p.2 then N.f p.1 p.2 (z p.1) (dec p.1 p.2 x) else 0) *
        (if x ∈ D p.1 p.2 then N.f p.2 p.1 (z p.2) (dec p.1 p.2 x) else 0) =
      if x ∈ D p.1 p.2 then N.f p.1 p.2 (z p.1) (dec p.1 p.2 x) * N.f p.2 p.1 (z p.2) (dec p.1 p.2 x) else 0 := by
    intro x; split_ifs <;> simp
  simp only [h1]
  rw [Finset.sum_ite_mem, Finset.inter_eq_right.2 (hD _ _ hp'),
    h _ _ hp' (fun θ => N.f p.1 p.2 (z p.1) θ * N.f p.2 p.1 (z p.2) θ)]
  simp [Network.Ψ, Network.lab, hp'.le]

/-- Tuples depend on the sets only where the predicate holds. -/
theorem tuples_congr' {ι X : Type*} [Fintype ι] [DecidableEq ι] (P : ι → Prop) [DecidablePred P] {T T' : ι → Finset X}
    (d : X) (h : ∀ i, P i → T i = T' i) : tuples P T d = tuples P T' d := by
  unfold tuples
  congr 1
  funext i
  split_ifs with hi
  · exact h i hi
  · rfl

theorem idxOf_map_inj {ι κ : Type*} [BEq ι] [LawfulBEq ι] [BEq κ] [LawfulBEq κ] {f : ι → κ}
    (hf : Function.Injective f) (e : List ι) (i : ι) : (e.map f).idxOf (f i) = e.idxOf i := by
  induction e with
  | nil => rfl
  | cons j e ih =>
    rw [List.map_cons, List.idxOf_cons, List.idxOf_cons, ih]
    by_cases h : j = i
    · subst h; simp
    · have h1 : (j == i) = false := by simpa using h
      have h2 : (f j == f i) = false := by simpa using fun h' => h (hf h')
      rw [h1, h2]

/-- cut reads only the first Σ c i bits. -/
theorem cut_take {ι : Type*} [DecidableEq ι] (c : ι → ℕ) (d : List Bool) (e : List ι) (w : List Bool) :
    cut c d e (w.take (e.map c).sum) = cut c d e w := by
  induction e generalizing w with
  | nil => rfl
  | cons i e ih =>
    simp only [cut, List.map_cons, List.sum_cons]
    rw [List.take_take, Nat.min_eq_left (Nat.le_add_right _ _), List.drop_take, Nat.add_sub_cancel_left, ih]

/-- A product over i < g*g as a product over pairs. -/
theorem prod_range_mul_self (g : ℕ) (F : ℕ → ℤ) :
    ∏ i ∈ range (g * g), F i = ∏ p : Fin g × Fin g, F (p.1.val * g + p.2.val) := by
  rw [Finset.prod_range, ← Fintype.prod_equiv finProdFinEquiv (fun p : Fin g × Fin g => F (p.1.val * g + p.2.val))
    (fun i : Fin (g * g) => F i.val)]
  intro p
  simp [finProdFinEquiv, Nat.mul_comm, Nat.add_comm]

namespace Prog.NetE

variable {C : Type} {K g : ℕ} (Np : PNet C)

/-- The colouring with the code x. -/
@[expose] public def chi (hK : 0 < K) (x : ℕ) (a : Fin g) : Fin K := ⟨col K x a, Nat.mod_lt _ hK⟩

/-- The members of a class, as elements of Fin g. -/
def membersF (K : ℕ) {g : ℕ} (x G : ℕ) : List (Fin g) := (List.finRange g).filter fun a => col K x a == G

theorem map_membersF (x G : ℕ) : (membersF K x G : List (Fin g)).map Fin.val = members K g x G := by
  unfold membersF members
  rw [← List.map_coe_finRange_eq_range, List.filter_map]
  rfl

theorem nodup_membersF (x G : ℕ) : (membersF K x G : List (Fin g)).Nodup :=
  (List.nodup_finRange g).filter _

theorem mem_membersF (x G : ℕ) (a : Fin g) : a ∈ membersF K x G ↔ col K x a = G := by
  simp [membersF]

/-- The pairs of members of two classes, as elements of Fin g × Fin g. -/
def prsF (K : ℕ) {g : ℕ} (x G G' : ℕ) : List (Fin g × Fin g) :=
  (membersF K x G).flatMap fun a => (membersF K x G').map fun b => (a, b)

theorem map_prsF (x G G' : ℕ) :
    (prsF K x G G' : List (Fin g × Fin g)).map (fun p => (p.1.val, p.2.val)) = prs K g x G G' := by
  unfold prsF prs
  rw [← map_membersF, ← map_membersF, List.map_flatMap, List.flatMap_map]
  simp [List.map_map, Function.comp_def]

theorem mem_prsF (x G G' : ℕ) (p : Fin g × Fin g) :
    p ∈ prsF K x G G' ↔ col K x p.1 = G ∧ col K x p.2 = G' := by
  obtain ⟨a, b⟩ := p
  simp [prsF, mem_membersF]

theorem nodup_prsF (x G G' : ℕ) : (prsF K x G G' : List (Fin g × Fin g)).Nodup := by
  have := (nodup_membersF (K := K) (g := g) x G).product (nodup_membersF (K := K) (g := g) x G')
  exact this

theorem stLens_eq (c : C) (x G : ℕ) :
    stLens K g Np c x G = (membersF K x G : List (Fin g)).map fun a => Np.n c a.val := by
  unfold stLens
  rw [← map_membersF, List.map_map]
  rfl

theorem lbLens_eq (c : C) (x G G' : ℕ) :
    lbLens K g Np c x G G' = (prsF K x G G' : List (Fin g × Fin g)).map fun p => Np.cap c p.1.val p.2.val := by
  unfold lbLens
  rw [← map_prsF, List.map_map]
  rfl

/-- The state of a member, by cut. -/
theorem zAt_eq_cut (c : C) (x G : ℕ) (z : List Bool) (a : Fin g) :
    zAt K g Np c x G z a.val = cut (fun a : Fin g => Np.n c a.val) [] (membersF K x G) z a := by
  rw [cut_eq_getD, ← stLens_eq, zAt, ← map_membersF, idxOf_map_inj Fin.val_injective]

/-- The label of a pair, by cut. -/
theorem lAt_eq_cut (c : C) (x G G' : ℕ) (θ : List Bool) (p : Fin g × Fin g) :
    lAt K g Np c x G G' θ (p.1.val, p.2.val) =
      cut (fun p : Fin g × Fin g => Np.cap c p.1.val p.2.val) [] (prsF K x G G') θ p := by
  rw [cut_eq_getD, ← lbLens_eq, lAt, ← map_prsF]
  have h := @idxOf_map_inj (Fin g × Fin g) (ℕ × ℕ) instBEqOfDecidableEq inferInstance _ _
      (fun p : Fin g × Fin g => (p.1.val, p.2.val))
      (fun p q h => by
        obtain ⟨h1, h2⟩ := Prod.mk.inj h
        exact Prod.ext (Fin.ext h1) (Fin.ext h2)) (prsF K x G G') p
  rw [h]

/-- The words of β bits that stand for a label of the classes G, G': a tuple of labels followed by
zeros. -/
@[expose] public def mD (K g : ℕ) (Np : PNet C) (c : C) (x β : ℕ) (G G' : Fin K) : Finset (List Bool) :=
  (words β).filter fun θ => (θ.drop (lbLen K g Np c x G G')).all fun b => !b

/-- The label that such a word stands for. -/
@[expose] public def mdec (K g : ℕ) (Np : PNet C) (c : C) (x : ℕ) (G G' : Fin K) (θ : List Bool) :
    Fin g × Fin g → List Bool :=
  fun p => lAt K g Np c x G G' θ (p.1.val, p.2.val)

theorem sum_mdec (hK : 0 < K) (c : C) (x β : ℕ) (G G' : Fin K) (hβ : lbLen K g Np c x G G' ≤ β)
    (F : (Fin g × Fin g → List Bool) → ℤ) :
    ∑ θ ∈ mD K g Np c x β G G', F (mdec K g Np c x G G' θ) =
      ∑ t ∈ tuples (fun p : Fin g × Fin g => chi hK x p.1 = G ∧ chi hK x p.2 = G')
        (fun p => words (Np.cap c p.1.val p.2.val)) [], F t := by
  have hlen : lbLen K g Np c x G G' =
      ((prsF K x G G' : List (Fin g × Fin g)).map fun p => Np.cap c p.1.val p.2.val).sum := by
    rw [lbLen, lbLens_eq]
  rw [← sum_cut (fun p : Fin g × Fin g => chi hK x p.1 = G ∧ chi hK x p.2 = G') (prsF K x G G')
    (nodup_prsF x G G') (fun p => by rw [mem_prsF]; simp [chi, Fin.ext_iff]), ← hlen]
  have hdec : ∀ θ, mdec K g Np c x G G' θ =
      cut (fun p : Fin g × Fin g => Np.cap c p.1.val p.2.val) [] (prsF K x G G') θ := by
    intro θ; funext p; exact lAt_eq_cut Np c x G G' θ p
  simp only [hdec]
  refine Finset.sum_nbij' (fun θ => θ.take (lbLen K g Np c x G G'))
    (fun w => w ++ List.replicate (β - lbLen K g Np c x G G') false) ?_ ?_ ?_ ?_ ?_
  · intro θ hθ
    simp only [mD, mem_filter, mem_words] at hθ
    simp only [mem_words, List.length_take]
    omega
  · intro w hw
    simp only [mem_words] at hw
    simp only [mD, mem_filter, mem_words, List.length_append, List.length_replicate]
    refine ⟨by omega, ?_⟩
    rw [← hw, List.drop_left]
    simp
  · intro θ hθ
    simp only [mD, mem_filter, mem_words] at hθ
    have h1 : θ.drop (lbLen K g Np c x G G') = List.replicate (β - lbLen K g Np c x G G') false := by
      rw [List.eq_replicate_iff]
      refine ⟨by rw [List.length_drop, hθ.1], fun b hb => ?_⟩
      have := List.all_eq_true.1 hθ.2 b hb
      simpa using this
    rw [← h1, List.take_append_drop]
  · intro w hw
    simp only [mem_words] at hw
    rw [← hw, List.take_left]
  · intro θ _
    rw [hlen, cut_take]

/-- The value of the instance of the merged network is the value of the network. -/
public theorem ZW_merged (hK : 0 < K) {c : C} {N : Network (Fin g) (List Bool) (List Bool)} {t S : ℕ}
    (hN : Np.Presents c N t S) (x β : ℕ) (hβ : ∀ G G' : Fin K, G < G' → lbLen K g Np c x G G' ≤ β) :
    Inst.ZW β [] ((N.merge (chi hK x) [] []).toInst (mD K g Np c x β) (mdec K g Np c x)) = N.value := by
  rw [Network.ZW_toInst (N.merge (chi hK x) [] []) β [] (mD K g Np c x β) (mdec K g Np c x)
    (fun a b _ => Finset.filter_subset _ _) ?_, Network.value_merge]
  intro G G' hlt F
  rw [sum_mdec Np hK c x β G G' (hβ G G' hlt) F]
  change _ = ∑ t ∈ tuples (fun p : Fin g × Fin g => chi hK x p.1 = G ∧ chi hK x p.2 = G')
    (fun p => N.lab p.1 p.2) [], F t
  rw [tuples_congr' _ [] (fun p hp => ?_)]
  refine (hN.lab_eq p.1 p.2 ?_).symm
  rintro he
  rw [he, hp.2] at hp
  exact hlt.ne hp.1.symm

theorem div_mod_pair (a b : Fin g) : (a.val * g + b.val) / g = a.val ∧ (a.val * g + b.val) % g = b.val := by
  have hg : 0 < g := a.pos
  constructor
  · rw [Nat.add_comm, Nat.add_mul_div_right _ _ hg, Nat.div_eq_of_lt b.2, Nat.zero_add]
  · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt b.2]

theorem getD_ofFn (θ : Fin K → List Bool) (G : Fin K) : (List.ofFn θ).getD G.val [] = θ G := by
  simp [List.getD_eq_getElem?_getD]

/-- The factor number a*g + b. -/
theorem termVal_pair {c : C} {N : Network (Fin g) (List Bool) (List Bool)} {t S : ℕ}
    (hN : Np.Presents c N t S) (x : ℕ) (q : IQ) (y : ℕ) (a b : Fin g) :
    termVal K g Np N ((((c, x), q), y), a.val * g + b.val) =
      if col K x a ≠ q.1 ∨ (col K x b = q.1 ∧ b < a) then 1
      else if a = b then N.W a (zA K g Np (((c, x), q), y) a)
      else if col K x b = q.1 then N.Ψ a b (zA K g Np (((c, x), q), y) a) (zA K g Np (((c, x), q), y) b)
      else N.f a b (zA K g Np (((c, x), q), y) a) (labOf K g Np ((c, x), q) a b) := by
  obtain ⟨h1, h2⟩ := div_mod_pair a b
  unfold termVal isOne isW isPsi nLab
  simp only [h1, h2, valW, valF, a.2, b.2, and_self, dite_true, Fin.eta, Bool.or_eq_true, bne_iff_ne, ne_eq,
    Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, Fin.val_fin_lt, Fin.val_inj]
  split_ifs with h3 h4 h5
  · rfl
  · rfl
  · rw [sum_toWord (Np.cap c a b) (fun θ => N.f a b (zA K g Np (((c, x), q), y) a) θ *
      N.f b a (zA K g Np (((c, x), q), y) b) θ), Network.Ψ, hN.lab_eq a b h4]
  · rfl

theorem chi_eq_iff (hK : 0 < K) (x : ℕ) (a : Fin g) (G : Fin K) : chi hK x a = G ↔ col K x a = G.val := by
  simp [chi, Fin.ext_iff]

theorem labOf_eq_mdec (hK : 0 < K) (c : C) (x : ℕ) (G G' : Fin K) (hne : G' ≠ G) (θ : Fin K → List Bool)
    (p : Fin g × Fin g) (hp : chi hK x p.2 = G') :
    labOf K g Np ((c, x), (G.val, List.ofFn θ)) p.1 p.2 =
      mdec K g Np c x (min G G') (max G G') (θ G') (if G < G' then p else p.swap) := by
  have hc := (chi_eq_iff hK x p.2 G').1 hp
  unfold labOf mdec
  simp only [hc, getD_ofFn, Fin.val_fin_lt]
  split_ifs with h
  · rw [min_eq_left h.le, max_eq_right h.le]
  · have h' : G' < G := lt_of_le_of_ne (not_lt.1 h) hne
    rw [min_eq_right h'.le, max_eq_left h'.le]
    rfl

/-- The product of the factors, regrouped: weights, inner interactions, factors towards the other
classes. -/
theorem prod_termVal (hK : 0 < K) {c : C} {N : Network (Fin g) (List Bool) (List Bool)} {t S : ℕ}
    (hN : Np.Presents c N t S) (x : ℕ) (G : Fin K) (θ : Fin K → List Bool) (y : ℕ) (Z : Fin g → List Bool)
    (hZ : ∀ a : Fin g, Z a = zA K g Np (((c, x), (G.val, List.ofFn θ)), y) a) :
    ∏ i ∈ range (g * g), termVal K g Np N ((((c, x), (G.val, List.ofFn θ)), y), i) =
      ((∏ a with chi hK x a = G, N.W a (Z a)) *
        ∏ p ∈ pairs (Fin g) with chi hK x p.1 = G ∧ chi hK x p.2 = G, N.Ψ p.1 p.2 (Z p.1) (Z p.2)) *
      ∏ G' ∈ univ.erase G, ∏ p : Fin g × Fin g with chi hK x p.1 = G ∧ chi hK x p.2 = G',
        N.f p.1 p.2 (Z p.1) (mdec K g Np c x (min G G') (max G G') (θ G') (if G < G' then p else p.swap)) := by
  rw [prod_range_mul_self]
  simp only [termVal_pair Np hN, ← hZ]
  have hT : ∀ p : Fin g × Fin g,
      (if col K x p.1 ≠ G.val ∨ (col K x p.2 = G.val ∧ p.2 < p.1) then (1 : ℤ)
      else if p.1 = p.2 then N.W p.1 (Z p.1)
      else if col K x p.2 = G.val then N.Ψ p.1 p.2 (Z p.1) (Z p.2)
      else N.f p.1 p.2 (Z p.1) (labOf K g Np ((c, x), (G.val, List.ofFn θ)) p.1 p.2)) =
      ((if chi hK x p.1 = G ∧ p.1 = p.2 then N.W p.1 (Z p.1) else 1) *
       (if p.1 < p.2 ∧ (chi hK x p.1 = G ∧ chi hK x p.2 = G) then N.Ψ p.1 p.2 (Z p.1) (Z p.2) else 1)) *
       (if chi hK x p.1 = G ∧ chi hK x p.2 ≠ G then
          N.f p.1 p.2 (Z p.1) (labOf K g Np ((c, x), (G.val, List.ofFn θ)) p.1 p.2) else 1) := by
    rintro ⟨a, b⟩
    simp only [chi_eq_iff, ne_eq]
    by_cases h1 : col K x a = G.val
    · by_cases h2 : a = b
      · subst h2; simp [h1]
      · by_cases h3 : col K x b = G.val
        · rcases lt_or_gt_of_ne h2 with h4 | h4
          · simp [h1, h2, h3, h4, h4.not_gt]
          · simp [h1, h2, h3, h4, h4.not_gt]
        · simp [h1, h2, h3]
    · simp [h1]
  simp only [hT, Finset.prod_mul_distrib]
  congr 1
  · congr 1
    · rw [Fintype.prod_prod_type, Finset.prod_filter]
      refine Finset.prod_congr rfl fun a _ => ?_
      by_cases h : chi hK x a = G
      · simp [h]
      · simp [h]
    · rw [pairs, Finset.filter_filter, Finset.prod_filter]
  · rw [← Finset.prod_filter, ← Finset.prod_fiberwise_of_maps_to
      (s := univ.filter fun p : Fin g × Fin g => chi hK x p.1 = G ∧ chi hK x p.2 ≠ G) (t := univ.erase G)
      (g := fun p => chi hK x p.2) (by intro p; simp)]
    refine Finset.prod_congr rfl fun G' hG' => ?_
    have hne : G' ≠ G := by simpa using hG'
    rw [Finset.filter_filter]
    have hset : (univ.filter fun p : Fin g × Fin g => (chi hK x p.1 = G ∧ chi hK x p.2 ≠ G) ∧ chi hK x p.2 = G') =
        univ.filter fun p : Fin g × Fin g => chi hK x p.1 = G ∧ chi hK x p.2 = G' := by
      refine Finset.filter_congr fun p _ => ?_
      constructor
      · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
      · rintro ⟨h1, h3⟩; exact ⟨⟨h1, h3 ▸ hne⟩, h3⟩
    rw [hset]
    refine Finset.prod_congr rfl fun p hp => ?_
    rw [labOf_eq_mdec Np hK c x G G' hne θ p (Finset.mem_filter.1 hp).2.2]

theorem validB_iff (c : C) (x β : ℕ) (G : Fin K) (θ : Fin K → List Bool) (hθ : ∀ G', G' ≠ G → (θ G').length = β) :
    validB K g Np ((c, x), (G.val, List.ofFn θ)) = true ↔
      ∀ G' : Fin K, G' ≠ G → θ G' ∈ mD K g Np c x β (min G G') (max G G') := by
  rw [validB, List.all_eq_true]
  constructor
  · intro h G' hne
    have h1 := h G'.val (List.mem_range.2 G'.2)
    rw [Bool.or_eq_true, beq_iff_eq, getD_ofFn] at h1
    have h2 := h1.resolve_left fun e => hne (Fin.ext e)
    rw [mD, mem_filter, mem_words]
    exact ⟨hθ G' hne, h2⟩
  · intro h G' hG'
    have hG'' := List.mem_range.1 hG'
    rw [Bool.or_eq_true, beq_iff_eq]
    by_cases e : G' = G.val
    · exact .inl e
    · right
      have h1 := h ⟨G', hG''⟩ fun e' => e (congrArg Fin.val e')
      rw [mD, mem_filter] at h1
      rw [← getD_ofFn θ ⟨G', hG''⟩] at h1
      exact h1.2

/-- mergedVal is the entry of the instance of the merged network. -/
public theorem toInst_eq_mergedVal (hK : 0 < K) {c : C} {N : Network (Fin g) (List Bool) (List Bool)} {t S : ℕ}
    (hN : Np.Presents c N t S) (x β : ℕ) (G : Fin K) (θ : Fin K → List Bool)
    (hθ : ∀ G', G' ≠ G → (θ G').length = β) :
    (N.merge (chi hK x) [] []).toInst (mD K g Np c x β) (mdec K g Np c x) G θ =
      mergedVal K g Np N ((c, x), (G.val, List.ofFn θ)) := by
  unfold mergedVal
  by_cases hv : validB K g Np ((c, x), (G.val, List.ofFn θ)) = true
  · rw [if_pos hv]
    have hv' := (validB_iff Np c x β G θ hθ).1 hv
    unfold Network.toInst
    have hS : (N.merge (chi hK x) [] []).S G =
        tuples (fun a => chi hK x a = G) (fun a : Fin g => words (Np.n c a.val)) [] := by
      change tuples (fun a => chi hK x a = G) N.S [] = _
      exact tuples_congr' _ [] fun a _ => hN.S_eq a
    have hlen : ((membersF K x G.val : List (Fin g)).map fun a => Np.n c a.val).sum = stLen K g Np c x G.val := by
      rw [stLen, stLens_eq]
    rw [hS, ← sum_cut_toWord (fun a => chi hK x a = G) (membersF K x G.val) (nodup_membersF x G.val)
      (fun a => by rw [mem_membersF, chi_eq_iff]), hlen]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [prod_termVal Np hK hN x G θ y
      (cut (fun a : Fin g => Np.n c a.val) [] (membersF K x G.val) (toWord (stLen K g Np c x G.val) y))
      (fun a => (zAt_eq_cut Np c x G.val _ a).symm)]
    congr 1
    refine Finset.prod_congr rfl fun G' hG' => ?_
    rw [if_pos (hv' G' (by simpa using hG'))]
    rfl
  · rw [if_neg hv]
    obtain ⟨G', hne, hG'⟩ : ∃ G', G' ≠ G ∧ θ G' ∉ mD K g Np c x β (min G G') (max G G') := by
      by_contra hcon
      push Not at hcon
      exact hv ((validB_iff Np c x β G θ hθ).2 hcon)
    unfold Network.toInst
    refine Finset.sum_eq_zero fun Z _ => ?_
    rw [Finset.prod_eq_zero (i := G') (by simp [hne]) (if_neg hG'), mul_zero]

/-! ### Good colourings -/

theorem sum_filter_range (g : ℕ) (p : ℕ → Bool) (f : ℕ → ℕ) :
    (((List.range g).filter p).map f).sum = ∑ b : Fin g with p b.val = true, f b.val := by
  rw [← List.map_coe_finRange_eq_range, List.filter_map, List.map_map,
    ← List.sum_toFinset _ ((List.nodup_finRange g).filter _)]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext b
  simp

theorem le_foldr_max {l : List ℕ} {x : ℕ} (h : x ∈ l) : x ≤ l.foldr max 0 := by
  induction l with
  | nil => simp at h
  | cons y l ih =>
    rcases List.mem_cons.1 h with rfl | h
    · exact le_max_left _ _
    · exact (ih h).trans (le_max_right _ _)

theorem foldr_max_le {l : List ℕ} {P : ℕ} (h : ∀ x ∈ l, x ≤ P) : l.foldr max 0 ≤ P := by
  induction l with
  | nil => simp
  | cons y l ih =>
    exact max_le (h y List.mem_cons_self) (ih fun x hx => h x (List.mem_cons_of_mem _ hx))

section
variable {c : C} {N : Network (Fin g) (List Bool) (List Bool)} {t S : ℕ}

theorem rowSum_eq (hN : Np.Presents c N t S) (a : Fin g) : rowSum g Np c a.val = ∑ b ∈ univ.erase a, N.c a b := by
  rw [rowSum, sum_filter_range]
  refine Finset.sum_congr ?_ fun b hb => (hN.c_eq a b (Finset.ne_of_mem_erase hb).symm).symm
  ext b
  simp [Fin.ext_iff]

public theorem Uc_eq (hN : Np.Presents c N t S) : Uc g Np c = N.U := by
  have h := sum_filter_range g (fun _ => true) (rowSum g Np c)
  rw [List.filter_true] at h
  rw [Uc, h, Network.U]
  simp only [Finset.filter_true]
  exact Finset.sum_congr rfl fun a _ => rowSum_eq Np hN a

theorem rowSum_le_Pc (a : Fin g) : rowSum g Np c a.val ≤ Pc g Np c :=
  le_foldr_max (List.mem_map.2 ⟨a.val, List.mem_range.2 a.2, rfl⟩)

public theorem Pc_le (hN : Np.Presents c N t S) {P B : ℕ} (hS : N.Sized P B) : Pc g Np c ≤ P := by
  refine foldr_max_le fun r hr => ?_
  obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hr
  rw [rowSum_eq Np hN ⟨a, List.mem_range.1 ha⟩]
  exact hS.sum_c _

public theorem length_members (hK : 0 < K) (x : ℕ) (G : Fin K) :
    (members K g x G.val).length = #{a : Fin g | chi hK x a = G} := by
  rw [← map_membersF, List.length_map, ← List.toFinset_card_of_nodup (nodup_membersF x G.val)]
  congr 1
  ext a
  simp [mem_membersF, chi_eq_iff]

public theorem lbLen_eq (hK : 0 < K) (hN : Np.Presents c N t S) (x : ℕ) {G G' : Fin K} (hne : G ≠ G') :
    lbLen K g Np c x G.val G'.val = (N.merge (chi hK x) [] []).c G G' := by
  change _ = ∑ p : Fin g × Fin g with chi hK x p.1 = G ∧ chi hK x p.2 = G', N.c p.1 p.2
  rw [lbLen, lbLens_eq, ← List.sum_toFinset _ (nodup_prsF x G.val G'.val)]
  refine Finset.sum_congr ?_ fun p hp => (hN.c_eq p.1 p.2 fun e => ?_).symm
  swap
  · obtain ⟨h1, h2⟩ := (Finset.mem_filter.1 hp).2
    rw [e, h2] at h1
    exact hne h1.symm
  ext p
  simp [mem_prsF, chi_eq_iff]

/-- What the test goodB of a colouring says: every class has fewer than 2g/K nodes, and two classes
share at most betaC
label bits. -/
public theorem goodB_iff (hK : 0 < K) (hN : Np.Presents c N t S) (x : ℕ) :
    goodB K g Np (c, x) = true ↔ (∀ G : Fin K, K * #{a : Fin g | chi hK x a = G} < 2 * g) ∧
      ∀ G G' : Fin K, G ≠ G' → (N.merge (chi hK x) [] []).c G G' ≤ betaC K g Np c := by
  simp only [goodB, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq, Bool.or_eq_true,
    beq_iff_eq]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun G => ?_, fun G G' hne => ?_⟩
    · rw [← length_members]; exact h1 G.val G.2
    · rw [← lbLen_eq Np hK hN x hne]
      exact (h2 G.val G.2 G'.val G'.2).resolve_left fun e => hne (Fin.ext e)
  · rintro ⟨h1, h2⟩
    refine ⟨fun G hG => ?_, fun G hG G' hG' => ?_⟩
    · rw [length_members hK x ⟨G, hG⟩]; exact h1 _
    · by_cases e : G = G'
      · exact .inl e
      · right
        have hne : (⟨G, hG⟩ : Fin K) ≠ ⟨G', hG'⟩ := fun e' => e (congrArg Fin.val e')
        rw [lbLen_eq Np hK hN x hne]
        exact h2 _ _ hne

/-- For g ≥ 3K⁸ some colouring among the K^g passes the test. -/
public theorem exists_goodB (hK : 2 ≤ K) (hg : 3 * K ^ 8 ≤ g) (hN : Np.Presents c N t S) {P B : ℕ}
    (hS : N.Sized P B) : ∃ x < K ^ g, goodB K g Np (c, x) = true := by
  have hK0 : 0 < K := by omega
  obtain ⟨χ, h1, h2⟩ := Colouring.exists_colouring_beta hK hg N.c hS.c_symm (Pc g Np c) (fun a => by
    rw [Finset.filter_ne', ← rowSum_eq Np hN]
    exact rowSum_le_Pc Np a)
  have hχ : chi hK0 (finFunctionFinEquiv χ).val = χ := by
    funext a
    have := congrFun (finFunctionFinEquiv.symm_apply_apply χ) a
    rw [← this]
    rfl
  refine ⟨(finFunctionFinEquiv χ).val, (finFunctionFinEquiv χ).2, (goodB_iff Np hK0 hN _).2 ?_⟩
  rw [hχ]
  refine ⟨h1, fun G G' hne => ?_⟩
  rw [Network.merge_c, betaC, Uc_eq Np hN, Network.U]
  have := h2 G G' hne
  simp only [Finset.filter_ne'] at this
  exact this

end

end Prog.NetE

end Groundwork
