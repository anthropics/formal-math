/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import StepMachines.Prog.NetProg

/-! The merging of the g nodes into K classes in the proof of Lemma 1: the program of
proof/machines/StepMachines/Prog/NetProg.lean that computes an entry of the
merged tensor of a class (a table of the clique whose nodes are the classes) computes the intended
value, with explicit bounds on the
number of steps and on the size. -/

namespace Groundwork.Prog.NetE

open Finset Stepped

variable {C : Type} (K g : ℕ) (Np : PNet C)

/-! ### Plain facts -/

theorem mem_members {x G a : ℕ} : a ∈ members K g x G ↔ a < g ∧ col K x a = G := by
  simp [members]

theorem sum_map_le {ι : Type} (l : List ι) (f : ι → ℕ) (M : ℕ) (h : ∀ i ∈ l, f i ≤ M) :
    (l.map f).sum ≤ l.length * M := by
  induction l with
  | nil => simp
  | cons i l ih =>
    have h1 := h i List.mem_cons_self
    have h2 := ih fun j hj => h j (List.mem_cons_of_mem _ hj)
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul]
    omega

theorem natAbs_le_of_abs_le {z : ℤ} {n : ℕ} (h : |z| ≤ (n : ℤ)) : z.natAbs ≤ n := by
  rw [Int.abs_eq_natAbs] at h
  exact_mod_cast h

section net

variable {K g Np} {c : C} {N : Network (Fin g) (List Bool) (List Bool)} {P B t S : ℕ}

theorem n_le (hN : Np.Presents c N t S) (hS : N.Sized P B) (a : Fin g) : Np.n c a ≤ P := by
  have := hS.card_S a
  rw [hN.S_eq, card_words] at this
  exact (Nat.pow_le_pow_iff_right (by omega)).1 this

theorem cap_le (hN : Np.Presents c N t S) (hS : N.Sized P B) {a b : Fin g} (hab : a ≠ b) :
    Np.cap c a b ≤ P := by
  rw [← hN.c_eq _ _ hab]
  exact (single_le_sum (f := fun b => N.c a b) (fun _ _ => Nat.zero_le _)
    (mem_erase.2 ⟨hab.symm, mem_univ b⟩)).trans (hS.sum_c a)

theorem cap_symm (hN : Np.Presents c N t S) (hS : N.Sized P B) (a b : Fin g) :
    Np.cap c a b = Np.cap c b a := by
  by_cases hab : a = b
  · rw [hab]
  · rw [← hN.c_eq _ _ hab, ← hN.c_eq _ _ (Ne.symm hab), hS.c_symm]

theorem stLen_le (hN : Np.Presents c N t S) (hS : N.Sized P B) {x G m : ℕ}
    (hm : (members K g x G).length ≤ m) : stLen K g Np c x G ≤ P * m := by
  unfold stLen stLens
  refine (sum_map_le _ _ P fun a ha => ?_).trans ?_
  · exact n_le hN hS ⟨a, ((mem_members K g).1 ha).1⟩
  · rw [Nat.mul_comm]; exact Nat.mul_le_mul_left _ hm

theorem valW_runs (hN : Np.Presents c N t S) (hS : N.Sized P B) {a : ℕ} (ha : a < g) {z : List Bool}
    (hz : z.length = Np.n c a) : Np.W.Runs (c, (a, z)) t S (valW N a z) ∧ (valW N a z).natAbs ≤ 2 ^ B := by
  have e : valW N a z = N.W ⟨a, ha⟩ z := dif_pos ha
  rw [e]
  exact ⟨hN.W_runs ⟨a, ha⟩ z hz, natAbs_le_of_abs_le (by exact_mod_cast hS.abs_W ⟨a, ha⟩ z)⟩

theorem valF_runs (hN : Np.Presents c N t S) (hS : N.Sized P B) {a b : ℕ} (ha : a < g) (hb : b < g)
    (hab : a ≠ b) {z θ : List Bool} (hz : z.length = Np.n c a) (hθ : θ.length = Np.cap c a b) :
    Np.f.Runs (c, ((a, b), (z, θ))) t S (valF N a b z θ) ∧ (valF N a b z θ).natAbs ≤ 2 ^ B := by
  have e : valF N a b z θ = N.f ⟨a, ha⟩ ⟨b, hb⟩ z θ := dif_pos ⟨ha, hb⟩
  rw [e]
  exact ⟨hN.f_runs ⟨a, ha⟩ ⟨b, hb⟩ z θ (fun h => hab (congrArg Fin.val h)) hz hθ,
    natAbs_le_of_abs_le (by exact_mod_cast hS.abs_f ⟨a, ha⟩ ⟨b, hb⟩ z θ)⟩

theorem psi_natAbs (hN : Np.Presents c N t S) (hS : N.Sized P B) {a b : ℕ} (ha : a < g) (hb : b < g)
    (hab : a ≠ b) (z z' : List Bool) :
    (∑ y ∈ range (2 ^ Np.cap c a b), valF N a b z (toWord (Np.cap c a b) y) *
      valF N b a z' (toWord (Np.cap c a b) y)).natAbs ≤ 2 ^ B := by
  have e : ∑ y ∈ range (2 ^ Np.cap c a b), valF N a b z (toWord (Np.cap c a b) y) *
      valF N b a z' (toWord (Np.cap c a b) y) = N.Ψ ⟨a, ha⟩ ⟨b, hb⟩ z z' := by
    rw [sum_toWord (Np.cap c a b) fun θ => valF N a b z θ * valF N b a z' θ, Network.Ψ,
      hN.lab_eq ⟨a, ha⟩ ⟨b, hb⟩ fun h => hab (congrArg Fin.val h)]
    refine sum_congr rfl fun θ _ => ?_
    rw [show valF N a b z θ = N.f ⟨a, ha⟩ ⟨b, hb⟩ z θ from dif_pos ⟨ha, hb⟩,
      show valF N b a z' θ = N.f ⟨b, hb⟩ ⟨a, ha⟩ z' θ from dif_pos ⟨hb, ha⟩]
  rw [e]
  exact natAbs_le_of_abs_le (by
    exact_mod_cast hS.abs_Ψ ⟨a, ha⟩ ⟨b, hb⟩ z z' fun h => hab (congrArg Fin.val h))

theorem length_zA {x G : ℕ} {θs : List (List Bool)} {y a : ℕ} (ha : a ∈ members K g x G) :
    (zA K g Np (((c, x), (G, θs)), y) a).length = Np.n c a := by
  unfold zA zAt zOf stLens
  rw [← cut_eq_getD]
  exact length_cut _ _ _ _ (by simp [stLen, stLens]) ha

theorem length_lAt {x G G' : ℕ} {θ : List Bool} {p : ℕ × ℕ} (hp : p ∈ prs K g x G G')
    (hθ : lbLen K g Np c x G G' ≤ θ.length) : (lAt K g Np c x G G' θ p).length = Np.cap c p.1 p.2 := by
  unfold lAt lbLens
  rw [← cut_eq_getD_beq (fun p : ℕ × ℕ => Np.cap c p.1 p.2)]
  exact length_cut_of_le _ _ _ _ hθ hp

theorem mem_prs {x G G' a b : ℕ} (ha : a ∈ members K g x G) (hb : b ∈ members K g x G') :
    (a, b) ∈ prs K g x G G' :=
  List.mem_flatMap.2 ⟨a, ha, List.mem_map.2 ⟨b, hb, rfl⟩⟩

theorem size_word (l : List Bool) : size l = 2 * l.length + 1 := by
  induction l with
  | nil => rfl
  | cons b l ih => simp only [size_list, List.map_cons, List.sum_cons, size_bool, List.length_cons] at ih ⊢; omega

/-! ### The hypotheses of mergedM_runs, and the factors -/

variable {x β : ℕ} {G : Fin K} {θ : Fin K → List Bool}

theorem length_labOf (hN : Np.Presents c N t S) (hS : N.Sized P B)
    (hβ : ∀ G < K, ∀ G' < K, G ≠ G' → lbLen K g Np c x G G' ≤ β) (hθ : ∀ G', G' ≠ G → (θ G').length = β)
    {a b : ℕ} (ha : a ∈ members K g x G) (hb : b < g) (hc : col K x b ≠ G) :
    (labOf K g Np ((c, x), (G.val, List.ofFn θ)) a b).length = Np.cap c a b := by
  have hK : 0 < K := G.pos
  have hG' : col K x b < K := Nat.mod_lt _ hK
  have hbm : b ∈ members K g x (col K x b) := (mem_members K g).2 ⟨hb, rfl⟩
  have hget : (List.ofFn θ).getD (col K x b) [] = θ ⟨col K x b, hG'⟩ := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos hG']; rfl
  have hlen : ((List.ofFn θ).getD (col K x b) []).length = β := by
    rw [hget]; exact hθ _ fun h => hc (congrArg Fin.val h)
  unfold labOf
  by_cases hlt : G.val < col K x b
  · rw [if_pos hlt]
    exact length_lAt (mem_prs ha hbm) (by rw [hlen]; exact hβ _ G.2 _ hG' (Ne.symm hc))
  · rw [if_neg hlt]
    rw [length_lAt (mem_prs hbm ha) (by rw [hlen]; exact hβ _ hG' _ G.2 hc)]
    exact cap_symm hN hS ⟨b, hb⟩ ⟨a, ((mem_members K g).1 ha).1⟩

variable [HasSize C]

/-- One factor of the product in an entry of the merged tensor of class G. The index i < g * g codes
the pair of nodes
(i / g, i % g); the factor is 1, a weight W, an interaction Ψ inside the class (a sum over the
labels of the pair), or a
factor f towards a node of another class. It has absolute value at most 2 ^ B. -/
theorem termM_runs (hN : Np.Presents c N t S) (hS : N.Sized P B) (ht : 1 ≤ t)
    (hβ : ∀ G < K, ∀ G' < K, G ≠ G' → lbLen K g Np c x G G' ≤ β) (hθ : ∀ G', G' ≠ G → (θ G').length = β)
    (y : ℕ) {i : ℕ} (hi : i < g * g) :
    (termM K g Np).Runs ((((c, x), (G.val, List.ofFn θ)), y), i) (2 ^ P * (2 * t + 2))
      (2 * size ((((c, x), (G.val, List.ofFn θ)), y), i) + 3 * P + 3 * B + S + 12)
      (termVal K g Np N ((((c, x), (G.val, List.ofFn θ)), y), i)) ∧
    (termVal K g Np N ((((c, x), (G.val, List.ofFn θ)), y), i)).natAbs ≤ 2 ^ B := by
  have hg : 0 < g := Nat.pos_of_ne_zero fun h => by simp [h] at hi
  have ha : i / g < g := Nat.div_lt_of_lt_mul hi
  have hb : i % g < g := Nat.mod_lt _ hg
  have h2P : 1 ≤ 2 ^ P := Nat.one_le_two_pow
  have h2B : 1 ≤ 2 ^ B := Nat.one_le_two_pow
  have hst : t ≤ 2 ^ P * (2 * t + 2) := by nlinarith
  cases h1 : isOne K g ((((c, x), (G.val, List.ofFn θ)), y), i) with
  | true =>
    have ev : termVal K g Np N ((((c, x), (G.val, List.ofFn θ)), y), i) = 1 := by
      simp only [termVal, h1, if_true]
    rw [ev]
    refine ⟨(ite_runs_true h1 (const_runs (1 : ℤ) _)).mono (by omega) ?_, by simpa using h2B⟩
    simp only [size_prod, size_nat, size_int]
    have : (1 : ℤ).natAbs.size = 1 := rfl
    omega
  | false =>
    have hcolA : col K x (i / g) = G.val := by
      by_contra hne
      have : isOne K g ((((c, x), (G.val, List.ofFn θ)), y), i) = true := by simp [isOne, hne]
      rw [h1] at this; cases this
    have ham : i / g ∈ members K g x G := (mem_members K g).2 ⟨ha, hcolA⟩
    cases h2 : isW g ((((c, x), (G.val, List.ofFn θ)), y), i) with
    | true =>
      have ev : termVal K g Np N ((((c, x), (G.val, List.ofFn θ)), y), i) = valW N (i / g)
          (zA K g Np (((c, x), (G.val, List.ofFn θ)), y) (i / g)) := by
        simp only [termVal, h1, h2, if_true, if_false, Bool.false_eq_true]
      rw [ev]
      obtain ⟨r1, r2⟩ := valW_runs hN hS ha (length_zA (θs := List.ofFn θ) (y := y) ham)
      exact ⟨(ite_runs_false h1 (ite_runs_true h2 (mapIn_runs r1))).mono hst (by omega), r2⟩
    | false =>
      have hab : i / g ≠ i % g := by
        intro he
        have : isW g ((((c, x), (G.val, List.ofFn θ)), y), i) = true := by simp [isW, he]
        rw [h2] at this; cases this
      cases h3 : isPsi K g ((((c, x), (G.val, List.ofFn θ)), y), i) with
      | false =>
        have hcolB : col K x (i % g) ≠ G.val := by
          intro he
          have : isPsi K g ((((c, x), (G.val, List.ofFn θ)), y), i) = true := by simp [isPsi, he]
          rw [h3] at this; cases this
        have ev : termVal K g Np N ((((c, x), (G.val, List.ofFn θ)), y), i) = valF N (i / g) (i % g)
            (zA K g Np (((c, x), (G.val, List.ofFn θ)), y) (i / g))
            (labOf K g Np ((c, x), (G.val, List.ofFn θ)) (i / g) (i % g)) := by
          simp only [termVal, h1, h2, h3, if_false, Bool.false_eq_true]
        rw [ev]
        obtain ⟨r1, r2⟩ := valF_runs hN hS ha hb hab (length_zA (θs := List.ofFn θ) (y := y) ham)
          (length_labOf hN hS hβ hθ ham hb hcolB)
        exact ⟨(ite_runs_false h1 (ite_runs_false h2 (ite_runs_false h3 (mapIn_runs r1)))).mono hst (by omega), r2⟩
      | true =>
        have hcolB : col K x (i % g) = G.val := by simpa [isPsi] using h3
        have hbm : i % g ∈ members K g x G := (mem_members K g).2 ⟨hb, hcolB⟩
        have hcap : Np.cap c (i / g) (i % g) ≤ P :=
          cap_le hN hS (a := ⟨i / g, ha⟩) (b := ⟨i % g, hb⟩) fun h => hab (congrArg Fin.val h)
        have ev : termVal K g Np N ((((c, x), (G.val, List.ofFn θ)), y), i) = ∑ y' ∈ range (2 ^ Np.cap c (i / g) (i % g)),
            valF N (i / g) (i % g) (zA K g Np (((c, x), (G.val, List.ofFn θ)), y) (i / g))
                (toWord (Np.cap c (i / g) (i % g)) y') *
            valF N (i % g) (i / g) (zA K g Np (((c, x), (G.val, List.ofFn θ)), y) (i % g))
                (toWord (Np.cap c (i / g) (i % g)) y') := by
          simp only [termVal, h1, h2, h3, if_true, if_false, Bool.false_eq_true, nLab]
        rw [ev]
        have hM : ∀ y' < nLab g Np ((((c, x), (G.val, List.ofFn θ)), y), i),
            (mul2 (mapIn (qP1 K g Np) Np.f) (mapIn (qP2 K g Np) Np.f)).Runs (((((c, x), (G.val, List.ofFn θ)), y), i), y')
                (t + 1 + t)
              (size ((((c, x), (G.val, List.ofFn θ)), y), i) + P + B + S + 4)
              (valF N (i / g) (i % g) (zA K g Np (((c, x), (G.val, List.ofFn θ)), y) (i / g))
                  (toWord (Np.cap c (i / g) (i % g)) y') *
               valF N (i % g) (i / g) (zA K g Np (((c, x), (G.val, List.ofFn θ)), y) (i % g))
                   (toWord (Np.cap c (i / g) (i % g)) y')) := by
          intro y' hy'
          obtain ⟨r1, r2⟩ := valF_runs hN hS ha hb hab (length_zA (θs := List.ofFn θ) (y := y) ham)
            (length_toWord (Np.cap c (i / g) (i % g)) y')
          obtain ⟨r3, _⟩ := valF_runs hN hS hb ha hab.symm (length_zA (θs := List.ofFn θ) (y := y) hbm)
            ((length_toWord (Np.cap c (i / g) (i % g)) y').trans (cap_symm hN hS ⟨i / g, ha⟩ ⟨i % g, hb⟩))
          refine (mul2_runs (mapIn_runs (f := qP1 K g Np) (a := (((((c, x), (G.val, List.ofFn θ)), y), i), y')) r1)
            (mapIn_runs (f := qP2 K g Np) (a := (((((c, x), (G.val, List.ofFn θ)), y), i), y')) r3)).mono le_rfl ?_
          have e1 : y'.size ≤ P := (Nat.size_le.2 hy').trans hcap
          have e2 := Nat.size_le_size r2
          rw [Nat.size_pow] at e2
          simp only [size_prod, size_nat, size_int]
          omega
        have hrun := sumRange_runs (N := nLab g Np) (a := ((((c, x), (G.val, List.ofFn θ)), y), i)) (fun _ => t + 1 + t) _
            (2 ^ B * 2 ^ B) _ hM
          (fun y' _ => by
            obtain ⟨_, r2⟩ := valF_runs hN hS ha hb hab (length_zA (θs := List.ofFn θ) (y := y) ham)
              (length_toWord (Np.cap c (i / g) (i % g)) y')
            obtain ⟨_, r4⟩ := valF_runs hN hS hb ha hab.symm (length_zA (θs := List.ofFn θ) (y := y) hbm)
              ((length_toWord (Np.cap c (i / g) (i % g)) y').trans (cap_symm hN hS ⟨i / g, ha⟩ ⟨i % g, hb⟩))
            rw [Int.natAbs_mul]
            exact Nat.mul_le_mul r2 r4)
        refine ⟨(ite_runs_false h1 (ite_runs_false h2 (ite_runs_true h3 hrun))).mono ?_ ?_,
          psi_natAbs hN hS ha hb hab _ _⟩
        · rw [sum_const, card_range, smul_eq_mul]
          exact Nat.mul_le_mul (Nat.pow_le_pow_right (by omega) hcap) (by omega)
        · have e : size (nLab g Np ((((c, x), (G.val, List.ofFn θ)), y), i)) = Np.cap c (i / g) (i % g) + 2 := by
            change size (2 ^ Np.cap c (i / g) (i % g)) = _
            simp [Nat.size_pow]
          have e' : size (nLab g Np ((((c, x), (G.val, List.ofFn θ)), y), i) * (2 ^ B * 2 ^ B)) =
              Np.cap c (i / g) (i % g) + (B + B) + 2 := by
            change size (2 ^ Np.cap c (i / g) (i % g) * (2 ^ B * 2 ^ B)) = _
            rw [← pow_add, ← pow_add]
            simp [Nat.size_pow]
          rw [e, e']
          omega

theorem size_u_le (hθ : ∀ G', G' ≠ G → (θ G').length = β) (hG : θ G = []) :
    size ((c, x), (G.val, List.ofFn θ)) ≤ size c + size x + size K + K * (2 * β + 2) + 1 := by
  have h1 : size (List.ofFn θ) ≤ K * (2 * β + 2) + 1 := by
    rw [size_list]
    have := sum_map_le (List.ofFn θ) (fun l => size l + 1) (2 * β + 2) (fun l hl => by
      obtain ⟨G', rfl⟩ : ∃ G', θ G' = l := by simpa [List.mem_ofFn] using hl
      rw [size_word]
      by_cases h : G' = G
      · rw [h, hG]; simp
      · rw [hθ G' h])
    rw [List.length_ofFn] at this
    omega
  have h2 : size G.val ≤ size K := by
    have := Nat.size_le_size G.2.le
    simp only [size_nat]; omega
  simp only [size_prod]
  omega

end net

variable [HasSize C]

/-- `mergedM` computes one entry of the tensor of class G of the merged instance, by brute force
over the states of the
members of G. Here x is a colouring in which any two classes share at most β label bits (β is the
length of the labels in
the query) and every class has at most m members. -/
public theorem mergedM_runs {c : C} {N : Network (Fin g) (List Bool) (List Bool)} {P B t S : ℕ}
    (hN : Np.Presents c N t S) (hS : N.Sized P B) (ht : 1 ≤ t) (x β m : ℕ)
    (hm : ∀ G < K, (members K g x G).length ≤ m)
    (hβ : ∀ G < K, ∀ G' < K, G ≠ G' → lbLen K g Np c x G G' ≤ β)
    (G : Fin K) (θ : Fin K → List Bool) (hθ : ∀ G', G' ≠ G → (θ G').length = β) (hG : θ G = []) :
    (mergedM K g Np).Runs ((c, x), (G.val, List.ofFn θ))
      (2 ^ (P * m) * (g * g * (2 ^ P * (2 * t + 3) + 2) + 1))
      (S + 4 * (size c + size x + size K + K * (2 * β + 2)) + 5 * (P * m) + 2 * (B * (g * g)) + 3 * size (g * g)
        + 3 * P + 3 * B + 28)
      (mergedVal K g Np N ((c, x), (G.val, List.ofFn θ))) := by
  have hsu := size_u_le (c := c) (x := x) hθ hG
  have hst : stLen K g Np c x G ≤ P * m := stLen_le hN hS (hm G G.2)
  cases hv : validB K g Np ((c, x), (G.val, List.ofFn θ)) with
  | false =>
    have ev : mergedVal K g Np N ((c, x), (G.val, List.ofFn θ)) = 0 := by
      simp only [mergedVal, hv, if_false, Bool.false_eq_true]
    rw [ev]
    refine (ite_runs_false hv (const_runs (0 : ℤ) _)).mono
      (Nat.succ_le_of_lt (Nat.mul_pos (Nat.pow_pos (by omega)) (Nat.succ_pos _))) ?_
    have : size (0 : ℤ) = 1 := rfl
    omega
  | true =>
    have ev : mergedVal K g Np N ((c, x), (G.val, List.ofFn θ)) = ∑ y ∈ range (nStates K g Np ((c, x), (G.val, List.ofFn θ))),
        ∏ i ∈ range (g * g), termVal K g Np N ((((c, x), (G.val, List.ofFn θ)), y), i) := by
      simp only [mergedVal, hv, if_true]
    rw [ev]
    have eN : nStates K g Np ((c, x), (G.val, List.ofFn θ)) = 2 ^ stLen K g Np c x G := rfl
    have hin : ∀ y < nStates K g Np ((c, x), (G.val, List.ofFn θ)), (prodRange (nPairs g) (termM K g Np)).Runs
        (((c, x), (G.val, List.ofFn θ)), y)
        (g * g * (2 ^ P * (2 * t + 2) + 1))
        (3 * (size ((c, x), (G.val, List.ofFn θ)) + (stLen K g Np c x G + 1)) + 3 * size (g * g) + B * (g * g)
            + 3 * P + 3 * B + S + 15)
        (∏ i ∈ range (g * g), termVal K g Np N ((((c, x), (G.val, List.ofFn θ)), y), i)) := by
      intro y hy
      have hy' : y.size ≤ stLen K g Np c x G := Nat.size_le.2 (eN ▸ hy)
      have := prodRange_runs (N := nPairs g) (M := termM K g Np) (a := (((c, x), (G.val, List.ofFn θ)), y))
        (fun _ => 2 ^ P * (2 * t + 2)) (fun i => termVal K g Np N ((((c, x), (G.val, List.ofFn θ)), y), i)) (2 ^ B)
        (2 * (size (((c, x), (G.val, List.ofFn θ)), y) + size (g * g)) + 3 * P + 3 * B + S + 12) Nat.one_le_two_pow
        (fun i hi => (termM_runs hN hS ht hβ hθ y hi).1.mono le_rfl (by
          have := Nat.size_le_size (Nat.le_of_lt hi)
          simp only [nPairs] at this
          simp only [size_prod, size_nat] at this ⊢
          omega))
        (fun i hi => (termM_runs hN hS ht hβ hθ y hi).2)
      refine this.mono (by simp [nPairs]) ?_
      simp only [nPairs, ← pow_mul]
      simp only [size_prod, size_nat, Nat.size_pow] at hsu ⊢
      omega
    have hout := sumRange_runs (N := nStates K g Np) (a := ((c, x), (G.val, List.ofFn θ)))
        (fun _ => g * g * (2 ^ P * (2 * t + 2) + 1))
      (fun y => ∏ i ∈ range (g * g), termVal K g Np N ((((c, x), (G.val, List.ofFn θ)), y), i)) ((2 ^ B) ^ (g * g)) _ hin
      (fun y _ => natAbs_prod_le _ _ _ fun i hi => (termM_runs hN hS ht hβ hθ y hi).2)
    refine (ite_runs_true hv hout).mono ?_ ?_
    · rw [sum_const, card_range, smul_eq_mul, eN]
      refine Nat.mul_le_mul (Nat.pow_le_pow_right (by omega) hst) (Nat.add_le_add_right (Nat.mul_le_mul_left _ ?_) 1)
      have : 2 ^ P * (2 * t + 2) ≤ 2 ^ P * (2 * t + 3) := Nat.mul_le_mul_left _ (by omega)
      omega
    · rw [eN, ← pow_mul, ← pow_add]
      simp only [size_nat, Nat.size_pow] at hsu ⊢
      omega

end Groundwork.Prog.NetE
