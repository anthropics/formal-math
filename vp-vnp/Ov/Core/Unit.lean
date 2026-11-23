/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Ov.Core.Spec
import Ov.Core.Network

/-!
# Unit tensors and wires

Relations between unit tensors, whose legs may be at any parties, also several at one party, and between wires. They are
what the proof of Lemma lem:exponents (`Paper/Tensors.lean`) uses.
-/

set_option linter.unusedSectionVars false

namespace Ov

open Finset

/-- A function f ≥ 1 on the positive integers that is multiplicative and monotone is a power function:
f(n) = n^e with e = log₂ f(2). -/
theorem eq_rpow_of_mul_mono (f : ℕ → ℝ) (h1 : ∀ n, 1 ≤ n → 1 ≤ f n)
    (hmul : ∀ m n, 1 ≤ m → 1 ≤ n → f (m * n) = f m * f n)
    (hmono : ∀ m n, 1 ≤ m → m ≤ n → f m ≤ f n) (n : ℕ) (hn : 1 ≤ n) :
    f n = (n : ℝ) ^ Real.logb 2 (f 2) := by
  have hone : f 1 = 1 := by
    have := hmul 1 1 le_rfl le_rfl
    have h0 := h1 1 le_rfl
    nlinarith
  have hpow : ∀ m, 1 ≤ m → ∀ k, f (m ^ k) = f m ^ k := by
    intro m hm k
    induction k with
    | zero => simpa using hone
    | succ k ih => rw [pow_succ, hmul _ _ (Nat.one_le_pow _ _ hm) hm, ih, pow_succ]
  have hfpos : ∀ m, 1 ≤ m → 0 < f m := fun m hm => lt_of_lt_of_le one_pos (h1 m hm)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  set a := Real.log (f 2) with ha
  have ha0 : 0 ≤ a := Real.log_nonneg (h1 2 (by norm_num))
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set x := Real.log (f n) * Real.log 2 - a * Real.log n with hx
  have key : ∀ k : ℕ, |(k : ℝ) * x| ≤ a * Real.log 2 := by
    intro k
    set m := Nat.log 2 (n ^ k)
    have hnk : n ^ k ≠ 0 := pow_ne_zero _ (by omega)
    have hm1 : 2 ^ m ≤ n ^ k := Nat.pow_log_le_self 2 hnk
    have hm2 : n ^ k ≤ 2 ^ (m + 1) := (Nat.lt_pow_succ_log_self (by norm_num) _).le
    have f1 : f 2 ^ m ≤ f n ^ k := by
      rw [← hpow 2 (by norm_num), ← hpow n hn]
      exact hmono _ _ (Nat.one_le_two_pow) hm1
    have f2 : f n ^ k ≤ f 2 ^ (m + 1) := by
      rw [← hpow 2 (by norm_num), ← hpow n hn]
      exact hmono _ _ (Nat.one_le_pow _ _ hn) hm2
    have g1 : (m : ℝ) * a ≤ k * Real.log (f n) := by
      have := Real.log_le_log (pow_pos (hfpos 2 (by norm_num)) m) f1
      rwa [Real.log_pow, Real.log_pow] at this
    have g2 : (k : ℝ) * Real.log (f n) ≤ (m + 1) * a := by
      have := Real.log_le_log (pow_pos (hfpos n hn) k) f2
      rw [Real.log_pow, Real.log_pow] at this
      exact_mod_cast this
    have g3 : (m : ℝ) * Real.log 2 ≤ k * Real.log n := by
      have : ((2 : ℝ) ^ m) ≤ (n : ℝ) ^ k := by exact_mod_cast hm1
      have := Real.log_le_log (by positivity) this
      rwa [Real.log_pow, Real.log_pow] at this
    have g4 : (k : ℝ) * Real.log n ≤ (m + 1) * Real.log 2 := by
      have : ((n : ℝ) ^ k) ≤ (2 : ℝ) ^ (m + 1) := by exact_mod_cast hm2
      have := Real.log_le_log (by positivity) this
      rw [Real.log_pow, Real.log_pow] at this
      exact_mod_cast this
    rw [abs_le]
    constructor
    · have e1 := mul_le_mul_of_nonneg_right g1 hl2.le
      have e2 := mul_le_mul_of_nonneg_left g4 ha0
      rw [hx]
      nlinarith
    · have e1 := mul_le_mul_of_nonneg_right g2 hl2.le
      have e2 := mul_le_mul_of_nonneg_left g3 ha0
      rw [hx]
      nlinarith
  have hx0 : x = 0 := by
    by_contra hne
    have hxp : 0 < |x| := abs_pos.2 hne
    obtain ⟨k, hk⟩ := exists_nat_gt (a * Real.log 2 / |x|)
    have := key k
    rw [abs_mul, Nat.abs_cast] at this
    rw [div_lt_iff₀ hxp] at hk
    linarith
  have hfin : Real.log (f n) = Real.logb 2 (f 2) * Real.log n := by
    rw [Real.logb, div_mul_eq_mul_div, eq_div_iff hl2.ne']
    linarith
  rw [Real.rpow_def_of_pos hnpos, mul_comm, ← hfin, Real.exp_log (hfpos n hn)]

namespace Ten

variable {K : Type} [Field K] {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-! ### Unit tensors -/

/-- The entry of a unit tensor at equal indices is 1. -/
theorem unit_val_of {r : ℕ} {x : J → Fin r} (h : ∀ i j, x i = x j) : (unit K J r).val x = 1 :=
  if_pos h

/-- The other entries of a unit tensor are 0. -/
theorem unit_val_not {r : ℕ} {x : J → Fin r} (h : ¬ ∀ i j, x i = x j) :
    (unit K J r).val x = 0 :=
  if_neg h

theorem unit_val_congr {L : Type} [Fintype L] [DecidableEq L] {r r' : ℕ} {x : J → Fin r}
    {y : L → Fin r'} (h : (∀ i j, x i = x j) ↔ ∀ i j, y i = y j) :
    (unit K J r).val x = (unit K L r').val y := by
  by_cases hx : ∀ i j, x i = x j
  · rw [unit_val_of hx, unit_val_of (h.1 hx)]
  · rw [unit_val_not hx, unit_val_not fun hy => hx (h.2 hy)]

/-- A smaller unit tensor is a restriction of a larger one. -/
theorem Restr.unit_mono {m n : ℕ} (h : m ≤ n) : Restr (unit K J m) (unit K J n) :=
  Restr.of_map' (fun _ => Fin.castLE h) fun x =>
    unit_val_congr (x := x) (y := fun p => Fin.castLE h (x p))
      ⟨fun hx i j => congr_arg _ (hx i j), fun hx i j => Fin.castLE_injective h (hx i j)⟩

/-- The product of the unit tensors of sizes m and n is the one of size m·n. -/
theorem Equi.unit_mul (m n : ℕ) : Equi (unit K J (m * n)) (unit K J m * unit K J n) :=
  Equi.symm <| Equi.of_equiv (fun _ => finProdFinEquiv) fun x => by
    change J → Fin m × Fin n at x
    show (unit K J m).val (fun p => (x p).1) * (unit K J n).val (fun p => (x p).2) =
      (unit K J (m * n)).val fun p => finProdFinEquiv (x p)
    by_cases h1 : ∀ i j, (x i).1 = (x j).1
    · by_cases h2 : ∀ i j, (x i).2 = (x j).2
      · rw [unit_val_of h1, unit_val_of h2, unit_val_of, _root_.mul_one]
        exact fun i j => congr_arg _ (Prod.ext (h1 i j) (h2 i j))
      · have hn : ¬ ∀ i j, finProdFinEquiv (x i) = finProdFinEquiv (x j) := fun h =>
          h2 fun i j => (Prod.ext_iff.1 (finProdFinEquiv.injective (h i j))).2
        rw [unit_val_not hn, unit_val_not h2, mul_zero]
    · have hn : ¬ ∀ i j, finProdFinEquiv (x i) = finProdFinEquiv (x j) := fun h =>
        h1 fun i j => (Prod.ext_iff.1 (finProdFinEquiv.injective (h i j))).1
      rw [unit_val_not hn, unit_val_not h1, zero_mul]

/-- The unit tensor of size 1 is 1. -/
theorem Equi.unit_one : Equi (unit K J 1) 1 :=
  Equi.of_equiv (fun _ => show Fin 1 ≃ Unit from Equiv.ofUnique _ _) fun x => by
    exact unit_val_of fun i j => Subsingleton.elim (α := Fin 1) _ _

/-- Several legs of a unit tensor at one party are as good as one leg. -/
theorem Equi.push_unit {L : Type} [Fintype L] [DecidableEq L] (ρ : L → J) (hρ : ρ.Surjective)
    (n : ℕ) : Equi (Ten.push ρ (unit K L n)) (unit K J n) := by
  classical
  constructor
  · let w : ∀ q, ({l : L // ρ l = q} → Fin n) → K := fun q a =>
      if ∀ l l', a l = a l' then 1 else 0
    refine Restr.of_map w (fun q a => a ⟨(hρ q).choose, (hρ q).choose_spec⟩) fun x => ?_
    change ∀ q, {l : L // ρ l = q} → Fin n at x
    show (unit K L n).val (fun l => x (ρ l) ⟨l, rfl⟩) =
      (∏ q, w q (x q)) *
        (unit K J n).val fun q => x q ⟨(hρ q).choose, (hρ q).choose_spec⟩
    have cast : ∀ l q (h' : ρ l = q), x (ρ l) ⟨l, rfl⟩ = x q ⟨l, h'⟩ := by rintro l _ rfl; rfl
    by_cases h : ∀ l l', x (ρ l) ⟨l, rfl⟩ = x (ρ l') ⟨l', rfl⟩
    · rw [unit_val_of h, unit_val_of, Finset.prod_eq_one, _root_.mul_one]
      · rintro q -
        refine if_pos (show ∀ l l', x q l = x q l' from fun l l' => ?_)
        rw [← cast l.1 q l.2, ← cast l'.1 q l'.2]
        exact h _ _
      · intro q q'
        rw [← cast _ _ (hρ q).choose_spec, ← cast _ _ (hρ q').choose_spec]
        exact h _ _
    · rw [unit_val_not h]
      by_cases h1 : ∀ q l l', x q l = x q l'
      · rw [unit_val_not, mul_zero]
        intro h2
        refine h fun i j => ?_
        rw [h1 (ρ i) ⟨i, rfl⟩ ⟨_, (hρ (ρ i)).choose_spec⟩,
          h1 (ρ j) ⟨j, rfl⟩ ⟨_, (hρ (ρ j)).choose_spec⟩]
        exact h2 _ _
      · push Not at h1
        obtain ⟨q, l, l', hq⟩ := h1
        rw [Finset.prod_eq_zero (Finset.mem_univ q), zero_mul]
        exact if_neg (show ¬ ∀ l l', x q l = x q l' from fun h => hq (h l l'))
  · refine Restr.of_map' (fun q a _ => a) fun x => ?_
    refine unit_val_congr (x := x) (y := fun l => x (ρ l)) ⟨fun h i j => h _ _, fun h i j => ?_⟩
    obtain ⟨i, rfl⟩ := hρ i
    obtain ⟨j, rfl⟩ := hρ j
    exact h i j

/-- A pushed unit tensor depends only on the set of parties that hold a leg. -/
theorem Equi.push_unit_congr {L : Type} [Fintype L] [DecidableEq L] (π : J → I) (π' : L → I)
    (h : Set.range π = Set.range π') (n : ℕ) :
    Equi (Ten.push π (unit K J n)) (Ten.push π' (unit K L n)) := by
  classical
  have key : ∀ {L : Type} [Fintype L] [DecidableEq L] (π' : L → I) (S : Finset I)
      (_ : Set.range π' = S),
      Equi (Ten.push π' (unit K L n)) (Ten.push (fun q : S => (q : I)) (unit K S n)) := by
    intro L _ _ π' S hS
    let ρ : L → S := fun l => ⟨π' l, by
      have : π' l ∈ (S : Set I) := hS ▸ Set.mem_range_self l
      exact this⟩
    have hρ : ρ.Surjective := by
      rintro ⟨q, hq⟩
      have : q ∈ Set.range π' := hS ▸ (show q ∈ (S : Set I) from hq)
      obtain ⟨l, hl⟩ := this
      exact ⟨l, Subtype.ext hl⟩
    exact ((Equi.push_push (fun q : S => (q : I)) ρ (unit K L n)).symm.trans
      ((Equi.push_unit ρ hρ n).push _))
  exact (key π (Set.toFinset (Set.range π)) (by simp)).trans
    (key π' (Set.toFinset (Set.range π)) (by simp [h])).symm

/-- A tensor with all its legs at one party is a restriction of 1. -/
theorem Restr.push_const (q : I) (t : Ten K J) : Restr (Ten.push (fun _ => q) t) 1 := by
  classical
  refine Restr.of_map (fun p a => if h : q = p then t.val fun j => a ⟨j, h⟩ else 1)
    (fun _ _ => ()) fun x => ?_
  have key : ∀ f : ∀ p, ∀ j : {j : J // q = p}, t.ι j.1, t.val (fun j => f q ⟨j, rfl⟩) =
      ∏ p, if h : q = p then t.val fun j => f p ⟨j, h⟩ else 1 := by
    intro f
    rw [Finset.prod_eq_single q]
    · simp
    · intro p _ hp
      rw [dif_neg fun h => hp h.symm]
    · simp
  exact (key x).trans (_root_.mul_one _).symm

/-! ### Wires -/

/-- A wire may be read in both directions. -/
theorem Equi.wire_comm (n : ℕ) (p q : I) : Equi (wire K n p q) (wire K n q p) :=
  Equi.push_unit_congr _ _ (by
    rw [Matrix.range_cons, Matrix.range_cons, Matrix.range_cons, Matrix.range_cons]
    simp [Set.pair_comm]) n

/-- A wire with both ends at one party is a restriction of 1. -/
theorem Restr.wire_self (n : ℕ) (p : I) : Restr (wire K n p p) 1 := by
  have : (![p, p] : Fin 2 → I) = fun _ => p := by
    funext i; fin_cases i <;> rfl
  rw [wire, this]
  exact Restr.push_const p _

/-- Two parallel wires are one wire, whose dimension is the product. -/
theorem Equi.wire_mul (m n : ℕ) (p q : I) :
    Equi (wire K (m * n) p q) (wire K m p q * wire K n p q) :=
  ((Equi.unit_mul m n).push _).trans (Equi.push_mul _ _ _)

/-- A wire of dimension 1 is 1. -/
theorem Equi.wire_one (p q : I) : Equi (wire K 1 p q) 1 :=
  (Equi.unit_one.push _).trans (Equi.push_one _)

private def tr {n : ℕ} (v : Fin 3) (x l : Fin 2 → Fin n) : K :=
  if v = 0 then (if x 0 = l 0 then 1 else 0) else
    if v = 1 then (if l 0 = l 1 then 1 else 0) else (if x 1 = l 1 then 1 else 0)

private theorem tr_sum {n : ℕ} (x : Fin 2 → Fin n) :
    (unit K (Fin 2) n).val x = ∑ l : Fin 2 → Fin n, ∏ v, tr (K := K) v x l := by
  rw [Finset.sum_eq_single (fun _ => x 0)]
  · rcases eq_or_ne (x 0) (x 1) with h | h
    · rw [unit_val_of (by simp [Fin.forall_fin_two, h])]
      simp [tr, h]
    · rw [unit_val_not (by simp [Fin.forall_fin_two, h])]
      simp [Fin.prod_univ_succ, tr, h.symm]
  · intro l _ hl
    by_cases h0 : x 0 = l 0
    · by_cases h1 : l 0 = l 1
      · refine absurd (funext fun i => ?_) hl
        fin_cases i
        · exact h0.symm
        · exact (h0.trans h1).symm
      · simp [Fin.prod_univ_succ, tr, h1]
    · simp [Fin.prod_univ_succ, tr, h0]
  · simp

/-- The wire from p to q is a restriction of the product of the wires from p to r and from r to q. -/
theorem Restr.wire_trans (n : ℕ) (p q r : I) :
    Restr (wire K n p q) (wire K n p r * wire K n r q) := by
  classical
  have h := Restr.of_edges (V := Fin 3) (E := Fin 2) (J := Fin 2) (K := K) ![p, q] ![p, r, q]
    (unit K (Fin 2) n) (fun _ => Fin n) ![0, 1] ![1, 2] tr
    (by
      intro v x x' l l' hx hl
      change Fin 2 → Fin n at x x'
      fin_cases v
      · have h0 : x 0 = x' 0 := hx 0 rfl
        have h1 := hl 0 (Or.inl rfl)
        simp [tr, h0, h1]
      · have h0 := hl 0 (Or.inr rfl)
        have h1 := hl 1 (Or.inl rfl)
        simp [tr, h0, h1]
      · have h0 : x 1 = x' 1 := hx 1 rfl
        have h1 := hl 1 (Or.inr rfl)
        simp [tr, h0, h1]) tr_sum
  refine h.trans ((Equi.prod_fin_two _).1.trans ?_)
  simp only [Fintype.card_fin]
  exact Restr.refl _

/-- Moving legs: the leg j can be moved from π' j to π j through a wire of its dimension. -/
theorem Restr.move (π π' : J → I) (t : Ten K J) :
    Restr (Ten.push π t)
      (Ten.prod (fun j => wire K (Fintype.card (t.ι j)) (π j) (π' j)) * Ten.push π' t) := by
  classical
  have h := Restr.of_network (V := J ⊕ J) (E := J) (κ := Unit) (M := fun _ => J) π
    (Sum.elim π π') t t.ι Sum.inl Sum.inr (fun _ => t) (fun _ j => Sum.inr j)
    (fun v x l y => match v with
      | Sum.inl j => if x j = l j then 1 else 0
      | Sum.inr j => if l j = y () j then 1 else 0)
    (by
      intro v x x' l l' y y' hx hl hy
      rcases v with j | j
      · simp only [hx j rfl, hl j (Or.inl rfl)]
      · simp only [hl j (Or.inr rfl), hy () j rfl])
    (by
      intro x
      rw [Finset.sum_eq_single x]
      · rw [Finset.sum_eq_single (fun _ => x)]
        · simp
        · intro y _ hy
          have : ∃ j, ¬ x j = y () j := by
            by_contra hcon
            push Not at hcon
            exact hy (funext fun _ => funext fun j => (hcon j).symm)
          obtain ⟨j, hj⟩ := this
          rw [Finset.prod_eq_zero (Finset.mem_univ (Sum.inr j)) (if_neg hj), zero_mul]
        · simp
      · intro l _ hl
        have : ∃ j, ¬ x j = l j := by
          by_contra hcon
          push Not at hcon
          exact hl (funext fun j => (hcon j).symm)
        obtain ⟨j, hj⟩ := this
        refine Finset.sum_eq_zero fun y _ => ?_
        rw [Finset.prod_eq_zero (Finset.mem_univ (Sum.inl j)) (if_neg hj), zero_mul]
      · simp)
  refine h.trans (Restr.mul (Restr.refl _) ?_)
  exact (Equi.prod_unique _).1

end Ten

namespace Spec

open Ten

variable {K : Type} [Field K] {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
variable (F : Spec K I)

/-- F of a pushed unit tensor of size at least 1 is at least 1. -/
theorem one_le_unit [Nonempty I] (π : J → I) {n : ℕ} (hn : 1 ≤ n) :
    1 ≤ F.F (Ten.push π (unit K J n)) := by
  refine F.one_le (y := fun _ _ => ⟨0, hn⟩) ?_
  show ite _ _ _ ≠ (0 : K)
  simp

/-- F of a unit tensor that has a leg is at most its size. -/
theorem unit_le [Nonempty J] (π : J → I) (n : ℕ) : F.F (Ten.push π (unit K J n)) ≤ n := by
  have h : SumRestr (unit K J n) (fun _ : Fin n => (1 : Ten K J)) :=
    RankLE.sumRestr (Restr.refl (unit K J n))
  have := F.le_sum _ _ (h.push π)
  simpa [F.congr (Equi.push_one π), F.one] using this

end Spec

end Ov
