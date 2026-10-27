/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import CircuitLowerBound.Interfaces
import Mathlib.Tactic

/-! # The circuit lower bound for E^NP (Section 7): small facts

The chains (`stChain`), the size of the variables of the formula of a table (`stVars`), the search
for a satisfying assignment (`stGreedy`), and the numbers of tables (`stCode`). -/

public section

namespace CircuitLowerBound

open ENP Groundwork

namespace SmallFacts

/-! ### The chains -/

theorem nu_two_mul {k : ℕ} (hk : k ≠ 0) : nu (2 * k) = nu k + 1 := by
  have : Nat.bits (2 * k) = false :: Nat.bits k := by
    rw [← Nat.bit_false_apply, Nat.bits_append_bit _ _ fun h => absurd h hk]
  simp [nu, this]

theorem nu_odd (s : ℕ) : nu (2 * s + 1) = 0 := by simp [nu]

theorem nu_pow_mul (a s : ℕ) : nu (2 ^ a * (2 * s + 1)) = a := by
  induction a with
  | zero => simpa using nu_odd s
  | succ a ih =>
    rw [pow_succ, Nat.mul_comm (2 ^ a) 2, Nat.mul_assoc, nu_two_mul (by positivity), ih]

theorem pack_lt {x y A M : ℕ} (hx : x < A) (hy : y < M) : x * M + y < A * M :=
  calc x * M + y < x * M + M := by omega
    _ = (x + 1) * M := by ring
    _ ≤ A * M := Nat.mul_le_mul_right _ hx

/-! ### The search -/

theorem length_greedy (φ : Cnf) (j : ℕ) : (greedy φ j).length = j := by
  induction j with
  | zero => rfl
  | succ j ih => simp [greedy, ih]

theorem greedy_prefix (φ : Cnf) {j j' : ℕ} (h : j ≤ j') : greedy φ j <+: greedy φ j' := by
  induction j', h using Nat.le_induction with
  | base => exact List.prefix_rfl
  | succ j' _ ih => exact ih.trans (by rw [greedy]; exact List.prefix_append _ _)

theorem sat_append {φ ψ : Cnf} {a : ℕ → Bool} : (∀ C ∈ φ ++ ψ, ∃ l ∈ C, a l.1 = l.2) ↔ (∀ C ∈ φ, ∃ l ∈ C, a l.1 = l.2) ∧ ∀ C ∈ ψ, ∃ l ∈ C, a l.1 = l.2 :=
  List.forall_mem_append

theorem sat_units {w : List Bool} {a : ℕ → Bool} : (∀ C ∈ units w, ∃ l ∈ C, a l.1 = l.2) ↔ ∀ i < w.length, a i = w.getD i false := by
  simp [units]

/-- The values found so far can always be continued to a satisfying assignment. -/
theorem sat_greedy {φ : Cnf} (h : Sat φ) (j : ℕ) : Sat (φ ++ units (greedy φ j)) := by
  classical
  induction j with
  | zero =>
    obtain ⟨a, ha⟩ := h
    exact ⟨a, sat_append.2 ⟨ha, by simp [greedy, units]⟩⟩
  | succ j ih =>
    rw [greedy]
    by_cases h0 : Sat (φ ++ units (greedy φ j ++ [false]))
    · simp [h0]
    · simp only [h0, decide_false, Bool.not_false]
      obtain ⟨a, ha⟩ := ih
      obtain ⟨h1, h2⟩ := sat_append.1 ha
      rw [sat_units] at h2
      have key : ∀ v : Bool, a j = v → ∀ C ∈ φ ++ units (greedy φ j ++ [v]), ∃ l ∈ C, a l.1 = l.2 := by
        intro v hv
        refine sat_append.2 ⟨h1, sat_units.2 fun i hi => ?_⟩
        rw [List.length_append, length_greedy, List.length_singleton] at hi
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
        · rw [List.getD_append _ _ _ _ (by rw [length_greedy]; exact hi)]
          exact h2 i (by rw [length_greedy]; exact hi)
        · rw [List.getD_append_right _ _ _ _ (by rw [length_greedy]), length_greedy]
          simpa using hv
      cases hv : a j with
      | false => exact absurd ⟨a, key false hv⟩ h0
      | true => exact ⟨a, key true hv⟩

/-! ### Numbers of tables -/

theorem ones_append (j : ℕ) (x : List Bool) : ones (List.replicate j true ++ false :: x) = j := by
  induction j with
  | zero => simp [ones]
  | succ j ih =>
    simp only [ones, List.replicate_succ, List.cons_append, List.takeWhile_cons, id, if_true, List.length_cons] at ih ⊢
    rw [ih]

theorem rest_append (j : ℕ) (x : List Bool) : rest (List.replicate j true ++ false :: x) = x := by
  induction j with
  | zero => simp [rest]
  | succ j ih =>
    simp only [rest, List.replicate_succ, List.cons_append, List.dropWhile_cons, id, if_true] at ih ⊢
    exact ih

/-- A word that ends with 1 is the list of binary digits of a number. -/
theorem bits_foldr (w : List Bool) : Nat.bits ((w ++ [true]).foldr Nat.bit 0) = w ++ [true] := by
  induction w with
  | nil => simp [Nat.bit]
  | cons b w ih =>
    rw [List.cons_append, List.foldr_cons, Nat.bits_append_bit _ _ fun h => ?_, ih]
    rw [h] at ih
    simp at ih

theorem le_foldr (j : ℕ) (w : List Bool) : j ≤ (List.replicate j true ++ w).foldr Nat.bit 0 := by
  induction j with
  | zero => exact Nat.zero_le _
  | succ j ih =>
    rw [List.replicate_succ, List.cons_append, List.foldr_cons, Nat.bit_true_apply]
    omega

/-- The i-th number of W bits in a word that begins with numbers of W bits. -/
theorem fld_flatten (W : ℕ) (r : List Bool) : ∀ (X : List ℕ), (∀ x ∈ X, x < 2 ^ W) → ∀ i, i < X.length →
    fld W ((X.map (toWord W)).flatten ++ r) i = X.getD i 0
  | [], _, i, hi => by simp at hi
  | x :: X, h, 0, _ => by
    have : block W 0 (((x :: X).map (toWord W)).flatten ++ r) = toWord W x := by
      simp only [block, Nat.zero_mul, List.drop_zero, List.map_cons, List.flatten_cons, List.append_assoc]
      exact List.take_left' (length_toWord _ _)
    rw [fld, this, ofWord_toWord (h x (by simp))]
    rfl
  | x :: X, h, i + 1, hi => by
    have : block W (i + 1) (((x :: X).map (toWord W)).flatten ++ r) = block W i ((X.map (toWord W)).flatten ++ r) := by
      simp only [block, List.map_cons, List.flatten_cons, List.append_assoc]
      rw [Nat.add_mul, Nat.one_mul, Nat.add_comm, ← List.drop_drop, List.drop_left' (length_toWord _ _)]
    have ih := fld_flatten W r X (fun y hy => h y (by simp [hy])) i (by simpa using hi)
    rw [fld] at ih ⊢
    rw [this, ih]
    rfl

/-- The five numbers of a literal. -/
def n5 (l : TLit) : List ℕ := [l.1, l.2.1, l.2.2.1, l.2.2.2.1, l.2.2.2.2.toNat]

/-- The fifteen numbers of a clause. -/
def n15 (c : TCl) : List ℕ := n5 c.1 ++ n5 c.2.1 ++ n5 c.2.2

theorem length_n15 (c : TCl) : (n15 c).length = 15 := by simp [n15, n5]

/-- Entry 15·r + i of the numbers of a list of clauses. -/
theorem getD_flat15 : ∀ (X : List TCl) (r i : ℕ), r < X.length → i < 15 → ((X.map n15).flatten).getD (15 * r + i) 0 = (n15 (X.getD r zeroCl)).getD i 0
  | [], r, i, hr, _ => by simp at hr
  | c :: X, 0, i, _, hi => by
    rw [List.map_cons, List.flatten_cons, Nat.mul_zero, Nat.zero_add, List.getD_append _ _ _ _ (by rw [length_n15]; exact hi)]
    rfl
  | c :: X, r + 1, i, hr, hi => by
    rw [List.map_cons, List.flatten_cons, List.getD_append_right _ _ _ _ (by rw [length_n15]; omega), length_n15,
      show 15 * (r + 1) + i - 15 = 15 * r + i by omega, getD_flat15 X r i (by simpa using hr) hi]
    rfl

theorem length_flat15 (X : List TCl) : ((X.map n15).flatten).length = 15 * X.length := by
  induction X with
  | nil => rfl
  | cons c X ih => rw [List.map_cons, List.flatten_cons, List.length_append, ih, length_n15, List.length_cons]; ring

end SmallFacts

open SmallFacts

/-- The chains. -/
theorem stChain : StChain := fun a s => by
  have h := nu_pow_mul a s
  refine ⟨h, ?_⟩
  rw [pos, h, Nat.mul_div_cancel_left _ (by positivity)]
  omega

/-- The variables of the formula of a table have L bits. -/
theorem stVars : StVars := by
  intro e L P hF C hC l hl
  obtain ⟨j, -, rfl⟩ := List.mem_map.1 hC
  have hlt : ∀ l' : TLit, vidx e L P (j / 2 ^ bq e L % 2 ^ bt e L) (j % 2 ^ bq e L) l' < 2 ^ L := by
    intro l'
    have ht : j / 2 ^ bq e L % 2 ^ bt e L < 2 ^ bt e L := Nat.mod_lt _ (by positivity)
    have h1 : l'.1 % 2 ^ kb e < 2 ^ kb e := Nat.mod_lt _ (by positivity)
    have h2 : tval (bt e L) (j / 2 ^ bq e L % 2 ^ bt e L) l'.2.1 < 2 ^ (bt e L + 1) := by
      rw [pow_succ]
      unfold tval
      split_ifs <;> omega
    have h3 : (qval P (j % 2 ^ bq e L) l'.2.2.1 + l'.2.2.2.1) % 2 ^ (bq e L + 1) < 2 ^ (bq e L + 1) := Nat.mod_lt _ (by positivity)
    have h5 : vidx e L P (j / 2 ^ bq e L % 2 ^ bt e L) (j % 2 ^ bq e L) l' < 2 ^ kb e * 2 ^ (bt e L + 1) * 2 ^ (bq e L + 1) :=
      pack_lt (pack_lt h1 h2) h3
    refine lt_of_lt_of_le h5 ?_
    rw [← pow_add, ← pow_add]
    refine Nat.pow_le_pow_right (by norm_num) ?_
    have := hF.1
    unfold bq bt
    omega
  simp only [clauseAt, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl <;> exact hlt _

/-- The search finds a satisfying assignment if there is one. -/
theorem stGreedy : StGreedy := by
  intro φ M hM hs C hC
  obtain ⟨a, ha⟩ := sat_greedy hs M
  obtain ⟨h1, h2⟩ := sat_append.1 ha
  rw [sat_units, length_greedy] at h2
  obtain ⟨l, hl, hal⟩ := h1 C hC
  refine ⟨l, hl, ?_⟩
  have hlt := hM C hC l hl
  obtain ⟨r, hr⟩ := greedy_prefix φ (show l.1 + 1 ≤ M from hlt)
  rw [← hal, h2 l.1 hlt, ← hr, List.getD_append _ _ _ _ (by rw [length_greedy]; omega)]

/-- Every table has arbitrarily large numbers. -/
theorem stCode : StCode := by
  intro e a₀
  obtain ⟨k₀, l₀, X⟩ := e
  obtain ⟨nums, hnums⟩ : ∃ nums, nums = k₀ :: l₀ :: (X.map n15).flatten := ⟨_, rfl⟩
  obtain ⟨W, hW⟩ : ∃ W, W = nums.sum + 1 := ⟨_, rfl⟩
  have hlt : ∀ x ∈ nums, x < 2 ^ W := fun x hx =>
    lt_of_le_of_lt (List.single_le_sum (by simp) x hx) (lt_trans (Nat.lt_succ_self _) (hW ▸ Nat.lt_two_pow_self))
  obtain ⟨v, hv⟩ : ∃ v, v = (nums.map (toWord W)).flatten ++ [true] := ⟨_, rfl⟩
  have hlen : nums.length = 2 + 15 * X.length := by rw [hnums, List.length_cons, List.length_cons, length_flat15]; omega
  have hvlen : v.length = nums.length * W + 1 := by
    rw [hv, List.length_append, List.length_flatten, List.map_map]
    have : (nums.map (List.length ∘ toWord W)) = List.replicate nums.length W := by
      rw [List.eq_replicate_iff]; simp
    rw [this]; simp
  have hf : ∀ i, i < nums.length → fld W v i = nums.getD i 0 := fun i hi => by rw [hv]; exact fld_flatten W _ nums hlt i hi
  refine ⟨((List.replicate a₀ true ++ false :: (List.replicate W true ++ false :: (nums.map (toWord W)).flatten)) ++ [true]).foldr Nat.bit 0, ?_, ?_⟩
  · rw [List.append_assoc]; exact le_foldr _ _
  · rw [codeOf, bits_foldr, List.append_assoc, List.cons_append, rest_append, List.append_assoc, List.cons_append, ← hv, codeOfWord, ones_append, rest_append]
    have hR : (v.length - 2 * W) / (15 * W) = X.length := by
      rw [hvlen, hlen]
      have : (2 + 15 * X.length) * W + 1 - 2 * W = 15 * W * X.length + 1 := by
        have : (2 + 15 * X.length) * W = 2 * W + 15 * W * X.length := by ring
        omega
      rw [this, Nat.mul_add_div (by omega), Nat.div_eq_of_lt (by omega), Nat.add_zero]
    have e0 : nums.getD 0 0 = k₀ := by rw [hnums]; rfl
    have e1 : nums.getD 1 0 = l₀ := by rw [hnums]; rfl
    rw [hR, hf 0 (by omega), hf 1 (by omega), e0, e1]
    have hlit : ∀ r < X.length, ∀ i, i + 5 ≤ 15 → ∀ l : TLit, (∀ f < 5, (n15 (X.getD r zeroCl)).getD (i + f) 0 = (n5 l).getD f 0) → litOf W v (2 + 15 * r + i) = l := by
      intro r hr i hi l hl
      have hg : ∀ f < 5, fld W v (2 + 15 * r + i + f) = (n5 l).getD f 0 := by
        intro f hf5
        rw [hf _ (by omega), hnums, show 2 + 15 * r + i + f = (15 * r + (i + f)) + 1 + 1 by omega, List.getD_cons_succ, List.getD_cons_succ,
          getD_flat15 X r (i + f) hr (by omega), hl f hf5]
      have g0 := hg 0 (by omega)
      have g1 := hg 1 (by omega)
      have g2 := hg 2 (by omega)
      have g3 := hg 3 (by omega)
      have g4 := hg 4 (by omega)
      simp only [Nat.add_zero] at g0
      rw [litOf, g0, g1, g2, g3, g4]
      obtain ⟨x1, x2, x3, x4, x5⟩ := l
      cases x5 <;> simp [n5]
    refine congrArg (fun z => (k₀, l₀, z)) ?_
    apply List.ext_getElem
    · simp
    · intro r h1 h2
      have hr : r < X.length := h2
      simp only [List.getElem_map, List.getElem_range]
      have hc : X.getD r zeroCl = X[r] := List.getD_eq_getElem _ _ hr
      refine Prod.ext ?_ (Prod.ext ?_ ?_)
      · exact hlit r hr 0 (by omega) _ fun f hf5 => by rw [hc]; interval_cases f <;> rfl
      · exact hlit r hr 5 (by omega) _ fun f hf5 => by rw [hc]; interval_cases f <;> rfl
      · exact hlit r hr 10 (by omega) _ fun f hf5 => by rw [hc]; interval_cases f <;> rfl

end CircuitLowerBound
