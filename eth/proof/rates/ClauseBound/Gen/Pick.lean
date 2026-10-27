/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ClauseBound.Gen.Defs
public import ClauseBound.Gen.PartA
public import PaddedDescent.F.FuelCert

/-! # The general recursion: picking the level

From a bound b in unary, the largest ℓ with K_ℓ ≤ b and the schedule of level ℓ, in polynomial time.
A loop over the units of b keeps the state
(ℓ, schedule of level ℓ, K_ℓ, 2^{3ℓ+x₀}, the precision D_ℓ = 3·m·2^{ℓ+4} with m = `P.m`), all
numbers in unary, and pushes the next step as long as K_{ℓ+1} = (2^{3ℓ+x₀}·K_ℓ)² ≤ b. The state is
cut off by a pad whose length is a polynomial in b; the mathematics shows that the cut-off is never
active. -/

public section

namespace ClauseBound.Gen.Pick

open Groundwork PaddedDescent.F ClauseBound.Alg Levels.Gen

/-! ### The numbers -/

theorem K_pos (x₀ l : ℕ) : 1 ≤ K x₀ l := by rw [K_eq]; exact Nat.one_le_two_pow

theorem K_succ (x₀ l : ℕ) : K x₀ (l + 1) = g x₀ l ^ 2 := rfl

theorem g_le_K_succ (x₀ l : ℕ) : g x₀ l ≤ K x₀ (l + 1) := by
  rw [K_succ]; exact Nat.le_self_pow (by norm_num) _

theorem K_le_g (x₀ l : ℕ) : K x₀ l ≤ g x₀ l := Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _)

theorem pow_le_g (x₀ l : ℕ) : 2 ^ (3 * l + x₀) ≤ g x₀ l := Nat.le_mul_of_pos_right _ (K_pos x₀ l)

theorem K_le_succ (x₀ l : ℕ) : K x₀ l ≤ K x₀ (l + 1) := (K_le_g x₀ l).trans (g_le_K_succ x₀ l)

theorem two_pow_le (x₀ l : ℕ) : 2 ^ l ≤ 2 ^ (3 * l + x₀) := Nat.pow_le_pow_right (by norm_num) (by omega)

/-- 2^{3ℓ+x₀} ≤ 8·K_ℓ. -/
theorem pow_le_K (x₀ l : ℕ) : 2 ^ (3 * l + x₀) ≤ 8 * K x₀ l := by
  cases l with
  | zero =>
    have : K x₀ 0 = 2 ^ x₀ := rfl
    rw [this, Nat.mul_zero, Nat.zero_add]; omega
  | succ l =>
    have h1 : 2 ^ (3 * (l + 1) + x₀) = 8 * 2 ^ (3 * l + x₀) := by ring
    rw [h1]
    exact Nat.mul_le_mul_left 8 ((pow_le_g x₀ l).trans (g_le_K_succ x₀ l))

/-- ℓ < K_{ℓ+1}. -/
theorem lt_K_succ (x₀ l : ℕ) : l < K x₀ (l + 1) :=
  Nat.lt_two_pow_self.trans_le ((two_pow_le x₀ l).trans ((pow_le_g x₀ l).trans (g_le_K_succ x₀ l)))

/-! ### The loop -/

/-- (ℓ, schedule, K_ℓ, 2^{3ℓ+x₀}, D_ℓ). -/
abbrev St : Type := U × List Step × U × U × U

/-- The state at level ℓ. -/
def state (P : PiecesF) (x₀ l : ℕ) : St :=
  (rep l, sched P x₀ l, rep (K x₀ l), rep (2 ^ (3 * l + x₀)), rep (3 * P.m * 2 ^ (l + 4)))

/-- One round: the next step is pushed if K_{ℓ+1} ≤ b. -/
def next (b : U) (st : St) : St :=
  if (st.2.2.2.1.length * st.2.2.1.length) ^ 2 ≤ b.length then
    (() :: st.1,
      ((st.2.2.1, List.replicate (st.2.2.2.1.length * st.2.2.1.length) (), List.replicate (st.2.2.2.1.length * st.2.2.1.length) ()),
        (st.2.2.2.2, []), (false, [], [])) :: st.2.1,
      List.replicate ((st.2.2.2.1.length * st.2.2.1.length) ^ 2) (), List.replicate (8 * st.2.2.2.1.length) (), st.2.2.2.2 ++ st.2.2.2.2)
  else st

theorem next_state (P : PiecesF) (x₀ l : ℕ) (b : U) :
    next b (state P x₀ l) = if K x₀ (l + 1) ≤ b.length then state P x₀ (l + 1) else state P x₀ l := by
  have h1 : 8 * 2 ^ (3 * l + x₀) = 2 ^ (3 * (l + 1) + x₀) := by ring
  have h2 : 3 * P.m * 2 ^ (l + 4) + 3 * P.m * 2 ^ (l + 4) = 3 * P.m * 2 ^ (l + 1 + 4) := by ring
  simp only [next, state, rep, List.length_replicate, List.replicate_append_replicate, h1, h2, sched, step, K, g, List.replicate_succ]
  rfl

/-- An upper bound for the length of the word of one step, together with the two symbols that the
list of steps adds around it (see `len_cons`), when K_{ℓ+1} ≤ k. -/
def stepB (m k : ℕ) : ℕ := 12 * k + 192 * (m * k) + 31

/-- An upper bound for the length of the word of the state at a level ℓ ≤ r with K_ℓ ≤ k. -/
def lenB (m r k : ℕ) : ℕ := r * stepB m k + 4 * r + 36 * k + 1536 * (m * k) + 18

theorem len_rep (n : ℕ) : len (rep n) = 4 * n + 2 := by rw [rep, len_units, List.length_replicate]

/-- D_ℓ ≤ 48·m·2^{3ℓ+x₀}. -/
theorem D_le (m x₀ l : ℕ) : 3 * m * 2 ^ (l + 4) ≤ 48 * (m * 2 ^ (3 * l + x₀)) := by
  have h : 3 * m * 2 ^ (l + 4) = 48 * (m * 2 ^ l) := by ring
  rw [h]
  exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (two_pow_le x₀ l))

theorem len_sched_le (P : PiecesF) (x₀ k : ℕ) : ∀ l, K x₀ l ≤ k → len (sched P x₀ l) ≤ l * stepB P.m k + 2
  | 0, _ => by simp [sched, len_nil]
  | l + 1, h => by
    have ih := len_sched_le P x₀ k l ((K_le_succ x₀ l).trans h)
    have h1 : g x₀ l ≤ k := (g_le_K_succ x₀ l).trans h
    have h2 : K x₀ l ≤ k := (K_le_succ x₀ l).trans h
    have h3 : 3 * P.m * 2 ^ (l + 4) ≤ 48 * (P.m * k) :=
      (D_le P.m x₀ l).trans (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ ((pow_le_g x₀ l).trans h1)))
    rw [sched, len_cons, step]
    simp only [len_pair, len_rep, len_nil, len_bool]
    have e : (l + 1) * stepB P.m k = l * stepB P.m k + stepB P.m k := Nat.succ_mul _ _
    rw [e]
    have e2 : stepB P.m k = 12 * k + 192 * (P.m * k) + 31 := rfl
    omega

theorem len_state_le (P : PiecesF) (x₀ k r l : ℕ) (hk : K x₀ l ≤ k) (hl : l ≤ r) : len (state P x₀ l) ≤ lenB P.m r k := by
  have h1 := len_sched_le P x₀ k l hk
  have h2 : 2 ^ (3 * l + x₀) ≤ 8 * k := (pow_le_K x₀ l).trans (Nat.mul_le_mul_left 8 hk)
  have h3 : 3 * P.m * 2 ^ (l + 4) ≤ 384 * (P.m * k) := by
    calc 3 * P.m * 2 ^ (l + 4) ≤ 48 * (P.m * 2 ^ (3 * l + x₀)) := D_le P.m x₀ l
      _ ≤ 48 * (P.m * (8 * k)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h2)
      _ = 384 * (P.m * k) := by ring
  have h4 : l * stepB P.m k ≤ r * stepB P.m k := Nat.mul_le_mul_right _ hl
  unfold state lenB
  simp only [len_pair, len_rep]
  omega

/-- The pad of the loop. -/
def padOf (m x₀ : ℕ) (b : U) : U := List.replicate (lenB m b.length (b.length + 2 ^ x₀)) ()

/-- The state after all rounds. -/
def loop (P : PiecesF) (x₀ : ℕ) (b : U) : St :=
  (List.replicate b.length ()).foldl (fun st _ => cap (padOf P.m x₀ b) ([], [], [], [], []) (next b st))
    (cap (padOf P.m x₀ b) ([], [], [], [], []) (state P x₀ 0))

/-- The level ℓ, together with the schedule of level ℓ and K_0, in unary. -/
def pick (P : PiecesF) (x₀ : ℕ) (b : U) : U × (List Step × U) := ((loop P x₀ b).1, ((loop P x₀ b).2.1, rep (K x₀ 0)))

/-- After r rounds the state is that of a level ℓ ≤ r with ℓ = 0 or K_ℓ ≤ b, and ℓ = r unless b <
K_{ℓ+1}. -/
theorem rounds (P : PiecesF) (x₀ : ℕ) (b : U) : ∀ r ≤ b.length, ∃ l,
    (List.replicate r ()).foldl (fun st _ => cap (padOf P.m x₀ b) ([], [], [], [], []) (next b st))
      (cap (padOf P.m x₀ b) ([], [], [], [], []) (state P x₀ 0)) = state P x₀ l ∧
    l ≤ r ∧ (l = 0 ∨ K x₀ l ≤ b.length) ∧ (r ≤ l ∨ b.length < K x₀ (l + 1)) := by
  have hcap : ∀ l, l ≤ b.length → (l = 0 ∨ K x₀ l ≤ b.length) →
      cap (padOf P.m x₀ b) ([], [], [], [], []) (state P x₀ l) = state P x₀ l := by
    intro l hl h
    refine cap_eq ?_
    rw [padOf, List.length_replicate]
    refine len_state_le P x₀ _ _ l ?_ hl
    rcases h with rfl | h
    · exact Nat.le_add_left _ _
    · exact h.trans (Nat.le_add_right _ _)
  intro r
  induction r with
  | zero => intro _; exact ⟨0, hcap 0 (Nat.zero_le _) (Or.inl rfl), le_rfl, Or.inl rfl, Or.inl le_rfl⟩
  | succ r ih =>
    intro hr
    obtain ⟨l, h1, h2, h3, h4⟩ := ih (by omega)
    rw [List.replicate_succ' (n := r), List.foldl_append, h1, List.foldl_cons, List.foldl_nil, next_state]
    by_cases hK : K x₀ (l + 1) ≤ b.length
    · rw [if_pos hK]
      exact ⟨l + 1, hcap _ (by omega) (Or.inr hK), by omega, Or.inr hK, Or.inl (by omega)⟩
    · rw [if_neg hK]
      exact ⟨l, hcap _ (by omega) h3, by omega, h3, Or.inr (by omega)⟩

@[fun_prop] theorem next_polyT : PolyT fun p : U × St => next p.1 p.2 := by
  unfold next; fun_prop

theorem padOf_polyT (m x₀ : ℕ) : PolyT (padOf m x₀) := by
  unfold padOf lenB stepB; fun_prop

theorem loop_polyT (P : PiecesF) (x₀ : ℕ) : PolyT (loop P x₀) := by
  unfold loop
  exact foldl_cap (pad := padOf P.m x₀) (l := fun b : U => List.replicate b.length ()) (a := fun _ => state P x₀ 0)
    (g := fun b st _ => next b st) ([], [], [], [], []) (padOf_polyT P.m x₀) (by fun_prop) (PolyT.const _)
    (PolyT.comp (g := fun p : U × St × Unit => (p.1, p.2.1)) next_polyT (by fun_prop))

theorem pick_polyT (P : PiecesF) (x₀ : ℕ) : PolyT (pick P x₀) := by
  have := loop_polyT P x₀
  unfold pick; fun_prop

/-- From a bound in unary: the largest ℓ with K_ℓ ≤ bound, the schedule of level ℓ and K_0, in
polynomial time. -/
theorem stPick : StPick := by
  intro P x₀
  refine ⟨pick P x₀, pick_polyT P x₀, fun b => ?_, fun b h0 => ?_, fun b => ?_⟩ <;>
    obtain ⟨l, h1, h2, h3, h4⟩ := rounds P x₀ b b.length le_rfl <;>
    have hl : loop P x₀ b = state P x₀ l := h1 <;>
    simp only [pick, hl, state, rep, List.length_replicate]
  · rfl
  · rcases h3 with rfl | h3
    · exact h0
    · exact h3
  · rcases h4 with h4 | h4
    · exact h4.trans_lt (lt_K_succ x₀ l)
    · exact h4

end ClauseBound.Gen.Pick
