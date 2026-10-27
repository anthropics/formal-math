/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSatStatement
public import Groundwork.Net.Defs
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Tactic.Ring
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Prod

/-! The network of a k-CNF, as in Section 6 of the paper (for k-CNFs, the proof of Theorem A (c)).
The clauses are cut into `g` clusters, the nodes. A state
of a cluster holds a bit for each literal slot, one-bit equalities join consecutive occurrences of a
variable, and the
weight of a cluster checks its clauses. The value of the network (`Network`, Groundwork.Net.Defs)
counts the states at which all weights
and interactions are 1 (`value_eq_card_good`); `good_toState`, `exists_model` and `toState_inj`
relate these states to the models over the occurring variables. -/

namespace Groundwork.SatNet

open Finset

section Chain

variable {ι V : Type}

/-- `q` is the next slot after `p` (in the order of `idx`) that carries the variable of `p`. -/
@[expose] public def Consec (idx : ι → ℕ) (lab : ι → Option V) (p q : ι) : Prop :=
  idx p < idx q ∧ lab p ≠ none ∧ lab p = lab q ∧ ∀ r, idx p < idx r → idx r < idx q → lab r ≠ lab p

public instance [Fintype ι] [DecidableEq V] (idx : ι → ℕ) (lab : ι → Option V) (p q : ι) : Decidable (Consec idx lab p q) := by
  unfold Consec; infer_instance

variable {idx : ι → ℕ} {lab : ι → Option V}

/-- A slot has at most one successor. -/
public theorem Consec.succ_unique (hidx : Function.Injective idx) {p q q' : ι}
    (h : Consec idx lab p q) (h' : Consec idx lab p q') : q = q' := by
  obtain ⟨h1, _, h3, h4⟩ := h
  obtain ⟨h1', _, h3', h4'⟩ := h'
  apply hidx
  rcases lt_trichotomy (idx q) (idx q') with hlt | heq | hgt
  · exact absurd h3.symm (h4' q h1 hlt)
  · exact heq
  · exact absurd h3'.symm (h4 q' h1' hgt)

/-- A slot has at most one predecessor. -/
public theorem Consec.pred_unique (hidx : Function.Injective idx) {p p' q : ι}
    (h : Consec idx lab p q) (h' : Consec idx lab p' q) : p = p' := by
  obtain ⟨h1, _, h3, h4⟩ := h
  obtain ⟨h1', _, h3', h4'⟩ := h'
  apply hidx
  rcases lt_trichotomy (idx p) (idx p') with hlt | heq | hgt
  · exact absurd (h3'.trans h3.symm) (h4 p' hlt h1')
  · exact heq
  · exact absurd (h3.trans h3'.symm) (h4' p hgt h1)

/-- Equal on consecutive occurrences implies equal on all occurrences of a variable. -/
public theorem eq_of_consec (hidx : Function.Injective idx) {z : ι → Bool}
    (hz : ∀ p q, Consec idx lab p q → z p = z q) {p q : ι} (hp : lab p ≠ none) (hpq : lab p = lab q) :
    z p = z q := by
  have key : ∀ n p q, idx p < idx q → idx q - idx p ≤ n → lab p ≠ none → lab p = lab q → z p = z q := by
    intro n
    induction n with
    | zero => intro p q h1 h2; omega
    | succ n ih =>
      intro p q h1 h2 hp hpq
      by_cases h : ∃ r, idx p < idx r ∧ idx r < idx q ∧ lab r = lab p
      · obtain ⟨r, hr1, hr2, hr3⟩ := h
        exact (ih p r hr1 (by omega) hp hr3.symm).trans
          (ih r q hr2 (by omega) (hr3 ▸ hp) (hr3.trans hpq))
      · exact hz p q ⟨h1, hp, hpq, fun r a b c => h ⟨r, a, b, c⟩⟩
  rcases lt_trichotomy (idx p) (idx q) with hlt | heq | hgt
  · exact key _ p q hlt le_rfl hp hpq
  · rw [hidx heq]
  · exact (key _ q p hgt le_rfl (hpq ▸ hp) hpq.symm).symm

end Chain

section Net

variable {V : Type}

/-- A slot of a cluster: (clause of the cluster, place in the clause). -/
public abbrev Sl (μ k : ℕ) : Type := Fin μ × Fin k

/-- A slot: a cluster and a slot of it. -/
public abbrev Slot (g μ k : ℕ) : Type := Fin g × Sl μ k

/-- The place of a slot in the reading order of the formula. -/
@[expose] public def idx {g μ k : ℕ} (p : Slot g μ k) : ℕ := (p.1.val * μ + p.2.1.val) * k + p.2.2.val

theorem mul_add_inj {k x y j j' : ℕ} (hj : j < k) (hj' : j' < k) (h : x * k + j = y * k + j') :
    x = y ∧ j = j' := by
  rcases lt_trichotomy x y with hlt | heq | hgt
  · have := Nat.mul_le_mul_right k (Nat.succ_le_of_lt hlt)
    rw [Nat.succ_mul] at this; omega
  · subst heq; exact ⟨rfl, by omega⟩
  · have := Nat.mul_le_mul_right k (Nat.succ_le_of_lt hgt)
    rw [Nat.succ_mul] at this; omega

public theorem mul_add_inj' {k x y j j' : ℕ} (hj : j < k) (hj' : j' < k) (h : x * k + j = y * k + j') :
    x = y ∧ j = j' := mul_add_inj hj hj' h

public theorem idx_injective {g μ k : ℕ} : Function.Injective (idx (g := g) (μ := μ) (k := k)) := by
  rintro ⟨a, c, j⟩ ⟨a', c', j'⟩ h
  obtain ⟨h1, h2⟩ := mul_add_inj j.2 j'.2 h
  obtain ⟨h3, h4⟩ := mul_add_inj c.2 c'.2 h1
  simp only [Prod.mk.injEq]
  exact ⟨Fin.ext h3, Fin.ext h4, Fin.ext h2⟩

/-- The literal written in a slot, if any. -/
@[expose] public def lit (φ : List (List (V × Bool))) {g μ k : ℕ} (p : Slot g μ k) : Option (V × Bool) :=
  (φ[p.1.val * μ + p.2.1.val]?).bind (·[p.2.2.val]?)

/-- The variable written in a slot, if any. -/
@[expose] public def lab (φ : List (List (V × Bool))) {g μ k : ℕ} (p : Slot g μ k) : Option V :=
  (lit φ p).map Prod.fst

/-- An equality test of Section 6 of the paper: `q` is the next occurrence of the variable at `p`. -/
public abbrev Link (φ : List (List (V × Bool))) {g μ k : ℕ} (p q : Slot g μ k) : Prop :=
  Consec idx (lab φ) p q

variable [DecidableEq V]

/-- Weight of a cluster: empty slots hold 0, its clauses hold, its internal equalities hold. -/
@[expose] public def weight (φ : List (List (V × Bool))) {g μ k : ℕ} (a : Fin g) (z : Sl μ k → Bool) : ℤ :=
  if (∀ s, lit φ (a, s) = none → z s = false) ∧
      (∀ c : Fin μ, a.val * μ + c.val < φ.length →
        ∃ j : Fin k, (lit φ (a, c, j)).map Prod.snd = some (z (c, j))) ∧
      (∀ s s', Link φ (a, s) (a, s') → z s = z s') then 1 else 0

/-- All weights and interactions are 1 at `z`. -/
@[expose] public def Good (φ : List (List (V × Bool))) {g μ k : ℕ} (z : Fin g → Sl μ k → Bool) : Prop :=
  (∀ p : Slot g μ k, lit φ p = none → z p.1 p.2 = false) ∧
    (∀ (a : Fin g) (c : Fin μ), a.val * μ + c.val < φ.length →
      ∃ j : Fin k, (lit φ (a, c, j)).map Prod.snd = some (z a (c, j))) ∧
    (∀ p q : Slot g μ k, Link φ p q → z p.1 p.2 = z q.1 q.2)

public instance (φ : List (List (V × Bool))) {g μ k : ℕ} (z : Fin g → Sl μ k → Bool) : Decidable (Good φ z) := by
  unfold Good; infer_instance

/-- A model over the occurring variables: satisfies `φ`, and is 0 on the variables that do not
occur. -/
@[expose] public def IsModel (φ : List (List (V × Bool))) (a : V → Bool) : Prop :=
  (∀ C ∈ φ, ∃ l ∈ C, a l.1 = l.2) ∧ ∀ v, (∀ C ∈ φ, ∀ l ∈ C, l.1 ≠ v) → a v = false

omit [DecidableEq V] in
theorem lit_mem {φ : List (List (V × Bool))} {g μ k : ℕ} {p : Slot g μ k} {l : V × Bool}
    (h : lit φ p = some l) : ∃ C ∈ φ, l ∈ C := by
  unfold lit at h
  obtain ⟨C, hC, hl⟩ := Option.bind_eq_some_iff.1 h
  exact ⟨C, List.mem_of_getElem? hC, List.mem_of_getElem? hl⟩

omit [DecidableEq V] in
/-- Every literal of every clause is written in some slot. -/
theorem exists_slot {φ : List (List (V × Bool))} {g μ k : ℕ} (hk : ∀ C ∈ φ, C.length ≤ k)
    (hm : φ.length ≤ g * μ) {C : List (V × Bool)} (hC : C ∈ φ) {l : V × Bool} (hl : l ∈ C) :
    ∃ p : Slot g μ k, lit φ p = some l := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hC
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hl
  have hμ : 0 < μ := by
    rcases Nat.eq_zero_or_pos μ with h | h
    · subst h; omega
    · exact h
  have hg : i / μ < g := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; omega)
  refine ⟨(⟨i / μ, hg⟩, ⟨i % μ, Nat.mod_lt _ hμ⟩, ⟨j, lt_of_lt_of_le hj (hk _ hC)⟩), ?_⟩
  simp [lit, Nat.div_add_mod', hi, hj]

/-- The state that an assignment induces. -/
@[expose] public def toState (φ : List (List (V × Bool))) {g μ k : ℕ} (a : V → Bool) (c : Fin g) (s : Sl μ k) : Bool :=
  match lit φ (c, s) with
  | none => false
  | some l => a l.1

variable {φ : List (List (V × Bool))} {g μ k : ℕ}

omit [DecidableEq V] in
theorem good_toState (hk : ∀ C ∈ φ, C.length ≤ k) {a : V → Bool} (ha : IsModel φ a) :
    Good φ (toState φ (g := g) (μ := μ) (k := k) a) := by
  refine ⟨fun p hp => by simp [toState, hp], fun c d hlt => ?_, fun p q h => ?_⟩
  · obtain ⟨l, hl, hal⟩ := ha.1 _ (List.getElem_mem hlt)
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hl
    refine ⟨⟨j, lt_of_lt_of_le hj (hk _ (List.getElem_mem hlt))⟩, ?_⟩
    simp [toState, lit, hlt, hj, hal]
  · obtain ⟨_, h2, h3, _⟩ := h
    unfold lab at h2 h3
    cases hp : lit φ p <;> cases hq : lit φ q <;> simp_all [toState]

theorem exists_model (hm : φ.length ≤ g * μ) {z : Fin g → Sl μ k → Bool} (hz : Good φ z) :
    ∃ a, IsModel φ a ∧ toState φ a = z := by
  classical
  let a : V → Bool := fun v =>
    if h : ∃ p : Slot g μ k, lab φ p = some v then z h.choose.1 h.choose.2 else false
  have key : ∀ (p : Slot g μ k) l, lit φ p = some l → a l.1 = z p.1 p.2 := by
    intro p l hp
    have h : ∃ p : Slot g μ k, lab φ p = some l.1 := ⟨p, by simp [lab, hp]⟩
    simp only [a, h, dite_true]
    have := h.choose_spec
    exact eq_of_consec (z := fun p => z p.1 p.2) idx_injective hz.2.2 (by rw [this]; simp)
      (by rw [this]; simp [lab, hp])
  refine ⟨a, ⟨?_, ?_⟩, ?_⟩
  · intro C hC
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hC
    have hμ : 0 < μ := by
      rcases Nat.eq_zero_or_pos μ with h | h
      · subst h; omega
      · exact h
    have hg : i / μ < g := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; omega)
    obtain ⟨j, hj⟩ := hz.2.1 ⟨i / μ, hg⟩ ⟨i % μ, Nat.mod_lt _ hμ⟩ (by simpa [Nat.div_add_mod'] using hi)
    obtain ⟨l, hl, hl2⟩ := Option.map_eq_some_iff.1 hj
    refine ⟨l, ?_, ?_⟩
    · have hl' := hl
      simp only [lit, Nat.div_add_mod', List.getElem?_eq_getElem hi, Option.bind_some] at hl'
      exact List.mem_of_getElem? hl'
    · rw [key _ _ hl]; exact hl2.symm
  · intro v hv
    suffices hne : ¬ ∃ p : Slot g μ k, lab φ p = some v by simp only [a, hne, dite_false]
    rintro ⟨p, hp⟩
    obtain ⟨l, hl, rfl⟩ := Option.map_eq_some_iff.1 hp
    obtain ⟨C, hC, hlC⟩ := lit_mem hl
    exact hv C hC l hlC rfl
  · funext c s
    cases h : lit φ (c, s) with
    | none => simp [toState, h, hz.1 (c, s) h]
    | some l => simp [toState, h, key (c, s) l h]

theorem toState_inj (hk : ∀ C ∈ φ, C.length ≤ k) (hm : φ.length ≤ g * μ) {a a' : V → Bool}
    (ha : IsModel φ a) (ha' : IsModel φ a')
    (h : toState φ (g := g) (μ := μ) (k := k) a = toState φ a') : a = a' := by
  funext v
  by_cases hv : ∃ C ∈ φ, ∃ l ∈ C, l.1 = v
  · obtain ⟨C, hC, l, hl, rfl⟩ := hv
    obtain ⟨p, hp⟩ := exists_slot (g := g) (μ := μ) hk hm hC hl
    have := congrFun (congrFun h p.1) p.2
    simpa [toState, hp] using this
  · have hv' : ∀ C ∈ φ, ∀ l ∈ C, l.1 ≠ v := fun C hC l hl h => hv ⟨C, hC, l, hl, h⟩
    rw [ha.2 v hv', ha'.2 v hv']

public instance [Fintype V] (φ : List (List (V × Bool))) (a : V → Bool) : Decidable (IsModel φ a) := by
  unfold IsModel; infer_instance

/-! ### The network -/

theorem idx_lt_of_fst_lt {p q : Slot g μ k} (h : p.1 < q.1) : idx p < idx q := by
  obtain ⟨a, c, j⟩ := p
  obtain ⟨b, d, i⟩ := q
  have h1 : a.val + 1 ≤ b.val := h
  have h2 := Nat.mul_le_mul_right μ h1
  rw [Nat.succ_mul] at h2
  have h3 : a.val * μ + c.val + 1 ≤ b.val * μ + d.val := by have := c.2; omega
  have h4 := Nat.mul_le_mul_right k h3
  rw [Nat.succ_mul] at h4
  have := j.2
  simp only [idx]
  omega

omit [DecidableEq V] in
theorem Link.fst_le {p q : Slot g μ k} (h : Link φ p q) : p.1 ≤ q.1 := by
  by_contra hlt
  exact absurd h.1 (not_lt.2 (idx_lt_of_fst_lt (not_le.1 hlt)).le)

/-- The slot `s` of cluster `a` has its next occurrence in cluster `b`. -/
@[expose] public def Out (φ : List (List (V × Bool))) {g μ k : ℕ} (a b : Fin g) (s : Sl μ k) : Prop :=
  ∃ s', Link φ (a, s) (b, s')

public instance (φ : List (List (V × Bool))) {g μ k : ℕ} (a b : Fin g) (s : Sl μ k) : Decidable (Out φ a b s) := by
  unfold Out; infer_instance

/-- The network of `φ`: `g` clusters of `μ` clauses of `k` places. A label of clusters a < b holds a
bit for each
slot of a whose next occurrence is in b (0 at the other slots). -/
@[expose] public def net (φ : List (List (V × Bool))) (g μ k : ℕ) :
    Network (Fin g) (Sl μ k → Bool) (Sl μ k → Bool) where
  S _ := univ
  W := weight φ
  Θ a b := if a < b then tuples (Out φ a b) (fun _ => univ) false else ∅
  f a b z θ :=
    if a < b then (if ∀ s, Out φ a b s → z s = θ s then 1 else 0)
    else (if ∀ s s', Link φ (b, s) (a, s') → z s' = θ s then 1 else 0)
  c a b := #{s : Sl μ k | Out φ (min a b) (max a b) s}

/-- The interaction of clusters a < b is the product of the equalities between them. -/
public theorem Ψ_of_lt {a b : Fin g} (h : a < b) (z z' : Sl μ k → Bool) :
    (net φ g μ k).Ψ a b z z' = if ∀ s s', Link φ (a, s) (b, s') → z s = z' s' then 1 else 0 := by
  have hba : ¬ b < a := not_lt.2 h.le
  simp only [Network.Ψ, Network.lab, net, min_eq_left h.le, max_eq_right h.le, if_pos h, if_neg hba]
  set θ₀ : Sl μ k → Bool := fun s => if Out φ a b s then z s else false with hθ₀
  rw [Finset.sum_eq_single θ₀]
  · have h1 : ∀ s, Out φ a b s → z s = θ₀ s := fun s hs => by simp [hθ₀, hs]
    rw [if_pos h1, one_mul]
    refine if_congr ⟨fun H s s' hl => ?_, fun H s s' hl => ?_⟩ rfl rfl
    · rw [H s s' hl, ← h1 s ⟨s', hl⟩]
    · rw [← h1 s ⟨s', hl⟩, H s s' hl]
  · intro θ hθ hne
    rw [if_neg, zero_mul]
    intro hA
    apply hne
    funext s
    by_cases hs : Out φ a b s
    · simp [hθ₀, hs, hA s hs]
    · have := Fintype.mem_piFinset.1 hθ s
      simp only [hs, ite_false, mem_singleton] at this
      simp [hθ₀, hs, this]
  · intro hnot
    exfalso
    apply hnot
    unfold tuples
    rw [Fintype.mem_piFinset]
    intro s
    by_cases hs : Out φ a b s <;> simp [hθ₀, hs]

theorem ite_mul_ite' (p q : Prop) [Decidable p] [Decidable q] :
    (if p then (1 : ℤ) else 0) * (if q then 1 else 0) = if p ∧ q then 1 else 0 := by
  split_ifs <;> simp_all

theorem term_eq (z : Fin g → Sl μ k → Bool) :
    (∏ a, (net φ g μ k).W a (z a)) * ∏ p ∈ pairs (Fin g), (net φ g μ k).Ψ p.1 p.2 (z p.1) (z p.2) =
      if Good φ z then 1 else 0 := by
  have hΨ : ∀ p ∈ pairs (Fin g), (net φ g μ k).Ψ p.1 p.2 (z p.1) (z p.2) =
      if ∀ s s', Link φ (p.1, s) (p.2, s') → z p.1 s = z p.2 s' then 1 else 0 :=
    fun p hp => Ψ_of_lt (Finset.mem_filter.1 hp).2 _ _
  rw [Finset.prod_congr rfl hΨ]
  simp only [net, weight]
  rw [Finset.prod_ite_zero, Finset.prod_ite_zero]
  simp only [Finset.prod_const_one]
  rw [ite_mul_ite']
  split_ifs with hAB hG hG
  · rfl
  · obtain ⟨hW, hP⟩ := hAB
    refine absurd ?_ hG
    refine ⟨fun p hp => (hW p.1 (mem_univ _)).1 p.2 hp, fun a c hc => (hW a (mem_univ _)).2.1 c hc, ?_⟩
    rintro ⟨a, s⟩ ⟨b, s'⟩ hl
    rcases lt_or_eq_of_le hl.fst_le with hlt | heq
    · exact hP (a, b) (Finset.mem_filter.2 ⟨mem_univ _, hlt⟩) s s' hl
    · simp only at heq
      subst heq
      exact (hW a (mem_univ _)).2.2 s s' hl
  · obtain ⟨h1, h2, h3⟩ := hG
    exact absurd ⟨fun a _ => ⟨fun s hs => h1 (a, s) hs, fun c hc => h2 a c hc, fun s s' hl => h3 (a, s) (a, s') hl⟩,
      fun p _ s s' hl => h3 (p.1, s) (p.2, s') hl⟩ hAB
  · rfl

/-- The value counts the states at which all weights and interactions are 1. -/
public theorem value_eq_card_good : (net φ g μ k).value = #{z | Good φ (g := g) (μ := μ) (k := k) z} := by
  unfold Network.value
  rw [Finset.sum_congr rfl fun z _ => term_eq z]
  simp [net]

/-! ### Sizes -/

omit [DecidableEq V] in
theorem Link.used_left {p q : Slot g μ k} (h : Link φ p q) : lit φ p ≠ none := by
  intro hp; exact h.2.1 (by simp [lab, hp])

omit [DecidableEq V] in
theorem Link.used_right {p q : Slot g μ k} (h : Link φ p q) : lit φ q ≠ none := by
  intro hq; exact h.2.1 (by rw [h.2.2.1]; simp [lab, hq])

omit [DecidableEq V] in
/-- At most `k` slots per clause are used. -/
theorem card_used_le : #{p : Slot g μ k | lit φ p ≠ none} ≤ φ.length * k := by
  have hc : #(range φ.length ×ˢ range k) = φ.length * k := by simp
  rw [← hc]
  refine Finset.card_le_card_of_injOn (fun p => (p.1.val * μ + p.2.1.val, p.2.2.val)) ?_ ?_
  · intro p hp
    have hp' : lit φ p ≠ none := by simpa using hp
    have hlt : p.1.val * μ + p.2.1.val < φ.length := by
      by_contra h
      exact hp' (by simp [lit, List.getElem?_eq_none (not_lt.1 h)])
    simp [hlt, p.2.2.2]
  · rintro ⟨a, c, j⟩ _ ⟨a', c', j'⟩ _ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨h3, h4⟩ := mul_add_inj c.2 c'.2 h.1
    simp only [Prod.mk.injEq]
    exact ⟨Fin.ext h3, Fin.ext h4, Fin.ext h.2⟩

theorem sum_card_eq (P : Fin g → Sl μ k → Prop) [∀ b s, Decidable (P b s)] :
    ∑ b, #{s | P b s} = #{q : Slot g μ k | P q.1 q.2} := by
  simp only [Finset.card_filter]
  rw [Fintype.sum_prod_type]

/-- The equalities that leave cluster `a` forwards. -/
theorem sum_out_le (a : Fin g) : ∑ b, #{s : Sl μ k | Out φ a b s} ≤ #{s : Sl μ k | lit φ (a, s) ≠ none} := by
  rw [sum_card_eq]
  refine Finset.card_le_card_of_injOn (fun q => q.2) ?_ ?_
  · intro q hq
    obtain ⟨s', hl⟩ : Out φ a q.1 q.2 := by simpa using hq
    simpa using hl.used_left
  · rintro ⟨b, s⟩ hq ⟨b', s₁⟩ hq' h
    simp only at h
    subst h
    obtain ⟨s', hl⟩ : Out φ a b s := by simpa using hq
    obtain ⟨s'', hl'⟩ : Out φ a b' s := by simpa using hq'
    have := hl.succ_unique idx_injective hl'
    simp only [Prod.mk.injEq] at this
    simp [this.1]

/-- The equalities that reach cluster `a` from before. -/
theorem sum_in_le (a : Fin g) : ∑ b, #{s : Sl μ k | Out φ b a s} ≤ #{s : Sl μ k | lit φ (a, s) ≠ none} := by
  rw [sum_card_eq]
  refine Finset.card_le_card_of_forall_subsingleton (fun (q : Slot g μ k) s' => Link φ q (a, s')) ?_ ?_
  · intro q hq
    obtain ⟨s', hl⟩ : Out φ q.1 a q.2 := by simpa using hq
    exact ⟨s', by simpa using hl.used_right, hl⟩
  · intro s' _ q hq q' hq'
    exact hq.2.pred_unique idx_injective hq'.2

theorem c_le (a b : Fin g) :
    (net φ g μ k).c a b ≤ #{s : Sl μ k | Out φ a b s} + #{s : Sl μ k | Out φ b a s} := by
  simp only [net]
  rcases le_total a b with h | h
  · rw [min_eq_left h, max_eq_right h]; omega
  · rw [min_eq_right h, max_eq_left h]; omega

theorem sum_c_le (a : Fin g) :
    ∑ b ∈ univ.erase a, (net φ g μ k).c a b ≤ 2 * #{s : Sl μ k | lit φ (a, s) ≠ none} := by
  calc ∑ b ∈ univ.erase a, (net φ g μ k).c a b ≤ ∑ b, (net φ g μ k).c a b :=
        Finset.sum_le_sum_of_subset (Finset.erase_subset _ _)
    _ ≤ ∑ b, (#{s : Sl μ k | Out φ a b s} + #{s : Sl μ k | Out φ b a s}) := Finset.sum_le_sum fun b _ => c_le a b
    _ = ∑ b, #{s : Sl μ k | Out φ a b s} + ∑ b, #{s : Sl μ k | Out φ b a s} := Finset.sum_add_distrib
    _ ≤ 2 * #{s : Sl μ k | lit φ (a, s) ≠ none} := by have := sum_out_le (φ := φ) (μ := μ) (k := k) a
                                                      have := sum_in_le (φ := φ) (μ := μ) (k := k) a
                                                      omega

/-- The label bits `c a b`, summed over all ordered pairs of clusters (`U`), are at most 2k times
the number of clauses. -/
public theorem U_net_le : (net φ g μ k).U ≤ 2 * k * φ.length := by
  unfold Network.U
  calc ∑ a, ∑ b ∈ univ.erase a, (net φ g μ k).c a b ≤ ∑ a, 2 * #{s : Sl μ k | lit φ (a, s) ≠ none} :=
        Finset.sum_le_sum fun a _ => sum_c_le a
    _ = 2 * #{p : Slot g μ k | lit φ p ≠ none} := by
        rw [← Finset.mul_sum, sum_card_eq (fun a s => lit φ (a, s) ≠ none)]
    _ ≤ 2 * k * φ.length := by
        have := card_used_le (φ := φ) (g := g) (μ := μ) (k := k)
        rw [Nat.mul_assoc, Nat.mul_comm k]
        omega

theorem abs_ite_le (p : Prop) [Decidable p] : |if p then (1 : ℤ) else 0| ≤ 1 := by
  split_ifs <;> simp

/-- The network has size 2kμ: at most 2^(2kμ) states a cluster and at most 2kμ label bits at a
cluster. All entries
are 0 or 1, so within 2^B for every `B`. -/
public theorem sized_net (B : ℕ) : (net φ g μ k).Sized (2 * k * μ) B where
  card_S a := by
    simp only [net, Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_prod, Fintype.card_fin]
    exact Nat.pow_le_pow_right (by norm_num) (by rw [Nat.mul_assoc, Nat.mul_comm k]; omega)
  abs_W a z := by
    simp only [net, weight]
    exact (abs_ite_le _).trans (one_le_pow₀ (by norm_num))
  c_symm a b := by simp only [net, min_comm, max_comm]
  sum_c a := by
    refine (sum_c_le a).trans ?_
    have : #{s : Sl μ k | lit φ (a, s) ≠ none} ≤ μ * k := by
      refine (Finset.card_filter_le _ _).trans ?_
      simp
    rw [Nat.mul_assoc, Nat.mul_comm k]
    omega
  card_lab a b hab := by
    have hlt : min a b < max a b := by
      rcases lt_or_gt_of_ne hab with h | h
      · rwa [min_eq_left h.le, max_eq_right h.le]
      · rwa [min_eq_right h.le, max_eq_left h.le]
    simp only [Network.lab, net, if_pos hlt, tuples, Fintype.card_piFinset]
    apply le_of_eq
    rw [Finset.prod_congr rfl (g := fun s => if Out φ (min a b) (max a b) s then 2 else 1)
      (fun s _ => by split_ifs <;> simp)]
    rw [Finset.prod_ite]
    simp
  abs_f a b z θ := by
    have h1 : (1 : ℤ) ≤ 2 ^ B := one_le_pow₀ (by norm_num)
    simp only [net]
    split_ifs <;> simp [h1]
  abs_Ψ a b z z' hab := by
    rcases lt_or_gt_of_ne hab with h | h
    · rw [Ψ_of_lt h]; exact (abs_ite_le _).trans (one_le_pow₀ (by norm_num))
    · have : (net φ g μ k).Ψ a b z z' = (net φ g μ k).Ψ b a z' z := by
        simp only [Network.Ψ, Network.lab, min_comm, max_comm, mul_comm]
      rw [this, Ψ_of_lt h]; exact (abs_ite_le _).trans (one_le_pow₀ (by norm_num))

end Net

/-- `g` clusters of ⌈m/g⌉ clauses hold all `m` clauses. -/
public theorem le_mul_ceil (m : ℕ) {g : ℕ} (hg : 0 < g) : m ≤ g * ((m + g - 1) / g) := by
  have := Nat.div_add_mod (m + g - 1) g
  have := Nat.mod_lt (m + g - 1) hg
  omega

/-- With μ = ⌈m/g⌉ clauses a cluster, `g` times the size 2kμ of `sized_net` is at most 2k(m+g). -/
public theorem mul_size_le (m g k : ℕ) : g * (2 * k * ((m + g - 1) / g)) ≤ 2 * k * (m + g) := by
  have h : g * ((m + g - 1) / g) ≤ m + g := (Nat.mul_div_le _ _).trans (by omega)
  calc g * (2 * k * ((m + g - 1) / g)) = 2 * k * (g * ((m + g - 1) / g)) := by ring
    _ ≤ 2 * k * (m + g) := Nat.mul_le_mul_left _ h

end Groundwork.SatNet

