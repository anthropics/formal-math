/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import CircuitLowerBound.Alg.Parse
public import GraphProblems.Engine
public import PaddedDescent.Host
import Mathlib.Tactic

/-! # The circuit lower bound for E^NP (Section 7): the nondeterministic algorithm as a computation cut into steps

On the input 1^m 0 y the algorithm writes down a formula with clauses of at most three literals
(`pre`) and accepts if and only if this formula is UNSATISFIABLE, which it finds out by counting the
satisfying assignments with the
engine for #3-SAT. Before the last place of a chain, and if there is room, y is read as a circuit on
m inputs, and the formula says «some clause of `Phi m` is violated by the assignment that the
circuit computes»; if y does not code such a circuit, the formula is the empty formula (the
algorithm rejects). In all other
cases `Phi m` is [] or [[]], and the formula is the constant formula with the opposite answer. The
file proves: the formula always has the shape that the engine asks for (`shaped_pre`); if it is
unsatisfiable, `Phi m` is
satisfiable (`sat_Phi_of_pre`); if a circuit computes a satisfying assignment of `Phi m`, then for
the code y of this circuit the formula is unsatisfiable and has few variables (`exists_guess`); the
computation ends on every input with
the right answer (`runs_algo`); and a machine of Mathlib has at most one output (`outputs_unique`). -/

@[expose] public section

namespace CircuitLowerBound

open ENP Groundwork Turing Parse

namespace Alg

/-! ### The formula -/

/-- The number of ones at the start of x, in unary. -/
def uOf (x : List Bool) : List Unit := (x.takeWhile id).map fun _ => ()

/-- The formula of the algorithm, with the functions of the schedule as parameters: (number of
variables in unary, formula). -/
def preG (cd : List Unit → MCode) (nx : List Unit → ℕ) (lt eq : List Unit → Bool) (ft : MCode × List Unit × ℕ → Bool)
    (F : (MCode × List Unit × ℕ) × List GateD → List Unit × Cnf) (fb : List Unit → Bool) (x : List Bool) : List Unit × Cnf :=
  bif lt (uOf x) then
    (bif ft (cd (uOf x), uOf x, nx (uOf x)) then
      (bif wfB (uOf x).length (decC (rest x)) then F ((cd (uOf x), uOf x, nx (uOf x)), decC (rest x)) else ([], []))
    else ([], [[]]))
  else (bif eq (uOf x) then (bif fb (uOf x) then ([], []) else ([], [[]])) else ([], [[]]))

/-- The formula of the algorithm. -/
def pre (F : (MCode × List Unit × ℕ) × List GateD → List Unit × Cnf) (fb : List Unit → Bool) : List Bool → List Unit × Cnf :=
  preG (fun u => codeOf (nu u.length)) (fun u => next u.length) (fun u => decide (pos u.length < top (nu u.length)))
    (fun u => decide (pos u.length = top (nu u.length))) (fun p => decide (Fits p.1 p.2.1.length p.2.2)) F fb

/-- Are all bits of a word 0? -/
def isZ (w : List Bool) : Bool := w.all (!·)

/-- The algorithm: the formula, the engine, «is the number 0?». -/
def algo (E : Stepped (List Unit × Prog.Fml) (List Bool)) (F : (MCode × List Unit × ℕ) × List GateD → List Unit × Cnf) (fb : List Unit → Bool) :
    Stepped (List Bool) Bool := Stepped.mapOut (Stepped.mapIn (pre F fb) E) isZ

/-- It is 1^m in unary, m the number of ones at the start of x. -/
theorem uOf_eq (x : List Bool) : uOf x = List.replicate (ones x) () := by
  unfold uOf ones
  rw [List.eq_replicate_iff]
  exact ⟨by simp, fun _ _ => rfl⟩

variable {F : (MCode × List Unit × ℕ) × List GateD → List Unit × Cnf} {fb : List Unit → Bool}

/-- The six cases of the definition. -/
theorem pre_cases (F : (MCode × List Unit × ℕ) × List GateD → List Unit × Cnf) (fb : List Unit → Bool) (x : List Bool) :
    (pos (ones x) < top (nu (ones x)) ∧ Fits (codeOf (nu (ones x))) (ones x) (next (ones x)) ∧ WF (ones x) (decC (rest x)) ∧
        pre F fb x = F ((codeOf (nu (ones x)), List.replicate (ones x) (), next (ones x)), decC (rest x))) ∨
    (pos (ones x) < top (nu (ones x)) ∧ Fits (codeOf (nu (ones x))) (ones x) (next (ones x)) ∧ ¬WF (ones x) (decC (rest x)) ∧ pre F fb x = ([], [])) ∨
    (pos (ones x) < top (nu (ones x)) ∧ ¬Fits (codeOf (nu (ones x))) (ones x) (next (ones x)) ∧ pre F fb x = ([], [[]])) ∨
    (pos (ones x) = top (nu (ones x)) ∧ fb (List.replicate (ones x) ()) = true ∧ pre F fb x = ([], [])) ∨
    (pos (ones x) = top (nu (ones x)) ∧ fb (List.replicate (ones x) ()) = false ∧ pre F fb x = ([], [[]])) ∨
    (top (nu (ones x)) < pos (ones x) ∧ pre F fb x = ([], [[]])) := by
  unfold pre preG
  rw [uOf_eq]
  simp only [List.length_replicate]
  rcases lt_trichotomy (pos (ones x)) (top (nu (ones x))) with h | h | h
  · by_cases h2 : Fits (codeOf (nu (ones x))) (ones x) (next (ones x))
    · by_cases h3 : WF (ones x) (decC (rest x))
      · exact Or.inl ⟨h, h2, h3, by simp [h, h2, (wfB_iff _ _).2 h3]⟩
      · have h4 : wfB (ones x) (decC (rest x)) = false := by
          rw [← Bool.not_eq_true, wfB_iff]
          exact h3
        exact Or.inr (Or.inl ⟨h, h2, h3, by simp [h, h2, h4]⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨h, h2, by simp [h, h2]⟩))
  · cases h5 : fb (List.replicate (ones x) ())
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h, rfl, by simp [h]⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h, rfl, by simp [h]⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h, by simp [not_lt.2 h.le, h.ne']⟩))))

/-- The empty formula has the shape. -/
theorem shaped_nil : Shaped3 0 [] := ⟨fun _ hD => absurd hD List.not_mem_nil, List.nodup_nil⟩

/-- The formula with the empty clause has the shape. -/
theorem shaped_false : Shaped3 0 [[]] :=
  ⟨fun D hD => by
    rw [List.mem_singleton] at hD
    subst hD
    exact ⟨Nat.zero_le _, fun l hl => absurd hl List.not_mem_nil⟩, List.nodup_singleton _⟩

/-- The empty formula is satisfiable. -/
theorem sat_nil : Sat [] := ⟨fun _ => false, fun _ hC => absurd hC List.not_mem_nil⟩

/-- The formula with the empty clause is not satisfiable. -/
theorem not_sat_false : ¬Sat [[]] := fun ⟨_, h⟩ => by
  obtain ⟨l, hl, _⟩ := h [] List.mem_cons_self
  exact absurd hl List.not_mem_nil

/-- What `StForm` says about F. -/
def FormOK (a₀ : ℕ) (g : MCode → ℕ) (F : (MCode × List Unit × ℕ) × List GateD → List Unit × Cnf) : Prop :=
  ∀ (e : MCode) (L P : ℕ) (C : List GateD), Fits e L P → WF L C →
    Shaped3 (F ((e, List.replicate L (), P), C)).1.length (F ((e, List.replicate L (), P), C)).2 ∧
    (F ((e, List.replicate L (), P), C)).1.length ≤ 3 * C.length + a₀ * (L + 1) + g e ∧
    (Sat (F ((e, List.replicate L (), P), C)).2 ↔ ¬∀ D ∈ tabF e L P, ∃ l ∈ D, eval (toC C) (toWord L l.1) = l.2)

/-- What `StFlip` says about fb. -/
def FlipOK (fb : List Unit → Bool) : Prop := ∀ m : ℕ, pos m = top (nu m) →
  (fb (List.replicate m ()) = true ↔ Fits (codeOf (nu m)) (2 ^ nu m) (2 ^ nu m) ∧ Sat (tabF (codeOf (nu m)) (2 ^ nu m) (2 ^ nu m)))

variable {a₀ : ℕ} {g : MCode → ℕ}

/-- The formula always has the shape that the engine asks for. -/
theorem shaped_pre (hF : FormOK a₀ g F) (x : List Bool) : Shaped3 (pre F fb x).1.length (pre F fb x).2 := by
  rcases pre_cases F fb x with ⟨_, h2, h3, e⟩ | ⟨_, _, _, e⟩ | ⟨_, _, e⟩ | ⟨_, _, e⟩ | ⟨_, _, e⟩ | ⟨_, e⟩ <;> rw [e]
  · exact (hF _ _ _ _ h2 h3).1
  · exact shaped_nil
  · exact shaped_false
  · exact shaped_nil
  · exact shaped_false
  · exact shaped_false

/-- If the formula is unsatisfiable, `Phi m` is satisfiable. -/
theorem sat_Phi_of_pre (hF : FormOK a₀ g F) (hb : FlipOK fb) (x : List Bool) (h : ¬Sat (pre F fb x).2) : Sat (Phi (ones x)) := by
  rcases pre_cases F fb x with ⟨h1, h2, h3, e⟩ | ⟨_, _, _, e⟩ | ⟨h1, h2, _⟩ | ⟨_, _, e⟩ | ⟨h1, h2, _⟩ | ⟨h1, _⟩
  · rw [e, (hF _ _ _ _ h2 h3).2.2, not_not] at h
    unfold Phi
    rw [if_pos h1, if_pos h2]
    exact ⟨fun i => eval (toC (decC (rest x))) (toWord (ones x) i), h⟩
  · rw [e] at h
    exact absurd sat_nil h
  · unfold Phi
    rw [if_pos h1, if_neg h2]
    exact sat_nil
  · rw [e] at h
    exact absurd sat_nil h
  · unfold Phi
    rw [if_neg (by omega), if_pos h1, if_neg fun h3 => by rw [(hb _ h1).2 h3] at h2; exact Bool.noConfusion h2]
    exact sat_nil
  · unfold Phi
    rw [if_neg (by omega), if_neg (by omega)]
    exact sat_nil

/-- If a circuit computes a satisfying assignment of `Phi m`, then for the code y of this circuit
the formula is unsatisfiable and has few variables. -/
theorem exists_guess (hF : FormOK a₀ g F) (hb : FlipOK fb) (hN : StNorm) {m : ℕ} (hm : 1 ≤ m) (hpos : pos m ≤ top (nu m)) (C : Circuit)
    (hC : ∀ D ∈ Phi m, ∃ l ∈ D, eval C (toWord m l.1) = l.2) :
    ∃ y : List Bool, y.length = (m + C.length) + 1 + C.length * (4 + 2 * (m + C.length)) ∧ ¬Sat (pre F fb (unary m ++ y)).2 ∧
      (pre F fb (unary m ++ y)).1.length ≤ 3 * C.length + a₀ * (m + 1) + g (codeOf (nu m)) := by
  obtain ⟨C', hW, hl, hev⟩ := hN m C hm
  have hdec : decC (encC (m + C.length) C') = C' := by
    refine decC_encC fun G hG => ?_
    obtain ⟨t, ht, rfl⟩ := List.mem_iff_getElem.1 hG
    have h1 := hW t ht
    have h2 : m + t < 2 ^ (m + C.length) := lt_of_lt_of_le (by omega) (Nat.lt_two_pow_self (n := m + C.length)).le
    exact ⟨h1.1.trans h2, h1.2.trans h2⟩
  refine ⟨encC (m + C.length) C', by rw [length_encC, hl], ?_⟩
  have ho := Parse.ones_unary_append m (encC (m + C.length) C')
  have hr := Parse.rest_unary_append m (encC (m + C.length) C')
  rcases pre_cases F fb (unary m ++ encC (m + C.length) C') with ⟨h1, h2, h3, e⟩ | ⟨_, _, h3, _⟩ | ⟨_, _, e⟩ | ⟨h1, h2, _⟩ | ⟨_, _, e⟩ | ⟨h1, _⟩
  · rw [ho] at h1 h2
    rw [ho, hr, hdec] at e h3
    rw [e]
    obtain ⟨-, h4, h5⟩ := hF _ _ _ _ h2 h3
    refine ⟨?_, by rw [← hl]; exact h4⟩
    rw [h5, not_not]
    intro D hD
    have h6 : Phi m = tabF (codeOf (nu m)) m (next m) := by
      unfold Phi
      rw [if_pos h1, if_pos h2]
    obtain ⟨l, hl', h7⟩ := hC D (h6 ▸ hD)
    exact ⟨l, hl', by rw [hev _ (length_toWord _ _)]; exact h7⟩
  · rw [ho, hr, hdec] at h3
    exact absurd hW h3
  · rw [e]
    exact ⟨not_sat_false, Nat.zero_le _⟩
  · rw [ho] at h1 h2
    have h6 : Phi m = [[]] := by
      unfold Phi
      rw [if_neg (by omega), if_pos h1, if_pos ((hb _ h1).1 h2)]
    obtain ⟨l, hl', _⟩ := hC [] (h6 ▸ List.mem_cons_self)
    exact absurd hl' List.not_mem_nil
  · rw [e]
    exact ⟨not_sat_false, Nat.zero_le _⟩
  · rw [ho] at h1
    omega

/-! ### Counting and satisfiability -/

/-- The number of satisfying assignments is 0 if and only if the formula is unsatisfiable. -/
theorem cntN_eq_zero_iff {N : ℕ} {ψ : Cnf} (h : ∀ D ∈ ψ, ∀ l ∈ D, l.1 < N) : CountKSat.cntN N ψ = 0 ↔ ¬Sat ψ := by
  unfold CountKSat.cntN
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  constructor
  · rintro h1 ⟨a, ha⟩
    refine h1 (Finset.mem_univ fun i : Fin N => a i) fun D hD => ?_
    obtain ⟨l, hl, h2⟩ := ha D hD
    exact ⟨l, hl, by rw [CountKSat.ext, dif_pos (h D hD l hl)]; exact h2⟩
  · intro h1 a _ h2
    exact h1 ⟨CountKSat.ext a, h2⟩

/-- There are at most 2^N assignments. -/
theorem cntN_lt (N : ℕ) (ψ : Cnf) : CountKSat.cntN N ψ < 2 ^ (N + 1) := by
  unfold CountKSat.cntN
  refine lt_of_le_of_lt (Finset.card_filter_le _ _) ?_
  rw [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  exact Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self N)

/-- All N + 1 bits of a number below 2^(N+1) are 0 if and only if the number is 0. -/
theorem isZ_binary {N c : ℕ} (h : c < 2 ^ (N + 1)) : isZ (SatK.binary N c) = true ↔ c = 0 := by
  unfold isZ SatK.binary
  rw [List.all_eq_true]
  constructor
  · intro h1
    by_contra h0
    obtain ⟨i, hi⟩ := Nat.exists_testBit_of_ne_zero h0
    have h2 : i < N + 1 := by
      by_contra h3
      rw [Nat.testBit_lt_two_pow (h.trans_le (Nat.pow_le_pow_right (by norm_num) (not_lt.1 h3)))] at hi
      exact Bool.noConfusion hi
    have := h1 _ (List.mem_map.2 ⟨i, List.mem_range.2 h2, rfl⟩)
    rw [hi] at this
    exact Bool.noConfusion this
  · rintro rfl b hb
    obtain ⟨i, _, rfl⟩ := List.mem_map.1 hb
    simp

/-- What the engine for #3-SAT is asked to do with E, for clauses of at most three literals: output
the number of satisfying assignments in binary, within c·2^{δN} steps. -/
def EngineOK (E : Stepped (List Unit × Prog.Fml) (List Bool)) (c : ℕ) (δ : ℝ) : Prop := ∀ (N : ℕ) (ψ : Prog.Fml),
  (∀ C ∈ ψ, C.length ≤ 3 ∧ ∀ l ∈ C, l.1 < N) → ψ.Nodup →
    ∃ T : ℕ, E.Runs (List.replicate N (), ψ) T (c * (N + 2) ^ c) (SatK.binary N (CountKSat.cntN N ψ)) ∧ (T : ℝ) ≤ c * (2 : ℝ) ^ (δ * N)

/-- The algorithm ends on every input, and its answer is «the formula is unsatisfiable». -/
theorem runs_algo {E : Stepped (List Unit × Prog.Fml) (List Bool)} {c : ℕ} {δ : ℝ} (hE : EngineOK E c δ) (hF : FormOK a₀ g F) (x : List Bool) :
    ∃ (T : ℕ) (b : Bool), (algo E F fb).Runs x T (c * ((pre F fb x).1.length + 2) ^ c) b ∧ (b = true ↔ ¬Sat (pre F fb x).2) ∧
      (T : ℝ) ≤ c * (2 : ℝ) ^ (δ * (pre F fb x).1.length) := by
  obtain ⟨h1, h2⟩ := shaped_pre (fb := fb) hF x
  obtain ⟨T, hr, hT⟩ := hE _ _ h1 h2
  have e : (List.replicate (pre F fb x).1.length (), (pre F fb x).2) = pre F fb x :=
    Prod.ext (List.eq_replicate_iff.2 ⟨rfl, fun _ _ => rfl⟩).symm rfl
  rw [e] at hr
  exact ⟨T, _, Stepped.mapOut_runs (Stepped.mapIn_runs hr),
    (isZ_binary (cntN_lt _ _)).trans (cntN_eq_zero_iff fun D hD => (h1 D hD).2), hT⟩

/-! ### Polynomial time -/

/-- The formula is computed in polynomial time, if the functions of the schedule are. -/
theorem preG_polyT {cd : List Unit → MCode} {nx : List Unit → ℕ} {lt eq : List Unit → Bool} {ft : MCode × List Unit × ℕ → Bool}
    (h1 : PolyT cd) (h2 : PolyT nx) (h3 : PolyT lt) (h4 : PolyT eq) (h5 : PolyT ft) (h6 : PolyT F) (h7 : PolyT fb) :
    PolyT (preG cd nx lt eq ft F fb) := by
  unfold preG uOf
  fun_prop

/-- The formula is computed in polynomial time. -/
theorem pre_polyT (hS : StCertSched) (h6 : PolyT F) (h7 : PolyT fb) : PolyT (pre F fb) :=
  preG_polyT hS.1 hS.2.1 hS.2.2.2.1 hS.2.2.2.2.1 hS.2.2.2.2.2 h6 h7

/-- The test for 0 is polynomial-time. -/
theorem isZ_polyT : PolyT isZ := by
  unfold isZ
  fun_prop

/-- All parts of the algorithm are polynomial-time. -/
@[instance_reducible] def isPolyT_algo {E : Stepped (List Unit × Prog.Fml) (List Bool)} [IsPolyT E] (hS : StCertSched) (h6 : PolyT F) (h7 : PolyT fb) :
    IsPolyT (algo E F fb) :=
  haveI := IsPolyT.mapIn (M := E) (pre_polyT hS h6 h7)
  IsPolyT.mapOut (M := Stepped.mapIn (pre F fb) E) isZ_polyT

/-! ### A machine has at most one output -/

/-- From a halted configuration there is no step. -/
theorem iterate_halt (tm : FinTM2) (o : List (tm.Γ tm.k₁)) (k : ℕ) :
    (flip bind tm.step)^[k + 1] (some (haltList tm o)) = none := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', ih]; rfl

/-- Two runs of a machine on the same input that end with an output end with the same output. -/
theorem outputs_unique {tm : FinTM2} {l : List (tm.Γ tm.k₀)} {o o' : List (tm.Γ tm.k₁)} {T T' : ℕ}
    (h : TM2OutputsInTime tm l (some o) T) (h' : TM2OutputsInTime tm l (some o') T') : o = o' := by
  have key : ∀ {n n' : ℕ} {o o' : List (tm.Γ tm.k₁)}, n ≤ n' → (flip bind tm.step)^[n] (some (initList tm l)) = some (haltList tm o) →
      (flip bind tm.step)^[n'] (some (initList tm l)) = some (haltList tm o') → o = o' := by
    intro n n' o o' hn h1 h2
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
    rw [Nat.add_comm, Function.iterate_add_apply, h1] at h2
    cases k with
    | zero =>
      have h3 := congrArg (fun c : tm.Cfg => c.stk tm.k₁) (Option.some.inj h2)
      simpa [haltList] using h3
    | succ k =>
      rw [iterate_halt] at h2
      exact absurd h2 (by simp)
  rcases le_total h.steps h'.steps with hn | hn
  · exact key hn h.evals_in_steps h'.evals_in_steps
  · exact (key hn h'.evals_in_steps h.evals_in_steps).symm

end Alg

end CircuitLowerBound
