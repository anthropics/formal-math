/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Wrap.Coding
import CircuitLowerBound.Tab.Sound
import CountKSat.Host
import StepMachines.Prog.Stepped
import ToTuring.Closure.Basic
import ToTuring.Lib.List1b

/-! # From a coding of the configurations of a machine to a machine around it

Given a coding `K` of the configurations of a machine M (`Wrap.Coding`) and polynomial-time
functions `pre`, `post` on bit strings, `sim K pre post` is the computation cut into steps that
starts with the value
for the start configuration of M on `pre x`, applies the coded step of M, and ends, once M has
halted, with `post` of M's output. All three of its parts are polynomial-time (`sim_isPolyT`). After
j steps its state is the value for
the configuration of M after j steps (`run_sim`), and each step adds at most a constant to the size
of that value (`size_rep_iterate_le`). So a run of M on `pre x` of at most t steps with output y is
a run of `sim K pre post` on x of at most t steps with
result `post y` and with states of size linear in |pre x| + t (`sim_runs`). The host machine
(`CountKSat.exists_tmW`) carries out such a computation on one of Mathlib's machines with a
polynomial overhead; this gives `wraps_of_coding`.
`everyMachineCanBeWrapped_of`: if every machine with finite alphabets has a coding, then every such
machine can be wrapped. -/

public section

namespace Wrap

open Turing Groundwork CircuitLowerBound.Tab

variable {M : TM2ComputableAux Bool Bool}

/-- The simulation of M as a computation cut into steps. Its states are the values that stand for
configurations of M. It starts with the value for the start configuration of M on `pre x`; one step
is the coded step of M; it has a result
once the value stands for a halted configuration, and the result is `post` of M's output. -/
@[expose] def sim (K : Coding M) (pre post : List Bool → List Bool) : Stepped (List Bool) (List Bool) where
  σ := Rep
  init x := K.init (pre x)
  step := K.step
  out r := (K.out r).map post

/-- The start of the simulation is polynomial-time if `pre` is. -/
theorem sim_init_polyT (K : Coding M) {pre : List Bool → List Bool} (hpre : PolyT pre) : PolyT fun x => K.init (pre x) :=
  K.init_poly.comp hpre

/-- Reading the result of the simulation is polynomial-time if `post` is. -/
theorem sim_out_polyT (K : Coding M) {post : List Bool → List Bool} (hpost : PolyT post) : PolyT fun r => (K.out r).map post := by
  have := K.out_poly
  fun_prop

/-- The start, the step and the reading of the result of the simulation are polynomial-time if `pre`
and `post` are. The states are encoded and measured by the library's instances for pairs, lists and
numbers. -/
@[instance_reducible, expose] def sim_isPolyT (K : Coding M) {pre post : List Bool → List Bool} (hpre : PolyT pre) (hpost : PolyT post) :
    IsPolyT (sim K pre post) where
  enc := (inferInstance : Enc Rep)
  carried := (inferInstance : Carried Rep)
  init := sim_init_polyT K hpre
  step := K.step_poly
  out := sim_out_polyT K hpost

/-- One step of the iteration of the simulation, on the value for the configuration c, gives the
value for the next configuration of M; a halted configuration stays as it is on both sides. -/
theorem next_sim (K : Coding M) (pre post : List Bool → List Bool) (c : M.tm.Cfg) :
    (sim K pre post).next (K.rep c) = K.rep (stay M c) := by
  by_cases h : c.l = none
  · rw [stay_of_halted M h]
    simp only [Stepped.next, sim, K.out_halted c h, Option.map_some]
  · simp only [Stepped.next, sim, K.out_running c h, Option.map_none, K.step_rep]

/-- After j steps the state of the simulation on x is the value for the configuration of M after j
steps on `pre x`. -/
theorem run_sim (K : Coding M) (pre post : List Bool → List Bool) (x : List Bool) (j : ℕ) :
    (sim K pre post).run x j = K.rep ((stay M)^[j] (initList M.tm ((pre x).map M.inputAlphabet.invFun))) := by
  induction j with
  | zero => exact K.init_rep (pre x)
  | succ j ih =>
    rw [Function.iterate_succ_apply', ← next_sim K pre post, ← ih]
    exact Function.iterate_succ_apply' _ _ _

/-- j steps of M add at most j times the constant of the coding to the size of the value. -/
theorem size_rep_iterate_le (K : Coding M) (c : M.tm.Cfg) (j : ℕ) : size (K.rep ((stay M)^[j] c)) ≤ size (K.rep c) + K.a * j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    have := K.size_step ((stay M)^[j] c)
    rw [Nat.mul_succ]
    omega

/-- If M puts out y on `pre x` within t steps, then the simulation ends on x with `post y` within t
steps, and all its states have size at most a·(|pre x| + 1) + a·t, where a is the constant of the
coding. -/
theorem sim_runs (K : Coding M) (pre post : List Bool → List Bool) {x y : List Bool} {t : ℕ} (h : Outputs M (pre x) y t) :
    (sim K pre post).Runs x t (K.a * ((pre x).length + 1) + K.a * t) (post y) := by
  obtain ⟨c₀, hc₀⟩ : ∃ c₀, c₀ = initList M.tm ((pre x).map M.inputAlphabet.invFun) := ⟨_, rfl⟩
  obtain ⟨n, hnt, hev⟩ : ∃ n ≤ t, (flip bind M.tm.step)^[n] (some c₀) = some (haltList M.tm (y.map M.outputAlphabet.invFun)) := by
    obtain ⟨ev⟩ := h
    exact ⟨ev.steps, ev.steps_le_m, by rw [hc₀]; exact ev.evals_in_steps⟩
  have hn : (stay M)^[n] c₀ = haltList M.tm (y.map M.outputAlphabet.invFun) := stay_of_evals M n hev
  have h0 : size (K.rep c₀) ≤ K.a * ((pre x).length + 1) := by
    rw [hc₀, ← K.init_rep]
    exact K.size_init _
  have hle : K.a * n ≤ K.a * t := Nat.mul_le_mul_left _ hnt
  have hsize : ∀ j, size (K.rep ((stay M)^[j] c₀)) ≤ K.a * ((pre x).length + 1) + K.a * t := fun j => by
    rcases Nat.le_total j n with hj | hj
    · have h1 := size_rep_iterate_le K c₀ j
      have h2 : K.a * j ≤ K.a * n := Nat.mul_le_mul_left _ hj
      omega
    · have h1 := size_rep_iterate_le K c₀ n
      rw [show j = (j - n) + n from (Nat.sub_add_cancel hj).symm, Function.iterate_add_apply, hn, iterate_stay_of_halted M rfl, ← hn]
      omega
  refine (Stepped.runs_of_run (t := n) ?_ fun j => ?_).mono hnt le_rfl
  · rw [run_sim, ← hc₀, hn]
    change (K.out _).map post = _
    rw [K.out_halted _ rfl, haltList_stk_self, List.map_map]
    have e : (M.outputAlphabet ∘ M.outputAlphabet.invFun) = id := funext fun b => M.outputAlphabet.right_inv b
    rw [e, List.map_id, Option.map_some]
  · rw [run_sim, ← hc₀]
    exact hsize j

/-- A bound on the number of steps may be made larger. -/
theorem Outputs.mono {N : TM2ComputableAux Bool Bool} {x y : List Bool} {t t' : ℕ} (h : Outputs N x y t) (ht : t ≤ t') : Outputs N x y t' := by
  obtain ⟨ev⟩ := h
  exact ⟨⟨ev.toEvalsTo, ev.steps_le_m.trans ht⟩⟩

/-- The numbers: for all q₀, a, c there is a q such that q₀·(t + 1)·(n + (a·(p + 1) + a·t) + 1)^q₀ ≤
q·(t + n + 1)^q whenever p ≤ c·(3n + 3)^c. (3n + 3 bounds the length of the word that stands for a
bit string of length n, plus 1; `pre` is polynomial in that length.) -/
theorem exists_bound (q₀ a c : ℕ) : ∃ q : ℕ, ∀ t n p : ℕ, p ≤ c * (3 * n + 2 + 1) ^ c →
    q₀ * (t + 1) * (n + (a * (p + 1) + a * t) + 1) ^ q₀ ≤ q * (t + n + 1) ^ q := by
  have pP : PB fun m => c * (3 * m + 2 + 1) ^ c := (PB.mono_bound c).1.comp (((PB.const 3).mul PB.id').add (PB.const 2))
  have pG : PB fun m => q₀ * (m + 1) * (m + (a * (c * (3 * m + 2 + 1) ^ c + 1) + a * m) + 1) ^ q₀ :=
    ((PB.const q₀).mul (PB.id'.add (PB.const 1))).mul
      (((PB.id'.add (((PB.const a).mul (pP.add (PB.const 1))).add ((PB.const a).mul PB.id'))).add (PB.const 1)).pow q₀)
  obtain ⟨q, hq⟩ := pG
  refine ⟨q, fun t n p hp => le_trans ?_ (hq (t + n))⟩
  have h1 : c * (3 * n + 2 + 1) ^ c ≤ c * (3 * (t + n) + 2 + 1) ^ c :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) c)
  have h2 : a * (p + 1) ≤ a * (c * (3 * (t + n) + 2 + 1) ^ c + 1) := Nat.mul_le_mul_left _ (by omega)
  have h3 : a * t ≤ a * (t + n) := Nat.mul_le_mul_left _ (by omega)
  exact Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (Nat.pow_le_pow_left (by omega) q₀)

/-- The composition lemma, from a coding: if the configurations of M have a coding, then for all
polynomial-time `pre`, `post` there are a machine N with finite alphabets and a number q such that,
whenever M puts out y on `pre x` within t steps, N puts out
`post y` on x within q·(t + |x| + 1)^q steps. -/
theorem wraps_of_coding {M : TM2ComputableAux Bool Bool} (K : Coding M) {pre post : List Bool → List Bool} (hpre : PolyT pre) (hpost : PolyT post) :
    ∃ (N : TM2ComputableAux Bool Bool) (q : ℕ), (∀ i, Finite (N.tm.Γ i)) ∧ Wraps M pre post N q := by
  have := sim_isPolyT K hpre hpost
  obtain ⟨N, q₀, hfin, hN⟩ := CountKSat.exists_tmW (sim K pre post)
  obtain ⟨-, c, -, hc⟩ := hpre
  obtain ⟨q, hq⟩ := exists_bound q₀ K.a c
  refine ⟨N, q, hfin, fun x y t h => ?_⟩
  have hp : (pre x).length ≤ c * (3 * x.length + 2 + 1) ^ c := by
    have := hc x
    rw [len_bools x] at this
    exact (length_le_len _).trans this
  exact Outputs.mono (hN x t _ (post y) (sim_runs K pre post h)) (hq t x.length _ hp)

/-- If every machine with finite alphabets has a coding of its configurations, then every such
machine can be given a polynomial-time front end and a polynomial-time last step. -/
theorem everyMachineCanBeWrapped_of (h : ∀ M : TM2ComputableAux Bool Bool, (∀ i, Finite (M.tm.Γ i)) → Nonempty (Coding M)) : EveryMachineCanBeWrapped :=
  fun M hM _ _ hpre hpost => (h M hM).elim fun K => wraps_of_coding K hpre hpost

end Wrap
