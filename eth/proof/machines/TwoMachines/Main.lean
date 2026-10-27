/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import TwoMachines.Defs
import Wrap.CodingExists
import CircuitLowerBound.Tab.Sound
import CountKSat.Host
import ToTuring.Poly.Comb
import ToTuring.Closure.Basic
import ToTuring.Closure.Cases
import ToTuring.Lib.List1b

/-! # Two machines in alternation, and a choice between two machines: the proofs

`alt_runs`: let h be the first time at which one of the two machines has halted; up to h the
alternation advances both, at h it has a result, and h is at most the smaller of the two numbers of
steps.
`alt_isPolyT`: its three parts are polynomial-time. `CountKSat.exists_tmW` carries the computation
out; `exists_bound₂` does the arithmetic. The choice is `Stepped.ite` of two simulations `Wrap.sim`;
its runs come from `Stepped.branch_runs_inl` and `Stepped.branch_runs_inr`, its polynomial time from
`IsPolyT.ite`. -/

public section

namespace TwoMachines

open Turing Groundwork Wrap CircuitLowerBound.Tab

variable {M₁ M₂ : TM2ComputableAux Bool Bool}

/-! ### The alternation -/

/-- As long as neither machine has halted the alternation has no result. -/
theorem alt_out_running (K₁ : Coding M₁) (K₂ : Coding M₂) (pre₁ pre₂ post₁ post₂ : List Bool → List Bool) {c₁ : M₁.tm.Cfg} {c₂ : M₂.tm.Cfg} (h₁ : c₁.l ≠ none) (h₂ : c₂.l ≠ none) :
    (alt K₁ K₂ pre₁ pre₂ post₁ post₂).out (K₁.rep c₁, K₂.rep c₂) = none := by
  simp only [alt, K₁.out_running c₁ h₁, K₂.out_running c₂ h₂, Option.map_none]

/-- One step of the alternation advances both configurations. -/
theorem alt_step_rep (K₁ : Coding M₁) (K₂ : Coding M₂) (pre₁ pre₂ post₁ post₂ : List Bool → List Bool) (c₁ : M₁.tm.Cfg) (c₂ : M₂.tm.Cfg) :
    (alt K₁ K₂ pre₁ pre₂ post₁ post₂).step (K₁.rep c₁, K₂.rep c₂) = (K₁.rep (stay M₁ c₁), K₂.rep (stay M₂ c₂)) := by
  simp only [alt, K₁.step_rep, K₂.step_rep]

/-- The alternation starts with the pair of the start configurations. -/
theorem alt_init (K₁ : Coding M₁) (K₂ : Coding M₂) (pre₁ pre₂ post₁ post₂ : List Bool → List Bool) (x : List Bool) :
    (alt K₁ K₂ pre₁ pre₂ post₁ post₂).init x = (K₁.rep (start M₁ (pre₁ x)), K₂.rep (start M₂ (pre₂ x))) := by
  simp only [alt, start, K₁.init_rep, K₂.init_rep]

/-- A run of M on x with output y within t steps: after some n ≤ t steps of the step that stays, M
is in the halted configuration with y on its output stack. -/
theorem exists_halt {M : TM2ComputableAux Bool Bool} {x y : List Bool} {t : ℕ} (h : Outputs M x y t) :
    ∃ n ≤ t, (stay M)^[n] (start M x) = haltList M.tm (y.map M.outputAlphabet.invFun) := by
  obtain ⟨ev⟩ := h
  exact ⟨ev.steps, ev.steps_le_m, stay_of_evals M ev.steps ev.evals_in_steps⟩

/-- If M is halted after i steps and reaches the halted configuration c after n steps, it is in c
after i steps already. -/
theorem eq_of_halted {M : TM2ComputableAux Bool Bool} {c₀ c : M.tm.Cfg} {i n : ℕ} (hi : ((stay M)^[i] c₀).l = none) (hin : i ≤ n) (hn : (stay M)^[n] c₀ = c) : (stay M)^[i] c₀ = c := by
  rw [← hn, show n = (n - i) + i from (Nat.sub_add_cancel hin).symm, Function.iterate_add_apply, iterate_stay_of_halted M hi]

/-- What a coding reads from the halted configuration with y on the output stack. -/
theorem out_haltList {M : TM2ComputableAux Bool Bool} (K : Coding M) (y : List Bool) : K.out (K.rep (haltList M.tm (y.map M.outputAlphabet.invFun))) = some y := by
  rw [K.out_halted _ rfl, haltList_stk_self, List.map_map]
  have e : (M.outputAlphabet ∘ M.outputAlphabet.invFun) = id := funext fun b => M.outputAlphabet.right_inv b
  rw [e, List.map_id]

/-- The size of the value for the configuration after i steps. -/
theorem size_rep_le {M : TM2ComputableAux Bool Bool} (K : Coding M) (x : List Bool) {i t : ℕ} (hi : i ≤ t) : size (K.rep ((stay M)^[i] (start M x))) ≤ K.a * (x.length + 1) + K.a * t := by
  have h1 := size_rep_iterate_le K (start M x) i
  have h0 : size (K.rep (start M x)) ≤ K.a * (x.length + 1) := by
    rw [start, ← K.init_rep]
    exact K.size_init _
  have h2 : K.a * i ≤ K.a * t := Nat.mul_le_mul_left _ hi
  omega

/-- If M₁ puts out y₁ on `pre₁ x` within t₁ steps, M₂ puts out y₂ on `pre₂ x` within t₂ steps and
the two results agree, the alternation ends on x with that result within min(t₁, t₂) steps, on
states of size linear in |pre₁ x| + |pre₂ x| + min(t₁, t₂). -/
theorem alt_runs (K₁ : Coding M₁) (K₂ : Coding M₂) (pre₁ pre₂ post₁ post₂ : List Bool → List Bool) {x y₁ y₂ : List Bool} {t₁ t₂ : ℕ}
    (h₁ : Outputs M₁ (pre₁ x) y₁ t₁) (h₂ : Outputs M₂ (pre₂ x) y₂ t₂) (he : post₁ y₁ = post₂ y₂) :
    (alt K₁ K₂ pre₁ pre₂ post₁ post₂).Runs x (min t₁ t₂)
      (K₁.a * ((pre₁ x).length + 1) + K₁.a * min t₁ t₂ + (K₂.a * ((pre₂ x).length + 1) + K₂.a * min t₁ t₂)) (post₁ y₁) := by
  classical
  obtain ⟨n₁, hn₁, e₁⟩ := exists_halt h₁
  obtain ⟨n₂, hn₂, e₂⟩ := exists_halt h₂
  obtain ⟨c₁, hc₁⟩ : ∃ c, c = start M₁ (pre₁ x) := ⟨_, rfl⟩
  obtain ⟨c₂, hc₂⟩ : ∃ c, c = start M₂ (pre₂ x) := ⟨_, rfl⟩
  rw [← hc₁] at e₁
  rw [← hc₂] at e₂
  have hex : ∃ j, ((stay M₁)^[j] c₁).l = none ∨ ((stay M₂)^[j] c₂).l = none := ⟨n₁, Or.inl (by rw [e₁]; rfl)⟩
  obtain ⟨h, hh⟩ : ∃ h, h = Nat.find hex := ⟨_, rfl⟩
  have hspec : ((stay M₁)^[h] c₁).l = none ∨ ((stay M₂)^[h] c₂).l = none := hh ▸ Nat.find_spec hex
  have hmin : ∀ i < h, ((stay M₁)^[i] c₁).l ≠ none ∧ ((stay M₂)^[i] c₂).l ≠ none := fun i hi => by
    have := Nat.find_min hex (hh ▸ hi)
    exact not_or.1 this
  have hh₁ : h ≤ n₁ := hh ▸ Nat.find_min' hex (Or.inl (by rw [e₁]; rfl))
  have hh₂ : h ≤ n₂ := hh ▸ Nat.find_min' hex (Or.inr (by rw [e₂]; rfl))
  have hht : h ≤ min t₁ t₂ := le_min (hh₁.trans hn₁) (hh₂.trans hn₂)
  obtain ⟨S, hS⟩ : ∃ S, S = K₁.a * ((pre₁ x).length + 1) + K₁.a * min t₁ t₂ + (K₂.a * ((pre₂ x).length + 1) + K₂.a * min t₁ t₂) := ⟨_, rfl⟩
  rw [← hS]
  have hsize : ∀ i ≤ h, size ((K₁.rep ((stay M₁)^[i] c₁), K₂.rep ((stay M₂)^[i] c₂)) : Rep × Rep) ≤ S := fun i hi => by
    have a₁ := size_rep_le K₁ (pre₁ x) (hi.trans hht)
    have a₂ := size_rep_le K₂ (pre₂ x) (hi.trans hht)
    rw [← hc₁] at a₁
    rw [← hc₂] at a₂
    rw [hS]
    exact Nat.add_le_add a₁ a₂
  have hout : (alt K₁ K₂ pre₁ pre₂ post₁ post₂).out (K₁.rep ((stay M₁)^[h] c₁), K₂.rep ((stay M₂)^[h] c₂)) = some (post₁ y₁) := by
    by_cases g₁ : ((stay M₁)^[h] c₁).l = none
    · rw [eq_of_halted g₁ hh₁ e₁]
      simp only [alt, out_haltList]
    · have g₂ : ((stay M₂)^[h] c₂).l = none := hspec.resolve_left g₁
      rw [eq_of_halted g₂ hh₂ e₂]
      simp only [alt, K₁.out_running _ g₁, out_haltList, Option.map_some, he]
  have key : ∀ d i, i + d = h → (alt K₁ K₂ pre₁ pre₂ post₁ post₂).Reaches S (post₁ y₁) (K₁.rep ((stay M₁)^[i] c₁), K₂.rep ((stay M₂)^[i] c₂)) d := by
    intro d
    induction d with
    | zero =>
      intro i hi
      have : i = h := by omega
      subst this
      exact .halt hout (hsize _ le_rfl)
    | succ d ih =>
      intro i hi
      obtain ⟨g₁, g₂⟩ := hmin i (by omega)
      refine .step (alt_out_running K₁ K₂ pre₁ pre₂ post₁ post₂ g₁ g₂) (hsize i (by omega)) ?_
      rw [alt_step_rep, ← Function.iterate_succ_apply' (stay M₁), ← Function.iterate_succ_apply' (stay M₂)]
      exact ih (i + 1) (by omega)
  have hr : (alt K₁ K₂ pre₁ pre₂ post₁ post₂).Runs x h S (post₁ y₁) := by
    unfold Stepped.Runs
    rw [alt_init, ← hc₁, ← hc₂]
    exact key h 0 (by omega)
  exact hr.mono hht le_rfl

/-- The three parts of the alternation are polynomial-time if the four functions are. -/
@[instance_reducible, expose] def alt_isPolyT (K₁ : Coding M₁) (K₂ : Coding M₂) {pre₁ pre₂ post₁ post₂ : List Bool → List Bool} (hpre₁ : PolyT pre₁) (hpre₂ : PolyT pre₂) (hpost₁ : PolyT post₁) (hpost₂ : PolyT post₂) :
    IsPolyT (alt K₁ K₂ pre₁ pre₂ post₁ post₂) where
  enc := (inferInstance : Enc (Rep × Rep))
  carried := (inferInstance : Carried (Rep × Rep))
  init := by
    have a := K₁.init_poly
    have b := K₂.init_poly
    change PolyT fun x => (K₁.init (pre₁ x), K₂.init (pre₂ x))
    fun_prop
  step := by
    have a := K₁.step_poly
    have b := K₂.step_poly
    change PolyT fun r : Rep × Rep => (K₁.step r.1, K₂.step r.2)
    fun_prop
  out := by
    have a := K₁.out_poly
    have b := K₂.out_poly
    have h : PolyT fun r : Rep × Rep => (K₁.out r.1).elim ((K₂.out r.2).map post₂) fun y => some (post₁ y) := by fun_prop
    refine h.congr fun r => ?_
    change _ = (match K₁.out r.1 with | some y => some (post₁ y) | none => (K₂.out r.2).map post₂)
    cases K₁.out r.1 <;> rfl

/-- The numbers: for all q₀, a₁, a₂, c₁, c₂ there is a q such that q₀·(t + 1)·(n + ((a₁·(p₁ + 1) +
a₁·t) + (a₂·(p₂ + 1) + a₂·t)) + 1)^q₀ ≤ q·(t + n + 1)^q whenever p₁ ≤ c₁·(3n + 3)^c₁ and p₂ ≤ c₂·(3n + 3)^c₂. -/
theorem exists_bound₂ (q₀ a₁ a₂ c₁ c₂ : ℕ) : ∃ q : ℕ, ∀ t n p₁ p₂ : ℕ, p₁ ≤ c₁ * (3 * n + 2 + 1) ^ c₁ → p₂ ≤ c₂ * (3 * n + 2 + 1) ^ c₂ →
    q₀ * (t + 1) * (n + (a₁ * (p₁ + 1) + a₁ * t + (a₂ * (p₂ + 1) + a₂ * t)) + 1) ^ q₀ ≤ q * (t + n + 1) ^ q := by
  have pP : ∀ c : ℕ, PB fun m => c * (3 * m + 2 + 1) ^ c := fun c => (PB.mono_bound c).1.comp (((PB.const 3).mul PB.id').add (PB.const 2))
  have pG : PB fun m => q₀ * (m + 1) * (m + (a₁ * (c₁ * (3 * m + 2 + 1) ^ c₁ + 1) + a₁ * m + (a₂ * (c₂ * (3 * m + 2 + 1) ^ c₂ + 1) + a₂ * m)) + 1) ^ q₀ :=
    ((PB.const q₀).mul (PB.id'.add (PB.const 1))).mul
      (((PB.id'.add ((((PB.const a₁).mul ((pP c₁).add (PB.const 1))).add ((PB.const a₁).mul PB.id')).add
        (((PB.const a₂).mul ((pP c₂).add (PB.const 1))).add ((PB.const a₂).mul PB.id')))).add (PB.const 1)).pow q₀)
  obtain ⟨q, hq⟩ := pG
  refine ⟨q, fun t n p₁ p₂ hp₁ hp₂ => le_trans ?_ (hq (t + n))⟩
  have m₁ : c₁ * (3 * n + 2 + 1) ^ c₁ ≤ c₁ * (3 * (t + n) + 2 + 1) ^ c₁ := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) c₁)
  have m₂ : c₂ * (3 * n + 2 + 1) ^ c₂ ≤ c₂ * (3 * (t + n) + 2 + 1) ^ c₂ := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) c₂)
  have u₁ : a₁ * (p₁ + 1) ≤ a₁ * (c₁ * (3 * (t + n) + 2 + 1) ^ c₁ + 1) := Nat.mul_le_mul_left _ (by omega)
  have u₂ : a₂ * (p₂ + 1) ≤ a₂ * (c₂ * (3 * (t + n) + 2 + 1) ^ c₂ + 1) := Nat.mul_le_mul_left _ (by omega)
  have v₁ : a₁ * t ≤ a₁ * (t + n) := Nat.mul_le_mul_left _ (by omega)
  have v₂ : a₂ * t ≤ a₂ * (t + n) := Nat.mul_le_mul_left _ (by omega)
  exact Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (Nat.pow_le_pow_left (by omega) q₀)

/-- The length of the value of a polynomial-time function on bit strings. -/
theorem exists_length_le {pre : List Bool → List Bool} (hpre : PolyT pre) : ∃ c : ℕ, ∀ x : List Bool, (pre x).length ≤ c * (3 * x.length + 2 + 1) ^ c := by
  obtain ⟨-, c, -, hc⟩ := hpre
  refine ⟨c, fun x => ?_⟩
  have := hc x
  rw [len_bools x] at this
  exact (length_le_len _).trans this

/-- Any two machines with finite alphabets can be run in alternation. -/
theorem everyTwoMachinesCanBeAlternated : EveryTwoMachinesCanBeAlternated := by
  intro M₁ M₂ hf₁ hf₂ pre₁ pre₂ post₁ post₂ hpre₁ hpre₂ hpost₁ hpost₂
  obtain ⟨K₁⟩ := coding_exists M₁ hf₁
  obtain ⟨K₂⟩ := coding_exists M₂ hf₂
  have := alt_isPolyT K₁ K₂ hpre₁ hpre₂ hpost₁ hpost₂
  obtain ⟨N, q₀, hfin, hN⟩ := CountKSat.exists_tmW (alt K₁ K₂ pre₁ pre₂ post₁ post₂)
  obtain ⟨c₁, hc₁⟩ := exists_length_le hpre₁
  obtain ⟨c₂, hc₂⟩ := exists_length_le hpre₂
  obtain ⟨q, hq⟩ := exists_bound₂ q₀ K₁.a K₂.a c₁ c₂
  exact ⟨K₁, K₂, N, q₀, q, hfin, hN, fun x y₁ y₂ t₁ t₂ h₁ h₂ he =>
    Outputs.mono (hN x _ _ _ (alt_runs K₁ K₂ pre₁ pre₂ post₁ post₂ h₁ h₂ he)) (hq (min t₁ t₂) x.length _ _ (hc₁ x) (hc₂ x))⟩

/-! ### The choice -/

/-- A polynomial-time test on the input can choose between any two machines with finite alphabets. -/
theorem everyTwoMachinesCanBeChosenBetween : EveryTwoMachinesCanBeChosenBetween := by
  intro M₁ M₂ hf₁ hf₂ test pre₁ pre₂ post₁ post₂ htest hpre₁ hpre₂ hpost₁ hpost₂
  obtain ⟨K₁⟩ := coding_exists M₁ hf₁
  obtain ⟨K₂⟩ := coding_exists M₂ hf₂
  have i₁ := sim_isPolyT K₁ hpre₁ hpost₁
  have i₂ := sim_isPolyT K₂ hpre₂ hpost₂
  have : IsPolyT (choose K₁ K₂ test pre₁ pre₂ post₁ post₂) := IsPolyT.ite htest
  obtain ⟨N, q₀, hfin, hN⟩ := CountKSat.exists_tmW (choose K₁ K₂ test pre₁ pre₂ post₁ post₂)
  obtain ⟨c₁, hc₁⟩ := exists_length_le hpre₁
  obtain ⟨c₂, hc₂⟩ := exists_length_le hpre₂
  obtain ⟨q₁, hq₁⟩ := exists_bound₂ q₀ K₁.a 1 c₁ 0
  obtain ⟨q₂, hq₂⟩ := exists_bound₂ q₀ K₂.a 1 c₂ 0
  refine ⟨K₁, K₂, N, q₀, max q₁ q₂, hfin, hN, fun x y t => ⟨fun ht h => ?_, fun ht h => ?_⟩⟩
  · have hr : (choose K₁ K₂ test pre₁ pre₂ post₁ post₂).Runs x t (K₁.a * ((pre₁ x).length + 1) + K₁.a * t + 1) (post₁ y) :=
      Stepped.branch_runs_inl (by simp [Stepped.iteSel, ht]) (sim_runs K₁ pre₁ post₁ h)
    refine Outputs.mono (hN x _ _ _ hr) (le_trans ?_ ((hq₁ t x.length _ 0 (hc₁ x) (Nat.zero_le _)).trans ?_))
    · exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) q₀)
    · exact Nat.mul_le_mul (le_max_left _ _) (Nat.pow_le_pow_right (by omega) (le_max_left _ _))
  · have hr : (choose K₁ K₂ test pre₁ pre₂ post₁ post₂).Runs x t (K₂.a * ((pre₂ x).length + 1) + K₂.a * t + 1) (post₂ y) :=
      Stepped.branch_runs_inr (by simp [Stepped.iteSel, ht]) (sim_runs K₂ pre₂ post₂ h)
    refine Outputs.mono (hN x _ _ _ hr) (le_trans ?_ ((hq₂ t x.length _ 0 (hc₂ x) (Nat.zero_le _)).trans ?_))
    · exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) q₀)
    · exact Nat.mul_le_mul (le_max_right _ _) (Nat.pow_le_pow_right (by omega) (le_max_right _ _))

end TwoMachines
