/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Eight.Cor.NSETH
public import Eight.ViaGrouping.CorDefs2
import GraphProblems.Host
import Mathlib.Tactic

/-! # Section 7, the sentence after Corollary 5: NSETH is false, from a machine for k-SAT that is a parameter

The paper: NSETH «is false as well: a k-DNF is a tautology exactly if its negation, a k-CNF, is
unsatisfiable, and a deterministic algorithm is in particular a nondeterministic one». The
definitions are in proof/networks/Eight/Cor/NSETHDefs.lean; the first half of the
sentence is `Eight.tautology_iff` (proof/networks/Eight/Cor/NSETH.lean), which does not use any
algorithm and is not repeated. The second half is proved here for a machine M for k-SAT, cut into
steps, that is a parameter (definitions in proof/networks/Eight/ViaGrouping/CorDefs2.lean):
* `Decides M k δ c`: M decides k-SAT on n variables within c·2^{δn} steps, on states of polynomial
  size;
* `verifier M`: take the witness off the input and ignore it, run M on the rest, answer with the
  opposite bit;
* `verifier_recognizes`, `tautInNTimeTM_of`, `not_NSETH_TM_of`. The lines are those of
  proof/networks/Eight/Cor/NSETH.lean with M in the place of the machine named there.
The proofs in this file name no algorithm for cliques or for networks.

Different from the paper: the negation of a k-DNF ψ is the k-CNF with the same lists and all
literals negated. That formula is satisfiable exactly if the k-CNF with the same lists and the same
literals is (negate the assignment), so the
machine runs on the code of ψ as it stands. -/

public section

namespace Eight.ViaGrouping

open Groundwork Groundwork.Prog Paper Turing

/-- The verifier has polynomial-time steps if M has. -/
theorem verifier_polyTimeSteps {M : StepMachine (List Bool) Bool} (hp : PolyTimeSteps M) : PolyTimeSteps (verifier M) := by
  obtain ⟨hI⟩ := hp
  have := IsPolyT.mapIn (M := M) stripW_polyT
  exact ⟨IsPolyT.mapOut (M := Stepped.mapIn stripW M) (f := fun b => [!b]) (by fun_prop)⟩

/-- **The verifier.** If M decides k-SAT with the exponent δ and the constant c, then `verifier M`,
on every witness w and the code of a k-DNF ψ on n variables, ends within c·2^{δn} steps with the bit
«ψ is a tautology». -/
theorem verifier_recognizes {M : StepMachine (List Bool) Bool} {k : ℕ} {δ : ℝ} {c : ℕ} (h : Decides M k δ c) (n : ℕ) (ψ : DNF n) (hψ : IsKDNF k ψ) (w : List Bool) :
    ∃ (T : ℕ) (b : Bool), (verifier M).Runs (withWitness w (SatK.enc k ψ)) T (c * ((SatK.enc k ψ).length + 1) ^ c) [b] ∧ (b = true ↔ Tautology ψ) ∧ (T : ℝ) ≤ c * (2 : ℝ) ^ (δ * n) := by
  obtain ⟨T, b, hr, hb, hT⟩ := h n ψ hψ
  rw [← stripW_withWitness w (SatK.enc k ψ)] at hr
  refine ⟨T, !b, ?_, ?_, hT⟩
  · have h2 := Stepped.mapOut_runs (f := fun b : Bool => [!b]) (Stepped.mapIn_runs hr)
    rwa [stripW_withWitness] at h2
  · rw [tautology_iff, ← hb]
    cases b <;> simp

open Classical in
/-- «A deterministic algorithm is in particular a nondeterministic one»: if a machine M with
polynomial-time steps decides k-SAT with the exponent δ/2, then the tautologies among the k-DNF
formulas on n variables are recognized in nondeterministic time O(2^{δn}).
The Turing machine simulates `verifier M`. If ψ is a tautology, the empty witness is accepted in
time; if some witness is accepted, the answer of the machine, which is the same on all witnesses, is
«tautology». -/
theorem tautInNTimeTM_of (k : ℕ) {δ : ℝ} (hδ : 0 < δ) {M : StepMachine (List Bool) Bool} (hp : PolyTimeSteps M) {c : ℕ} (hM : Decides M k (δ / 2) c) : TautInNTimeTM k δ := by
  obtain ⟨hI⟩ := verifier_polyTimeSteps hp
  have h := verifier_recognizes hM
  obtain ⟨a₀, ha₀⟩ : ∃ a₀, a₀ = k * 2 ^ k + 1 := ⟨_, rfl⟩
  obtain ⟨c', hc'⟩ : ∃ c', c' = c * a₀ ^ c + (k + 1) * c := ⟨_, rfl⟩
  obtain ⟨N, C, hfin, hN⟩ := GraphProblems.tm_of_stepped (verifier M) (ι := (n : ℕ) × {ψ : DNF n // IsKDNF k ψ} × List Bool)
    (fun x => withWitness x.2.2 (SatK.enc k x.2.1.1)) (fun x => [decide (Tautology x.2.1.1)]) (fun x => x.1 + x.2.2.length) hδ c' (a₀ + 2) (k + 1)
    (fun x => by
      obtain ⟨n, ⟨ψ, hψ⟩, w⟩ := x
      have hl : (SatK.enc k ψ).length + 1 ≤ a₀ * (n + 2) ^ (k + 1) := ha₀ ▸ DecodeK.length_enc_succ_le hψ
      have h1 : (n + 2) ^ (k + 1) ≤ (n + w.length + 2) ^ (k + 1) := Nat.pow_le_pow_left (by omega) _
      have h2 : n + w.length + 2 ≤ (n + w.length + 2) ^ (k + 1) := Nat.le_self_pow (by omega) _
      have h3 := Nat.mul_le_mul_left a₀ h1
      simp only [withWitness, List.length_append, List.length_replicate, List.length_cons]
      rw [add_mul]
      omega)
    (fun x => by
      obtain ⟨n, ⟨ψ, hψ⟩, w⟩ := x
      obtain ⟨T, b, hr, hb, hT⟩ := h n ψ hψ w
      have hbd : b = decide (Tautology ψ) := by
        by_cases ht : Tautology ψ
        · simp [ht, hb.2 ht]
        · cases b
          · simp [ht]
          · exact absurd (hb.1 rfl) ht
      have hl : (SatK.enc k ψ).length + 1 ≤ a₀ * (n + 2) ^ (k + 1) := ha₀ ▸ DecodeK.length_enc_succ_le hψ
      have hcc : c ≤ c' := by
        have h1 : 1 ≤ a₀ ^ c := Nat.one_le_pow _ _ (by omega)
        rw [hc']
        exact (Nat.le_mul_of_pos_right c h1).trans (Nat.le_add_right _ _)
      refine ⟨T, hbd ▸ hr.mono le_rfl ?_, hT.trans ?_⟩
      · calc c * ((SatK.enc k ψ).length + 1) ^ c ≤ c * (a₀ * (n + 2) ^ (k + 1)) ^ c := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hl c)
          _ = (c * a₀ ^ c) * (n + 2) ^ ((k + 1) * c) := by rw [mul_pow, ← pow_mul, mul_assoc]
          _ ≤ c' * (n + w.length + 2) ^ c' := by
            rw [hc']
            exact Nat.mul_le_mul (Nat.le_add_right _ _) ((Nat.pow_le_pow_left (by omega) _).trans (Nat.pow_le_pow_right (by omega) (Nat.le_add_left _ _)))
      · have h5 : (2 : ℝ) ^ (δ / 2 * n) ≤ (2 : ℝ) ^ (δ / 2 * ((n + w.length : ℕ) : ℝ)) := by
          refine Real.rpow_le_rpow_of_exponent_le one_le_two (mul_le_mul_of_nonneg_left ?_ (by positivity))
          exact_mod_cast Nat.le_add_right _ _
        have h6 : (c : ℝ) ≤ c' := by exact_mod_cast hcc
        exact mul_le_mul h6 h5 (by positivity) (by positivity))
  refine ⟨N, C, hfin, fun n ψ hψ => ⟨fun ht => ⟨[], ?_⟩, ?_⟩⟩
  · have h1 := hN ⟨n, ⟨ψ, hψ⟩, []⟩
    simpa [ht] using h1
  · rintro ⟨w, ⟨ev⟩⟩
    obtain ⟨ev'⟩ := hN ⟨n, ⟨ψ, hψ⟩, w⟩
    have h5 := CircuitLowerBound.Alg.outputs_unique ev ev'
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at h5
    have h6 := N.outputAlphabet.symm.injective h5
    exact of_decide_eq_true h6.symm

/-- **NSETH is false** (the sentence after Corollary 5), for Turing machines and nondeterministic
time in verifier form (`NSETH_TM` of proof/networks/Eight/Cor/NSETHDefs.lean), if for every k ≥ 1
and δ > 0 some machine with polynomial-time steps decides k-SAT with the exponent δ. -/
theorem not_NSETH_TM_of (hS : ∀ k : ℕ, 1 ≤ k → ∀ δ : ℝ, 0 < δ → ∃ M : StepMachine (List Bool) Bool, PolyTimeSteps M ∧ ∃ c : ℕ, Decides M k δ c) : ¬ NSETH_TM := by
  intro h
  obtain ⟨k, hk, hn⟩ := h (1 / 2) (by norm_num)
  obtain ⟨M, hp, c, hM⟩ := hS k hk ((1 - 1 / 2) / 2) (by norm_num)
  exact hn (tautInNTimeTM_of k (by norm_num) hp hM)

end Eight.ViaGrouping
