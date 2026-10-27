/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import OccurM.TiedDefs
public import VariableBound.Paper.Rename.Math
import OccurM.Prep
import OccurM.Arith
import CountKSatRate.Pad
import VariableBound.Paper.Rename.Code
import VariableBound.Paper.Rename.Cert

/-! # The top level in m after the preparation

`GeneralPieces.Tied.TopM S pick (SatM.rPow α)` is the bound in m for the named top level (`AM`,
`eM`) on formulas in which every variable occurs. `after_front` puts a front end before both
functions: a polynomial-time function that maps
the code of (k, φ), in any coding, to `SatM.enc k (ren φ)`, the code of the formula with the
variables that occur numbered. It gives what becomes the five fields of `TopOccur`:

* both functions stay polynomial-time (composition);
* correctness and the rate are those of `TopM` at `ren φ`, which has as many clauses as φ, with log
  m in place of log₂(m+2) (`shift_le`);
* the machine is the padding machine (`CountKSatRate.stPaddedW`) on the two composed functions, so
  it computes the named function on every input; its steps are bounded by `steps_le`.

`topOccurOfTop` is this for the compact code with `rencC` and for the code with N in unary with
`renc`. -/

public section

namespace OccurM

open Groundwork PaddedDescent PaddedDescent.F ClauseBound.Alg ClauseBound.Gen Turing MainTheoremForms ClausesOccur VariableBound.Rename
open Sat3 (CNF)

/-- The compact code is not empty. -/
theorem one_le_length_encC (k N : ℕ) (φ : CNF N) : 1 ≤ (encC k φ).length := by
  simp only [encC, List.length_append, List.length_cons]
  omega

/-- The code with N in unary is not empty. -/
theorem one_le_length_enc (k N : ℕ) (φ : CNF N) : 1 ≤ (SatM.enc k φ).length := by
  simp only [SatM.enc, List.length_append, List.length_cons]
  omega

variable {Idx : Type} [Enc Idx] {S : Solver Idx} {pick : U → U × Idx} {α : ℝ}

/-- The exponent of the top level at the renamed formula is at most G·km/(log m)^α, with the G of
`TopM.rate`. -/
theorem rate_ren (h0 : 0 ≤ α) {G : ℕ}
    (hG : ∀ (k n : ℕ) (φ : CNF n), 1 ≤ k → 1 ≤ φ.length → SatK.IsKCNF k φ → SatM.AllOccur φ →
      (eM S pick (SatM.enc k φ) : ℝ) ≤ G * ((k : ℝ) * φ.length * SatM.rPow α φ.length))
    {k N : ℕ} (φ : CNF N) (hk : 1 ≤ k) (hm : 2 ≤ φ.length) (hφ : SatK.IsKCNF k φ) :
    (eM S pick (SatM.enc k (ren φ)) : ℝ) ≤ G * expClauses α k φ.length := by
  have h := hG k _ (ren φ) hk (by rw [length_ren]; omega) (isKCNF_ren φ hφ) (allOccur_ren φ)
  rw [length_ren] at h
  exact h.trans (mul_le_mul_of_nonneg_left (shift_le h0 k hm) (Nat.cast_nonneg G))

/-- For any coding `code` by nonempty words and any polynomial-time `front` that maps the code of
(k, φ) to `SatM.enc k (ren φ)`: five statements, which for the compact code with `rencC` are the
five fields of `TopOccur`, and for the code with N in unary with `renc` those of
`TopOccurUnary`. -/
theorem after_front (h0 : 0 ≤ α) (h1 : α ≤ 1) (hT : GeneralPieces.Tied.TopM S pick (SatM.rPow α))
    (code : ∀ (_ : ℕ) {N : ℕ}, CNF N → List Bool) {front : List Bool → List Bool} (hfront : PolyT front)
    (hcode : ∀ (k N : ℕ) (φ : CNF N), 1 ≤ k → SatK.IsKCNF k φ → front (code k φ) = SatM.enc k (ren φ))
    (hlen : ∀ (k N : ℕ) (φ : CNF N), 1 ≤ (code k φ).length) :
    PolyT (fun p : List Bool × U => AM S pick (front p.1, p.2)) ∧ PolyT (fun x => eM S pick (front x)) ∧
    (∀ (k N : ℕ) (φ : CNF N), 1 ≤ k → 1 ≤ φ.length → SatK.IsKCNF k φ → ∀ pad : U, 2 ^ eM S pick (front (code k φ)) ≤ pad.length →
      AM S pick (front (code k φ), pad) = SatK.binary (numOcc φ) (numSatOcc φ)) ∧
    (∃ G : ℕ, ∀ (k N : ℕ) (φ : CNF N), 1 ≤ k → 2 ≤ φ.length → SatK.IsKCNF k φ → (eM S pick (front (code k φ)) : ℝ) ≤ G * expClauses α k φ.length) ∧
    ∃ (M : TM2ComputableAux Bool Bool) (q C : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧
      (∀ x : List Bool, Nonempty (TM2OutputsInTime M.tm (x.map M.inputAlphabet.invFun)
        (some ((AM S pick (front x, pad (eM S pick (front x)))).map M.outputAlphabet.invFun)) (q * (x.length + 2 ^ eM S pick (front x) + 1) ^ q))) ∧
      ∀ (k N : ℕ) (φ : CNF N), 1 ≤ k → SatK.IsKCNF k φ → 2 ≤ φ.length →
        Nonempty (TM2OutputsInTime M.tm ((code k φ).map M.inputAlphabet.invFun)
          (some ((SatK.binary (numOcc φ) (numSatOcc φ)).map M.outputAlphabet.invFun)) (timeClauses α C k φ.length + C * (code k φ).length ^ C)) := by
  have hA : PolyT (fun p : List Bool × U => AM S pick (front p.1, p.2)) := hT.poly_A.comp ((hfront.comp PolyT.id'.fst).prodMk PolyT.id'.snd)
  have he : PolyT (fun x => eM S pick (front x)) := hT.poly_e.comp hfront
  have hc : ∀ (k N : ℕ) (φ : CNF N), 1 ≤ k → 1 ≤ φ.length → SatK.IsKCNF k φ → ∀ pad : U, 2 ^ eM S pick (front (code k φ)) ≤ pad.length →
      AM S pick (front (code k φ), pad) = SatK.binary (numOcc φ) (numSatOcc φ) := by
    intro k N φ hk hm hφ pad hp
    rw [hcode k N φ hk hφ] at hp ⊢
    rw [hT.correct k _ (ren φ) hk (by rw [length_ren]; exact hm) (isKCNF_ren φ hφ) (allOccur_ren φ) pad hp, numSat_ren]
  obtain ⟨G, hG⟩ := hT.rate
  have hr : ∀ (k N : ℕ) (φ : CNF N), 1 ≤ k → 2 ≤ φ.length → SatK.IsKCNF k φ → (eM S pick (front (code k φ)) : ℝ) ≤ G * expClauses α k φ.length := by
    intro k N φ hk hm hφ
    rw [hcode k N φ hk hφ]
    exact rate_ren h0 hG φ hk hm hφ
  obtain ⟨M, q, hfin, hM⟩ := CountKSatRate.stPaddedW (fun x => eM S pick (front x)) (fun p => AM S pick (front p.1, p.2)) he hA
  refine ⟨hA, he, hc, ⟨G, hr⟩, M, q, stepsC q G, hfin, hM, fun k N φ hk hφ hm => ?_⟩
  have hx := hM (code k φ)
  simp only [hc k N φ hk (by omega) hφ (pad (eM S pick (front (code k φ)))) (by simp [pad])] at hx
  obtain ⟨ev⟩ := hx
  exact ⟨⟨ev.toEvalsTo, ev.steps_le_m.trans (steps_le q G (hr k N φ hk hm hφ) (one_le_expClauses h0 h1 hk hm) (hlen k N φ))⟩⟩

/-- From the bound in m for the named top level on formulas in which every variable occurs to the
bound for the same top level after the named preparation, for both codes. -/
theorem topOccurOfTop : TopOccurOfTopStmt := by
  intro Idx _ S pick α h0 h1 hT
  obtain ⟨a1, a2, a3, a4, a5⟩ := after_front h0 h1 hT (fun k _ φ => encC k φ) rencC_polyT (fun k N φ hk hφ => rencC_encC φ hk hφ.1) one_le_length_encC
  obtain ⟨b1, b2, b3, b4, b5⟩ := after_front h0 h1 hT (fun k _ φ => SatM.enc k φ) renc_polyT (fun k N φ hk hφ => renc_enc φ hk hφ.1) one_le_length_enc
  exact ⟨⟨a1, a2, a3, a4, a5⟩, ⟨b1, b2, b3, b4, b5⟩⟩

end OccurM
