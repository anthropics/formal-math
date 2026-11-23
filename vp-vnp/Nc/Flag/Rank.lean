/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Flag.Blow

/-!
# The growth function and what a contracting length gives along a homomorphism from matrices
-/

open Finset Matrix

namespace Nc.Flag

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {G : Type*} [Group G]

/-- The growth allowed by the contraction. -/
noncomputable def grow (m : ℕ) (s : ℝ) (r : ℕ) : ℝ :=
  m * (Nat.log m r + 1) * s ^ Nat.log m r

theorem grow_nonneg (m : ℕ) {s : ℝ} (hs : 1 ≤ s) (r : ℕ) : 0 ≤ grow m s r := by
  unfold grow
  positivity

theorem grow_mono (m : ℕ) {s : ℝ} (hs : 1 ≤ s) {r r' : ℕ} (h : r ≤ r') :
    grow m s r ≤ grow m s r' := by
  unfold grow
  have hl : Nat.log m r ≤ Nat.log m r' := Nat.log_mono_right h
  have hl' : (Nat.log m r : ℝ) ≤ Nat.log m r' := by exact_mod_cast hl
  have hp : s ^ Nat.log m r ≤ s ^ Nat.log m r' := pow_le_pow_right₀ hs hl
  have : 0 ≤ s ^ Nat.log m r := by positivity
  gcongr

/-- Facts about `f = l ∘ τ`. -/
structure Good (f : Matrix ι ι F2 → ℝ) (m : ℕ) (s : ℝ) : Prop where
  nonneg : ∀ M, 0 ≤ f M
  zero : f 0 = 0
  add : ∀ M N, f (M + N) ≤ f M + f N
  digit : ∀ (q : ℕ) (e : Fin m × Fin q ↪ ι) (i : Fin m),
    DM f (dg ((univ : Finset (Fin m × Fin q)).map e)) ≤
      s ^ 2 * DM f (dg ((({i} : Finset (Fin m)) ×ˢ univ).map e))

theorem good_of_contr (l : Len G) {m : ℕ} {s : ℝ} (hC : Contr l m s)
    (τ : Matrix ι ι F2 → G) (hτ : ∀ M N, τ (M + N) = τ M * τ N) :
    Good (fun M => l.val (τ M)) m s where
  nonneg _ := l.nonneg _
  zero := by
    have h := hτ 0 0
    rw [add_zero] at h
    have : τ 0 = 1 := by simpa using h
    simp only [this, l.one']
  add M N := by
    simp only [hτ]
    exact l.mul' _ _
  digit _ e i := DM_digit l hC τ hτ e i

variable {f : Matrix ι ι F2 → ℝ} {m : ℕ} {s : ℝ}

theorem Good.dg_zero (h : Good f m s) : DM f (dg (∅ : Finset ι)) = 0 := by
  simp [DM, dg_empty, h.zero]

end Nc.Flag
