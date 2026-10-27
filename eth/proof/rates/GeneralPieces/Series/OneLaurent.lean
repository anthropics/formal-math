/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import GeneralPieces.Series.Expansion

/-! # A step in the proof of Lemma 9 (Appendix B), paragraph "One Laurent polynomial"

From an expansion f± = Σ_c Γ_c·ε±^{N_c}·n_c alone: (ω₁ − ω₂)^H·f₊ and (ω₁ − ω₂)^H·f₋ are the same
element F = Σ_c Γ_c·(ω₁ − ω₂)^{H − N_c}·n_c of 𝓛 (`dW_pow_mul_fP`, `dW_pow_mul_fM`), and
F(1,1) = G·[π = σ] (`ev_F`), where G is the sum of the Γ_c with N_c = H. Only (ω₁ − ω₂)·ε± = 1 is
used. -/

@[expose] public section

namespace GeneralPieces.Series

open ClauseBound.Boson

variable {a b : List ℕ} {G : ℚ} {π σ : Multiset ℕ}

/-- F = Σ_c Γ_c·(ω₁ − ω₂)^{H − N_c}·n_c, an element of 𝓛. -/
noncomputable def Expansion.F (X : Expansion a b G π σ) : L := (X.terms.map fun c => c.1 • (dW ^ (a.sum + b.sum - c.2.1) * c.2.2)).sum

/-- One term: if d·e = 1 and N ≤ H then d^H·(Γ·(e^N·n)) = Γ·(d^{H−N}·n). -/
theorem pow_mul_term {A : Type} [CommRing A] [Algebra ℚ A] {d e : A} (h : d * e = 1) {N H : ℕ} (hN : N ≤ H) (r : ℚ) (n : A) :
    d ^ H * (r • (e ^ N * n)) = r • (d ^ (H - N) * n) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hN
  rw [Nat.add_sub_cancel_left, mul_smul_comm, pow_add, show d ^ N * d ^ k * (e ^ N * n) = (d * e) ^ N * (d ^ k * n) by rw [mul_pow]; ring, h, one_pow, one_mul]

/-- The same for a sum of terms and a homomorphism φ from 𝓛. -/
theorem pow_mul_terms (φ : L →ₐ[ℚ] S) {e : S} (h : φ dW * e = 1) (H : ℕ) (l : List (ℚ × ℕ × L)) (hl : ∀ c ∈ l, c.2.1 ≤ H) :
    φ dW ^ H * (l.map fun c => c.1 • (e ^ c.2.1 * φ c.2.2)).sum = φ (l.map fun c => c.1 • (dW ^ (H - c.2.1) * c.2.2)).sum := by
  induction l with
  | nil => simp
  | cons c l ih =>
    rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons, mul_add, ih fun c' hc' => hl c' (List.mem_cons_of_mem _ hc'), map_add,
      pow_mul_term h (hl c List.mem_cons_self), map_smul, map_mul, map_pow]

/-- (ω₁ − ω₂)^H·f₊ = F in 𝓛₊. -/
theorem Expansion.dW_pow_mul_fP (X : Expansion a b G π σ) : toP dW ^ (a.sum + b.sum) * fP a b π σ = toP X.F := by
  rw [X.plus, Expansion.F]
  exact pow_mul_terms toP dW_mul_epsP _ _ X.le

/-- (ω₁ − ω₂)^H·f₋ = F in 𝓛₋. -/
theorem Expansion.dW_pow_mul_fM (X : Expansion a b G π σ) : toM dW ^ (a.sum + b.sum) * fM a b π σ = toM X.F := by
  rw [X.minus, Expansion.F]
  exact pow_mul_terms toM dW_mul_epsM _ _ X.le

/-- F ↦ F(1,1): the homomorphism 𝓛 → ℚ that maps ω₁ and ω₂ to 1. -/
noncomputable def ev : L →ₐ[ℚ] ℚ := AddMonoidAlgebra.lift ℚ ℚ (ℤ × ℤ) 1

theorem ev_W (x y : ℤ) : ev (W x y) = 1 := by
  rw [ev, W, AddMonoidAlgebra.lift_single]
  simp

theorem ev_dW : ev dW = 0 := by rw [dW, map_sub, ev_W, ev_W, sub_self]

/-- At ω₁ = ω₂ = 1 only the terms with N_c = H remain. -/
theorem ev_terms (H : ℕ) (v : L) (l : List (ℚ × ℕ × L)) (hl : ∀ c ∈ l, c.2.1 ≤ H) (ht : ∀ c ∈ l, c.2.1 = H → c.2.2 = v) :
    ev (l.map fun c => c.1 • (dW ^ (H - c.2.1) * c.2.2)).sum = ((l.filter fun c => c.2.1 = H).map fun c => c.1).sum * ev v := by
  induction l with
  | nil => simp
  | cons c l ih =>
    rw [List.map_cons, List.sum_cons, map_add, ih (fun c' hc' => hl c' (List.mem_cons_of_mem _ hc')) (fun c' hc' => ht c' (List.mem_cons_of_mem _ hc')),
      map_smul, map_mul, map_pow, ev_dW]
    by_cases h : c.2.1 = H
    · rw [List.filter_cons_of_pos (by simpa using h), List.map_cons, List.sum_cons, ht c List.mem_cons_self h, h, Nat.sub_self, pow_zero, one_mul, smul_eq_mul, add_mul]
    · have h2 := hl c List.mem_cons_self
      rw [List.filter_cons_of_neg (by simpa using h), zero_pow (by omega), zero_mul, smul_zero, zero_add]

/-- F(1,1) = G·[π = σ]. -/
theorem Expansion.ev_F (X : Expansion a b G π σ) : ev X.F = if π = σ then G else 0 := by
  rw [Expansion.F, ev_terms _ _ _ X.le X.top, X.tot]
  split_ifs <;> simp

end GeneralPieces.Series
