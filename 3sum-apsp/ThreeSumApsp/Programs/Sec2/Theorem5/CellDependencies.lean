/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec2.Theorem5.Contracts

/-!
# The memory map of Theorem 5: what depends on which cells

SharedReady.dirs lists the cells of the directory that the solver reads. SharedTables are the tables
of the shared block without the directory and the encodings; they depend only on the cells between
these two (SharedTables.congr), and all that the shared stage leaves behind depends only on the
cells of the shared block, without the last of the 32 cells of the directory, which the shared stage
does not use (SharedReady.congr, SharedReady.of_agree).
-/

public section

namespace Light.Sec2

open ThreeSumApsp

/-! ## The directory -/

variable {p : Par} {hmL : p.m ≤ p.L} {aX aY b0 : ℕ}
  {X : Matrix (Fin p.N) (Fin (ThreeSumApsp.D p.m)) ℤ}
  {Y : Matrix (Fin (ThreeSumApsp.D p.m)) (Fin p.N) ℤ} {μ μ' : ℕ → ℤ}

/-- Cell j of the directory, with the address in the form in which the evaluation of mem[b0 + j]
meets it. -/
theorem SharedReady.dir_read (h : SharedReady p hmL aX aY b0 X Y μ) {j : ℕ} (hj : j < 31) :
    μ ((b0 : ℤ) + j).toNat = ((dirList p aX aY b0).getD j 0 : ℕ) := by
  rw [toNat_natCast_add_natCast]
  exact h.dir.read (by simpa [dirList] using hj)

/-- The cells of the directory that the solver reads, one equation for each. -/
theorem SharedReady.dirs (h : SharedReady p hmL aX aY b0 X Y μ) :
    μ ((b0 : ℤ) + 4).toNat = (p.Lo : ℕ) ∧ μ ((b0 : ℤ) + 7).toNat = (p.K0 : ℕ)
      ∧ μ ((b0 : ℤ) + 9).toNat = (p.nB : ℕ) ∧ μ ((b0 : ℤ) + 10).toNat = (p.T : ℕ)
      ∧ μ ((b0 : ℤ) + 17).toNat = (p.aP10 b0 : ℕ) ∧ μ ((b0 : ℤ) + 21).toNat = (p.aMASK b0 : ℕ)
      ∧ μ ((b0 : ℤ) + 22).toNat = (p.aBAND b0 : ℕ) ∧ μ ((b0 : ℤ) + 24).toNat = (p.aDIG3 b0 : ℕ)
      ∧ μ ((b0 : ℤ) + 26).toNat = (p.aENCA b0 : ℕ) ∧ μ ((b0 : ℤ) + 27).toNat = (p.aENCB b0 : ℕ)
      ∧ μ ((b0 : ℤ) + 30).toNat = (p.sharedEnd b0 : ℕ) :=
  ⟨h.dir_read (j := 4) (by omega), h.dir_read (j := 7) (by omega),
    h.dir_read (j := 9) (by omega), h.dir_read (j := 10) (by omega),
    h.dir_read (j := 17) (by omega), h.dir_read (j := 21) (by omega),
    h.dir_read (j := 22) (by omega), h.dir_read (j := 24) (by omega),
    h.dir_read (j := 26) (by omega), h.dir_read (j := 27) (by omega),
    h.dir_read (j := 30) (by omega)⟩

/-! ## Only the shared block matters -/

/-- The tables lie between the directory and the encodings: they are still there in a memory that
agrees on these cells. -/
theorem SharedTables.congr {p : Par} {b0 : ℕ} {μ μ' : ℕ → ℤ} (h : SharedTables p b0 μ)
    (he : ∀ x, p.aP3 b0 ≤ x → x < p.aENCA b0 → μ' x = μ x) : SharedTables p b0 μ' := by
  have hplaces := p.places b0
  have lp : ∀ b, (powList b (p.L + 1)).length = p.L + 1 := fun b => length_powList b _
  have lphi := Spec.length_phiFlat
  have lpsi := Spec.length_psiFlat
  refine
    { p3 := h.p3.congr fun i hi => he _ (by omega) (by rw [lp] at hi; omega)
      p4 := h.p4.congr fun i hi => he _ (by omega) (by rw [lp] at hi; omega)
      p7 := h.p7.congr fun i hi => he _ (by omega) (by rw [lp] at hi; omega)
      p10 := h.p10.congr fun i hi => he _ (by omega) (by rw [lp] at hi; omega)
      phi := h.phi.congr fun i hi => he _ (by omega) (by omega)
      psi := h.psi.congr fun i hi => he _ (by omega) (by omega)
      mask := fun s hs => (h.mask s hs).congr fun i hi => he _ (by omega) ?_
      band := fun I hI => (he _ (by omega) (by omega)).trans (h.band I hI)
      block := fun I hI => (he _ (by omega) (by omega)).trans (h.block I hI)
      dig3 := fun I hI => (h.dig3 I hI).congr fun i hi => he _ (by omega) ?_
      dig4 := fun x hx => (h.dig4 x hx).congr fun i hi => he _ (by omega) ?_ }
  · rw [List.length_map, Spec.length_unrank] at hi
    have := Nat.mul_add_lt_mul hs hi
    omega
  · have := Nat.mul_add_lt_mul hI (show i < p.Lo by simpa [ThreeSumApsp.digitList] using hi)
    omega
  · have := Nat.mul_add_lt_mul hx (show i < p.m by simpa [ThreeSumApsp.digitList] using hi)
    omega

/-- What the shared stage leaves behind is kept by a memory that agrees on the cells of the shared
block, but for cell 31 of the directory, which the shared stage does not use. -/
theorem SharedReady.congr (h : SharedReady p hmL aX aY b0 X Y μ)
    (hag : ∀ a, b0 ≤ a → a < p.sharedEnd b0 → a ≠ b0 + 31 → μ' a = μ a) :
    SharedReady p hmL aX aY b0 X Y μ' := by
  have hplaces := p.places b0
  have tb : SharedTables p b0 μ' :=
    h.toSharedTables.congr fun x hlo hx => hag x (by omega) (by omega) (by omega)
  have henc : ∀ {a β i : ℕ}, p.aENCA b0 ≤ a → a + p.nB * p.T ≤ p.sharedEnd b0 → β < p.nB →
      i < p.T → μ' (a + β * p.T + i) = μ (a + β * p.T + i) := fun ha hend hβ hi => by
    have := Nat.mul_add_lt_mul hβ hi
    exact hag _ (by omega) (by omega) (by omega)
  refine
    { tb with
      dir := h.dir.congr fun i hi => ?_
      encA := fun β hβ => (h.encA β hβ).congr fun i hi =>
        henc le_rfl (by omega) hβ (by rwa [Spec.length_arrT] at hi)
      encB := fun β hβ => (h.encB β hβ).congr fun i hi =>
        henc (by omega) (by omega) hβ (by rwa [Spec.length_arrT] at hi) }
  simp only [dirList, List.length_map, List.length_cons, List.length_nil] at hi
  simp only [Par.aDIR]
  exact hag _ (by omega) (by omega) (by omega)

/-- What the shared stage leaves behind is kept by a memory that agrees on all cells below the end
of the shared block, but for cell 31 of the directory. -/
theorem SharedReady.of_agree (h : SharedReady p hmL aX aY b0 X Y μ)
    (hag : ∀ a, a < p.sharedEnd b0 → a ≠ b0 + 31 → μ' a = μ a) :
    SharedReady p hmL aX aY b0 X Y μ' :=
  h.congr fun a _ => hag a

end Light.Sec2
