/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Ov.Core.Wire

/-!
# Prices of wires: the definition

For a field K and a finite set V of parties, `Prices K V` is the closure (for pointwise limits) of the
multiples c·d_F, c ≥ 0, of the metrics d_F(u,v) = F.e u v of the spectral points F over V. A function w
on pairs of any set Y is a price (`IsPrice K w`) if its pull-backs to finite sets are in `Prices`.
That prices are pseudometrics, closed under pull-backs, multiples and limits, and compact below a bound is
in `Paper/Prices.lean`. At the end there are two lemmas on the entries of a wire, for the files that compute with them.
-/

namespace Nc.Price

open Ov Finset

section Finite

variable (K : Type) [Field K]

/-- The multiples of the metrics of spectral points. -/
def specCone (V : Type) [Fintype V] [DecidableEq V] : Set (V → V → ℝ) :=
  {d | ∃ (F : Spec K V) (c : ℝ), 0 ≤ c ∧ d = fun u v => c * F.e u v}

/-- The prices of a finite set of parties. -/
def Prices (V : Type) [Fintype V] [DecidableEq V] : Set (V → V → ℝ) := closure (specCone K V)

variable {K} {U V : Type} [Fintype U] [DecidableEq U] [Fintype V] [DecidableEq V]

theorem specCone_comp (f : U → V) {d : V → V → ℝ} (h : d ∈ specCone K V) :
    (fun a b => d (f a) (f b)) ∈ specCone K U := by
  obtain ⟨F, c, hc, rfl⟩ := h
  exact ⟨F.pull f, c, hc, by funext a b; rw [F.pull_e]⟩

theorem continuous_comp {X Y : Type*} (f : X → Y) :
    Continuous fun (d : Y → Y → ℝ) (a b : X) => d (f a) (f b) := by
  fun_prop

theorem prices_comp (f : U → V) {d : V → V → ℝ} (h : d ∈ Prices K V) :
    (fun a b => d (f a) (f b)) ∈ Prices K U :=
  map_mem_closure (continuous_comp f) h fun _ hd => specCone_comp f hd

theorem specCone_smul {d : V → V → ℝ} (h : d ∈ specCone K V) {c : ℝ} (hc : 0 ≤ c) :
    (fun a b => c * d a b) ∈ specCone K V := by
  obtain ⟨F, c', hc', rfl⟩ := h
  exact ⟨F, c * c', mul_nonneg hc hc', by funext a b; ring⟩

theorem prices_smul {d : V → V → ℝ} (h : d ∈ Prices K V) {c : ℝ} (hc : 0 ≤ c) :
    (fun a b => c * d a b) ∈ Prices K V :=
  map_mem_closure (f := fun (d : V → V → ℝ) a b => c * d a b) (by fun_prop) h
    fun _ hd => specCone_smul hd hc

/-- A closed property of the metrics of spectral points that is kept by multiples holds for
prices. -/
theorem prices_induction {d : V → V → ℝ} (h : d ∈ Prices K V) {S : Set (V → V → ℝ)}
    (hS : IsClosed S) (hF : ∀ (F : Spec K V) (c : ℝ), 0 ≤ c → (fun u v => c * F.e u v) ∈ S) :
    d ∈ S := by
  refine closure_minimal ?_ hS h
  rintro _ ⟨F, c, hc, rfl⟩
  exact hF F c hc

end Finite

section General

variable (K : Type) [Field K]

/-- A function w on pairs of a set Y is a price if all its pull-backs to finite sets are. -/
def IsPrice {Y : Type*} (w : Y → Y → ℝ) : Prop :=
  ∀ (n : ℕ) (f : Fin n → Y), (fun i j => w (f i) (f j)) ∈ Prices K (Fin n)

variable {K}

theorem IsPrice.mem {Y : Type*} {w : Y → Y → ℝ} (h : IsPrice K w) {V : Type} [Fintype V]
    [DecidableEq V] (g : V → Y) : (fun a b => w (g a) (g b)) ∈ Prices K V := by
  have h1 := prices_comp (Fintype.equivFin V) (h _ fun i => g ((Fintype.equivFin V).symm i))
  simpa using h1

theorem isPrice_of_mem {V : Type} [Fintype V] [DecidableEq V] {d : V → V → ℝ}
    (h : d ∈ Prices K V) : IsPrice K d := fun _ f => prices_comp f h

/-- The metric of a spectral point is a price. -/
theorem isPrice_spec {V : Type} [Fintype V] [DecidableEq V] (F : Spec K V) :
    IsPrice K F.e :=
  isPrice_of_mem (subset_closure ⟨F, 1, zero_le_one, by simp⟩)

/-- A function is a price if its restrictions to finite subsets are. -/
theorem isPrice_of_finset {Y : Type*} {w : Y → Y → ℝ}
    (h : ∀ S : Finset Y, IsPrice K fun a b : S => w a b) : IsPrice K w := by
  classical
  intro n f
  exact h (Finset.univ.image f) n fun i => ⟨f i, by simp⟩

variable {Y : Type*} {w : Y → Y → ℝ}

/-- Approximation by the metric of a spectral point. -/
theorem IsPrice.exists_spec (h : IsPrice K w) {V : Type} [Fintype V] [DecidableEq V] (g : V → Y)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ (F : Spec K V) (c : ℝ), 0 ≤ c ∧ ∀ a b, |w (g a) (g b) - c * F.e a b| < δ := by
  obtain ⟨d, ⟨F, c, hc, rfl⟩, hd⟩ := Metric.mem_closure_iff.1 (h.mem g) δ hδ
  refine ⟨F, c, hc, fun a b => ?_⟩
  have := (dist_pi_lt_iff hδ).1 ((dist_pi_lt_iff hδ).1 hd a) b
  rwa [Real.dist_eq] at this

/-- 0 is a price. -/
theorem isPrice_zero : IsPrice K fun _ _ : Y => 0 := fun n _ =>
  subset_closure ⟨Paper.trivialPoint K (Fin n), 0, le_rfl, by simp⟩

end General

section Unit

open Ov.Ten

variable {K : Type} [Field K]

/-- The entries of the unit tensor with two legs (a wire before it is placed). -/
theorem unit_two_val {n : ℕ} (y : Fin 2 → Fin n) :
    (unit K (Fin 2) n).val y = if y 0 = y 1 then 1 else 0 := by
  rw [unit_val]
  simp [Fin.forall_fin_two, eq_comm]

theorem unit_two_val' {n : ℕ} {β : Type} [DecidableEq β] (ε : Fin n ≃ β) (y : Fin 2 → Fin n) :
    (unit K (Fin 2) n).val y = if ε (y 0) = ε (y 1) then 1 else 0 := by
  rw [unit_two_val]
  simp only [ε.injective.eq_iff]

end Unit

end Nc.Price
