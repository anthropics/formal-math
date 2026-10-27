/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Eight.ViaGrouping.Table
public import Eight.SecNetworks_Tables
public import Eight.SecNetworks_Clique

/-! # Proof of Lemma 1, «The algorithm»: the tables that the algorithm computes are the display of W̃_γ

«Put W̃_γ(Θ) = [all appended bits are 0] Σ_{(z_a), a ∈ G_γ} ∏_{a ∈ G_γ} W_a(z_a) ∏_{{a,b} ⊆ G_γ}
Ψ_{a,b}(z_a, z_b) ∏_{a ∈ G_γ, b ∉ G_γ} f_{a,b}(z_a, θ_{a,b}). Here each z_a ranges over S_a.»
The statements `StTable` and `StValue` speak of the tables
`Paper.groupedTables Np.toPaperNetwork c N.toPaperNetwork`, which are defined in two steps.
`SecNetworks.tables_eq` (proof/networks/Eight/SecNetworks_Tables.lean) shows that they are given by
the formula of the paper. Here that formula gets a name
(`display`), and the statement `StTable` is said again with it:
* `groupedTables_eq_display`: the tables are the display, at every Θ : [K] ∖ {γ} → {0,1}^L;
* `tableM_display`: the procedure `tableM` of the algorithm returns the display, within the steps
  and sizes of `StTable`, and the display obeys the bound on the entries. -/

@[expose] public section

namespace Eight.ViaGrouping

open Groundwork Groundwork.Prog Groundwork.Prog.NetE Finset Stepped Eight.SecNetworks

variable {C : Type} [HasSize C] {g K : ℕ}

/-- **The display of W̃_γ(Θ)** of the proof of Lemma 1, for the grouping number x of a network N
(Definition 2). (z_a) is a function on all nodes, with the empty string outside G_γ; each z_a ranges
over S_a;
the pairs {a, b} ⊆ G_γ are the pairs a < b. The appended bits (`SecNetworks.appendedBits`) and
θ_{a,b} (`SecNetworks.thetaAt`) are cut out of Θ at the positions that the numbers c_{a,b} given by
the procedures fix. -/
def display (Np : Procs C) (c : C) (N : Net g) (hK0 : 0 < K) (x : ℕ) (γ : Fin K) (Θ : Fin K → List Bool) : ℤ :=
  (if ∀ γ', γ' ≠ γ → ∀ bit ∈ appendedBits (g := g) Np.toPaperNetwork c x γ γ' (Θ γ'), bit = false then 1 else 0) *
    ∑ z ∈ tuples (fun a => Paper.grouping hK0 x a = γ) N.S [],
      (∏ a with Paper.grouping hK0 x a = γ, N.W a (z a)) *
        (∏ p ∈ pairs (Fin g) with Paper.grouping hK0 x p.1 = γ ∧ Paper.grouping hK0 x p.2 = γ, N.Ψ p.1 p.2 (z p.1) (z p.2)) *
        ∏ p : Fin g × Fin g with Paper.grouping hK0 x p.1 = γ ∧ Paper.grouping hK0 x p.2 ≠ γ, N.f p.1 p.2 (z p.1) (thetaAt Np.toPaperNetwork c hK0 x Θ p.1 p.2)

variable {Np : Procs C} {c : C} {N : Net g} {P B τ S : ℕ}

/-- The tables of `StTable` and `StValue` are the display, for Θ : [K] ∖ {γ} → {0,1}^L and Y_{γ,γ'}
≤ L. This is `SecNetworks.tables_eq`, for procedures that need not give B. -/
theorem groupedTables_eq_display (h : IsNetworkP Np c N P B τ S) (hK0 : 0 < K) (x L : ℕ) (hL : ∀ γ γ' : Fin K, γ ≠ γ' → Y N.c (Paper.grouping hK0 x) γ γ' ≤ L)
    (γ : Fin K) (Θ : Fin K → List Bool) (hΘ : ∀ γ', γ' ≠ γ → (Θ γ').length = L) :
    Paper.groupedTables Np.toPaperNetwork c N.toPaperNetwork hK0 x L γ Θ = display Np c N hK0 x γ Θ :=
  tables_eq (Table.isNetwork h) hK0 x L hL γ Θ hΘ

/-- **The procedure `tableM` computes the display.** For a grouping with (G1) and Y_{γ,γ'} ≤ L ≤
2gP, and every query (γ, Θ) with L bits for every other group and the empty string at γ: `tableM`
returns the display of W̃_γ(Θ) within c₁·2^{P·⌊2g/K⌋}·τ steps, on states of size at most
S + c₁·(size c + P + B)^{c₁}, and the display is at most 2^{P·⌊2g/K⌋ + g²B} in absolute value. The
constant depends on K and g only. -/
theorem tableM_display (K g : ℕ) : ∃ c₁ : ℕ, 1 ≤ c₁ ∧ ∀ (hK0 : 0 < K) (C : Type) [HasSize C] (Np : Procs C) (c : C) (N : Net g) (P B τ S : ℕ), IsNetworkP Np c N P B τ S →
    ∀ x < K ^ g, ∀ L ≤ 2 * (g * P), (∀ γ : Fin K, K * #{a : Fin g | Paper.grouping hK0 x a = γ} ≤ 2 * g) → (∀ γ γ' : Fin K, γ ≠ γ' → Y N.c (Paper.grouping hK0 x) γ γ' ≤ L) →
    ∀ (γ : Fin K) (Θ : Fin K → List Bool), (∀ γ', γ' ≠ γ → (Θ γ').length = L) → Θ γ = [] →
      (tableM K g Np).Runs ((c, x), γ.1, List.ofFn Θ) (c₁ * 2 ^ (P * (2 * g / K)) * τ) (S + c₁ * (size c + P + B) ^ c₁) (display Np c N hK0 x γ Θ) ∧
        |display Np c N hK0 x γ Θ| ≤ 2 ^ (P * (2 * g / K) + g ^ 2 * B) := by
  obtain ⟨c₁, h1, hc₁⟩ := stTable K g
  refine ⟨c₁, h1, fun hK0 C _ Np c N P B τ S h x hx L hL hG1 hY γ Θ hΘ hγ => ?_⟩
  rw [← groupedTables_eq_display h hK0 x L hY γ Θ hΘ]
  exact hc₁ hK0 C Np c N P B τ S h x hx L hL hG1 hY γ Θ hΘ hγ

end Eight.ViaGrouping
