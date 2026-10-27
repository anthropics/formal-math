/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Paper.SecNetworks_Model
public import StepMachines.Prog.BruteE
public import StepMachines.Prog.NetProg
public import StepMachines.Prog.NetRun
public import StepMachines.Prog.NetVal
public import StepMachines.Math.RebalanceArith
import all StepMachines.Prog.NetVal
public import ToTuring.Poly.Spec
public import ToTuring.Poly.Brute
public import ToTuring.Poly.NetFun
public import ToTuring.Poly.Basic
public import ToTuring.Poly.Range
public import ToTuring.Poly.Comb

/-! # Section 3 of the paper: networks, cliques, achievable pairs, and the grouping in the proof of Lemma 1

Definition 1 (factoring through c bits) is in `Paper/SecNetworks_DefFactor.lean`. -/

@[expose] public section

namespace Paper

open Groundwork Groundwork.Prog Finset

/-! ### Networks: the general problem, a sum of products over pairs of nodes -/

/-- A network on the node set `J` (as in Definition 2): for each node `a` a finite set `S a` of
settings and a function `W a`; for each pair
of nodes the number `c a b` of shared bits and the two factors `f a b`, `f b a`.
Differences from the paper: Ψ is not given separately but *defined* from its factorization
(`Network.Ψ`), and θ ranges over a finite
set `N.lab a b` of labels, which Definition 2 below requires to be {0,1}^{c a b}. -/
abbrev Network (J σ τ : Type*) := Groundwork.Network J σ τ

/-- Ψ_ab(z, z') = Σ_θ f_ab(z, θ) · f_ba(z', θ) (Definition 2). -/
theorem Psi_def {J σ τ : Type*} [LinearOrder J] (N : Network J σ τ) (a b : J) (z z' : σ) :
    N.Ψ a b z z' = ∑ θ ∈ N.lab a b, N.f a b z θ * N.f b a z' θ := rfl

/-! ### Definition 2: a network with parameters P, B, τ -/

/-- A network given to an algorithm: procedures (step machines) that compute the values of W and f,
and the numbers P_a
(`n`) and c_ab (`cap`). All of them may depend on a context `c : C`, which stands for whatever the
calling algorithm holds in memory. -/
abbrev NetworkProcedures (C : Type) := PNet C

/-- **Definition 2.** `N` is a network on [g] with parameters P, B, τ, given by the procedures `Np`
in the context `c`.
* `sized`: |S_a| ≤ 2^P; c_ab = c_ba; (i) Σ_{b ≠ a} c_ab ≤ P; at most 2^{c_ab} labels θ for the pair
  {a,b}; (ii) all values of W, Ψ, f
  are at most 2^B in absolute value (the paper: below 2^B).
* `presented`: (iii) S_a = {0,1}^{P_a}, θ ranges over {0,1}^{c_ab}, and every value of W and f is
  computed within τ steps on states
  of size at most `S`.
Differences from the paper: S_a is all of {0,1}^{P_a} (a string that is not a setting gets W = 0
instead of a membership test);
there is no procedure for Ψ (Ψ is computed from f); the algorithm is given the numbers P_a and c_ab
but not P
and B; and a bound `S` on the size of the states is carried along, which is needed to turn steps
into time. -/
structure IsNetwork {C : Type} {g : ℕ} (Np : NetworkProcedures C) (c : C) (N : Network (Fin g) (List Bool) (List Bool))
    (P B τ S : ℕ) : Prop where
  sized : N.Sized P B
  presented : Np.Presents c N τ S

/-! ### Definition 3: the (K, λ)-clique -/

/-- The tables W_1, …, W_K of a clique on K nodes: `W w Θ` is the entry of the table of node `w` at
the setting `Θ`, which gives
for every other node `w'` the string on the edge {w, w'} (and the empty string at `w` itself). -/
abbrev Tables (K : ℕ) := Inst (Fin K) (List Bool)

/-- **Definition 3**, the value of the (K, λ)-clique with tables `W`: the sum, over all choices of
one string of λ bits per edge, of
the product of the K table entries. Here the two copies of the string on an edge
have already been identified, as in the remark after Definition 3. The clique as a network (two
copies of each string, Ψ an equality test) is not used in this file. -/
abbrev cliqueValue {K : ℕ} (lam : ℕ) (W : Tables K) : ℤ := Inst.ZW lam [] W

theorem cliqueValue_def {K : ℕ} (lam : ℕ) (W : Tables K) :
    cliqueValue lam W = ∑ Λ ∈ tuples (fun p : Fin K × Fin K => p.1 < p.2) (fun _ => words lam) [], ∏ w, W w (star Λ w) := rfl

/-! ### Definition 4: achievable pairs -/

/-- An algorithm for cliques: given λ and a procedure that answers table queries, a step machine
that returns an integer. -/
abbrev CliqueAlgorithm := Evaluator

/-- The bound of Definition 4 for the algorithm `E`: there is a constant `A` (the paper's C) such
that for all λ ≥ 1, all B ≥ 0 and all
tables with entries at most 2^B in absolute value, `E` returns the value of the (K, λ)-clique within
A · 2^{e K² λ} · (B + λ)^A · t steps, where
`t` is the cost of one query; all states have size at most S + A · (size of the context + B + λ)^A. -/
abbrev CliqueAlgorithm.Within (E : CliqueAlgorithm) (K : ℕ) (e : ℝ) : Prop := E.Correct K e

/-- The steps of the algorithm `E` are polynomial time, provided that λ is given in unary and the
steps of the procedure that
answers the queries are polynomial time. -/
abbrev CliqueAlgorithm.PolyTimeSteps (E : CliqueAlgorithm) : Prop := E.Keeps

/-- **Definition 4.** The pair (K, e) is achievable: some algorithm with polynomial-time steps
computes the value of every
(K, λ)-clique within C · 2^{e K² λ} · (B + λ)^C steps, times the cost of a query.
Differences from the paper: steps with polynomial-time cost instead of operations; a query costs `t`
steps and the
bound has the factor `t`; entries are at most 2^B, not below 2^B; the algorithm is not given B, and
B = 0 is allowed; there is also
a bound on the size of the states (see `CliqueAlgorithm.Within`); K ≥ 2 and e ≥ 0 are not part of
the definition. -/
def Achievable (K : ℕ) (e : ℝ) : Prop := ∃ E : CliqueAlgorithm, E.PolyTimeSteps ∧ E.Within K e

/-- "If (K, e) is achievable, so is (K, e₁) for every e₁ ≥ e" (after Definition 4). -/
theorem Achievable.mono {K : ℕ} {e e₁ : ℝ} (h : Achievable K e) (he : e ≤ e₁) : Achievable K e₁ :=
  let ⟨E, hk, hc⟩ := h
  ⟨E, hk, hc.mono he⟩

/-- "Trying all 2^{λK(K-1)/2} choices of one string per edge shows that (K, 1/2) is achievable for
every K" (after
Definition 4). -/
theorem achievable_half (K : ℕ) : Achievable K (1 / 2) := ⟨bruteE K, bruteE_keeps K, bruteE_correct K⟩

/-- e*: "the infimum of all e such that (K, e) is achievable for infinitely many K" (after
Definition 4). The condition e ≥ 0, which
the paper puts into Definition 4, is put here. "For infinitely many K" is written as: for every K₀
there is such a K ≥ K₀. -/
noncomputable def eStar : ℝ := sInf {e : ℝ | 0 ≤ e ∧ ∀ K₀ : ℕ, ∃ K, K₀ ≤ K ∧ Achievable K e}

/-- 0 ≤ e*. -/
theorem eStar_nonneg : 0 ≤ eStar :=
  le_csInf ⟨1 / 2, by norm_num, fun K₀ => ⟨K₀, le_rfl, achievable_half K₀⟩⟩ fun _ he => he.1

/-! ### Lemma 1 -/

/-! #### The length L of the groups -/

section Grouping

variable {g K : ℕ}

/-- L = max{1, ⌊(U + gP/K)/K²⌋}, written as max{1, ⌊(KU + gP)/K³⌋}. -/
abbrev groupedLength (K g U P : ℕ) : ℕ := Colouring.beta K g U P

theorem groupedLength_def (K g U P : ℕ) : groupedLength K g U P = max 1 ((K * U + g * P) / K ^ 3) := rfl

/-- "K²L ≤ K² + U + gP/K" (multiplied by K). -/
theorem groupedLength_le (K g U P : ℕ) : K ^ 3 * groupedLength K g U P ≤ K ^ 3 + K * U + g * P := Colouring.beta_le K g U P

end Grouping

/-! #### "The algorithm" -/

section Algorithm

open NetE Stepped

variable {C : Type} {g K : ℕ}

/-- The grouping number x, for x < K^g: the digits of x in base K. -/
abbrev grouping (hK : 0 < K) (x : ℕ) : Fin g → Fin K := chi hK x

/-- The tables W̃_γ of the (K, L)-clique whose nodes are the groups of the grouping number x:
W̃_γ(Θ) = [all appended bits are 0] · Σ_{(z_a), a ∈ G_γ} ∏_{a ∈ G_γ} W_a(z_a) ∏_{{a,b} ⊆ G_γ}
Ψ_ab(z_a, z_b) ∏_{a ∈ G_γ, b ∉ G_γ} f_ab(z_a, θ_ab).
In two steps: `merge` makes each group one node, `toInst` sums over the settings of that node and
cuts Θ into its blocks. -/
abbrev groupedTables (Np : NetworkProcedures C) (c : C) (N : Network (Fin g) (List Bool) (List Bool)) (hK0 : 0 < K) (x L : ℕ) :
    Tables K :=
  (N.merge (grouping hK0 x) [] []).toInst (mD K g Np c x L) (mdec K g Np c x)

/-- "… so the value equals Z": the (K, L)-clique with the tables W̃ has the value of the network. -/
theorem grouped_value (Np : NetworkProcedures C) {c : C} {N : Network (Fin g) (List Bool) (List Bool)} {P B τ S : ℕ}
    (hK0 : 0 < K) (hN : IsNetwork Np c N P B τ S) (x L : ℕ)
    (hL : ∀ γ γ' : Fin K, γ ≠ γ' → (N.merge (grouping hK0 x) [] []).c γ γ' ≤ L) :
    cliqueValue L (groupedTables Np c N hK0 x L) = N.value :=
  ZW_merged Np hK0 hN.presented x L fun G G' hlt => by
    rw [lbLen_eq Np hK0 hN.presented x hlt.ne]
    exact hL _ _ hlt.ne

end Algorithm

end Paper
