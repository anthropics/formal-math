/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Eight.ViaGrouping.Search
public import StepMachines.Math.RebalanceArith
import Mathlib.Tactic

/-! # Lemma 1 along the printed proof: «Cost», and the lemma for the algorithm of its proof

The file puts the steps of the proof of Lemma 1 together for the algorithm `netAlg K g E` of
proof/networks/Eight/ViaGrouping/Defs.lean. It takes three steps as hypotheses: the search finds a
good grouping (`StSearch`), the procedure `tableM` answers the queries to the tables W̃
(`StTable`), and the clique of the groups has the value of the network (`StValue`). It proves the
other sentences of the paragraph «Cost», one lemma or a few for each (namespace
`Eight.ViaGrouping.Cost`); «each a product of at most g² values» and «one entry costs
2^{2gP/K}·poly(P + B)·τ operations» are part of `StTable`, and the count of the search («Go through
all K^g groupings (a constant)», 2·K^g steps) is `searchP_runs` of
proof/networks/Eight/ViaGrouping/Search.lean.
* «The sum defining W̃_γ(Θ) has at most (2^P)^{2g/K} = 2^{2gP/K} terms»: `terms_le`;
* «So |W̃_γ| < 2^{B'} with B' = ⌈2gP/K⌉ + g²B»: `Bp`, `le_Bp`, `serves_Bp`;
* «Run the algorithm for (K, e) with L, B' in the roles of λ, B; this is legitimate because
  Definition 4 covers all integer tables. Answer each of its at most C·2^{eK²L}(B' + L)^C queries by
  computing the entry»: `run_clique`;
* «Since K²L ≤ K² + U + gP/K and L ≤ 2gP, the bound follows»: `K2L_le_real`, `exponent_le`,
  `base_le`, `bound_follows`.
Then `netAlg_correct` (any g ≥ K for which the search succeeds; K need not divide 2g) and
`stLemGrouping_of` (g = 3K⁸).

Different from the paper: steps of step machines are counted, and the sizes of their states are
bounded too (`Groundwork.RebalanceArith.size_le`); a group has at most ⌊2g/K⌋ nodes, so the sum has
at most 2^{P·⌊2g/K⌋} terms; «at most 2^{B'}» stands for «below 2^{B'}», as in the
form of Definition 4 that this development uses; there a query costs t steps and the bound carries
the factor t, which is how «answer each query by computing the entry» is counted. -/

public section

namespace Eight.ViaGrouping

open Groundwork Groundwork.Prog Groundwork.Prog.NetE Finset Stepped Eight.SecNetworks

namespace Cost

/-! ## The sentences of «Cost» that are arithmetic -/

/-- P·⌊2g/K⌋ ≤ 2gP/K. -/
theorem floor_le (K g P : ℕ) : ((P * (2 * g / K) : ℕ) : ℝ) ≤ 2 * ((g : ℝ) * P) / K := by
  have h : ((2 * g / K : ℕ) : ℝ) ≤ ((2 * g : ℕ) : ℝ) / K := Nat.cast_div_le
  have hP : (0 : ℝ) ≤ P := Nat.cast_nonneg P
  calc ((P * (2 * g / K) : ℕ) : ℝ) = P * ((2 * g / K : ℕ) : ℝ) := by push_cast; ring
    _ ≤ P * (((2 * g : ℕ) : ℝ) / K) := mul_le_mul_of_nonneg_left h hP
    _ = 2 * ((g : ℝ) * P) / K := by push_cast; ring

/-- «The sum defining W̃_γ(Θ) has at most (2^P)^{2g/K} = 2^{2gP/K} terms»: the number 2^{P·⌊2g/K⌋}
of strings that `tableM` runs through is at most 2^{2gP/K}. K need not divide 2g. -/
theorem terms_le (K g P : ℕ) : ((2 ^ (P * (2 * g / K)) : ℕ) : ℝ) ≤ (2 : ℝ) ^ (2 * ((g : ℝ) * P) / K) := by
  rw [Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast]
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (floor_le K g P)

/-- «B' = ⌈2gP/K⌉ + g²B». -/
@[expose] noncomputable def Bp (K g P B : ℕ) : ℕ := ⌈2 * ((g : ℝ) * P) / K⌉₊ + g ^ 2 * B

/-- The exponent P·⌊2g/K⌋ + g²B that the count of the terms and of the g² values in a term gives is
at most B'. -/
theorem le_Bp (K g P B : ℕ) : P * (2 * g / K) + g ^ 2 * B ≤ Bp K g P B :=
  Nat.add_le_add_right (Nat.cast_le.1 ((floor_le K g P).trans (Nat.le_ceil _))) _

/-- B' ≤ (2g + g²)(P + B): B' is polynomial in P + B. -/
theorem Bp_le {K : ℕ} (g P B : ℕ) (hK : 1 ≤ K) : Bp K g P B ≤ (2 * g + g ^ 2) * (P + B) := by
  have h1 : ⌈2 * ((g : ℝ) * P) / K⌉₊ ≤ 2 * g * P := by
    refine Nat.ceil_le.2 ?_
    have hK' : (1 : ℝ) ≤ K := by exact_mod_cast hK
    push_cast
    calc 2 * ((g : ℝ) * P) / K ≤ 2 * ((g : ℝ) * P) := div_le_self (by positivity) hK'
      _ = 2 * g * P := by ring
  have e : (2 * g + g ^ 2) * (P + B) = 2 * g * P + g ^ 2 * B + (2 * g * B + g ^ 2 * P) := by ring
  unfold Bp
  omega

/-- «K²L ≤ K² + U + gP/K», for L = max{1, ⌊(U + gP/K)/K²⌋}. -/
theorem K2L_le_real {K : ℕ} (g U P : ℕ) (hK : 1 ≤ K) :
    (K : ℝ) ^ 2 * (Paper.groupedLength K g U P : ℝ) ≤ (K : ℝ) ^ 2 + U + (g : ℝ) * P / K := by
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hK
  have h : (K : ℝ) ^ 3 * (Paper.groupedLength K g U P : ℝ) ≤ (K : ℝ) ^ 3 + K * U + g * P := by exact_mod_cast K2L_le K g U P
  refine le_of_mul_le_mul_right ?_ hKpos
  have e : ((K : ℝ) ^ 2 + U + (g : ℝ) * P / K) * K = (K : ℝ) ^ 3 + K * U + g * P := by field_simp
  rw [e]
  calc (K : ℝ) ^ 2 * (Paper.groupedLength K g U P : ℝ) * K = (K : ℝ) ^ 3 * (Paper.groupedLength K g U P : ℝ) := by ring
    _ ≤ _ := h

/-- The exponents: e·K²L + 2gP/K ≤ e·K² + (e·U + (e + 2)·gP/K), from «K²L ≤ K² + U + gP/K». The term
e·K² is a constant. -/
theorem exponent_le {K : ℕ} (g U P : ℕ) {e : ℝ} (hK : 1 ≤ K) (h0 : 0 ≤ e) :
    e * (K : ℝ) ^ 2 * (Paper.groupedLength K g U P : ℝ) + 2 * ((g : ℝ) * P) / K ≤ e * (K : ℝ) ^ 2 + (e * U + (e + 2) * ((g : ℝ) * P) / K) := by
  have h := mul_le_mul_of_nonneg_left (K2L_le_real g U P hK) h0
  have e1 : (e + 2) * ((g : ℝ) * P) / K = e * ((g : ℝ) * P / K) + 2 * ((g : ℝ) * P) / K := by ring
  rw [e1]
  linarith

/-- B' + L ≤ (4g + g²)(P + B), from «L ≤ 2gP»: the factor (B' + L)^C is polynomial in P + B. -/
theorem base_le {K g : ℕ} (U P B : ℕ) (hK : 1 ≤ K) (hg : 1 ≤ g) (hP : 1 ≤ P) (hU : U ≤ g * P) :
    Bp K g P B + Paper.groupedLength K g U P ≤ (4 * g + g ^ 2) * (P + B) := by
  have h1 := Bp_le g P B hK
  have h2 := L_le hK hg hP hU
  have e : (4 * g + g ^ 2) * (P + B) = (2 * g + g ^ 2) * (P + B) + 2 * (g * P) + 2 * (g * B) := by ring
  omega

/-- «Since K²L ≤ K² + U + gP/K and L ≤ 2gP, the bound follows.» T_E is the number of steps of the
algorithm for cliques, at most A·2^{eK²L}·(B' + L)^A times the cost c₁·2^{P·⌊2g/K⌋}·τ of an entry; s
is the constant number of steps of the search and of the passage
from the search to the call. Then the total T ≤ s + T_E is at most A'·2^{eU + (e+2)gP/K}·(P +
B)^{A'}·τ, and A' depends only on K, g, e, A, c₁, s. -/
theorem bound_follows {K g : ℕ} (A c₁ s : ℕ) {e : ℝ} (hK : 1 ≤ K) (hg : 1 ≤ g) (h0 : 0 ≤ e) :
    ∃ A' : ℕ, ∀ P B τ U TE T : ℕ, 1 ≤ P → 1 ≤ τ → U ≤ g * P →
      (TE : ℝ) ≤ A * (2 : ℝ) ^ (e * (K : ℝ) ^ 2 * (Paper.groupedLength K g U P : ℝ)) * ((Bp K g P B : ℝ) + (Paper.groupedLength K g U P : ℝ)) ^ A
        * ((c₁ * 2 ^ (P * (2 * g / K)) * τ : ℕ) : ℝ) →
      T ≤ s + TE →
      (T : ℝ) ≤ A' * (2 : ℝ) ^ (e * U + (e + 2) * ((g : ℝ) * P) / K) * ((P : ℝ) + B) ^ A' * τ := by
  obtain ⟨E₀, hE₀⟩ : ∃ E₀ : ℕ, E₀ = ⌈e * (K : ℝ) ^ 2⌉₊ := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D : ℕ, D = 4 * g + g ^ 2 := ⟨_, rfl⟩
  obtain ⟨M, hM⟩ : ∃ M : ℕ, M = A * D ^ A * c₁ * 2 ^ E₀ := ⟨_, rfl⟩
  refine ⟨A + s + M, fun P B τ U TE T hP hτ hU hTE hT => ?_⟩
  obtain ⟨A', hA'⟩ : ∃ A' : ℕ, A' = A + s + M := ⟨_, rfl⟩
  rw [← hA']
  obtain ⟨L, hL⟩ : ∃ L : ℕ, L = Paper.groupedLength K g U P := ⟨_, rfl⟩
  rw [← hL] at hTE
  obtain ⟨X, hX⟩ : ∃ X : ℝ, X = (2 : ℝ) ^ (e * U + (e + 2) * ((g : ℝ) * P) / K) := ⟨_, rfl⟩
  rw [← hX]
  obtain ⟨Y, hY⟩ : ∃ Y : ℝ, Y = (P : ℝ) + B := ⟨_, rfl⟩
  rw [← hY]
  obtain ⟨n, hn⟩ : ∃ n : ℝ, n = ((2 ^ (P * (2 * g / K)) : ℕ) : ℝ) := ⟨_, rfl⟩
  have hn0 : 0 ≤ n := hn ▸ Nat.cast_nonneg _
  have hX1 : 1 ≤ X := hX ▸ Real.one_le_rpow (by norm_num) (by positivity)
  have hY1 : 1 ≤ Y := by
    rw [hY]
    exact_mod_cast (by omega : 1 ≤ P + B)
  have hτ1 : (1 : ℝ) ≤ τ := by exact_mod_cast hτ
  have hYA : Y ^ A ≤ Y ^ A' := pow_le_pow_right₀ hY1 (by omega)
  have hYA1 : 1 ≤ Y ^ A' := one_le_pow₀ hY1
  have hbase : (Bp K g P B : ℝ) + L ≤ D * Y := by
    rw [hY, hD, hL]
    exact_mod_cast base_le U P B hK hg hP hU
  have hexp : (2 : ℝ) ^ (e * (K : ℝ) ^ 2 * L) * n ≤ (2 : ℝ) ^ E₀ * X := by
    calc (2 : ℝ) ^ (e * (K : ℝ) ^ 2 * L) * n ≤ (2 : ℝ) ^ (e * (K : ℝ) ^ 2 * L) * (2 : ℝ) ^ (2 * ((g : ℝ) * P) / K) :=
          mul_le_mul_of_nonneg_left (hn ▸ terms_le K g P) (Real.rpow_pos_of_pos (by norm_num) _).le
      _ ≤ (2 : ℝ) ^ E₀ * X := by
          rw [hX, ← Real.rpow_natCast 2 E₀, ← Real.rpow_add (by norm_num), ← Real.rpow_add (by norm_num)]
          refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
          have h1 := exponent_le (K := K) g U P hK h0
          have h2 : e * (K : ℝ) ^ 2 ≤ E₀ := hE₀ ▸ Nat.le_ceil _
          rw [← hL] at h1
          linarith
  have hcost : ((c₁ * 2 ^ (P * (2 * g / K)) * τ : ℕ) : ℝ) = c₁ * n * τ := by rw [hn]; push_cast; ring
  have hTE' : (TE : ℝ) ≤ M * (X * Y ^ A' * τ) := by
    calc (TE : ℝ) ≤ A * (2 : ℝ) ^ (e * (K : ℝ) ^ 2 * L) * ((Bp K g P B : ℝ) + L) ^ A * (c₁ * n * τ) := hcost ▸ hTE
      _ ≤ A * (2 : ℝ) ^ (e * (K : ℝ) ^ 2 * L) * ((D : ℝ) * Y) ^ A * (c₁ * n * τ) := by gcongr
      _ = A * (D : ℝ) ^ A * c₁ * ((2 : ℝ) ^ (e * (K : ℝ) ^ 2 * L) * n) * Y ^ A * τ := by rw [mul_pow]; ring
      _ ≤ A * (D : ℝ) ^ A * c₁ * ((2 : ℝ) ^ E₀ * X) * Y ^ A' * τ := by gcongr
      _ = M * (X * Y ^ A' * τ) := by rw [hM]; push_cast; ring
  have hone : 1 ≤ X * Y ^ A' * τ := by
    have := mul_le_mul (mul_le_mul hX1 hYA1 zero_le_one (by linarith)) hτ1 zero_le_one (by positivity)
    simpa using this
  have hT' : (T : ℝ) ≤ s + TE := by exact_mod_cast hT
  calc (T : ℝ) ≤ s * (X * Y ^ A' * τ) + M * (X * Y ^ A' * τ) := by
        have : (s : ℝ) ≤ s * (X * Y ^ A' * τ) := le_mul_of_one_le_right (by positivity) hone
        linarith
    _ ≤ A' * (X * Y ^ A' * τ) := by
        rw [← add_mul]
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        rw [hA']
        push_cast
        have : (0 : ℝ) ≤ A := by positivity
        linarith
    _ = A' * X * Y ^ A' * τ := by ring

/-! ## The sentences of «Cost» that speak of the model -/

section Model

variable {C : Type} [HasSize C] {Np : Procs C} {c : C} {g : ℕ} {N : Net g} {P B τ S : ℕ}

/-- «So |W̃_γ| < 2^{B'} with B' = ⌈2gP/K⌉ + g²B»: query access with the bound 2^{P·⌊2g/K⌋ + g²B} on
the entries is query access with the bound 2^{B'}. Different from the paper: «at most» for «below». -/
theorem serves_Bp {D : Type} {R : Stepped (D × IQ) ℤ} {d : D} {K : ℕ} {L t S' : ℕ} {W : Paper.Tables K} (g P B : ℕ)
    (h : ServesInst R d L (P * (2 * g / K) + g ^ 2 * B) t S' W) : ServesInst R d L (Bp K g P B) t S' W := fun v θ hθ hv =>
  ⟨(h v θ hθ hv).1, (h v θ hθ hv).2.trans (pow_le_pow_right₀ (by norm_num) (le_Bp K g P B))⟩

end Model

/-- «Run the algorithm for (K, e) with L, B' in the roles of λ, B; this is legitimate because
Definition 4 covers all integer tables. Answer each of its at most C·2^{eK²L}(B' + L)^C queries by
computing the entry.» For a good grouping number x, the algorithm E for
cliques, run with L and with `tableM` as the procedure that answers its queries, returns the value
of the network within A·2^{eK²L}·(B' + L)^A·t' steps, where t' = c₁·2^{P·⌊2g/K⌋}·τ is the cost of
one entry. A is the constant of E (the paper's C), c₁ that of `StTable`.
In the form of Definition 4 that this development uses, a query costs t' steps and the bound carries
the factor t'. -/
theorem run_clique (hT : StTable) (hV : StValue) {K : ℕ} (g : ℕ) {e : ℝ} {E : Paper.CliqueAlgorithm} (hK0 : 0 < K) (hg : 1 ≤ g) (h : E.Within K e) :
    ∃ A c₁ : ℕ, 1 ≤ c₁ ∧ ∀ (C : Type) [HasSize C] (Np : Procs C) (c : C) (N : Net g) (P B τ S : ℕ), IsNetworkP Np c N P B τ S →
      ∀ x < K ^ g, Good N.c P (Paper.grouping hK0 x) →
      ∃ TE : ℕ, (E.app (lamP K g Np) (tableM K g Np)).Runs (c, x) TE
          (S + c₁ * (size c + P + B) ^ c₁ + A * (size (c, x) + Bp K g P B + Paper.groupedLength K g N.U P) ^ A) N.value ∧
        (TE : ℝ) ≤ A * (2 : ℝ) ^ (e * (K : ℝ) ^ 2 * (Paper.groupedLength K g N.U P : ℝ)) * ((Bp K g P B : ℝ) + (Paper.groupedLength K g N.U P : ℝ)) ^ A
          * ((c₁ * 2 ^ (P * (2 * g / K)) * τ : ℕ) : ℝ) := by
  obtain ⟨A, hA⟩ := h
  obtain ⟨c₁, h1, hc₁⟩ := hT K g
  refine ⟨A, c₁, h1, fun C _ Np c N P B τ S hN x hx hgood => ?_⟩
  obtain ⟨L, hL⟩ : ∃ L : ℕ, L = Paper.groupedLength K g N.U P := ⟨_, rfl⟩
  rw [← hL]
  have hlam : lamP K g Np (c, x) = L := (lamP_eq hN x).trans hL.symm
  have hL1 : 1 ≤ L := hL ▸ Colouring.one_le_beta _ _ _ _
  have hLle : L ≤ 2 * (g * P) := hL ▸ L_le hK0 hg hN.is.P_pos (U_le hN.is)
  have hY : ∀ γ γ' : Fin K, γ ≠ γ' → Y N.c (Paper.grouping hK0 x) γ γ' ≤ L := fun γ γ' hne => hL ▸ Y_le_of_good hK0 hgood hne
  have hserve := serves_Bp g P B (hc₁ hK0 C Np c N P B τ S hN x hx L hLle hgood.G1 hY)
  have ht' : 1 ≤ c₁ * 2 ^ (P * (2 * g / K)) * τ := Nat.mul_pos (Nat.mul_pos h1 (Nat.two_pow_pos _)) hN.τ_pos
  obtain ⟨TE, hrun, hTE⟩ := hA (C × ℕ) (lamP K g Np) (tableM K g Np) (c, x) (Bp K g P B) _ _ _ (hlam ▸ hL1) ht' (hlam ▸ hserve)
  rw [hlam, show Inst.ZW L [] (Paper.groupedTables Np.toPaperNetwork c N.toPaperNetwork hK0 x L) = N.value from hV K g hK0 C Np c N P B τ S hN x L hY] at hrun
  rw [hlam] at hTE
  exact ⟨TE, hrun, hTE⟩

end Cost

open Cost

/-! ## Lemma 1 -/

/-- The bound of Lemma 1 for the algorithm of its proof, on networks on [g], for every g ≥ K for
which the search finds a good grouping (hypothesis `hS`; for g = 3K⁸ this is `StSearch`). K need not
divide 2g. The proof runs through the paragraphs «The algorithm» and «Cost»:
the search (`searchP_runs`), the call of the algorithm for cliques (`Cost.run_clique`), «the bound
follows» (`Cost.bound_follows`), and the same for the sizes of the states
(`Groundwork.RebalanceArith.size_le`). -/
theorem netAlg_correct (hT : StTable) (hV : StValue) {K g : ℕ} {e : ℝ} {E : Paper.CliqueAlgorithm} (hK : 2 ≤ K) (hKg : K ≤ g) (h0 : 0 ≤ e) (h : E.Within K e)
    (hS : ∀ (C : Type) [HasSize C] (Np : Procs C) (c : C) (N : Net g) (P B τ S : ℕ), IsNetworkP Np c N P B τ S →
      ∃ x < K ^ g, (List.range (K ^ g)).find? (fun x => goodP K g Np (c, x)) = some x ∧ Good N.c P (Paper.grouping (g := g) (by omega : 0 < K) x)) :
    Correct (netAlg K g E) g K e (e + 2) := by
  have hK0 : 0 < K := by omega
  -- the constants
  obtain ⟨A, c₁, hc₁1, hrunE⟩ := run_clique hT hV g hK0 (by omega) h
  obtain ⟨c₂, hc₂⟩ : ∃ c₂ : ℕ, c₂ = c₁ + 5 * size (K ^ g) + 20 := ⟨_, rfl⟩
  obtain ⟨A1, hA1⟩ := bound_follows (K := K) (g := g) A c₁ (2 * K ^ g + 1) (by omega) (by omega) h0
  obtain ⟨A2, hA2⟩ := RebalanceArith.size_le (K := K) (g := g) A c₂ (2 * g + g ^ 2) hK hKg
  refine ⟨max A1 A2, fun C _ Np c N P B τ S hN => ?_⟩
  have hP := hN.is.P_pos
  have hU := U_le hN.is
  -- «fix the first good one», number x
  obtain ⟨x, hxlt, hfind, hgood⟩ := hS C Np c N P B τ S hN
  have hsearch := searchP_runs K g Np c
  rw [hfind] at hsearch
  -- «run the algorithm for (K, e) …»
  obtain ⟨TE, hrun, hTE⟩ := hrunE C Np c N P B τ S hN x hxlt hgood
  have hall := optBind_runs_some (dflt := zeroOf) hsearch hrun
  have hZ1 : 1 ≤ size c + P + B := by omega
  have hpow : ∀ {a b : ℕ}, a ≤ b → a * (size c + P + B) ^ a ≤ b * (size c + P + B) ^ b := fun hab =>
    Nat.mul_le_mul hab (Nat.pow_le_pow_right hZ1 hab)
  refine ⟨2 * K ^ g + 1 + TE, hall.mono le_rfl ?_, ?_⟩
  · -- the sizes of the states
    refine (hA2 P B N.U (Paper.groupedLength K g N.U P) (Bp K g P B) S (S + c₁ * (size c + P + B) ^ c₁) (size c) (size (c, x)) _ hP hU (K2L_le K g N.U P)
      (Bp_le g P B (by omega)) (Nat.add_le_add_left (hpow (by omega)) _) ?_ ?_).trans (Nat.add_le_add_left (hpow (le_max_right _ _)) _)
    · have hx : size x ≤ size (K ^ g) := by
        simp only [size_nat]
        exact Nat.succ_le_succ (Nat.size_le_size hxlt.le)
      have h3 : size c + size (K ^ g) ≤ c₂ * (size c + P) := by
        have h4 : 1 * size c ≤ c₂ * size c := Nat.mul_le_mul_right _ (by omega)
        have h5 : c₂ * 1 ≤ c₂ * P := Nat.mul_le_mul_left _ hP
        rw [Nat.mul_add]
        omega
      simp only [size_prod]
      omega
    · have h3 : c₂ * (size c + P + B) ≤ c₂ * (size c + P + B) ^ c₂ :=
        Nat.mul_le_mul_left _ (Nat.le_self_pow (by omega) _)
      have h4 : 5 * size c + 5 * size (K ^ g) + 20 ≤ c₂ * (size c + P + B) := by
        have h5 : 5 * size c ≤ c₂ * size c := Nat.mul_le_mul_right _ (by omega)
        have h6 : c₂ * 1 ≤ c₂ * P := Nat.mul_le_mul_left _ hP
        rw [Nat.mul_add, Nat.mul_add]
        omega
      omega
  · -- «the bound follows»
    refine (hA1 P B τ N.U TE (2 * K ^ g + 1 + TE) hP hN.τ_pos hU hTE le_rfl).trans ?_
    have hY : (1 : ℝ) ≤ (P : ℝ) + B := by exact_mod_cast (by omega : 1 ≤ P + B)
    have hAm : (A1 : ℝ) ≤ ((max A1 A2 : ℕ) : ℝ) := by exact_mod_cast le_max_left _ _
    have hYp : ((P : ℝ) + B) ^ A1 ≤ ((P : ℝ) + B) ^ (max A1 A2) := pow_le_pow_right₀ hY (le_max_left _ _)
    gcongr

/-- **Lemma 1 for the algorithm of its proof** (`StLemGrouping`), from the three steps «a good
grouping exists … fix the first good one», «one entry costs …» and «so the value equals Z». -/
theorem stLemGrouping_of (hS : StSearch) (hT : StTable) (hV : StValue) : StLemGrouping := fun K _ _ hK h0 h =>
  netAlg_correct hT hV hK (by
    have : K ≤ K ^ 8 := Nat.le_self_pow (by norm_num) K
    omega) h0 h fun C _ Np c N P B τ S hN => hS K hK C Np c N P B τ S hN

/-- The exponent of `Correct` with ε = e and b = e + 2 is the exponent of Lemma 1: e·U + (e + 2)·gP/K =
e(U + gP/K) + 2gP/K. -/
theorem exponent_eq (e U g P K : ℝ) : e * U + (e + 2) * (g * P) / K = e * (U + g * P / K) + 2 * (g * P) / K := by ring

end Eight.ViaGrouping
