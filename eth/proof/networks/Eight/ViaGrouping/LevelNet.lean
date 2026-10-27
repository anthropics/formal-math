/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Eight.ViaGrouping.LevelDefs
public import Eight.ViaGrouping.Bridge
public import Eight.SecLevel_GridWords
public import StepMachines.Prog.GridDefs
import Mathlib.Tactic

/-! # Proof of Proposition 3: «Both networks satisfy Definition 2»

The sentence of the paper (Section 5, proof of Proposition 3, paragraph «Two networks for each ι»):
«Both networks satisfy Definition 2 with P = g³λ (so gP = N), with B₁ = gB + g²λ + 1 in the role of
B, and with τ = poly(B + λ): indeed
∑_{a' ∈ [g]∖{a}} c_{a,a'} ≤ g³λ, |W_a| < 2^{gB}, and Ψ_{a,a'} and the functions of its factorization
are products of indicators and of g(g−1)/2 numbers of absolute value at most 2^t ≤ 2^λ.»
Here it is a statement about the objects that Algorithm 1 runs: the network `levelNetP g tr λ y W`
(tr = false: rows, tr = true: columns; y is the number of ι in base t + 1; W are the tables of the
clique on g² nodes), which is `Eight.Level.netOfι` read as
the data of Definition 2 (proof/networks/Eight/ViaGrouping/LevelDefs.lean), and the procedures
`levelProcs g tr psi lam R` that CLIQUE hands to NETWORK, for any function psi that computes
Ψ_{a,a'} on settings (`StPsiOK`). `levelNetP_isNetworkP_of` has gB + g²t + 1, t = ⌈λ/3⌉, in the role
of B, which is what the reason given in the sentence yields; `levelNetP_isNetworkP_printed_of` has
the printed B₁. The paragraph «Cost» of the proof applies Lemma 1 to `levelNetP` by the first.
The parts: (i), (ii) and the number of settings are in proof/networks/Eight/SecLevel_GridWords.lean
(`netOfι_sized_t`); that the procedures for W_a and f_{a,a'} present the networks is a hypothesis
here (`Eight.Level.StPresents`); the run of
the procedure for Ψ_{a,a'} is `lvlPsi_netOfι_runs` below; the passage to the printed form of
Definition 2 is in proof/networks/Eight/ViaGrouping/Bridge.lean.

Different from the paper: τ is explicit, a·(B + λ)^a·t₀ with a constant a that depends on g only and
t₀ the cost of a query to the tables of the clique; the tables satisfy |W_w| ≤ 2^B where the paper
has < 2^B; a bound on the sizes of the states is
carried along; «B is given» is not part of the statement (`IsNetworkP`); a setting of a row has g³λ
bits, one dummy string of λ bits per grid point for the grid point itself, where the paper encodes
it in g(g² − 1)λ bits, so P_a = P = g³λ (proof/networks/Eight/SecLevel_GridWords.lean). -/

@[expose] public section

namespace Eight.ViaGrouping

open Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Stepped Finset Eight.SecNetworks Eight.Level

/-- In Definition 2 without (iii), the bound B on the values may be raised. -/
theorem is_mono_B {g P B B' : ℕ} {N : Net g} (h : N.Is P B) (hB : B ≤ B') : N.Is P B' :=
  have hp : (2 : ℤ) ^ B ≤ 2 ^ B' := pow_le_pow_right₀ (by norm_num) hB
  { h with
    B_pos := h.B_pos.trans hB
    ii_W := fun a z hz => (h.ii_W a z hz).trans_le hp
    ii_Ψ := fun a b hab z hz z' hz' => (h.ii_Ψ a b hab z hz z' hz').trans_le hp
    ii_f := fun a b hab z hz θ hθ => (h.ii_f a b hab z hz θ hθ).trans_le hp }

/-- The same for Definition 2 with its procedures. -/
theorem isNetworkP_mono_B {C : Type} {g : ℕ} {Np : Procs C} {c : C} {N : Net g} {P B B' τ S : ℕ} (h : IsNetworkP Np c N P B τ S) (hB : B ≤ B') : IsNetworkP Np c N P B' τ S :=
  ⟨is_mono_B h.is hB, h.τ_pos, h.given⟩

/-- «The value is Z_ι», for the network in the printed form. -/
theorem value_levelNetP {lam : ℕ} (hlam : 1 ≤ lam) (g : ℕ) (tr : Bool) (y : ℕ) (Rm : Inst (Fin (g * g)) (List Bool)) :
    (levelNetP g tr lam y Rm).value = Zι (gridR0 g g lam Rm) (Level.patOf g lam y) := value_netOfι hlam g tr y Rm

/-- The total is the number that the algorithm compares (`useRowP`). -/
theorem U_levelNetP (g : ℕ) (tr : Bool) (lam y : ℕ) (Rm : Inst (Fin (g * g)) (List Bool)) : (levelNetP g tr lam y Rm).U = totalG eightF g g tr 0 lam y := U_netOfι g tr lam y Rm

/-! ## The procedure for Ψ -/

/-- A number, depending on g only, for the size of a query for Ψ and of its answer. -/
def lvlPsiSize (g : ℕ) : ℕ := 2 * nRect g + 2 * size g + 4 * g ^ 3 + g + g ^ 2 + 10

/-- A plain function run as a procedure for Ψ: one step; the states are the query and the answer. -/
theorem lvlPsi_runs {C : Type} [HasSize C] (psi : ℕ → ℕ → PsiQ → ℤ) (lam : C → ℕ) (c : C) {y g a b L Bv : ℕ} {z z' : List Bool} {v : ℤ}
    (hv : psi (lam c) y ((a, b), (z, z')) = v) (ha : a < g) (hb : b < g) (hz : z.length = L) (hz' : z'.length = L) (hB : |v| ≤ 2 ^ Bv) :
    (ofFun fun x : (C × ℕ) × PsiQ => psi (lam x.1.1) x.1.2 x.2).Runs ((c, y), ((a, b), (z, z'))) 1 (size c + size y + 2 * size g + 4 * L + Bv + 8) v := by
  have h := ofFun_runs (fun x : (C × ℕ) × PsiQ => psi (lam x.1.1) x.1.2 x.2) ((c, y), ((a, b), (z, z')))
  simp only [hv] at h
  refine h.mono le_rfl ?_
  have h1 : size a ≤ size g := size_nat_mono ha.le
  have h2 : size b ≤ size g := size_nat_mono hb.le
  have h3 : size v ≤ Bv + 2 := by
    rw [size_int]
    have h4 : v.natAbs ≤ 2 ^ Bv := by
      rw [Int.abs_eq_natAbs] at hB
      exact_mod_cast hB
    have := Nat.size_le_size h4
    rw [Nat.size_pow] at this
    omega
  simp only [size_prod, size_bits, hz, hz']
  omega

/-- The sizes of a query for Ψ and of its answer add up to at most `lvlPsiSize g`·(size of c + B +
λ). -/
theorem lvlPsiSize_le (g sc B n sy B' : ℕ) (hn : 1 ≤ n) (hy : sy ≤ 2 * nRect g * n + 1) (hB' : B' ≤ g * B + g ^ 2 * n) :
    sc + sy + 2 * size g + 4 * (g ^ 3 * n) + B' + 8 ≤ lvlPsiSize g * (sc + B + n) := by
  have h1 : lvlPsiSize g * (sc + B + n) = 2 * nRect g * n + 2 * size g * n + 4 * (g ^ 3 * n) + g * B + g ^ 2 * n + 10 * n + 10 * sc
      + ((2 * nRect g + 2 * size g + 4 * g ^ 3 + g + g ^ 2) * sc + (2 * nRect g + 2 * size g + 4 * g ^ 3 + g ^ 2 + 10) * B + g * n) := by
    unfold lvlPsiSize
    ring
  have h2 : 2 * size g ≤ 2 * size g * n := Nat.le_mul_of_pos_right _ hn
  omega

/-- Definition 2(iii) for Ψ: the function for Ψ, run as a procedure, answers every query on settings
of the network of ι in one step, on states of size at most `lvlPsiSize g`·(size of c + B + λ). -/
theorem lvlPsi_netOfι_runs {C : Type} [HasSize C] {g : ℕ} {tr : Bool} {psi : ℕ → ℕ → PsiQ → ℤ} (hΨ : StPsiOK g tr psi) (lam : C → ℕ) (c : C) {y B : ℕ}
    {Rm : Inst (Fin (g * g)) (List Bool)} (hl : 1 ≤ lam c) (hy : y < (tOf (lam c) + 1) ^ nRect g) (hR : BoundedInst (lam c) B Rm) (a b : Fin (nParts g g tr)) (hab : a ≠ b)
    {z z' : List Bool} (hz : z ∈ (netOfι g tr (lam c) y Rm).S a) (hz' : z' ∈ (netOfι g tr (lam c) y Rm).S b) :
    (ofFun fun x : (C × ℕ) × PsiQ => psi (lam x.1.1) x.1.2 x.2).Runs ((c, y), ((a.val, b.val), (z, z'))) 1 (lvlPsiSize g * (size c + B + lam c))
      ((netOfι g tr (lam c) y Rm).Ψ a b z z') := by
  have hg : nParts g g tr = g := by cases tr <;> rfl
  have htn : tOf (lam c) ≤ lam c := by unfold tOf; omega
  have hrun := lvlPsi_runs psi lam c (hΨ (lam c) y Rm hl hy a b hab z hz z' hz') (lt_of_lt_of_eq a.2 hg) (lt_of_lt_of_eq b.2 hg)
    (mem_words.1 (netOfι_S g tr (lam c) y Rm a ▸ hz)) (mem_words.1 (netOfι_S g tr (lam c) y Rm b ▸ hz')) ((netOfι_sized_t hl g tr y hR).abs_Ψ a b z z' hab)
  refine hrun.mono le_rfl (lvlPsiSize_le g (size c) B (lam c) (size y) _ hl ?_ (Nat.add_le_add_left (Nat.mul_le_mul_left _ htn) _))
  have h1 : y < 2 ^ ((tOf (lam c) + 1) * nRect g) := by
    refine hy.trans_le ?_
    rw [pow_mul]
    exact Nat.pow_le_pow_left Nat.lt_two_pow_self.le _
  have h2 := Nat.size_le.2 h1
  have h3 : (tOf (lam c) + 1) * nRect g ≤ 2 * nRect g * lam c := by
    calc (tOf (lam c) + 1) * nRect g ≤ 2 * lam c * nRect g := Nat.mul_le_mul_right _ (by omega)
      _ = 2 * nRect g * lam c := by ring
  rw [size_nat]
  omega

/-! ## The sentence -/

/-- «Both networks satisfy Definition 2 with P = g³λ …», with gB + g²t + 1, t = ⌈λ/3⌉, in the role
of B. For every g ≥ 1 there is a constant a ≥ 1 such that, for every function psi that computes
Ψ_{a,a'} on settings, λ = lam c ≥ 1, every y < (t + 1)^{|ℛ|}, and tables W
of the clique on g² nodes with |W_w| ≤ 2^B that the procedure R answers within t₀ ≥ 1 steps on
states of size at most S: the procedures that CLIQUE hands to NETWORK give, in the context (c, y),
the network `levelNetP g tr λ y W`, and it is a network in the
sense of Definition 2 with the parameters P = g³λ, gB + g²t + 1 and τ = a·(B + λ)^a·t₀. -/
theorem levelNetP_isNetworkP_of (hPr : StPresents) (g : ℕ) (hg : 1 ≤ g) : ∃ a : ℕ, 1 ≤ a ∧ ∀ (tr : Bool) (psi : ℕ → ℕ → PsiQ → ℤ), StPsiOK g tr psi →
    ∀ (C : Type) [HasSize C] (lam : C → ℕ) (R : Stepped (C × IQ) ℤ) (c : C) (B t S : ℕ)
    (Rm : Inst (Fin (g * g)) (List Bool)) (y : ℕ), 1 ≤ lam c → 1 ≤ t → y < (tOf (lam c) + 1) ^ nRect g → ServesInst R c (lam c) B t S Rm →
    IsNetworkP (levelProcs g tr psi lam R) (c, y) (levelNetP g tr (lam c) y Rm) (g ^ 3 * lam c) (g * B + g ^ 2 * tOf (lam c) + 1)
      (a * (B + lam c) ^ a * t) (S + a * (size c + B + lam c) ^ a + 2) := by
  obtain ⟨ar, har⟩ := hPr g false
  obtain ⟨ac, hac⟩ := hPr g true
  obtain ⟨a, ha⟩ : ∃ a, a = ar + ac + 1 + lvlPsiSize g := ⟨_, rfl⟩
  refine ⟨a, by omega, fun tr psi hΨ C _ lam R c B t S Rm y hl ht hy hR => ?_⟩
  have hmono : ∀ a' X : ℕ, a' ≤ a → 1 ≤ X → a' * X ^ a' ≤ a * X ^ a := fun a' X h1 h2 => Nat.mul_le_mul h1 (Nat.pow_le_pow_right h2 h1)
  have hP1 : 1 ≤ g ^ 3 * lam c := Nat.mul_pos (pow_pos hg 3) hl
  have ht1 : 1 ≤ a * (B + lam c) ^ a * t := Nat.mul_pos (Nat.mul_pos (by omega) (pow_pos (by omega) a)) ht
  have hBd : BoundedInst (lam c) B Rm := fun v θ h1 h2 => (hR v θ h1 h2).2
  have hpres : (levelNet g tr lam R).Presents (c, y) (netOfι g tr (lam c) y Rm) (a * (B + lam c) ^ a * t) (S + a * (size c + B + lam c) ^ a) := by
    cases tr
    · exact (har C lam R c B t S Rm y hl ht hy hR).mono (Nat.mul_le_mul_right _ (hmono ar _ (by omega) (by omega))) (Nat.add_le_add_left (hmono ar _ (by omega) (by omega)) _)
    · exact (hac C lam R c B t S Rm y hl ht hy hR).mono (Nat.mul_le_mul_right _ (hmono ac _ (by omega) (by omega))) (Nat.add_le_add_left (hmono ac _ (by omega) (by omega)) _)
  have hSΨ : lvlPsiSize g * (size c + B + lam c) ≤ S + a * (size c + B + lam c) ^ a :=
    le_trans (Nat.mul_le_mul (by omega) (Nat.le_self_pow (by omega) _)) (Nat.le_add_left _ _)
  have h := isNetworkP_ofNetwork (Np := levelNet g tr lam R) (Pf := fun c : C × ℕ => g ^ 3 * lam c.1) (Q := ofFun fun x : (C × ℕ) × PsiQ => psi (lam x.1.1) x.1.2 x.2)
    hP1 ht1 ⟨netOfι_sized_t hl g tr y hBd, hpres⟩ rfl
    fun a b hab z hz z' hz' => (lvlPsi_netOfι_runs hΨ lam c hl hy hBd a b hab hz hz').mono ht1 hSΨ
  have hlen : (fun a : Fin (nParts g g tr) => (levelNet g tr lam R).n (c, y) a) = fun _ => g ^ 3 * lam c := by
    funext _
    change nMemb g g tr * (g * g) * lam c = g ^ 3 * lam c
    have : nMemb g g tr = g := by cases tr <;> rfl
    rw [this]
    ring
  rw [hlen] at h
  exact h

/-- **«Both networks satisfy Definition 2 with P = g³λ (so gP = N), with B₁ = gB + g²λ + 1 in the
role of B, and with τ = poly(B + λ)»** (proof of Proposition 3). As `levelNetP_isNetworkP_of`, with
the printed B₁; t ≤ λ. Different from the paper: τ is written
out as a·(B + λ)^a·t₀, with t₀ the cost of a query to the tables of the clique; |W_w| ≤ 2^B in place
of < 2^B; the sizes of the states are bounded too; the procedures do not give B₁; a setting of a row
has g³λ bits, one dummy string of λ bits per grid point for the grid point itself, where the paper
encodes it in g(g² − 1)λ bits, so P_a = P = g³λ (proof/networks/Eight/SecLevel_GridWords.lean). -/
theorem levelNetP_isNetworkP_printed_of (hPr : StPresents) (g : ℕ) (hg : 1 ≤ g) : ∃ a : ℕ, ∀ (tr : Bool) (psi : ℕ → ℕ → PsiQ → ℤ), StPsiOK g tr psi →
    ∀ (C : Type) [HasSize C] (lam : C → ℕ) (R : Stepped (C × IQ) ℤ) (c : C) (B t S : ℕ)
    (Rm : Inst (Fin (g * g)) (List Bool)) (y : ℕ), 1 ≤ lam c → 1 ≤ t → y < (tOf (lam c) + 1) ^ nRect g → ServesInst R c (lam c) B t S Rm →
    IsNetworkP (levelProcs g tr psi lam R) (c, y) (levelNetP g tr (lam c) y Rm) (g ^ 3 * lam c) (g * B + g ^ 2 * lam c + 1)
      (a * (B + lam c) ^ a * t) (S + a * (size c + B + lam c) ^ a + 2) := by
  obtain ⟨a, -, ha⟩ := levelNetP_isNetworkP_of hPr g hg
  refine ⟨a, fun tr psi hΨ C _ lam R c B t S Rm y hl ht hy hR => isNetworkP_mono_B (ha tr psi hΨ C lam R c B t S Rm y hl ht hy hR) ?_⟩
  have : g ^ 2 * tOf (lam c) ≤ g ^ 2 * lam c := Nat.mul_le_mul_left _ (by unfold tOf; omega)
  omega

end Eight.ViaGrouping
