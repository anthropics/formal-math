/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Eight.ViaGrouping.Defs
import Mathlib.Tactic

/-! # From a network in the form of proof/networks/Paper to Definition 2 as printed

The networks that Sections 5 and 6 (and the corollaries of Section 7) build are written in the form
of proof/networks/Paper (proof/networks/Paper/SecNetworks_Networks.lean): every string of P_a bits
is a setting, Ψ_{a,b} is defined as Σ_θ f_{a,b}·f_{b,a}, values are «at most 2^B». Lemma 1 along the
printed proof
(`Correct`, proof/networks/Eight/ViaGrouping/Defs.lean) speaks of networks as Definition 2 prints
them. This file passes from the first form to the second, given a procedure Q that computes Ψ_{a,b}
on settings.
* `isNetworkP_ofNetwork`: such a network, with Q, is a network in the sense of Definition 2 with
  parameters P, B + 1, τ; `value_ofNetwork`, `U_ofNetwork`: same value, same total; `stBridge` puts
  the three together.
* `Correct.absorb`: the constant of the bound of Lemma 1 takes up the passage from B to B + 1.
* `keeps_ofProcs`, `keepsP_ofProcs`: the procedures have polynomial-time steps if those of
  proof/networks/Paper and Q have, and give P in unary if Pf does.
Nothing here is a statement of the paper: the file joins two renderings of Definition 2. -/

public section

namespace Eight.ViaGrouping

open Groundwork Groundwork.Prog Finset Stepped Eight.SecNetworks

variable {g : ℕ}

/-- The value is the same: both are Σ_z ∏_a W_a(z_a) ∏_{a<b} Ψ_{a,b}(z_a, z_b) with the same S, W,
Ψ. -/
theorem value_ofNetwork (N : Paper.Network (Fin g) (List Bool) (List Bool)) (n : Fin g → ℕ) : (ofNetwork N n).value = N.value := rfl

/-- The total U is the same. -/
theorem U_ofNetwork (N : Paper.Network (Fin g) (List Bool) (List Bool)) (n : Fin g → ℕ) : (ofNetwork N n).U = N.U := rfl

/-- The Ψ that proof/networks/Paper defines from the factors is symmetric: Ψ_{b,a}(z', z) =
Ψ_{a,b}(z, z'). -/
theorem Ψ_swap_ofPaperNetwork (N : Paper.Network (Fin g) (List Bool) (List Bool)) (a b : Fin g) (z z' : List Bool) : N.Ψ b a z' z = N.Ψ a b z z' := by
  unfold Groundwork.Network.Ψ Groundwork.Network.lab
  rw [min_comm, max_comm]
  exact Finset.sum_congr rfl fun θ _ => mul_comm _ _

/-- P_a ≤ P for a network of proof/networks/Paper: it has 2^{P_a} settings at a, and at most 2^P. -/
theorem n_le_ofPaperNetwork {C : Type} {Np : Paper.NetworkProcedures C} {c : C} {N : Paper.Network (Fin g) (List Bool) (List Bool)} {P B τ S : ℕ}
    (h : Paper.IsNetwork Np c N P B τ S) (a : Fin g) : Np.n c a ≤ P := by
  have h1 := h.sized.card_S a
  rw [h.presented.S_eq a, card_words] at h1
  exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h1

/-- Definition 2, all but (iii), with B + 1 for B: «at most 2^B» gives «below 2^{B+1}». -/
theorem is_ofNetwork {C : Type} {Np : Paper.NetworkProcedures C} {c : C} {N : Paper.Network (Fin g) (List Bool) (List Bool)} {P B τ S : ℕ}
    (hP : 1 ≤ P) (h : Paper.IsNetwork Np c N P B τ S) : (ofNetwork N fun a => Np.n c a).Is P (B + 1) := by
  have hlt : ∀ x : ℤ, |x| ≤ 2 ^ B → |x| < 2 ^ (B + 1) := fun x hx => by
    have : (0 : ℤ) < 2 ^ B := by positivity
    rw [pow_succ]
    omega
  exact
  { P_pos := hP
    B_pos := by omega
    len_S := fun a z hz => by
      have hz' : z ∈ N.S a := hz
      rw [h.presented.S_eq a] at hz'
      exact mem_words.1 hz'
    len_le := n_le_ofPaperNetwork h
    Ψ_symm := fun a b _ z _ z' _ => Ψ_swap_ofPaperNetwork N a b z z'
    c_symm := h.sized.c_symm
    fact := fun a b hab z _ z' _ => by
      change N.Ψ a b z z' = ∑ θ ∈ words (N.c a b), N.f a b z θ * N.f b a z' θ
      rw [Paper.Psi_def, h.presented.lab_eq a b hab, h.presented.c_eq a b hab]
    i := h.sized.sum_c
    ii_W := fun a z _ => hlt _ (h.sized.abs_W a z)
    ii_Ψ := fun a b hab z _ z' _ => hlt _ (h.sized.abs_Ψ a b z z' hab)
    ii_f := fun a b _ z _ θ _ => hlt _ (h.sized.abs_f a b z θ) }

/-- **The bridge.** A network of proof/networks/Paper with parameters P, B, τ, together with a
procedure Q that computes its Ψ on settings within τ steps, is a network in the sense of Definition
2 (without the part of condition (iii) that gives B to the algorithm as input) with parameters P, B +
1, τ.
The test for membership forgets the query and says yes in one step, on states of size 2; hence S + 2. -/
theorem isNetworkP_ofNetwork {C : Type} [HasSize C] {Np : Paper.NetworkProcedures C} {Pf : C → ℕ} {Q : Stepped (C × PsiQ) ℤ} {c : C}
    {N : Paper.Network (Fin g) (List Bool) (List Bool)} {P B τ S : ℕ} (hP : 1 ≤ P) (hτ : 1 ≤ τ) (h : Paper.IsNetwork Np c N P B τ S) (hPf : Pf c = P)
    (hQ : ∀ a b : Fin g, a ≠ b → ∀ z ∈ N.S a, ∀ z' ∈ N.S b, Q.Runs (c, ((a.val, b.val), (z, z'))) τ S (N.Ψ a b z z')) :
    IsNetworkP (ofProcs Np Pf Q) c (ofNetwork N fun a => Np.n c a) P (B + 1) τ (S + 2) where
  is := is_ofNetwork hP h
  τ_pos := hτ
  given :=
  { P_eq := hPf
    len_eq := fun _ => rfl
    cap_eq := fun a b hab => (h.presented.c_eq a b hab).symm
    mem_runs := fun a z hz => by
      have hz' : z.length = Np.n c a := hz
      have hmem : decide (z ∈ (ofNetwork N fun a => Np.n c a).S a) = true := by
        change decide (z ∈ N.S a) = true
        rw [h.presented.S_eq a]
        exact decide_eq_true (mem_words.2 hz')
      rw [hmem]
      refine (mapIn_runs (f := fun _ : C × WQ => ()) (a := (c, (a.val, z))) (const_runs true ())).mono hτ ?_
      simp only [size_unit, size_bool]
      omega
    W_runs := fun a z hz => by
      have hz' : z ∈ N.S a := hz
      rw [h.presented.S_eq a] at hz'
      exact (h.presented.W_runs a z (mem_words.1 hz')).mono le_rfl (by omega)
    Ψ_runs := fun a b hab z hz z' hz' => (hQ a b hab z hz z' hz').mono le_rfl (by omega)
    f_runs := fun a b hab z hz θ hθ => by
      have hz' : z ∈ N.S a := hz
      rw [h.presented.S_eq a] at hz'
      have hθ' : θ ∈ words (N.c a b) := hθ
      rw [h.presented.c_eq a b hab] at hθ'
      exact (h.presented.f_runs a b z θ hab (mem_words.1 hz') (mem_words.1 hθ')).mono le_rfl (by omega) }

/-- **The bridge** (`StBridge` of proof/networks/Eight/ViaGrouping/Defs.lean): a network of
proof/networks/Paper with parameters P, B, τ, together with a procedure that computes its Ψ within τ
steps, is a network in the sense of Definition 2 (without the part of condition (iii) that gives B
to the algorithm as input), with parameters P, B + 1, τ, and has the same value
and the same total. -/
theorem stBridge : StBridge := fun _ _ _ _ _ _ _ N _ _ _ _ hP hτ h hPf hQ => ⟨isNetworkP_ofNetwork hP hτ h hPf hQ, value_ofNetwork N _, U_ofNetwork N _⟩

/-- The bound of Lemma 1 with B + 1 and S + 2 taken up by the constant: if NA has the bound of Lemma
1 (`Correct`), then there is a constant A such that NA outputs the value of every network with
parameters P, B + 1, τ, given on states of size at most S + 2,
within A·2^{εU + b·gP/K}·(P + B)^A·τ steps, on states of size at most S + A·(size c + P + B)^A; by P +
B + 1 ≤ 2(P + B). -/
theorem Correct.absorb {NA : NetAlg} {K : ℕ} {ε b : ℝ} (h : Correct NA g K ε b) :
    ∃ A : ℕ, ∀ (C : Type) [HasSize C] (Np : Procs C) (c : C) (N : Net g) (P B t S : ℕ), IsNetworkP Np c N P (B + 1) t (S + 2) →
      ∃ T : ℕ, (NA.app Np).Runs c T (S + A * (size c + P + B) ^ A) N.value ∧
        (T : ℝ) ≤ A * (2 : ℝ) ^ (ε * (N.U : ℝ) + b * ((g : ℝ) * P) / K) * ((P : ℝ) + B) ^ A * t := by
  obtain ⟨A₀, hA₀⟩ := h
  obtain ⟨A, hA⟩ : ∃ A : ℕ, A = A₀ * 2 ^ A₀ + 2 := ⟨_, rfl⟩
  have hA₀A : A₀ ≤ A := by
    have : A₀ * 1 ≤ A₀ * 2 ^ A₀ := Nat.mul_le_mul_left _ Nat.one_le_two_pow
    omega
  refine ⟨A, fun C _ Np c N P B t S hN => ?_⟩
  have hP : 1 ≤ P := hN.is.P_pos
  obtain ⟨T, hrun, hT⟩ := hA₀ C Np c N P (B + 1) t _ hN
  refine ⟨T, hrun.mono le_rfl ?_, ?_⟩
  · -- the sizes of the states
    obtain ⟨Z, hZ⟩ : ∃ Z : ℕ, Z = size c + P + B := ⟨_, rfl⟩
    have e0 : size c + P + (B + 1) = Z + 1 := by omega
    rw [e0, ← hZ]
    have hZ1 : 1 ≤ Z := by omega
    have h1 : (Z + 1) ^ A₀ ≤ 2 ^ A₀ * Z ^ A := by
      calc (Z + 1) ^ A₀ ≤ (2 * Z) ^ A₀ := Nat.pow_le_pow_left (by omega) _
        _ = 2 ^ A₀ * Z ^ A₀ := mul_pow _ _ _
        _ ≤ 2 ^ A₀ * Z ^ A := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hZ1 hA₀A)
    have h2 : 1 ≤ Z ^ A := Nat.one_le_pow _ _ hZ1
    have h5 : A₀ * (Z + 1) ^ A₀ ≤ A₀ * (2 ^ A₀ * Z ^ A) := Nat.mul_le_mul_left _ h1
    have e : A * Z ^ A = A₀ * (2 ^ A₀ * Z ^ A) + 2 * Z ^ A := by rw [hA]; ring
    omega
  · -- the number of steps
    obtain ⟨X, hX⟩ : ∃ X : ℝ, X = (2 : ℝ) ^ (ε * (N.U : ℝ) + b * ((g : ℝ) * P) / K) := ⟨_, rfl⟩
    rw [← hX] at hT ⊢
    have hX0 : 0 ≤ X := hX ▸ (Real.rpow_pos_of_pos (by norm_num) _).le
    have hY : (1 : ℝ) ≤ (P : ℝ) + B := by exact_mod_cast (by omega : 1 ≤ P + B)
    have hY2 : (P : ℝ) + ((B + 1 : ℕ) : ℝ) ≤ 2 * ((P : ℝ) + B) := by push_cast; linarith
    have hY0 : (0 : ℝ) ≤ (P : ℝ) + ((B + 1 : ℕ) : ℝ) := by positivity
    have hYp : ((P : ℝ) + B) ^ A₀ ≤ ((P : ℝ) + B) ^ A := pow_le_pow_right₀ hY hA₀A
    have hAC : (A₀ : ℝ) * 2 ^ A₀ ≤ A := by exact_mod_cast (by omega : A₀ * 2 ^ A₀ ≤ A)
    calc (T : ℝ) ≤ A₀ * X * ((P : ℝ) + ((B + 1 : ℕ) : ℝ)) ^ A₀ * t := hT
      _ ≤ A₀ * X * (2 * ((P : ℝ) + B)) ^ A₀ * t := by gcongr
      _ = A₀ * 2 ^ A₀ * X * ((P : ℝ) + B) ^ A₀ * t := by rw [mul_pow]; ring
      _ ≤ A * X * ((P : ℝ) + B) ^ A * t := by gcongr

/-- The procedures `ofProcs Np Pf Q` have polynomial-time steps (and give P_a and c_{a,b} in unary)
if those of proof/networks/Paper have and Q has. -/
theorem keeps_ofProcs {C : Type} [HasSize C] [Enc C] [Carried C] {Np : PNet C} (Pf : C → ℕ) {Q : Stepped (C × PsiQ) ℤ} (h : Np.Keeps) (hQ : Nonempty (IsPolyT Q)) :
    (ofProcs Np Pf Q).Keeps :=
  haveI := IsPolyT.const (α := Unit) true
  ⟨h.n, h.cap, ⟨IsPolyT.mapIn (M := (const true : Stepped Unit Bool)) (f := fun _ : C × WQ => ()) (by fun_prop)⟩, h.W, hQ, h.f⟩

/-- The same, with P given in unary: what an algorithm for networks asks of its procedures
(`AlgKeeps`). -/
theorem keepsP_ofProcs {C : Type} [HasSize C] [Enc C] [Carried C] {Np : PNet C} {Pf : C → ℕ} {Q : Stepped (C × PsiQ) ℤ} (h : Np.Keeps) (hP : Unary Pf) (hQ : Nonempty (IsPolyT Q)) :
    KeepsP (ofProcs Np Pf Q) := ⟨keeps_ofProcs Pf h hQ, hP⟩

end Eight.ViaGrouping
