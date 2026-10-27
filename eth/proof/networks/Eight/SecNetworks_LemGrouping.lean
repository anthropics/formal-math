/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Eight.SecNetworks_Defs
public import SingleBitPieces.SecNetworks_LemGrouping
public import ToTuring.Poly.Comb
import Mathlib.Tactic

/-! # Section 3 «Networks»: from a network as Definition 2 prints it to the form of proof/networks/Paper

This file passes from a network as Definition 2 prints it (file SecNetworks_Defs: sets S_a ⊆
{0,1}^{P_a}, functions W_a, Ψ_{a,b}, f_{a,b} with values below 2^B, and four procedures) to the form
of the namespace `Paper`, in two steps.
1. `Net.toPaperNetwork`: a network in the printed form gives a `Paper.Network`
   (proof/networks/Paper/SecNetworks_Networks.lean). A node's settings become all strings of P_a
   bits, and W_a and f_{a,b} are set to 0 at strings outside S_a.
   It has the same value (`value_toPaperNetwork`) and the same total U, and satisfies the size
   conditions of proof/networks/Paper with the same P and B (`sized_toPaperNetwork`).
2. `Procs.toPaperNetwork`: the procedures for it. Each first runs the membership test, and then runs
   the procedure for W_a (or f_{a,b}) or returns 0. They answer within 2τ + 1 steps
   (`presents_toPaperNetwork`) and have polynomial-time steps (`keeps_toPaperNetwork`).

`Paper.Network` has no Ψ of its own and `Paper.NetworkProcedures` no procedure for Ψ: Ψ_{a,b} is
defined from f_{a,b} and f_{b,a}, and the procedure for Ψ and the numbers P and B are not passed on.

The last section has three inequalities that the text uses, in the paper's numbers: U ≤ gP, L ≤ 2gP
and K²L ≤ K² + U + gP/K. -/

@[expose] public section

namespace Eight.SecNetworks

open Groundwork Groundwork.Prog Finset Stepped

/-! ## A procedure behind a test -/

section Gated

variable {α : Type} [HasSize α]

/-- Run the test M; if it says yes, run N on the same input; if it says no, return 0. -/
def gated (M : Stepped α Bool) (N : Stepped α ℤ) : Stepped α ℤ :=
  bind M (ite (fun p : α × Bool => p.2) (mapIn Prod.fst N) (const 0))

/-- If the test and the procedure each take at most τ steps on states of size at most S, then
`gated` takes at most 2τ + 1 steps on states of size at most S + 4 + the size of the input. The
procedure needs to work only where the test says yes. -/
theorem gated_runs {M : Stepped α Bool} {N : Stepped α ℤ} {a : α} {τ S : ℕ} {b : Bool} {v : ℤ} (hτ : 1 ≤ τ) (h : M.Runs a τ S b)
    (h' : b = true → N.Runs a τ S v) : (gated M N).Runs a (2 * τ + 1) (size a + S + 4) (if b = true then v else 0) := by
  cases b with
  | true =>
    have := bind_runs h (ite_runs_true (p := fun p : α × Bool => p.2) (N := const 0) rfl (mapIn_runs (f := Prod.fst) (a := (a, true)) (h' rfl)))
    exact this.mono (by omega) (by omega)
  | false =>
    have := bind_runs h (ite_runs_false (p := fun p : α × Bool => p.2) (M := mapIn Prod.fst N) rfl (const_runs (0 : ℤ) (a, false)))
    refine this.mono (by omega) ?_
    simp only [size_prod, size_bool, size_int, Int.natAbs_zero, Nat.size_zero]
    omega

/-- `gated` has polynomial-time steps if the test and the procedure have. -/
@[instance_reducible] def gated_isPolyT [Enc α] [Carried α] (M : Stepped α Bool) (N : Stepped α ℤ) [IsPolyT M] [IsPolyT N] : IsPolyT (gated M N) :=
  haveI := IsPolyT.mapIn (M := N) (f := (Prod.fst : α × Bool → α)) (by fun_prop)
  haveI := IsPolyT.const (α := α × Bool) (0 : ℤ)
  haveI := IsPolyT.ite (p := fun p : α × Bool => p.2) (M := mapIn Prod.fst N) (N := const 0) (by fun_prop)
  IsPolyT.bind

end Gated

/-- The size of a bit string of length n is 2n + 1. -/
theorem size_bits (w : List Bool) : size w = 2 * w.length + 1 := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    simp only [size_list, List.map_cons, List.sum_cons, size_bool, List.length_cons] at ih ⊢
    omega

/-! ## From the printed form of a network to the form of proof/networks/Paper -/

namespace Net

variable {g : ℕ} (N : Net g)

/-- The network of proof/networks/Paper (`Paper.Network`) that belongs to N: the settings of a are
all strings of P_a bits; W_a is 0 outside S_a; f_{a,b}(z, θ) is 0 unless a ≠ b, z ∈ S_a and θ has
c_{a,b} bits; θ ranges over {0,1}^{c_{a,b}}.
`Paper.Network` has no Ψ of its own: it defines Ψ_{a,b} from f_{a,b} and f_{b,a}. -/
def toPaperNetwork : Paper.Network (Fin g) (List Bool) (List Bool) where
  S a := words (N.len a)
  W a z := if z ∈ N.S a then N.W a z else 0
  Θ a b := words (N.c a b)
  f a b z θ := if a ≠ b ∧ z ∈ N.S a ∧ θ ∈ words (N.c a b) then N.f a b z θ else 0
  c := N.c

variable {N} {P B : ℕ}

/-- In the network of proof/networks/Paper, θ ranges over {0,1}^{c_{a,b}} for the pair {a, b}, in
either order. -/
theorem lab_toPaperNetwork (h : N.Is P B) (a b : Fin g) : N.toPaperNetwork.lab a b = words (N.c a b) := by
  rcases le_total a b with hab | hab
  · simp [Groundwork.Network.lab, toPaperNetwork, min_eq_left hab, max_eq_right hab]
  · simp [Groundwork.Network.lab, toPaperNetwork, min_eq_right hab, max_eq_left hab, h.c_symm a b]

/-- On S_a × S_b, the Ψ_{a,b} that proof/networks/Paper defines from the factors is the Ψ_{a,b} of
N, because (f_{a,b}, f_{b,a}) is a factorization of Ψ_{a,b} (Definition 2). -/
theorem Ψ_toPaperNetwork (h : N.Is P B) {a b : Fin g} (hab : a ≠ b) {z z' : List Bool} (hz : z ∈ N.S a) (hz' : z' ∈ N.S b) :
    N.toPaperNetwork.Ψ a b z z' = N.Ψ a b z z' := by
  rw [h.fact a b hab z hz z' hz', Groundwork.Network.Ψ, lab_toPaperNetwork h]
  refine Finset.sum_congr rfl fun θ hθ => ?_
  have hθ' : θ ∈ words (N.c b a) := h.c_symm a b ▸ hθ
  simp only [toPaperNetwork]
  rw [if_pos ⟨hab, hz, hθ⟩, if_pos ⟨hab.symm, hz', hθ'⟩]

/-- Off S_a × S_b, the Ψ_{a,b} that proof/networks/Paper defines from the factors is 0. -/
theorem Ψ_toPaperNetwork_eq_zero {a b : Fin g} {z z' : List Bool} (hz : ¬(z ∈ N.S a ∧ z' ∈ N.S b)) : N.toPaperNetwork.Ψ a b z z' = 0 := by
  rw [Groundwork.Network.Ψ]
  refine Finset.sum_eq_zero fun θ _ => ?_
  simp only [toPaperNetwork]
  by_cases h1 : z ∈ N.S a
  · rw [if_neg (c := b ≠ a ∧ _ ∧ _) fun h => hz ⟨h1, h.2.1⟩, mul_zero]
  · rw [if_neg (c := a ≠ b ∧ _ ∧ _) fun h => h1 h.2.1, zero_mul]

/-- The value Z is the same: a choice z with some z_a outside S_a contributes 0, since W_a is 0
there, and the other choices contribute what they contribute in N. -/
theorem value_toPaperNetwork (h : N.Is P B) : N.toPaperNetwork.value = N.value := by
  unfold Net.value Groundwork.Network.value
  symm
  refine Finset.sum_subset_zero_on_sdiff (Fintype.piFinset_subset _ _ fun a z hz => mem_words.2 (h.len_S a z hz)) (fun z hz => ?_) fun z hz => ?_
  · obtain ⟨a, ha⟩ : ∃ a, z a ∉ N.S a := by
      by_contra hcon
      exact (Finset.mem_sdiff.1 hz).2 (Fintype.mem_piFinset.2 fun a => by_contra fun ha => hcon ⟨a, ha⟩)
    rw [Finset.prod_eq_zero (Finset.mem_univ a) (by simp only [toPaperNetwork]; rw [if_neg ha]), zero_mul]
  · have hz' := Fintype.mem_piFinset.1 hz
    congr 1
    · exact Finset.prod_congr rfl fun a _ => by simp only [toPaperNetwork]; rw [if_pos (hz' a)]
    · refine Finset.prod_congr rfl fun p hp => ?_
      have hlt : p.1 < p.2 := (Finset.mem_filter.1 hp).2
      exact (Ψ_toPaperNetwork h hlt.ne (hz' _) (hz' _)).symm

/-- The network of proof/networks/Paper satisfies the size conditions of proof/networks/Paper with
the same P and B: |S_a| ≤ 2^P, c symmetric, (i), 2^{c_{a,b}} strings θ, and all values at most 2^B
in absolute value («below 2^B» gives «at most 2^B»). -/
theorem sized_toPaperNetwork (h : N.Is P B) : N.toPaperNetwork.Sized P B where
  card_S a := by
    change #(words (N.len a)) ≤ _
    rw [card_words]
    exact Nat.pow_le_pow_right (by norm_num) (h.len_le a)
  c_symm := h.c_symm
  sum_c := h.i
  card_lab a b _ := by
    rw [lab_toPaperNetwork h, card_words]
    exact le_rfl
  abs_W a z := by
    simp only [toPaperNetwork]
    split_ifs with hz
    · exact (h.ii_W a z hz).le
    · simp
  abs_f a b z θ := by
    simp only [toPaperNetwork]
    split_ifs with hz
    · exact (h.ii_f a b hz.1 z hz.2.1 θ hz.2.2).le
    · simp
  abs_Ψ a b z z' hab := by
    by_cases hz : z ∈ N.S a ∧ z' ∈ N.S b
    · rw [Ψ_toPaperNetwork h hab hz.1 hz.2]
      exact (h.ii_Ψ a b hab z hz.1 z' hz.2).le
    · rw [Ψ_toPaperNetwork_eq_zero hz]
      simp

/-- c_{a,b} ≤ P, by (i). -/
theorem c_le (h : N.Is P B) {a b : Fin g} (hab : a ≠ b) : N.c a b ≤ P :=
  (Finset.single_le_sum (f := fun b => N.c a b) (fun _ _ => Nat.zero_le _) (Finset.mem_erase.2 ⟨hab.symm, Finset.mem_univ b⟩)).trans (h.i a)

end Net

/-! ## The procedures -/

/-- From a query ((a, b), (z, θ)) for a value of f to the query (a, z) for membership. -/
def memOfF {C : Type} (q : C × FQ) : C × WQ := (q.1, (q.2.1.1, q.2.2.1))

/-- The procedures of proof/networks/Paper that belong to the four procedures of Definition 2(iii).
For W_a(z): test z ∈ S_a, then run the procedure for W_a or return 0. For f_{a,b}(z, θ): test z ∈
S_a, then run the procedure for f_{a,b} or return 0.
`Paper.NetworkProcedures` has no procedure for Ψ, so the procedure for Ψ and the numbers P and B are
not passed on. -/
def Procs.toPaperNetwork {C : Type} [HasSize C] (Np : Procs C) : Paper.NetworkProcedures C where
  n := Np.len
  cap := Np.cap
  W := gated Np.mem Np.W
  f := gated (mapIn memOfF Np.mem) Np.f

/-- If the four procedures give N within τ steps on states of size at most S (Definition 2(iii)),
then the procedures of proof/networks/Paper give `N.toPaperNetwork` within 2τ + 1 steps on states of
size at most S + (size of c) + 2·(size of g) + 4P + 6. -/
theorem presents_toPaperNetwork {C : Type} [HasSize C] {Np : Procs C} {c : C} {g : ℕ} {N : Net g} {P B τ S : ℕ} (h : IsNetwork Np c N P B τ S) :
    Np.toPaperNetwork.Presents c N.toPaperNetwork (2 * τ + 1) (S + (size c + 2 * size g + 4 * P + 6)) where
  S_eq a := by
    change words (N.len a) = words (Np.len c a)
    rw [h.given.len_eq]
  c_eq a b hab := (h.given.cap_eq a b hab).symm
  lab_eq a b hab := by
    rw [Net.lab_toPaperNetwork h.is]
    change _ = words (Np.cap c a b)
    rw [h.given.cap_eq a b hab]
  W_runs a z hz := by
    have hz' : z.length = N.len a := hz.trans (h.given.len_eq a)
    have hrun := gated_runs h.τ_pos (h.given.mem_runs a z hz') (v := N.W a z) fun hb => h.given.W_runs a z (of_decide_eq_true hb)
    have hv : (if decide (z ∈ N.S a) = true then N.W a z else 0) = N.toPaperNetwork.W a z := by
      simp only [Net.toPaperNetwork, decide_eq_true_eq]
    rw [hv] at hrun
    refine hrun.mono le_rfl ?_
    have h1 : size a.val ≤ size g := by
      simp only [size_nat]
      exact Nat.succ_le_succ (Nat.size_le_size a.2.le)
    have h2 := h.is.len_le a
    simp only [size_prod, size_bits, hz']
    omega
  f_runs a b z θ hab hz hθ := by
    have hz' : z.length = N.len a := hz.trans (h.given.len_eq a)
    have hθ' : θ.length = N.c a b := hθ.trans (h.given.cap_eq a b hab)
    have hrun := gated_runs (M := mapIn memOfF Np.mem) (a := (c, ((a.val, b.val), (z, θ)))) h.τ_pos (mapIn_runs (h.given.mem_runs a z hz'))
      (v := N.f a b z θ) fun hb => h.given.f_runs a b hab z (of_decide_eq_true hb) θ (mem_words.2 hθ')
    have hv : (if decide (z ∈ N.S a) = true then N.f a b z θ else 0) = N.toPaperNetwork.f a b z θ := by
      simp only [Net.toPaperNetwork, decide_eq_true_eq, mem_words, hθ', hab, ne_eq, not_false_eq_true, true_and, and_true]
    rw [hv] at hrun
    refine hrun.mono le_rfl ?_
    have h1 : size a.val ≤ size g := by
      simp only [size_nat]
      exact Nat.succ_le_succ (Nat.size_le_size a.2.le)
    have h1' : size b.val ≤ size g := by
      simp only [size_nat]
      exact Nat.succ_le_succ (Nat.size_le_size b.2.le)
    have h2 := h.is.len_le a
    have h3 := Net.c_le h.is hab
    simp only [size_prod, size_bits, hz', hθ']
    omega

/-- The procedures of proof/networks/Paper have polynomial-time steps if those of Definition 2(iii)
have. The certificate for the procedure for Ψ is not used. -/
theorem keeps_toPaperNetwork {C : Type} [HasSize C] [Enc C] [Carried C] {Np : Procs C} (h : Np.Keeps) : Np.toPaperNetwork.Keeps := by
  obtain ⟨hm⟩ := h.mem
  obtain ⟨hW⟩ := h.W
  obtain ⟨hf⟩ := h.f
  have := IsPolyT.mapIn (M := Np.mem) (f := (memOfF : C × FQ → C × WQ)) (by unfold memOfF; fun_prop)
  exact ⟨h.len, h.cap, ⟨gated_isPolyT _ _⟩, ⟨gated_isPolyT _ _⟩⟩

/-! ## Three inequalities of the text, in the paper's numbers -/

/-- «U ≤ |J|·P by (i)» (after Definition 2). -/
theorem U_le {g P B : ℕ} {N : Net g} (h : N.Is P B) : N.U ≤ g * P := by
  unfold Net.U
  calc ∑ a, ∑ b ∈ univ.erase a, N.c a b ≤ ∑ _a : Fin g, P := Finset.sum_le_sum fun a _ => h.i a
    _ = g * P := by simp

/-- «K²L ≤ K² + U + gP/K» (end of the proof of Lemma 1), multiplied by K, for L = max{1, ⌊(U +
gP/K)/K²⌋}. -/
theorem K2L_le (K g U P : ℕ) : K ^ 3 * Paper.groupedLength K g U P ≤ K ^ 3 + K * U + g * P := Paper.groupedLength_le K g U P

/-- «L ≤ 2gP» (end of the proof of Lemma 1), for L = max{1, ⌊(U + gP/K)/K²⌋} and U ≤ gP. -/
theorem L_le {K g U P : ℕ} (hK : 1 ≤ K) (hg : 1 ≤ g) (hP : 1 ≤ P) (hU : U ≤ g * P) : Paper.groupedLength K g U P ≤ 2 * (g * P) := by
  have hgP : 1 ≤ g * P := Nat.mul_pos hg hP
  rw [Paper.groupedLength_def]
  refine max_le (by omega) ?_
  have hK3 : 0 < K ^ 3 := Nat.pow_pos hK
  rw [Nat.div_le_iff_le_mul_add_pred hK3]
  have h1 : K ≤ K ^ 3 := Nat.le_self_pow (by norm_num) K
  have h2 : K * U ≤ K ^ 3 * (g * P) := Nat.mul_le_mul h1 hU
  have h3 : 1 * (g * P) ≤ K ^ 3 * (g * P) := Nat.mul_le_mul_right _ hK3
  have e : K ^ 3 * (2 * (g * P)) = K ^ 3 * (g * P) + K ^ 3 * (g * P) := by ring
  omega

end Eight.SecNetworks
