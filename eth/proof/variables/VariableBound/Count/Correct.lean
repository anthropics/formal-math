/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import VariableBound.Count.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # One sparse formula counted as in Steps 1 to 4 of Appendix D: the count is right

Proves `VariableBound.StCountD` from the statements on the parts: the parameters (`StParamSpec`,
`ParamIneq`), display (63) and the remark on the empty list of Step 1, Lemma 13 for the listed
family (`Fld.StFamD`), the search of
Step 2 (`StSearchD`), and the networks of Step 3 (`Net.StFit`, `Net.StTbMax`, `Net.StNPrMax`,
`Net.StEvXF`).

* From n ≥ 29·⌈log₂(2Δ)⌉ + 19: the computed n̄, r̄, t̄ are those of the text, and n̄ ≥ 2.
* If m ≤ n̄: β = n + 1, so M ≤ 14n; the empty list is fit for an evaluation and has X = 0.
* If m > n̄: display (61) and t̄ ≤ `tbMax`; every list with display (67) is fit for an evaluation,
  so the program computes its X, and its word fits under the pad (`len_le`); so the search finds a
  list with X = 0.
* In both cases the program computes F(𝓛), which is the number of ξ that violate no clause (display
  (63)), that is `nSat n ψ` (`card_Vof`). -/

public section

namespace VariableBound.Count

open Groundwork Groundwork.Prog PaddedDescent.F PaddedDescent.F.Mark ClauseBound.Alg ClauseBound.ParityChecks AppVariables VariableBound.Net Finset

/-! ### Assignments that violate no clause -/

/-- A clause is not violated iff one of its literals is true. -/
theorem not_vio_iff (σ : ℕ → Bool) (C : List (ℕ × Bool)) : ¬ vio σ C = true ↔ ∃ l ∈ C, σ l.1 = l.2 := by
  unfold vio
  rw [List.all_eq_true]
  simp only [not_forall, exists_prop, bne_iff_ne, ne_eq, not_not]

/-- ξ violates no clause iff it satisfies the formula. -/
theorem Vof_eq_empty_iff {n : ℕ} (ψ : Fml) (ξ : Fin n → Bool) : Vof ψ ξ = ∅ ↔ ∀ C ∈ ψ, ∃ l ∈ C, Mark.ext ξ l.1 = l.2 := by
  rw [Vof, filter_eq_empty_iff]
  constructor
  · intro H C hC
    obtain ⟨e, he, rfl⟩ := List.mem_iff_getElem.1 hC
    have h1 := H (mem_univ (⟨e, he⟩ : Fin ψ.length))
    rw [List.getD_eq_getElem _ _ he] at h1
    exact (not_vio_iff _ _).1 h1
  · intro H e _
    have h1 := H _ (List.getElem_mem e.2)
    rw [List.getD_eq_getElem _ _ e.2]
    exact (not_vio_iff _ _).2 h1

/-- The number of ξ with V(ξ) = ∅ is the number of satisfying assignments. -/
theorem card_Vof (n : ℕ) (ψ : Fml) : #{ξ : Fin n → Bool | Vof ψ ξ = ∅} = nSat n ψ := by
  unfold nSat
  exact congrArg card (filter_congr fun ξ _ => Vof_eq_empty_iff ψ ξ)

/-! ### Logarithms -/

/-- log(2Δ) ≤ ⌈log₂(2Δ)⌉, for Δ ≥ 1. -/
theorem lg_le_LD (Δ : ℕ) (hΔ : 1 ≤ Δ) : lg (2 * Δ) ≤ LD Δ := by
  have h1 : (2 * Δ : ℕ) ≤ 2 ^ LD Δ := Nat.le_pow_clog (by norm_num) _
  have h2 : (2 * Δ : ℝ) ≤ 2 ^ LD Δ := by exact_mod_cast h1
  have h3 : (0 : ℝ) < 2 * Δ := by
    have : (0 : ℝ) < Δ := by exact_mod_cast hΔ
    positivity
  unfold lg
  calc Real.logb 2 (2 * Δ) ≤ Real.logb 2 (2 ^ LD Δ) := Real.logb_le_logb_of_le (by norm_num) h3 h2
    _ = LD Δ := by rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one]

/-- (2Δ)² ≤ 2^n, if 2·⌈log₂(2Δ)⌉ ≤ n. -/
theorem sq_le (n Δ : ℕ) (h : 2 * LD Δ ≤ n) : (2 * Δ) ^ 2 ≤ 2 ^ n := by
  have h1 : 2 * Δ ≤ 2 ^ LD Δ := Nat.le_pow_clog (by norm_num) _
  calc (2 * Δ) ^ 2 ≤ (2 ^ LD Δ) ^ 2 := Nat.pow_le_pow_left h1 2
    _ = 2 ^ (LD Δ * 2) := (pow_mul 2 _ 2).symm
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)

/-- A check with n̄·|Λ| ≤ 16m has at most `sbMax Δ` clauses: s̄ = 16m/n̄ < 32Δ·log(2Δ). Hypotheses:
the inequalities of «Setting and parameters», 2 ≤ Δ, m ≤ Δn, n̄ the number of the text. -/
theorem row_le (hIneq : ParamIneq) (n Δ m nb c : ℕ) (hΔ : 2 ≤ Δ) (hm : m ≤ Δ * n) (hNb : IsNb n Δ nb) (h : nb * c ≤ 16 * m) : c ≤ sbMax Δ := by
  have h1 := (hIneq.sb_lt n Δ m nb hΔ hm hNb).2
  have h2 := lg_le_LD Δ (by omega)
  have h0 : (0 : ℝ) < nb := by
    obtain ⟨a, rfl⟩ := hNb.1
    positivity
  have h3 : (nb : ℝ) * c ≤ 16 * m := by exact_mod_cast h
  have h4 : (c : ℝ) ≤ 16 * m / nb := by rw [le_div_iff₀ h0]; linarith
  have h5 : (32 : ℝ) * Δ * lg (2 * Δ) ≤ 32 * Δ * LD Δ := mul_le_mul_of_nonneg_left h2 (by positivity)
  have h6 : (c : ℝ) ≤ (sbMax Δ : ℕ) := by unfold sbMax; push_cast; linarith
  exact_mod_cast h6

/-! ### The word of a list of checks -/

/-- The word of a list l of numbers that are at most N has length at most |l|·(3·size(N) + 4) + 2. -/
theorem len_row (N : ℕ) (l : List ℕ) (h : ∀ E ∈ l, E ≤ N) : len l ≤ l.length * (3 * Nat.size N + 4) + 2 := by
  induction l with
  | nil => rw [len_nil]; omega
  | cons a t ih =>
    have h1 := ih fun E hE => h E (List.mem_cons_of_mem _ hE)
    have h2 := Nat.size_le_size (h a List.mem_cons_self)
    rw [len_cons, len_nat, List.length_cons, add_mul, one_mul]
    omega

/-- The word of a list L of lists whose words have length at most c has length at most |L|·(c + 2) + 2. -/
theorem len_rows (c : ℕ) (L : List (List ℕ)) (h : ∀ l ∈ L, len l ≤ c) : len L ≤ L.length * (c + 2) + 2 := by
  induction L with
  | nil => rw [len_nil]; omega
  | cons a t ih =>
    have h1 := ih fun l hl => h l (List.mem_cons_of_mem _ hl)
    have h2 := h a List.mem_cons_self
    rw [len_cons, List.length_cons, add_mul, one_mul]
    omega

/-- The word of a list of at most R lists of at most s numbers that are at most N has length at most
8(R + 1)(s + 1)(size(N) + 2) + 8. -/
theorem len_le (R s N : ℕ) (L : List (List ℕ)) (h1 : L.length ≤ R) (h2 : ∀ l ∈ L, l.length ≤ s ∧ ∀ E ∈ l, E ≤ N) :
    len L ≤ 8 * (R + 1) * (s + 1) * (Nat.size N + 2) + 8 := by
  have h3 : ∀ l ∈ L, len l ≤ s * (3 * Nat.size N + 4) + 2 := fun l hl =>
    (len_row N l (h2 l hl).2).trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ (h2 l hl).1) _)
  have h4 := len_rows _ L h3
  have h5 : L.length * (s * (3 * Nat.size N + 4) + 2 + 2) ≤ R * (s * (3 * Nat.size N + 4) + 2 + 2) := Nat.mul_le_mul_right _ h1
  generalize Nat.size N = z at *
  nlinarith [Nat.zero_le (R * s * z), Nat.zero_le (R * s), Nat.zero_le (R * z), Nat.zero_le (s * z), Nat.zero_le R, Nat.zero_le s, Nat.zero_le z]

/-! ### The count -/

section
variable {Idx : Type} [Enc Idx] {S : Solver Idx}

/-- If the list 𝓛 is fit for an evaluation, M ≥ β − 1 + r, M ≥ n + r and X(𝓛) = 0, the program's
F(𝓛) is the number of satisfying assignments. Further hypotheses: the statements on the evaluation,
on the number of
profiles and display (63); a correct solver with K ≥ 2; the pad fits. -/
theorem evF_eq (hEv : Net.StEvXF) (hNP : Net.StNPrMax) (hProd : AppVariables.ProductStmt) {ok : Idx → Prop} (hC : S.Correct ok) {k : ℕ} {pad : U} {i : Idx} {n Δ nb M : ℕ} {ψ : Fml}
    {L : List (List ℕ)} (hok : ok i) (hK : 2 ≤ S.K i) (hfit : FitsD S k i n Δ pad.length) (hF : Fit k n Δ nb M (ψ, L)) (h1 : beta n ψ.length nb - 1 + L.length ≤ M)
    (h2 : n + L.length ≤ M) (h0 : Xsum (Vof (n := n) ψ) nb (chksD ψ.length L) = 0) : (evF S k pad i n Δ nb M (ψ, L)).toNat = nSat n ψ := by
  have h := (hEv Idx S ok hC k pad i n Δ nb M (ψ, L) hok hK hF ((hNP k (S.K i) n Δ nb M (ψ, L) hF).trans hfit.prof) hfit.net h1 h2).2 h0
  rw [h]
  have h3 := hProd (Fin n → Bool) (Fin ψ.length) (Vof (n := n) ψ) nb (chksD ψ.length L) h0
  have h4 : Fsum (Vof (n := n) (ψ, L).1) nb (chks (ψ, L)) = Fsum (Vof (n := n) ψ) nb (chksD ψ.length L) := rfl
  rw [h4, h3, Int.toNat_natCast, card_Vof]

end

end VariableBound.Count

namespace VariableBound

open Groundwork Groundwork.Prog PaddedDescent.F PaddedDescent.F.Mark ClauseBound.Alg ClauseBound.ParityChecks AppVariables VariableBound.Net Finset

/-- Steps 1 to 4 of Appendix D: the count of one sparse formula is right, given the statements on
the evaluation by networks (`Net.StEvXF`, `Net.StFit`, `Net.StTbMax`, `Net.StNPrMax`), on the search
(`StSearchD`), on the listed
family of Lemma 13 (`Fld.StFamD`), on the parameters (`StParamSpec`, `ParamIneq`), display (63) and
the remark that the empty list has X = 0 if m ≤ n̄. -/
theorem stCountD (hEv : Net.StEvXF) (hFit : Net.StFit) (hTb : Net.StTbMax) (hNP : Net.StNPrMax) (hS : StSearchD) (hFam : Fld.StFamD) (hSpec : StParamSpec)
    (hIneq : ParamIneq) (hProd : AppVariables.ProductStmt) (hEmpty : AppVariables.EmptyListStmt) : StCountD := by
  intro Idx _ S ok hC k pad i n Δ ψ hok hK hwf hocc hm hΔ hn hfit
  have hlg := Count.lg_le_LD Δ (by omega)
  have hsq : (2 * Δ) ^ 2 ≤ 2 ^ n := Count.sq_le n Δ (by omega)
  have h2Δ : 2 * Δ ≤ 2 ^ n := le_trans (by nlinarith) hsq
  have hNb : IsNb n Δ (nbD n Δ) := hSpec.1 n Δ (by omega) h2Δ
  have hnb2 : 2 ≤ nbD n Δ := hSpec.2.1 n Δ (by omega) hsq
  have hRb : IsRb (beta n ψ.length (nbD n Δ)) (rbD (beta n ψ.length (nbD n Δ))) := hSpec.2.2.1 _
  have hTbI : IsTb ψ.length (nbD n Δ) (rbD (beta n ψ.length (nbD n Δ))) (tbD ψ.length (nbD n Δ) (rbD (beta n ψ.length (nbD n Δ)))) := hSpec.2.2.2 _ _ _ hnb2
  have hnR : (29 : ℝ) * LD Δ + 19 ≤ n := by exact_mod_cast hn
  simp only [countD]
  generalize nbD n Δ = nb at *
  generalize hβ : beta n ψ.length nb = β at *
  generalize rbD β = rb at *
  generalize tbD ψ.length nb rb = tb at *
  have hβn : n + 1 ≤ β := by rw [← hβ]; unfold beta; omega
  have hM : Mb β rb = rb + β - 1 := rfl
  by_cases hc : ψ.length ≤ nb
  · rw [decide_eq_true hc, cond_true]
    have hβ1 : β = n + 1 := by
      rw [← hβ]; unfold beta
      rw [Nat.choose_eq_zero_of_lt (by omega), Nat.clog_of_right_le_one (by omega)]
    have hr := hIneq.rb_le β rb hRb
    have hr' : (rb : ℝ) ≤ 13 * n - 1 := by
      rw [hβ1] at hr; push_cast at hr
      have : (0 : ℝ) ≤ LD Δ := by positivity
      linarith
    have hr'' : rb + 1 ≤ 13 * n := by
      have : ((rb + 1 : ℕ) : ℝ) ≤ ((13 * n : ℕ) : ℝ) := by push_cast; linarith
      exact_mod_cast this
    have hF := (hFit k n Δ nb rb tb (Mb β rb) ψ [] hwf hΔ hocc hm hNb (by rw [hM]; omega)).2 hc
    refine Count.evF_eq hEv hNP hProd hC hok hK hfit hF (by rw [hβ, hM, List.length_nil]; omega) (by rw [hM, List.length_nil]; omega) ?_
    exact hEmpty (Fin n → Bool) (Fin ψ.length) (Vof (n := n) ψ) nb (by rw [Fintype.card_fin]; exact hc)
  · rw [decide_eq_false hc, cond_false]
    have hlt : nb < ψ.length := by omega
    obtain ⟨hrb10, hM14⟩ := hIneq.large n Δ ψ.length nb rb hΔ hlt hm hNb (by rw [hβ]; exact hRb) (by linarith)
    rw [hβ] at hM14
    have htb : tb ≤ tbMax n Δ := hTb n Δ ψ.length tb (by omega) hm (hIneq.tb_le n Δ ψ.length nb rb tb hΔ (by omega) hNb hrb10 hTbI)
    have hfitL : ∀ L, StructD ψ.length nb rb tb L → Fit k n Δ nb (Mb β rb) (ψ, L) := fun L hL =>
      (hFit k n Δ nb rb tb (Mb β rb) ψ L hwf hΔ hocc hm hNb hM14).1 hlt hL hrb10 (by rw [hM]; omega) (by rw [hM]; omega) htb
    have hl1 : ∀ L, StructD ψ.length nb rb tb L → beta n ψ.length nb - 1 + L.length ≤ Mb β rb := fun L hL => by
      have := hL.1; rw [hβ, hM]; omega
    have hl2 : ∀ L, StructD ψ.length nb rb tb L → n + L.length ≤ Mb β rb := fun L hL => by
      have := hL.1; rw [hM]; omega
    obtain ⟨a, ha⟩ := hNb.1
    have hlog : Nat.log 2 nb = a := by rw [ha]; exact Nat.log_pow (by norm_num) a
    have ha1 : 1 ≤ a := by
      rcases Nat.eq_zero_or_pos a with h | h
      · rw [ha, h] at hnb2; norm_num at hnb2
      · exact h
    obtain ⟨hne, -, hinc, hfam⟩ := hFam ψ.length a ha1 (by rw [← ha]; omega)
    rw [hlog]
    rw [← ha] at hfam
    have hres := hS (Fin n → Bool) ψ.length (Vof (n := n) ψ) n nb rb tb pad (fun L => evX S k pad i n Δ nb (Mb β rb) β (ψ, L)) (Fld.famD ψ.length a)
      (by simp) (by omega) (by rw [hβ]; exact hRb) hTbI hne (fun l hl => ⟨(hinc l hl).1, (hinc l hl).2.2⟩) hfam
      (fun L hL => by
        have := (hEv Idx S ok hC k pad i n Δ nb (Mb β rb) (ψ, L) hok hK (hfitL L hL) ((hNP k (S.K i) n Δ nb (Mb β rb) (ψ, L) (hfitL L hL)).trans hfit.prof) hfit.net
          (hl1 L hL) (hl2 L hL)).1
        have e : beta n (ψ, L).1.length nb = β := hβ
        rw [e] at this; exact this)
      (fun L hL => by
        refine (Count.len_le (10 * n) (sbMax Δ) (Δ * n) L (hL.1.trans hrb10) fun l hl => ⟨?_, fun E hE => ?_⟩).trans hfit.lists
        · exact Count.row_le hIneq n Δ ψ.length nb l.length hΔ hm hNb (hL.2.1 l hl).2.2
        · exact (Nat.le_of_lt ((hL.2.1 l hl).2.1 E hE)).trans hm)
    rw [hβ] at hres
    exact Count.evF_eq hEv hNP hProd hC hok hK hfit (hfitL _ hres.1) (hl1 _ hres.1) (hl2 _ hres.1) hres.2

end VariableBound
