/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/PairCeiling/NumericCert.lean — the NUMERIC CERTIFICATE half of the bandwidth-1 pair-correlation ceiling theorem:
a kernel-checkable fixed-point interval checker for the grid discrepancies of a periodic
configuration, given per-frequency ENCLOSURES of its form factor.

Conventions: N = period = total multiplicity; S(j) (j = 1..N) the form factor at integer
frequency j; the spectral measure puts mass s_j := S(j)/N at x_j := j/N; C(x) := Σ_{x_j ≤ x} s_j (right-continuous step), D := C − x²/2,
E(x) := ∫₀ˣ D.  On the grid:  T_j := Σ_{i≤j} S(i),  U_j := Σ_{i≤j} T_{i−1},
   D(x_j) = T_j/N − j²/(2N²) =: Dright j,   D(x_j⁻) = T_{j−1}/N − j²/(2N²) =: Dleft j,   E(x_j) = U_j/N² − j³/(6N³) =: Egrid j
(E is cellwise ∫_{x_{i−1}}^{x_i}(C(x_{i−1}) − t²/2)dt = T_{i−1}/N² − (i³ − (i−1)³)/(6N³)).  Between atoms D is decreasing, so sup_{(0,1]}|D| is the
grid maximum of |Dleft|, |Dright|, and |E′| = |D| gives sup_{[0,1]}|E| ≤ max_j|Egrid j| + sup|D|/N — those two bridges belong to the analytic
half (Stability.lean); this file delivers the GRID bounds.

THE CERTIFICATE.  Data: N, a scale K, integer enclosures (lo_j, hi_j) meaning lo_j ≤ K·S(j) ≤ hi_j, and rational targets.  `check` runs ONE pass
of exact integer interval arithmetic (only +, ·, max, |·| on ℤ — every quantity is an integer combination of the K·S(j): 2N²K·Dright j =
2N·(K T_j) − j²K, 6N³K·Egrid j = 6N·(K U_j) − j³K) and compares with the targets by cross-multiplication.  `cert_of_check`: if `check d = true`
then FOR EVERY real sequence S inside the enclosures the four families of bounds hold.  The instance files prove `check d = true` with
`decide +kernel` (kernel evaluation; no native_decide, no extra axioms).  What is NOT proved here: that the true form factor of a given
configuration lies in the enclosures — for a concrete law those come from an interval-arithmetic computation outside Lean and are a displayed
hypothesis of the final statement.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.BigOperators.Intervals

noncomputable section

open Finset

namespace Zeta23
namespace PairCeiling

/-! ## 1. Real-side grid quantities (shared with the stability lemma) -/

section Defs
variable (S : ℕ → ℝ) (N : ℕ)

/-- T_j := Σ_{i=1}^{j} S(i). -/
def T (j : ℕ) : ℝ := ∑ i ∈ range j, S (i + 1)

/-- U_j := Σ_{i=1}^{j} T_{i−1}. -/
def U (j : ℕ) : ℝ := ∑ i ∈ range j, T S i

/-- D(x_j) (right limit): C(x_j) − x_j²/2 with C(x_j) = T_j/N. -/
def Dright (j : ℕ) : ℝ := T S j / N - (j : ℝ) ^ 2 / (2 * (N : ℝ) ^ 2)

/-- D(x_j⁻) (left limit): C(x_{j−1}) − x_j²/2. -/
def Dleft (j : ℕ) : ℝ := T S (j - 1) / N - (j : ℝ) ^ 2 / (2 * (N : ℝ) ^ 2)

/-- E(x_j) = U_j/N² − j³/(6N³). -/
def Egrid (j : ℕ) : ℝ := U S j / (N : ℝ) ^ 2 - (j : ℝ) ^ 3 / (6 * (N : ℝ) ^ 3)

/-- D(1) and E(1). -/
def D1 : ℝ := Dright S N N
def E1 : ℝ := Egrid S N N

lemma T_zero : T S 0 = 0 := by simp [T]
lemma T_succ (j : ℕ) : T S (j + 1) = T S j + S (j + 1) := by simp [T, sum_range_succ]
lemma U_zero : U S 0 = 0 := by simp [U]
lemma U_succ (j : ℕ) : U S (j + 1) = U S j + T S j := by simp [U, sum_range_succ]

end Defs

/-! ## 2. Enclosure hypothesis -/

/-- `EnclOK K S j l`: the list l = [(lo,hi), …] encloses K·S(j+1), K·S(j+2), … in order. -/
def EnclOK (K : ℕ) (S : ℕ → ℝ) : ℕ → List (ℤ × ℤ) → Prop
  | _, [] => True
  | j, e :: l => ((e.1 : ℝ) ≤ K * S (j + 1) ∧ (K : ℝ) * S (j + 1) ≤ e.2) ∧ EnclOK K S (j + 1) l

/-! ## 3. The integer checker -/

/-- certificate data: period N, scale K, enclosures for j = 1..N, and rational targets n/d for |D(1)|, |E(1)|, the grid sup of |D| (both
one-sided limits) and the combined 'max_j |E(x_j)| + sup|D|/N'. -/
structure CertData where
  N : ℕ
  K : ℕ
  encl : List (ℤ × ℤ)
  bD1n : ℕ
  bD1d : ℕ
  bE1n : ℕ
  bE1d : ℕ
  b1n : ℕ
  b1d : ℕ
  b2n : ℕ
  b2d : ℕ

/-- loop state after the first j enclosures: integer bounds for K·T_j, K·U_j, and running maxima
M1 ≥ |2N²K·D(x_i^±)|, M2 ≥ |6N³K·E(x_i)| over i ≤ j; ok = all enclosures were nonempty. -/
structure St where
  j : ℕ
  Tlo : ℤ
  Thi : ℤ
  Ulo : ℤ
  Uhi : ℤ
  M1 : ℤ
  M2 : ℤ
  ok : Bool

/-- the initial state. -/
def St.init : St := ⟨0, 0, 0, 0, 0, 0, 0, true⟩

/-- one step of the interval propagation (written without lets so that `simp only [step]` exposes the fields). -/
def step (N K : ℕ) (s : St) (e : ℤ × ℤ) : St where
  j := s.j + 1
  Tlo := s.Tlo + e.1
  Thi := s.Thi + e.2
  Ulo := s.Ulo + s.Tlo
  Uhi := s.Uhi + s.Thi
  M1 := max s.M1 (max (max |2 * (N : ℤ) * s.Tlo - ((s.j : ℤ) + 1) ^ 2 * K| |2 * (N : ℤ) * s.Thi - ((s.j : ℤ) + 1) ^ 2 * K|)
                     (max |2 * (N : ℤ) * (s.Tlo + e.1) - ((s.j : ℤ) + 1) ^ 2 * K| |2 * (N : ℤ) * (s.Thi + e.2) - ((s.j : ℤ) + 1) ^ 2 * K|))
  M2 := max s.M2 (max |6 * (N : ℤ) * (s.Ulo + s.Tlo) - ((s.j : ℤ) + 1) ^ 3 * K| |6 * (N : ℤ) * (s.Uhi + s.Thi) - ((s.j : ℤ) + 1) ^ 3 * K|)
  ok := s.ok && decide (e.1 ≤ e.2)

/-- run the loop over the enclosure list. -/
def run (N K : ℕ) (l : List (ℤ × ℤ)) (s : St) : St := l.foldl (step N K) s

/-- **the checker** (pure integer arithmetic). -/
def check (d : CertData) : Bool :=
  let s := run d.N d.K d.encl St.init
  let aD1 : ℤ := max |2 * (d.N : ℤ) * s.Tlo - (d.N : ℤ) ^ 2 * d.K| |2 * (d.N : ℤ) * s.Thi - (d.N : ℤ) ^ 2 * d.K|
  let aE1 : ℤ := max |6 * (d.N : ℤ) * s.Ulo - (d.N : ℤ) ^ 3 * d.K| |6 * (d.N : ℤ) * s.Uhi - (d.N : ℤ) ^ 3 * d.K|
  s.ok && decide (s.j = d.N) && decide (0 < d.N) && decide (0 < d.K)
    && decide (0 < d.bD1d) && decide (0 < d.bE1d) && decide (0 < d.b1d) && decide (0 < d.b2d)
    && decide (aD1 * d.bD1d ≤ d.bD1n * (2 * (d.N : ℤ) ^ 2 * d.K))
    && decide (aE1 * d.bE1d ≤ d.bE1n * (6 * (d.N : ℤ) ^ 3 * d.K))
    && decide (s.M1 * d.b1d ≤ d.b1n * (2 * (d.N : ℤ) ^ 2 * d.K))
    && decide ((s.M2 + 3 * s.M1) * d.b2d ≤ d.b2n * (6 * (d.N : ℤ) ^ 3 * d.K))

/-! ## 4. Soundness -/

section Sound

variable {S : ℕ → ℝ} {N K : ℕ}

/-- a ≤ x ≤ b ⇒ |x| ≤ max |a| |b|. -/
lemma abs_le_max_abs {a b x : ℝ} (ha : a ≤ x) (hb : x ≤ b) : |x| ≤ max |a| |b| := by
  rcases le_or_gt 0 x with hx | hx
  · rw [abs_of_nonneg hx]; exact le_max_of_le_right (hb.trans (le_abs_self b))
  · rw [abs_of_neg hx]; exact le_max_of_le_left ((neg_le_neg ha).trans (neg_le_abs a))

/-- the loop invariant. -/
structure LoopInv (S : ℕ → ℝ) (N K : ℕ) (s : St) : Prop where
  tlo : (s.Tlo : ℝ) ≤ K * T S s.j
  thi : (K : ℝ) * T S s.j ≤ s.Thi
  ulo : (s.Ulo : ℝ) ≤ K * U S s.j
  uhi : (K : ℝ) * U S s.j ≤ s.Uhi
  dl : ∀ i, 1 ≤ i → i ≤ s.j → |(2 * (N : ℝ) ^ 2 * K) * Dleft S N i| ≤ (s.M1 : ℝ)
  dr : ∀ i, 1 ≤ i → i ≤ s.j → |(2 * (N : ℝ) ^ 2 * K) * Dright S N i| ≤ (s.M1 : ℝ)
  eg : ∀ i, 1 ≤ i → i ≤ s.j → |(6 * (N : ℝ) ^ 3 * K) * Egrid S N i| ≤ (s.M2 : ℝ)

lemma loopInv_init : LoopInv S N K St.init :=
  ⟨by simp [St.init, T_zero], by simp [St.init, T_zero], by simp [St.init, U_zero], by simp [St.init, U_zero],
   fun i h1 h2 => by change i ≤ 0 at h2; omega, fun i h1 h2 => by change i ≤ 0 at h2; omega,
   fun i h1 h2 => by change i ≤ 0 at h2; omega⟩

/-- the scaled grid quantities are integer combinations of K·T, K·U (N ≠ 0). -/
lemma scaled_Dright (hN : 0 < N) (j : ℕ) :
    (2 * (N : ℝ) ^ 2 * K) * Dright S N j = 2 * N * (K * T S j) - (j : ℝ) ^ 2 * K := by
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  unfold Dright; field_simp; try ring
lemma scaled_Dleft (hN : 0 < N) (j : ℕ) :
    (2 * (N : ℝ) ^ 2 * K) * Dleft S N j = 2 * N * (K * T S (j - 1)) - (j : ℝ) ^ 2 * K := by
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  unfold Dleft; field_simp; try ring
lemma scaled_Egrid (hN : 0 < N) (j : ℕ) :
    (6 * (N : ℝ) ^ 3 * K) * Egrid S N j = 6 * N * (K * U S j) - (j : ℝ) ^ 3 * K := by
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  unfold Egrid; field_simp; try ring

/-- one step preserves the invariant. -/
lemma loopInv_step (hN : 0 < N) {s : St} (h : LoopInv S N K s) {e : ℤ × ℤ}
    (he : (e.1 : ℝ) ≤ K * S (s.j + 1) ∧ (K : ℝ) * S (s.j + 1) ≤ e.2) : LoopInv S N K (step N K s e) := by
  have hT : T S (s.j + 1) = T S s.j + S (s.j + 1) := T_succ S s.j
  have hU : U S (s.j + 1) = U S s.j + T S s.j := U_succ S s.j
  have tlo' : ((s.Tlo + e.1 : ℤ) : ℝ) ≤ K * T S (s.j + 1) := by rw [hT]; push_cast; linarith [h.tlo, he.1]
  have thi' : (K : ℝ) * T S (s.j + 1) ≤ ((s.Thi + e.2 : ℤ) : ℝ) := by rw [hT]; push_cast; linarith [h.thi, he.2]
  have ulo' : ((s.Ulo + s.Tlo : ℤ) : ℝ) ≤ K * U S (s.j + 1) := by rw [hU]; push_cast; linarith [h.ulo, h.tlo]
  have uhi' : (K : ℝ) * U S (s.j + 1) ≤ ((s.Uhi + s.Thi : ℤ) : ℝ) := by rw [hU]; push_cast; linarith [h.uhi, h.thi]
  refine ⟨tlo', thi', ulo', uhi', ?_, ?_, ?_⟩
  · intro i h1 h2
    simp only [step] at h2 ⊢
    rcases Nat.lt_or_ge i (s.j + 1) with hlt | hge
    · exact (h.dl i h1 (by omega)).trans (by exact_mod_cast le_max_left _ _)
    · have hi : i = s.j + 1 := le_antisymm h2 hge
      subst hi
      rw [scaled_Dleft hN]
      simp only [Nat.add_sub_cancel]
      have hb := abs_le_max_abs (a := 2 * N * (s.Tlo : ℝ) - ((s.j : ℝ) + 1) ^ 2 * K) (b := 2 * N * (s.Thi : ℝ) - ((s.j : ℝ) + 1) ^ 2 * K)
        (x := 2 * N * (K * T S s.j) - ((s.j + 1 : ℕ) : ℝ) ^ 2 * K)
        (by push_cast; nlinarith [h.tlo, (Nat.cast_nonneg N : (0:ℝ) ≤ N)]) (by push_cast; nlinarith [h.thi, (Nat.cast_nonneg N : (0:ℝ) ≤ N)])
      refine hb.trans ?_
      push_cast [Int.cast_max, Int.cast_abs]
      exact le_trans (le_max_left _ _) (le_max_right _ _)
  · intro i h1 h2
    simp only [step] at h2 ⊢
    rcases Nat.lt_or_ge i (s.j + 1) with hlt | hge
    · exact (h.dr i h1 (by omega)).trans (by exact_mod_cast le_max_left _ _)
    · have hi : i = s.j + 1 := le_antisymm h2 hge
      subst hi
      rw [scaled_Dright hN]
      have hb := abs_le_max_abs (a := 2 * N * ((s.Tlo + e.1 : ℤ) : ℝ) - ((s.j : ℝ) + 1) ^ 2 * K) (b := 2 * N * ((s.Thi + e.2 : ℤ) : ℝ) - ((s.j : ℝ) + 1) ^ 2 * K)
        (x := 2 * N * (K * T S (s.j + 1)) - ((s.j + 1 : ℕ) : ℝ) ^ 2 * K)
        (by push_cast at tlo' ⊢; nlinarith [tlo', (Nat.cast_nonneg N : (0:ℝ) ≤ N)]) (by push_cast at thi' ⊢; nlinarith [thi', (Nat.cast_nonneg N : (0:ℝ) ≤ N)])
      refine hb.trans ?_
      push_cast [Int.cast_max, Int.cast_abs]
      exact le_trans (le_max_right _ _) (le_max_right _ _)
  · intro i h1 h2
    simp only [step] at h2 ⊢
    rcases Nat.lt_or_ge i (s.j + 1) with hlt | hge
    · exact (h.eg i h1 (by omega)).trans (by exact_mod_cast le_max_left _ _)
    · have hi : i = s.j + 1 := le_antisymm h2 hge
      subst hi
      rw [scaled_Egrid hN]
      have hb := abs_le_max_abs (a := 6 * N * ((s.Ulo + s.Tlo : ℤ) : ℝ) - ((s.j : ℝ) + 1) ^ 3 * K) (b := 6 * N * ((s.Uhi + s.Thi : ℤ) : ℝ) - ((s.j : ℝ) + 1) ^ 3 * K)
        (x := 6 * N * (K * U S (s.j + 1)) - ((s.j + 1 : ℕ) : ℝ) ^ 3 * K)
        (by push_cast at ulo' ⊢; nlinarith [ulo', (Nat.cast_nonneg N : (0:ℝ) ≤ N)]) (by push_cast at uhi' ⊢; nlinarith [uhi', (Nat.cast_nonneg N : (0:ℝ) ≤ N)])
      refine hb.trans ?_
      push_cast [Int.cast_max, Int.cast_abs]
      exact le_max_right _ _

/-- the ok flag only decreases. -/
lemma step_ok_imp {s : St} {e : ℤ × ℤ} (h : (step N K s e).ok = true) : s.ok = true := by
  simp [step, Bool.and_eq_true] at h; exact h.1

lemma run_ok_imp {l : List (ℤ × ℤ)} : ∀ {s : St}, (run N K l s).ok = true → s.ok = true := by
  induction l with
  | nil => intro s h; exact h
  | cons e l ih => intro s h; exact step_ok_imp (ih h)

lemma run_j {l : List (ℤ × ℤ)} : ∀ {s : St}, (run N K l s).j = s.j + l.length := by
  induction l with
  | nil => intro s; rfl
  | cons e l ih => intro s; show (run N K l (step N K s e)).j = _; rw [ih]; simp [step]; omega

/-- the loop preserves the invariant along an enclosed list. -/
lemma loopInv_run (hN : 0 < N) {l : List (ℤ × ℤ)} : ∀ {s : St}, LoopInv S N K s → EnclOK K S s.j l → (run N K l s).ok = true →
    LoopInv S N K (run N K l s) := by
  induction l with
  | nil => intro s h _ _; exact h
  | cons e l ih =>
    intro s h hencl hok
    have hstep : LoopInv S N K (step N K s e) := loopInv_step hN h hencl.1
    have hj : (step N K s e).j = s.j + 1 := rfl
    exact ih hstep (hj ▸ hencl.2) hok

/-- **soundness of the checker.** -/
theorem cert_of_check (d : CertData) (hc : check d = true) (S : ℕ → ℝ) (hS : EnclOK d.K S 0 d.encl) :
    |D1 S d.N| ≤ (d.bD1n : ℝ) / d.bD1d ∧ |E1 S d.N| ≤ (d.bE1n : ℝ) / d.bE1d ∧
    (∀ j, 1 ≤ j → j ≤ d.N → |Dleft S d.N j| ≤ (d.b1n : ℝ) / d.b1d ∧ |Dright S d.N j| ≤ (d.b1n : ℝ) / d.b1d) ∧
    (∀ i j, 1 ≤ i → i ≤ d.N → 1 ≤ j → j ≤ d.N →
        |Egrid S d.N j| + |Dleft S d.N i| / d.N ≤ (d.b2n : ℝ) / d.b2d ∧ |Egrid S d.N j| + |Dright S d.N i| / d.N ≤ (d.b2n : ℝ) / d.b2d) := by
  -- unpack the Bool
  simp only [check, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hok, hj⟩, hN⟩, hK⟩, hbD1d⟩, hbE1d⟩, hb1d⟩, hb2d⟩, hD1⟩, hE1⟩, hM1⟩, hM2⟩ := hc
  set s := run d.N d.K d.encl St.init with hs
  have hinv : LoopInv S d.N d.K s := loopInv_run hN loopInv_init (by simpa [St.init] using hS) hok
  have hN0 : (0 : ℝ) < d.N := by exact_mod_cast hN
  have hK0 : (0 : ℝ) < d.K := by exact_mod_cast hK
  have hsc2 : (0 : ℝ) < 2 * (d.N : ℝ) ^ 2 * d.K := by positivity
  have hsc6 : (0 : ℝ) < 6 * (d.N : ℝ) ^ 3 * d.K := by positivity
  have hjN : s.j = d.N := hj
  -- D(1)
  have hD1r : |(2 * (d.N : ℝ) ^ 2 * d.K) * D1 S d.N| ≤
      ((max |2 * (d.N : ℤ) * s.Tlo - (d.N : ℤ) ^ 2 * d.K| |2 * (d.N : ℤ) * s.Thi - (d.N : ℤ) ^ 2 * d.K| : ℤ) : ℝ) := by
    unfold D1; rw [scaled_Dright hN]
    have h1 := hinv.tlo; have h2 := hinv.thi
    rw [hjN] at h1 h2
    refine (abs_le_max_abs (a := 2 * d.N * (s.Tlo : ℝ) - (d.N : ℝ) ^ 2 * d.K) (b := 2 * d.N * (s.Thi : ℝ) - (d.N : ℝ) ^ 2 * d.K)
      (by nlinarith [hN0.le]) (by nlinarith [hN0.le])).trans (le_of_eq ?_)
    push_cast [Int.cast_max, Int.cast_abs]; rfl
  have hE1r : |(6 * (d.N : ℝ) ^ 3 * d.K) * E1 S d.N| ≤
      ((max |6 * (d.N : ℤ) * s.Ulo - (d.N : ℤ) ^ 3 * d.K| |6 * (d.N : ℤ) * s.Uhi - (d.N : ℤ) ^ 3 * d.K| : ℤ) : ℝ) := by
    unfold E1; rw [scaled_Egrid hN]
    have h1 := hinv.ulo; have h2 := hinv.uhi
    rw [hjN] at h1 h2
    refine (abs_le_max_abs (a := 6 * d.N * (s.Ulo : ℝ) - (d.N : ℝ) ^ 3 * d.K) (b := 6 * d.N * (s.Uhi : ℝ) - (d.N : ℝ) ^ 3 * d.K)
      (by nlinarith [hN0.le]) (by nlinarith [hN0.le])).trans (le_of_eq ?_)
    push_cast [Int.cast_max, Int.cast_abs]; rfl
  -- helper: from |c·x| ≤ A and A·den ≤ num·c conclude |x| ≤ num/den
  have key : ∀ {c x A : ℝ} {num den : ℕ}, 0 < c → 0 < den → |c * x| ≤ A → A * den ≤ num * c → |x| ≤ (num : ℝ) / den := by
    intro c x A num den hc hden h1 h2
    rw [le_div_iff₀ (by exact_mod_cast hden : (0:ℝ) < den)]
    rw [abs_mul, abs_of_pos hc] at h1
    have hden0 : (0:ℝ) ≤ den := by positivity
    nlinarith [mul_le_mul_of_nonneg_right h1 hden0, abs_nonneg x]
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact key hsc2 hbD1d hD1r (by push_cast [Int.cast_max, Int.cast_abs]; exact_mod_cast hD1)
  · exact key hsc6 hbE1d hE1r (by push_cast [Int.cast_max, Int.cast_abs]; exact_mod_cast hE1)
  · intro j h1 h2
    rw [← hjN] at h2
    have hM1r : (s.M1 : ℝ) * d.b1d ≤ d.b1n * (2 * (d.N : ℝ) ^ 2 * d.K) := by exact_mod_cast hM1
    exact ⟨key hsc2 hb1d (hinv.dl j h1 h2) hM1r, key hsc2 hb1d (hinv.dr j h1 h2) hM1r⟩
  · intro i j hi1 hi2 hj1 hj2
    rw [← hjN] at hi2 hj2
    have hEg := hinv.eg j hj1 hj2
    have hDl := hinv.dl i hi1 hi2
    have hDr := hinv.dr i hi1 hi2
    have hM2r : ((s.M2 + 3 * s.M1 : ℤ) : ℝ) * d.b2d ≤ d.b2n * (6 * (d.N : ℝ) ^ 3 * d.K) := by exact_mod_cast hM2
    -- 6N³K·(|E| + |D|/N) ≤ M2 + 3·M1  (since 6N³K/N · |D| = 3 · (2N²K|D|))
    have comb : ∀ {Dv : ℝ}, |(2 * (d.N : ℝ) ^ 2 * d.K) * Dv| ≤ (s.M1 : ℝ) →
        |Egrid S d.N j| + |Dv| / d.N ≤ (d.b2n : ℝ) / d.b2d := by
      intro Dv hDv
      rw [le_div_iff₀ (by exact_mod_cast hb2d : (0:ℝ) < d.b2d)]
      rw [abs_mul, abs_of_pos hsc6] at hEg
      rw [abs_mul, abs_of_pos hsc2] at hDv
      have e6 : (6 * (d.N : ℝ) ^ 3 * d.K) * (|Egrid S d.N j| + |Dv| / d.N)
          = (6 * (d.N : ℝ) ^ 3 * d.K) * |Egrid S d.N j| + 3 * ((2 * (d.N : ℝ) ^ 2 * d.K) * |Dv|) := by
        field_simp; ring
      have hb2d0 : (0:ℝ) ≤ d.b2d := by positivity
      have : (6 * (d.N : ℝ) ^ 3 * d.K) * (|Egrid S d.N j| + |Dv| / d.N) ≤ ((s.M2 + 3 * s.M1 : ℤ) : ℝ) := by
        rw [e6]; push_cast; linarith
      nlinarith [mul_le_mul_of_nonneg_right this hb2d0, abs_nonneg (Egrid S d.N j), abs_nonneg Dv, hN0]
    exact ⟨comb hDl, comb hDr⟩

end Sound

end PairCeiling
end Zeta23

end
