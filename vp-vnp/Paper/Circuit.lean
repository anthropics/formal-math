/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Paper.CircuitPhi
import Paper.Universal
import Paper.LowDeg
import Nc.End.PermThm

/-!
# The paper, section "One scale is all scales": small circuits are accelerators
-/

set_option linter.unusedSectionVars false

namespace Paper

open Finset NS1
open _root_.NS1.Tree

variable {A : Type} [CommRing A] {θ : List Bool → A}

theorem wordG_self {Γ : Type} (b : Γ) (z : Tree) : Nc.Dl.wordG b b z = List.replicate z.size b := by
  induction z with
  | nil => rfl
  | cons x y ihx ihy =>
    rw [Nc.Dl.wordG, ihx, ihy, List.replicate_append_replicate, Tree.size]
    rw [show x.size + y.size + 1 = (x.size + y.size) + 1 from rfl, List.replicate_succ]

theorem wordG_bits {Γ : Type} (f : Bool → Γ) (z : Tree) :
    Nc.Dl.wordG (f false) (f true) z = (tbits z).map f := by
  induction z with
  | nil => rfl
  | cons x y ihx ihy => simp only [tbits, Nc.Dl.wordG, List.map_cons, List.map_append, ihx, ihy]

/-- In a nonzero ring the two symbols of a universal automaton are different: with one symbol the words of two plain
instances of equal size, with the values 1 and 0, would be equal. -/
theorem universal_symbols_ne [Nontrivial A] {S Γ Q : Type} [Fintype S] [DecidableEq S] [Fintype Γ] [DecidableEq Γ]
    [Fintype Q] [DecidableEq Q] {mu : Nc.Letter S Unit Γ → Matrix Q Q A} {i e : Q} {b0 b1 : Γ} {C : ℕ}
    (h : ∀ (τ : ℕ) (z : Tree) (t : ℕ), Plain θ τ z → C * (z.size + τ) * lg (z.size + τ) ^ 2 ≤ t →
      Nc.runVal mu i e t (fun _ => Nc.Dl.wordG b0 b1 z) = pv θ z) : b0 ≠ b1 := by
  intro hb
  subst hb
  obtain ⟨c1, hc1⟩ : ∃ c, c = (Fm.quote .nil).code := ⟨_, rfl⟩
  obtain ⟨c2, hc2⟩ : ∃ c, c = Fm.fail.code := ⟨_, rfl⟩
  have e1 : Ev θ (Fm.ofTree (Tree.cons c1 c2).hd) (Tree.cons c1 c2).tl [Run.det 1 .nil] := by
    show Ev θ (Fm.ofTree c1) c2 _
    rw [hc1, Fm.ofTree_code]
    exact .quote _ _
  have e2 : Ev θ (Fm.ofTree (Tree.cons c2 c1).hd) (Tree.cons c2 c1).tl [] := by
    show Ev θ (Fm.ofTree c2) c1 _
    rw [hc2, Fm.ofTree_code]
    exact .fail _
  have hs : (Tree.cons c2 c1).size = (Tree.cons c1 c2).size := by simp only [Tree.size]; omega
  obtain ⟨t, ht⟩ : ∃ t, t = C * ((Tree.cons c1 c2).size + 1) * lg ((Tree.cons c1 c2).size + 1) ^ 2 := ⟨_, rfl⟩
  have h1 := h 1 (.cons c1 c2) t ⟨e1.hl, by rw [e1.evl]; simp [Run.det]⟩ ht.ge
  have h2 := h 1 (.cons c2 c1) t ⟨e2.hl, by rw [e2.evl]; simp⟩ (by rw [hs]; exact ht.ge)
  simp only [wordG_self, hs] at h1 h2
  rw [h1, pv, pv, e1.evl, e2.evl] at h2
  simp [pval, Run.det] at h2

open MvPolynomial in
/-- **Paper: proof of Lemma lem:circuit, Φ for the universal automaton.** "By Corollary cor:clauses a circuit for the
permanent gives one for Φ ... By Proposition prop:universal its value is pv(z) at the code of a plain z": an affine
projection of every family that is complete for clause sums, of degree at most n = v^(H−32)+1, with these values. The
symbols of other letters than the two of words of trees are set to 0. -/
theorem lem_circuit_universal (hθ : (Function.support θ).Finite) {H : ℕ} (hH : 32 ≤ H) (κ : ℕ) :
    ∃ B₀ v₀ : ℕ, 0 < B₀ ∧ ∀ (F : Type) [Field F] [Algebra A F] (G : ∀ S, MvPolynomial (Fin S × Fin S) F),
      Nc.GridComplete F G κ → ∀ v m, v₀ ≤ v → v ^ B₀ ≤ m →
      ∃ Mat : Fin m × Fin m → MvPolynomial (Fin (v ^ (H - 32) + 1) × Option Bool) F,
        (∀ q, Nc.IsAffine (Mat q)) ∧ (aeval Mat (G m)).totalDegree ≤ v ^ (H - 32) + 1 ∧
        ∀ z : Tree, z.size ≤ v ^ (H - 32) → Plain θ (v ^ H) z →
          eval (codeB F (v ^ (H - 32) + 1) (tbits z)) (aeval Mat (G m)) = algebraMap A F (pv θ z) := by
  obtain ⟨S, Γ, Q, _, _, _, _, _, _, mu, i, e, b0, b1, C, huni⟩ := prop_universal θ hθ
  obtain ⟨cs, hcs⟩ : ∃ cs, cs = Fintype.card Q + Fintype.card S + Fintype.card Γ + 2 := ⟨_, rfl⟩
  obtain ⟨n₀, hn₀⟩ := poly_lg (2 * C * (H + 1) ^ 2) 2
  refine ⟨9 * (H + 2) + 1, 1600 * κ + cs + n₀ + 4, Nat.succ_pos _, fun F _ _ G hG v m hv hm => ?_⟩
  have : Nontrivial A := (algebraMap A F).domain_nontrivial
  have hb : Function.Injective fun b => if b = true then b1 else b0 := by
    have hne := universal_symbols_ne huni
    intro x y hxy
    rcases x <;> rcases y <;> simp_all [eq_comm]
  obtain ⟨bt, hbt⟩ : ∃ bt : Bool → Γ, bt = fun b => if b = true then b1 else b0 := ⟨_, rfl⟩
  rw [← hbt] at hb
  obtain ⟨n, hn⟩ : ∃ n, n = v ^ (H - 32) + 1 := ⟨_, rfl⟩
  obtain ⟨t, ht⟩ : ∃ t, t = v ^ (H + 1) := ⟨_, rfl⟩
  rw [← hn]
  obtain ⟨V, K, _, _, _, _, lits, wt, hne, hocc, hwt, hlit, hdeg, hev⟩ :=
    lem_circuit_phi (fun a => (mu a).map (algebraMap A F)) i e t n
  have hv1 : 1 ≤ v := by omega
  have hsize : κ * ∑ k, (lits k).length ≤ m := by
    have e1 : t + n + Fintype.card Q + Fintype.card S + Fintype.card Γ + 2 ≤ v ^ (H + 2) := by
      have a1 : v ^ (H - 32) ≤ v ^ (H + 1) := pow_le_pow hv1 (by omega)
      have a2 : v ≤ v ^ (H + 1) := Nat.le_self_pow (by omega) v
      have a3 : v ^ (H + 2) = v ^ (H + 1) * v := pow_succ _ _
      have a4 : v ^ (H + 1) * 4 ≤ v ^ (H + 1) * v := Nat.mul_le_mul_left _ (by omega)
      omega
    calc κ * ∑ k, (lits k).length ≤ κ * (1600 * (v ^ (H + 2)) ^ 9) :=
          Nat.mul_le_mul_left _ (hlit.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left e1 9)))
      _ = 1600 * κ * v ^ (9 * (H + 2)) := by rw [← pow_mul, Nat.mul_comm (H + 2) 9]; ring
      _ ≤ v * v ^ (9 * (H + 2)) := Nat.mul_le_mul_right _ (by omega)
      _ = v ^ (9 * (H + 2) + 1) := (pow_succ' _ _).symm
      _ ≤ m := hm
  obtain ⟨Mat, hMat, he⟩ := clauses_of_complete hG lits hne hocc wt hwt hsize
  have e0 : aeval (fun q => aeval (letS F bt n) (Mat q)) (G m) = aeval (letS F bt n) (aeval Mat (G m)) :=
    (comp_aeval_apply Mat (aeval (letS F bt n)) (G m)).symm
  refine ⟨fun q => aeval (letS F bt n) (Mat q), fun q => isAffine_aeval_letS bt n (hMat q), ?_, fun z hz hpl => ?_⟩
  · rw [e0, he]
    exact (totalDegree_aeval_le _ _ (totalDegree_letS bt n)).trans hdeg
  · rw [e0, he, eval_code1 hb, hev _ (by rw [List.length_map, length_tbits]; omega),
      Nc.runVal_map (algebraMap A F) mu i e _ _]
    refine congrArg _ ?_
    have hw : (tbits z).map bt = Nc.Dl.wordG b0 b1 z := by
      rw [← wordG_bits bt z, hbt]
      rfl
    rw [hw]
    refine huni (v ^ H) z t hpl ?_
    have h1 : z.size + v ^ H ≤ 2 * v ^ H := by
      have := hz.trans (pow_le_pow hv1 (show H - 32 ≤ H by omega))
      omega
    have h2 : lg (z.size + v ^ H) ≤ (H + 1) * lg v := by
      refine (lg_mono (h1.trans ?_)).trans (lg_pow_le (by omega))
      rw [pow_succ']
      exact Nat.mul_le_mul_right _ (by omega)
    calc C * (z.size + v ^ H) * lg (z.size + v ^ H) ^ 2 ≤ C * (2 * v ^ H) * ((H + 1) * lg v) ^ 2 :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ h1) (Nat.pow_le_pow_left h2 2)
      _ = v ^ H * (2 * C * (H + 1) ^ 2 * lg v ^ 2) := by ring
      _ ≤ v ^ H * v := Nat.mul_le_mul_left _ (hn₀ v (by omega))
      _ = t := by rw [ht, pow_succ]

open Nc.Acc in
/-- **Paper: proof of Lemma lem:circuit, the program.** "Lemma lem:lowdeg turns it into a program with v^O(a+1) constants
that takes v^(H−32)((a+1) lg v)^O(1) ≤ v^(H−16) steps, as n bounds the degree. All its runs halt, its names have
O((a+1) lg v) bits, and B = 1": for n = v^(H−32)+1, the degree bound n and a circuit over any commutative ring. -/
theorem lem_circuit_program (H : ℕ) (hH : 32 ≤ H) : ∃ c : ℕ, ∀ v a, 100 ≤ v → c * (a + H + 2) * lg v ≤ v →
    ∀ (A : Type) [CommRing A] (R : Type) [CommRing R] [Algebra A R] (θ : List Bool → A) (s : ℕ)
      (p : MvPolynomial (Fin (v ^ (H - 32) + 1) × Option Bool) R), s ≤ v ^ a → Nc.Computes p s →
    ∃ (K : KT R) (D : Tree), (∀ z : Tree, z.size ≤ v ^ (H - 32) → Hl θ (Fm.ofTree D) z ∧
        (∀ r ∈ evl θ (Fm.ofTree D) z, r.cost ≤ v ^ (H - 16) ∧ ∀ q ∈ r.bill, K.InB 1 q) ∧
        val K.lk (evl θ (Fm.ofTree D) z) = ∑ i ∈ Finset.range (v ^ (H - 32) + 1 + 1),
          MvPolynomial.eval (codeB R (v ^ (H - 32) + 1) (tbits z)) (MvPolynomial.homogeneousComponent i p)) ∧
      K.nds ≤ v ^ (3 * a + H + 20) ∧ D.size ≤ v ^ (3 * a + H + 20) ∧ K.ht ≤ (3 * a + H + 20) * lg v := by
  obtain ⟨c, hc⟩ := lem_lowdeg
  refine ⟨c + 10000, fun v a hv hlv A _ R _ _ θ s p hs hp => ?_⟩
  obtain ⟨d, hdd⟩ : ∃ d, d = v ^ (H - 32) + 1 := ⟨_, rfl⟩
  have hN1 : v ^ (H - 32) < v ^ (H - 32) + 1 := Nat.lt_succ_self _
  have hd : d ≤ v ^ (H - 24) := by
    rw [hdd]
    exact Nat.succ_le_of_lt (Nat.pow_lt_pow_right (by omega) (by omega))
  have hN2 : v ^ (H - 32) + 1 ≤ v ^ H := Nat.succ_le_of_lt (Nat.pow_lt_pow_right (by omega) (by omega))
  have hv1 : 1 ≤ v := by omega
  have hv100 : 100 ≤ v := by omega
  obtain ⟨l, hl⟩ : ∃ l, l = lg v := ⟨_, rfl⟩
  have hl2 : 2 ≤ l := hl ▸ lg_ge_two (by omega)
  rw [← hl] at hlv
  obtain ⟨M, hM⟩ : ∃ M, M = lg (v ^ (a + 1)) := ⟨_, rfl⟩
  obtain ⟨m, hm⟩ : ∃ m, m = lg (v ^ H) := ⟨_, rfl⟩
  have hMl : M ≤ (a + 1) * l := by rw [hM, hl]; exact lg_pow_le (by omega)
  have hml : m ≤ H * l := by rw [hm, hl]; exact lg_pow_le (by omega)
  have hMm : M + m + 1 ≤ (a + H + 2) * l := by
    have : (a + H + 2) * l = (a + 1) * l + H * l + l := by ring
    omega
  have hsM : s ≤ 2 ^ M := by
    have h1 := lt_two_pow_lg (v ^ (a + 1))
    rw [← hM] at h1
    exact (hs.trans (Nat.pow_le_pow_right hv1 (Nat.le_succ a))).trans h1.le
  have hNm : v ^ (H - 32) + 1 ≤ 2 ^ m := by
    have h1 := lt_two_pow_lg (v ^ H)
    rw [← hm] at h1
    exact hN2.trans h1.le
  obtain ⟨K, D, hnds, hht, hDsize, hkv⟩ := hc R M m (v ^ (H - 32) + 1) d s p hp hsM hNm
  have hcost : ∀ z : Tree, z.size ≤ v ^ (H - 32) →
      (d + 1) * (800 * (M + m) + 4000) + (z.size + 2) * (40 * m + 60) + 10 * m + 100 ≤ v ^ (H - 16) := by
    intro z hz
    have e1 : 10000 * ((a + H + 2) * l) ≤ v := by
      refine le_trans ?_ hlv
      have : (c + 10000) * (a + H + 2) * l = c * ((a + H + 2) * l) + 10000 * ((a + H + 2) * l) := by ring
      rw [this]
      exact Nat.le_add_left _ _
    have e2 : 800 * (M + m) + 4000 ≤ v := by omega
    have e3 : 40 * m + 60 ≤ v := by omega
    have e4 : v ^ (H - 24) * v ^ 8 = v ^ (H - 16) := by rw [← pow_add]; congr 1; omega
    have e5 : v ^ (H - 32) ≤ v ^ (H - 24) := Nat.pow_le_pow_right hv1 (by omega)
    have e6 : 1 ≤ v ^ (H - 24) := Nat.one_le_pow _ _ hv1
    have e7 : (d + 1) * (800 * (M + m) + 4000) ≤ 2 * v ^ (H - 24) * v := Nat.mul_le_mul (by omega) e2
    have e8 : (z.size + 2) * (40 * m + 60) ≤ 3 * v ^ (H - 24) * v := Nat.mul_le_mul (by omega) e3
    have e9 : 10 * m + 100 ≤ 2 * v ^ (H - 24) * v := by
      have : v ≤ v ^ (H - 24) * v := Nat.le_mul_of_pos_left _ (by omega)
      have h2 : 2 * v ^ (H - 24) * v = 2 * (v ^ (H - 24) * v) := by ring
      omega
    have e10 : 7 * v ≤ v ^ 8 := by
      calc 7 * v ≤ v * v := Nat.mul_le_mul_right _ (by omega)
        _ = v ^ 2 := (pow_two v).symm
        _ ≤ v ^ 8 := Nat.pow_le_pow_right hv1 (by norm_num)
    calc (d + 1) * (800 * (M + m) + 4000) + (z.size + 2) * (40 * m + 60) + 10 * m + 100
        ≤ 2 * v ^ (H - 24) * v + 3 * v ^ (H - 24) * v + 2 * v ^ (H - 24) * v := by omega
      _ = v ^ (H - 24) * (7 * v) := by ring
      _ ≤ v ^ (H - 24) * v ^ 8 := Nat.mul_le_mul_left _ e10
      _ = v ^ (H - 16) := e4
  refine ⟨K, D, fun z hz => ?_, ?_, ?_, ?_⟩
  · obtain ⟨a1, a2, a3⟩ := hkv A θ z (lt_of_le_of_lt hz hN1)
    rw [hdd] at a3
    exact ⟨a1, fun r hr => ⟨(a2 r hr).1.trans (hcost z hz), (a2 r hr).2⟩, a3⟩
  · -- the number of constants
    have h1 : 2 ^ M ≤ 2 * v ^ (a + 1) := by
      have h2 := two_pow_lg_le (n := v ^ (a + 1)) (by positivity)
      have h3 : M = M - 1 + 1 := by
        have : 1 ≤ lg (v ^ (a + 1)) := by unfold lg; omega
        omega
      rw [← hM] at h2
      rw [h3, pow_succ]
      omega
    have h2 : 2 ^ m ≤ 2 * v ^ H := by
      have h2 := two_pow_lg_le (n := v ^ H) (by positivity)
      have h3 : m = m - 1 + 1 := by
        have : 1 ≤ lg (v ^ H) := by unfold lg; omega
        omega
      rw [← hm] at h2
      rw [h3, pow_succ]
      omega
    have h3 : 2 ^ (3 * M + 1) ≤ 16 * v ^ (3 * a + H + 3) := by
      calc 2 ^ (3 * M + 1) = 2 * (2 ^ M) ^ 3 := by rw [pow_succ, mul_comm 3 M, pow_mul]; ring
        _ ≤ 2 * (2 * v ^ (a + 1)) ^ 3 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h1 3)
        _ = 16 * v ^ (3 * a + 3) := by rw [mul_pow, ← pow_mul]; ring
        _ ≤ 16 * v ^ (3 * a + H + 3) := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hv1 (by omega))
    have h4 : 2 ^ (M + m + 3) ≤ 32 * v ^ (3 * a + H + 3) := by
      calc 2 ^ (M + m + 3) = 8 * (2 ^ M * 2 ^ m) := by rw [pow_add, pow_add]; ring
        _ ≤ 8 * (2 * v ^ (a + 1) * (2 * v ^ H)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul h1 h2)
        _ = 32 * v ^ (a + 1 + H) := by rw [pow_add v (a + 1) H]; ring
        _ ≤ 32 * v ^ (3 * a + H + 3) := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hv1 (by omega))
    have h5 : 1 ≤ v ^ (3 * a + H + 3) := Nat.one_le_pow _ _ hv1
    calc K.nds ≤ 2 ^ (3 * M + 1) + 2 ^ (M + m + 3) + 3 := hnds
      _ ≤ 100 * v ^ (3 * a + H + 3) := by omega
      _ ≤ v * v ^ (3 * a + H + 3) := Nat.mul_le_mul_right _ hv100
      _ = v ^ (3 * a + H + 4) := by ring
      _ ≤ v ^ (3 * a + H + 20) := Nat.pow_le_pow_right hv1 (by omega)
  · -- the size of the program
    have h2 : c * (M + m + 1) ≤ v := by
      refine le_trans (Nat.mul_le_mul_left c hMm) (le_trans ?_ hlv)
      have : (c + 10000) * (a + H + 2) * l = c * ((a + H + 2) * l) + 10000 * ((a + H + 2) * l) := by ring
      rw [this]
      exact Nat.le_add_right _ _
    have h3 : d ≤ v ^ H := hd.trans (Nat.pow_le_pow_right hv1 (by omega))
    have h4 : v ≤ v ^ H := Nat.le_self_pow (by omega) v
    calc D.size ≤ 100 * v ^ H := by omega
      _ ≤ v * v ^ H := Nat.mul_le_mul_right _ hv100
      _ = v ^ (H + 1) := by ring
      _ ≤ v ^ (3 * a + H + 20) := Nat.pow_le_pow_right hv1 (by omega)
  · -- the length of names
    refine hht.trans ?_
    rw [← hl]
    have : (3 * a + H + 20) * l = 3 * ((a + 1) * l) + H * l + 17 * l := by ring
    omega

/-- **Paper: proof of Lemma lem:circuit, the names.** "Its names have O((a+1) lg v) bits": less than the L² bits that
Definition def:acc allows. -/
theorem lem_circuit_names {H v a k : ℕ} (hv : 4 ≤ v) (hk : k ≤ (3 * a + H + 20) * lg v) :
    k ≤ lg (max (v ^ H) (v ^ (3 * a + H + 20))) ^ 2 := by
  have hl := lg_ge_two hv
  obtain ⟨l, hl'⟩ : ∃ l, lg v = l + 1 := ⟨Nat.log 2 v, rfl⟩
  obtain ⟨X, hX⟩ : ∃ X, X = lg (max (v ^ H) (v ^ (3 * a + H + 20))) := ⟨_, rfl⟩
  have h1 : (3 * a + H + 20) * l + 1 ≤ X := by
    rw [hX]
    refine le_trans ?_ (lg_mono (le_max_right _ _))
    have := le_lg_pow (n := v) (k := 3 * a + H + 20) (by omega)
    rw [hl', Nat.add_sub_cancel] at this
    exact this
  have h2 : (3 * a + H + 20) * 1 ≤ (3 * a + H + 20) * l := Nat.mul_le_mul_left _ (by omega)
  have h3 : (3 * a + H + 20) * (l + 1) ≤ 2 * X := by rw [mul_add]; omega
  rw [← hX, pow_two]
  rw [hl'] at hk
  exact hk.trans (h3.trans (Nat.mul_le_mul_right _ (by omega)))

/-- The arithmetic of the constants of Lemma lem:circuit. -/
theorem lem_circuit_bound {c H v a : ℕ} (hc : c + H + 8 + 1 ≤ lg v) (h0 : c * (H + 7) * lg v ≤ v)
    (hl : lg v ^ ((H + 35) * a) ≤ v) : c * (a + 5 + H + 2) * lg v ≤ v := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · refine le_trans (le_of_eq ?_) h0
    ring
  · have h6 : a + 5 + H + 2 ≤ lg v * lg v ^ a := by
      calc a + 5 + H + 2 ≤ lg v * 2 ^ a := by
            have : a < 2 ^ a := Nat.lt_two_pow_self
            nlinarith
        _ ≤ lg v * lg v ^ a := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
    refine le_trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul (show c ≤ lg v by omega) h6)) (le_trans ?_ hl)
    calc lg v * (lg v * lg v ^ a) * lg v = lg v ^ (a + 3) := by ring
      _ ≤ lg v ^ ((H + 35) * a) := Nat.pow_le_pow_right (by omega) (by nlinarith)

/-- **Paper: Lemma lem:circuit.** "There are constants B₀, C, v₀ such that for all integers a ≥ 0 and v ≥ v₀ with
(lg v)^(Ca) ≤ v: if PERM_m has a circuit with at most v^a gates over a field R that is an A-algebra in which 2 ≠ 0, for
some m ≥ v^B₀, then R has an accelerator of size v^(C(a+1)) at scale v." In this general form G is any family that is
complete for grid sums, as the permanent (2 ≠ 0) and the Hamiltonian cycle polynomial are; see lem_circuit_perm. -/
theorem lem_circuit (hθ : (Function.support θ).Finite) {H : ℕ} (hH : 32 ≤ H) (κ : ℕ) :
    ∃ B₀ C v₀ : ℕ, 0 < B₀ ∧ ∀ (F : Type) [Field F] [Algebra A F] (G : ∀ S, MvPolynomial (Fin S × Fin S) F),
      Nc.GridComplete F G κ → ∀ v, v₀ ≤ v → ∀ a, lg v ^ (C * a) ≤ v → ∀ m, v ^ B₀ ≤ m → Nc.Computes (G m) (v ^ a) →
        HasAcc θ F H v (v ^ (C * (a + 1))) := by
  obtain ⟨B₀, Z, hB₀, hproj⟩ := lem_circuit_universal hθ hH κ
  obtain ⟨c, hc⟩ := lem_circuit_program H hH
  obtain ⟨n₀, hn₀⟩ := poly_lg (c * (H + 7)) 1
  refine ⟨B₀, H + 35, Z + n₀ + 2 ^ (c + H + 8) + 100, hB₀, fun F _ _ G hG v hv a hl m hm hs => ?_⟩
  have hp := Nat.one_le_two_pow (n := c + H + 8)
  have hlv : c + H + 8 + 1 ≤ lg v := le_lg_of_two_pow_le (by omega)
  have hcv := lem_circuit_bound hlv (by simpa using hn₀ v (by omega)) hl
  obtain ⟨Mat, hMat, hdeg, hev⟩ := hproj F G hG v m (by omega) hm
  -- O(v^a) gates for Φ
  have hgates : 5 * v ^ a ≤ v ^ (a + 5) := by
    rw [pow_add, Nat.mul_comm]
    exact Nat.mul_le_mul_left _ (le_trans (by omega : 5 ≤ v) (Nat.le_self_pow (by norm_num) v))
  obtain ⟨K, D, hD, hn, hsz, hht⟩ := hc v (a + 5) (by omega) hcv A F θ (5 * v ^ a) (MvPolynomial.aeval Mat (G m)) hgates
    (hs.aeval _ hMat)
  have hle : v ^ (3 * (a + 5) + H + 20) ≤ v ^ ((H + 35) * (a + 1)) :=
    Nat.pow_le_pow_right (by omega) (by nlinarith)
  have hlg := lg_mono (max_le_max (le_refl (v ^ H)) hle)
  refine ⟨K, 1, D, ⟨fun z hz => ⟨(hD z hz).1, (hD z hz).2.1⟩, fun z hz hpl => ?_⟩, hn.trans hle, hsz.trans hle,
    (lem_circuit_names (by omega) hht).trans (Nat.pow_le_pow_left hlg 2), Nat.one_le_pow _ _ (Nat.succ_pos _)⟩
  rw [(hD z hz).2.2, ← Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hdeg)), ← map_sum,
    MvPolynomial.sum_homogeneousComponent, hev z hz hpl]
  intro i _ hi
  rw [Finset.mem_range] at hi
  rw [MvPolynomial.homogeneousComponent_eq_zero _ _ (by omega), map_zero]

/-- **Paper: Lemma lem:circuit, as printed**, for the permanent. -/
theorem lem_circuit_perm (hθ : (Function.support θ).Finite) {H : ℕ} (hH : 32 ≤ H) :
    ∃ B₀ C v₀ : ℕ, ∀ (F : Type) [Field F] [Algebra A F], (2 : F) ≠ 0 → ∀ v, v₀ ≤ v → ∀ a, lg v ^ (C * a) ≤ v →
      ∀ m, v ^ B₀ ≤ m → Nc.Computes (Nc.genPerm F m) (v ^ a) → HasAcc θ F H v (v ^ (C * (a + 1))) := by
  obtain ⟨B₀, C, v₀, -, h⟩ := lem_circuit hθ hH 3
  exact ⟨B₀, C, v₀, fun F _ _ h2 => h F (Nc.genPerm F) (gridComplete_perm h2)⟩

end Paper
