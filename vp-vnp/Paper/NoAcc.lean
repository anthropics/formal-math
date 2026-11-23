/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Paper.Next
import NS1.Diag
import NS1.Finite

/-!
# The paper, section "One scale is all scales": no small accelerators
-/

namespace Paper

open NS1
open _root_.NS1.Tree

variable {A : Type} [CommRing A] {θ : List Bool → A} {R : Type} [CommRing R] [Algebra A R]

/-- **Paper: proof of Theorem thm:noacc, the finite field.** "As A is finitely generated, so is the ring that its
constants generate over A; modulo a maximal ideal this is a finite field E, over which it is still an accelerator." -/
theorem thm_noacc_finite_field [Algebra.FiniteType ℤ A] [Nontrivial R] {H v t : ℕ} {K : KT R} {B : ℕ} {D : Tree}
    (h : IsAccT θ H v t K B D) : ∃ (E : Type) (_ : Field E) (_ : Algebra A E) (_ : Finite E) (K' : KT E),
      IsAccT θ H v t K' B D ∧ K'.nds = K.nds ∧ K'.ht = K.ht := by
  let S : Subalgebra A R := Algebra.adjoin A K.consts
  obtain ⟨K', hK'⟩ := KT.exists_lift S K Algebra.subset_adjoin
  have h1 : IsAccT θ H v t K' B D := by
    rw [← hK'] at h
    exact h.of_map Subtype.val_injective
  have f1 : (Int.castRingHom A).FiniteType := by
    rw [← algebraMap_int_eq, RingHom.finiteType_algebraMap]
    infer_instance
  have f2 : (algebraMap A S).FiniteType := by
    rw [RingHom.finiteType_algebraMap]
    exact .adjoin_of_finite K.consts_finite
  obtain ⟨I, hI⟩ := Ideal.exists_maximal S
  have f3 : (Ideal.Quotient.mk I).FiniteType := RingHom.FiniteType.of_surjective _ Ideal.Quotient.mk_surjective
  have f4 : (Int.castRingHom (S ⧸ I)).FiniteType := by
    have := (f3.comp f2).comp f1
    rwa [Subsingleton.elim (((Ideal.Quotient.mk I).comp (algebraMap A S)).comp (Int.castRingHom A))
      (Int.castRingHom (S ⧸ I))] at this
  let _ : Field (S ⧸ I) := Ideal.Quotient.field I
  refine ⟨S ⧸ I, inferInstance, inferInstance, finite_of_finiteType_int _ f4, K'.map (Ideal.Quotient.mkₐ A I), h1.map _, ?_, ?_⟩
  · rw [KT.nds_map, ← hK', KT.nds_map]
  · rw [KT.ht_map, ← hK', KT.ht_map]

/-- **Paper: proof of Theorem thm:noacc, the number m_E.** "As E is finite, there is m_E such that every j ≥ 0 has an
r(j) < m_E with c^(2^j) = c^(2^r(j)) for all c ∈ E; this is where finiteness is needed." Here M is m_E and red is r. -/
theorem thm_noacc_periodic (R : Type) [CommRing R] [Finite R] :
    ∃ (M : ℕ) (red : ℕ → ℕ), (∀ i, red i < M) ∧ ∀ (c : R) i, c ^ 2 ^ red i = c ^ 2 ^ i := by
  classical
  let f : ℕ → R → R := fun i c => c ^ 2 ^ i
  have hfin : (Set.range f).Finite := Set.toFinite _
  let red : ℕ → ℕ := fun i => Nat.find (⟨i, rfl⟩ : ∃ j, f j = f i)
  have hred : ∀ i, f (red i) = f i := fun i => Nat.find_spec (⟨i, rfl⟩ : ∃ j, f j = f i)
  have hinj : ∀ i j, f i = f j → red i = red j := by
    intro i j hij
    simp only [red, hij]
  have hbdd : (Set.range red).Finite := by
    have : Set.range red ⊆ (fun g : R → R => if h : ∃ i, f i = g then red h.choose else 0) '' Set.range f := by
      rintro _ ⟨i, rfl⟩
      refine ⟨f i, ⟨i, rfl⟩, ?_⟩
      have h : ∃ j, f j = f i := ⟨i, rfl⟩
      show (if h : ∃ j, f j = f i then red h.choose else 0) = red i
      rw [dif_pos h]
      exact hinj _ _ h.choose_spec
    exact (hfin.image _).subset this
  obtain ⟨M, hM⟩ := hbdd.bddAbove
  refine ⟨M + 1, red, fun i => Nat.lt_succ_of_le (hM ⟨i, rfl⟩), fun c i => congrFun (hred i) c⟩

set_option maxHeartbeats 1000000 in
/-- **Paper: proof of Theorem thm:noacc, the diagonal.** "Let v be large against E and the number of constants": the
program P guesses a bit, and for one value accepts with weight 1, for the other guesses exponents e, names λ^e and runs D
on the instance z_e of P applied to P; so its value V satisfies V = 1 + V, "impossible in E". -/
theorem thm_noacc_diagonal {h : ℕ} (hh : 17 ≤ h) [Nontrivial R] {v : ℕ} {K : KT R} {B : ℕ} {D : Tree}
    (hD : IsAccT θ (16 * h) v (v ^ (16 * h - 16)) K B D) (hcst : cst ≤ v) (hK : K.nds ≤ v) (hDs : D.size ≤ v ^ (4 * h))
    {M : ℕ} {red : ℕ → ℕ} (hM : ∀ i, red i < M) (hred : ∀ (c : R) i, c ^ 2 ^ red i = c ^ 2 ^ i) {J X : ℕ}
    (hJ : v ^ (16 * h - 15) < 2 ^ J) (hX : K.ht + max B M + J + 1 ≤ X) (hX10 : 10 ≤ X) (hXv : 1000 * X ^ 3 ≤ v) :
    False := by
  set B' := max B M with hB'
  have hX3 : 10 * X ^ 2 ≤ X ^ 3 := by
    have : X ^ 3 = X * X ^ 2 := by ring
    rw [this]
    exact Nat.mul_le_mul_right _ hX10
  have hX2 : 10 * X ≤ X ^ 2 := by rw [pow_two]; exact Nat.mul_le_mul_right _ hX10
  rw [cst_def] at hcst
  obtain ⟨sU, hsU⟩ : ∃ n, n = UF.code.size := ⟨_, rfl⟩
  obtain ⟨sW, hsW⟩ : ∃ n, n = WF.code.size := ⟨_, rfl⟩
  rw [← hsU, ← hsW] at hcst
  have hv4 : 2000 ≤ v := by omega
  have hv1 : 1 ≤ v := by omega
  have pu : ∀ a, v ^ (a + 1) = v * v ^ a := fun a => by rw [pow_succ]; ring
  have pbig : ∀ a, 2000 * v ^ a ≤ v ^ (a + 1) := fun a => by rw [pu]; exact Nat.mul_le_mul_right _ hv4
  have ppos : ∀ a, 1 ≤ v ^ a := fun a => Nat.one_le_pow _ _ (by omega)
  set nB := (K.expand B').nds with hnB
  have hnB1 : nB ≤ K.nds * (2 * X) := (KT.nds_expand B' K).trans (Nat.mul_le_mul_left _ (by omega))
  have hnBX : ∀ c, c * X ^ 2 ≤ 1000 * X ^ 3 → nB * (c * X) ≤ 2 * v ^ 2 := by
    intro c hc
    calc nB * (c * X) ≤ K.nds * (2 * X) * (c * X) := Nat.mul_le_mul_right _ hnB1
      _ = K.nds * (2 * (c * X ^ 2)) := by ring
      _ ≤ v * (2 * v) := Nat.mul_le_mul hK (by omega)
      _ = 2 * v ^ 2 := by ring
  have hJX : J + 1 ≤ X := by omega
  -- the program
  set g : Fm := gt red J B' K [] with hg
  set p : Tree := (diagF D g).code with hp
  have hps : p.size ≤ v ^ (4 * h + 1) := by
    have s3 := size_gt red J B' K [] M (fun i _ => (hM i).le)
    rw [List.length_nil] at s3
    have s4 : g.code.size ≤ 2 * v ^ 2 := by
      have := hnBX (14 * X) (by
        rw [show 14 * X * X ^ 2 = 14 * X ^ 3 by ring]
        omega)
      calc g.code.size ≤ nB * ((J + 1) * (4 * (0 + K.ht + M) + 100)) := s3
        _ ≤ nB * (X * (14 * X)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul hJX (by
            have := le_max_right B M
            omega))
        _ = nB * (14 * X * X) := by ring
        _ ≤ 2 * v ^ 2 := this
    have s5 : p.size ≤ D.size + g.code.size + sW + 500 := by
      simp only [hp, diagF, app, ZE, Fm.code, Tree.size, size_num, hsW]
      omega
    have s6 : v ^ 2 ≤ v ^ (4 * h) := pow_le_pow hv1 (by omega)
    have s7 : sW + 500 ≤ v ^ (4 * h) := by
      calc sW + 500 ≤ v ^ 1 := by rw [pow_one]; omega
        _ ≤ _ := pow_le_pow hv1 (by omega)
    have := pbig (4 * h)
    omega
  have hgev : ∀ z : Tree, ∃ l, Ev θ g z l ∧ List.Forall₂ (RelG K.lk (K.InB B') ((8 * J + 10) * nB)) l
      ((K.expand B').budg J) := by
    intro z
    refine gt_ev z K [] fun q hq i _ => ⟨?_, ?_⟩
    · obtain ⟨c, hc⟩ := hq.lk
      rw [List.nil_append, hc, hc, hred]
    · exact hq.inB (lt_of_lt_of_le (hM i) (le_max_right _ _))
  have hqs : ∀ q ∈ (K.expand B').budg J, q.1.ht ≤ K.ht + B' + J + 1 ∧ q.1.nds ≤ nB * (J + 1) := by
    intro q hq
    have h1 := KT.ht_budg hq
    have h2 := KT.ht_expand B' K
    exact ⟨by omega, KT.nds_budg hq⟩
  have hn4 : 4 * (nB * (J + 1)) ≤ 2 * v ^ 2 := by
    have := hnBX 4 (by omega)
    calc 4 * (nB * (J + 1)) ≤ 4 * (nB * X) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hJX)
      _ = nB * (4 * X) := by ring
      _ ≤ _ := this
  have hsz : ∀ q ∈ (K.expand B').budg J, (zq p p q.1).size ≤ v ^ (16 * h - 32) := by
    intro q hq
    have h1 := Bt.size_enc q.1
    have h2 := (hqs q hq).2
    have s1 : v ^ 2 ≤ v ^ (4 * h + 1) := pow_le_pow hv1 (by omega)
    have s2 : sW + 10 ≤ v ^ (4 * h + 1) := by
      calc sW + 10 ≤ v ^ 1 := by rw [pow_one]; omega
        _ ≤ _ := pow_le_pow hv1 (by omega)
    have s3 := pbig (4 * h + 1)
    have s4 : v ^ (4 * h + 1 + 1) ≤ v ^ (16 * h - 32) := pow_le_pow hv1 (by omega)
    simp only [zq, Tree.size]
    rw [← hsW]
    omega
  -- its runs
  obtain ⟨lg, eg, rg⟩ := hgev p
  obtain ⟨l, e, hl, hval⟩ := diagF_ev (D := D) eg rg (tD := v ^ (16 * h - 16)) fun q hq => by
    obtain ⟨a1, a2⟩ := hD.run _ (hsz q hq)
    exact ⟨a1, fun r hr => ⟨(a2 r hr).1, fun n hn => ((a2 r hr).2 n hn).mono (le_max_left _ _)⟩⟩
  have ep : Ev θ (Fm.ofTree p) p l := by rw [hp, Fm.ofTree_code]; exact e
  -- time
  have hT : ∀ r ∈ l, r.cost ≤ v ^ (16 * h - 15) := by
    intro r hr
    refine (hl r hr).1.trans ?_
    have m1 : (8 * J + 10) * nB ≤ 2 * v ^ 2 := by
      have := hnBX 9 (by omega)
      calc (8 * J + 10) * nB ≤ 9 * X * nB := Nat.mul_le_mul_right _ (by omega)
        _ = nB * (9 * X) := by ring
        _ ≤ _ := this
    have m2 : v ^ 2 ≤ v ^ (16 * h - 16) := pow_le_pow hv1 (by omega)
    have m3 := pbig (16 * h - 16)
    have m4 := ppos (16 * h - 16)
    have m5 : 16 * h - 15 = 16 * h - 16 + 1 := by omega
    rw [m5]
    omega
  have hJ' : ∀ r ∈ l, r.bill.length < 2 ^ J := fun r hr =>
    lt_of_le_of_lt ((bill_le ep r hr).trans (hT r hr)) hJ
  -- Lemma lem:postpone for the program applied to itself
  have hbill : ∀ r ∈ l, ∀ n ∈ r.bill, K.lk n = (K.expand B').lookup n := fun r hr n hn => KT.lookup_expand ((hl r hr).2 n hn)
  obtain ⟨hsum, hze⟩ := lem_postpone p p (T := v ^ (16 * h - 15)) hJ ep.hl (by rw [ep.evl]; exact hT)
    (K.expand B') K.lk (by rw [ep.evl]; exact hbill)
  rw [ep.evl] at hsum
  have hpl : ∀ q ∈ (K.expand B').budg J, Plain θ (v ^ (16 * h)) (zq p p q.1) := by
    intro q hq
    obtain ⟨pl, -, -⟩ := hze q hq
    refine Plain.of_le pl ?_
    have hht := KT.ht_expand B' K
    have m1 : 1000 + 100 * ((K.expand B').ht + J + 1) + 2 ≤ v := by omega
    have m2 : 40 * (nB * (J + 1)) ≤ 20 * v ^ 2 := by omega
    have m3 : v ^ 2 ≤ v ^ (16 * h - 16) := pow_le_pow hv1 (by omega)
    have m4 := pbig (16 * h - 16)
    have m5 : 16 * h - 15 = 16 * h - 16 + 1 := by omega
    have m6 : 1 ≤ v ^ (16 * h - 16) := ppos _
    have m7 : 40 * (nB * (J + 1)) + 40 ≤ v ^ (16 * h - 15) := by
      rw [m5]
      omega
    have m8 : v * v ^ (16 * h - 15) ≤ v ^ (16 * h) := by
      rw [← pu]
      exact pow_le_pow hv1 (by omega)
    rw [← hnB]
    calc (1000 + 100 * ((K.expand B').ht + J + 1)) * v ^ (16 * h - 15) + 40 * (nB * (J + 1)) + 40
        ≤ (1000 + 100 * ((K.expand B').ht + J + 1) + 2) * v ^ (16 * h - 15) := by rw [add_mul _ 2]; omega
      _ ≤ v * v ^ (16 * h - 15) := Nat.mul_le_mul_right _ m1
      _ ≤ _ := m8
  -- 1 + its own value
  have key : val K.lk l = 1 + val K.lk l := by
    conv_lhs => rw [hval]
    congr 1
    rw [hsum]
    refine congrArg List.sum (List.map_congr_left fun q hq => congrArg (q.2 * ·) ?_)
    exact hD.val _ (hsz q hq) (hpl q hq)
  have : (1 : R) = 0 := by
    have := congrArg (· - val K.lk l) key
    simpa using this.symm
  exact one_ne_zero this

/-- What the iteration keeps at a scale u: "programs with the two properties of an accelerator, with programs of size
at most u^(4h₀), the same constants, and exponent bounds O(lg u)³". -/
structure AllScales (θ : List Bool → A) (h : ℕ) (u : ℕ) (K : KT R) (B : ℕ) (D : Tree) : Prop where
  acc : IsAccT θ (16 * h) u (u ^ (16 * h - 16)) K B D
  nds : K.nds ≤ u
  size : D.size ≤ u ^ (4 * h)
  ht : K.ht ≤ 100000 * h ^ 3 * lg u ^ 3
  B_le : B ≤ 100000 * h ^ 3 * lg u ^ 3

set_option maxHeartbeats 2000000 in
/-- **Paper: proof of Theorem thm:noacc, all scales.** "Proposition prop:next with α = max(5,a), and then again and
again with α = 5, gives programs with the two properties of an accelerator at arbitrarily large scales v_i, with programs
of size at most v_i^(4h₀), with the same constants and with exponent bounds O(lg v_i)³." -/
theorem thm_noacc_all_scales {h : ℕ} (hh : 17 ≤ h) {C₀ v₀ : ℕ} (hcut : CutHyp θ (16 * h) C₀ v₀) :
    ∃ C v₁ : ℕ, ∀ (R : Type) [CommRing R] [Algebra A R], ∀ v, v₁ ≤ v → ∀ a, lg v ^ (C * a) ≤ v →
      ∀ (K : KT R) (B : ℕ) (D : Tree), IsAccT θ (16 * h) v (v ^ (16 * h - 16)) K B D → K.nds ≤ v ^ a → D.size ≤ v ^ a →
      K.ht ≤ lg (max (v ^ (16 * h)) (v ^ a)) ^ 2 → B ≤ lg (max (v ^ (16 * h)) (v ^ a)) ^ 3 →
      ∀ n, ∃ u B' D', n ≤ u ∧ AllScales θ h u K B' D' := by
  obtain ⟨C, v₂, hnext⟩ := prop_next hh hcut 4
  obtain ⟨n5, hn5⟩ := poly_lg 1 (C * 5)
  refine ⟨C, v₂ + n5 + 2 ^ (100000 * h ^ 3) + 4, fun R _ _ v hv a ha K B D hD hKn hDs hKh hB => ?_⟩
  have hp : 1 ≤ 2 ^ (100000 * h ^ 3) := Nat.one_le_two_pow
  have hh3 : h ≤ h ^ 3 := Nat.le_self_pow (by norm_num) h
  have hv4 : 4 ≤ v := by omega
  have hv1 : 1 ≤ v := by omega
  have hl2 := lg_ge_two hv4
  have hlbig : 100000 * h ^ 3 + 1 ≤ lg v := le_lg_of_two_pow_le (by omega)
  obtain ⟨l, hl⟩ : ∃ l, l = lg v := ⟨_, rfl⟩
  rw [← hl] at ha hl2 hlbig
  obtain ⟨α, hα⟩ : ∃ α, α = max 5 a := ⟨_, rfl⟩
  have hα5 : 5 ≤ α := hα ▸ le_max_left _ _
  have haα : a ≤ α := hα ▸ le_max_right _ _
  have hlog : l ^ (C * α) ≤ v := by
    rcases le_total 5 a with h5 | h5
    · rw [hα, max_eq_right h5]
      exact ha
    · rw [hα, max_eq_left h5]
      simpa [hl] using hn5 v (by omega)
  obtain ⟨P, hP⟩ : ∃ P, P = h * α * l := ⟨_, rfl⟩
  have hVs : lg (max (v ^ (16 * h)) (v ^ a)) ≤ 16 * P := by
    have hmax : max (v ^ (16 * h)) (v ^ a) ≤ v ^ (16 * h * α) := by
      apply max_le
      · exact pow_le_pow hv1 (Nat.le_mul_of_pos_right _ (by omega))
      · exact pow_le_pow hv1 (haα.trans (Nat.le_mul_of_pos_left _ (by omega)))
    refine (lg_mono hmax).trans ((lg_pow_le (Nat.mul_pos (by omega) (by omega))).trans (le_of_eq ?_))
    rw [hP, ← hl]
    ring
  have hPpos : 1 ≤ P := hP ▸ Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)
  have hB3 : B ≤ 4096 * P ^ 3 := hB.trans ((Nat.pow_le_pow_left hVs 3).trans (le_of_eq (by ring)))
  have hK3 : K.ht ≤ 256 * P ^ 3 := by
    refine hKh.trans ((Nat.pow_le_pow_left hVs 2).trans ?_)
    rw [mul_pow]
    exact Nat.mul_le_mul le_rfl (Nat.pow_le_pow_right hPpos (by norm_num))
  have hP4 : 4096 * P ^ 3 ≤ (α * l) ^ 4 := by
    calc 4096 * P ^ 3 = 4096 * h ^ 3 * (α * l) ^ 3 := by rw [hP]; ring
      _ ≤ α * l * (α * l) ^ 3 := Nat.mul_le_mul_right _ (by
          have : l ≤ α * l := Nat.le_mul_of_pos_left _ (by omega)
          omega)
      _ = (α * l) ^ 4 := by ring
  have hah : a ≤ h * α := haα.trans (Nat.le_mul_of_pos_left _ (by omega))
  obtain ⟨D₁, hD₁, hs₁⟩ := hnext R v (by omega) α hα5 (hl ▸ hlog) K B D hD (hKn.trans (pow_le_pow hv1 hah))
    (hDs.trans (pow_le_pow hv1 hah)) (by rw [← hl]; omega) (by rw [← hl]; omega)
  rw [← hl] at hD₁
  have hinc : 51 * h * α ^ 2 * l ≤ 51 * P ^ 3 := by
    calc 51 * h * α ^ 2 * l ≤ 51 * (h * α * l) ^ 2 := by
          have : h * α ^ 2 * l ≤ h * h * (α ^ 2 * (l * l)) := by
            calc h * α ^ 2 * l = h * 1 * (α ^ 2 * (l * 1)) := by ring
              _ ≤ _ := by gcongr <;> omega
          calc 51 * h * α ^ 2 * l = 51 * (h * α ^ 2 * l) := by ring
            _ ≤ 51 * (h * h * (α ^ 2 * (l * l))) := Nat.mul_le_mul_left _ this
            _ = _ := by ring
      _ ≤ 51 * P ^ 3 := hP ▸ Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (hP ▸ hPpos) (by norm_num))
  have hlgα : α * l ≤ 2 * lg (v ^ α) := by
    have h1 := le_lg_pow (n := v) (k := α) (by omega)
    have h2 : α * (l - 1) = α * l - α := by rw [Nat.mul_sub, Nat.mul_one]
    have h3 : α * 2 ≤ α * l := Nat.mul_le_mul_left _ hl2
    rw [← hl] at h1
    omega
  have hcBP : 12500 * P ^ 3 ≤ 100000 * h ^ 3 * lg (v ^ α) ^ 3 := by
    calc 12500 * P ^ 3 = 12500 * h ^ 3 * (α * l) ^ 3 := by rw [hP]; ring
      _ ≤ 12500 * h ^ 3 * (2 * lg (v ^ α)) ^ 3 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hlgα 3)
      _ = _ := by ring
  have hvα : v ≤ v ^ α := Nat.le_self_pow (by omega) v
  have start : AllScales θ h (v ^ α) K (B + 51 * h * α ^ 2 * l) D₁ :=
    ⟨hD₁.mono (pow_le_pow (by omega) (by omega)) le_rfl, hKn.trans (pow_le_pow hv1 haα), hs₁, by omega, by omega⟩
  -- again and again with α = 5
  have step : ∀ u B' D', v ≤ u → AllScales θ h u K B' D' → ∃ B'' D'', AllScales θ h (u ^ 5) K B'' D'' := by
    intro u B' D' hu hI
    have hu1 : 1 ≤ u := by omega
    have hlu : lg v ≤ lg u := lg_mono hu
    have hlu5 : 2 * lg u ≤ lg (u ^ 5) := by
      have := le_lg_pow (n := u) (k := 5) (by omega)
      omega
    have hh5 := hI.ht
    have hB5 := hI.B_le
    obtain ⟨L, hL⟩ : ∃ L, L = lg u := ⟨_, rfl⟩
    rw [← hL] at hlu hlu5 hh5 hB5
    have h4 : 100000 * h ^ 3 * L ^ 3 ≤ (5 * L) ^ 4 := by
      calc 100000 * h ^ 3 * L ^ 3 ≤ L * L ^ 3 := Nat.mul_le_mul_right _ (by omega)
        _ ≤ _ := by rw [← pow_succ']; exact Nat.pow_le_pow_left (by omega) _
    obtain ⟨D'', hD'', hs''⟩ := hnext R u (by omega) 5 le_rfl (by simpa [Nat.mul_comm] using hn5 u (by omega)) K B' D'
      hI.acc (hI.nds.trans (Nat.le_self_pow (Nat.mul_ne_zero (by omega) (by norm_num)) u))
      (hI.size.trans (pow_le_pow hu1 (by omega))) (by rw [← hL]; omega) (by rw [← hL]; omega)
    rw [← hL] at hD''
    have h8 : 8 * (100000 * h ^ 3 * L ^ 3) ≤ 100000 * h ^ 3 * lg (u ^ 5) ^ 3 := by
      calc 8 * (100000 * h ^ 3 * L ^ 3) = 100000 * h ^ 3 * (2 * L) ^ 3 := by ring
        _ ≤ _ := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hlu5 3)
    have h6 : 1275 * (h * L) ≤ 100000 * h ^ 3 * L ^ 3 := by
      calc 1275 * (h * L) ≤ 100000 * (h ^ 3 * L ^ 3) :=
            Nat.mul_le_mul (by norm_num) (Nat.mul_le_mul hh3 (Nat.le_self_pow (by norm_num) L))
        _ = _ := by ring
    have e5 : 51 * h * 5 ^ 2 * L = 1275 * (h * L) := by ring
    exact ⟨_, D'', hD''.mono (pow_le_pow (Nat.one_le_pow _ _ (by omega)) (by omega)) le_rfl,
      hI.nds.trans (Nat.le_self_pow (by norm_num) u), hs'', by omega, by omega⟩
  intro n
  suffices ∃ u B' D', n ≤ u ∧ v ≤ u ∧ AllScales θ h u K B' D' by
    obtain ⟨u, B', D', h1, -, h2⟩ := this
    exact ⟨u, B', D', h1, h2⟩
  induction n with
  | zero => exact ⟨_, _, _, Nat.zero_le _, hvα, start⟩
  | succ n ih =>
    obtain ⟨u, B', D', hn, hu, hI⟩ := ih
    obtain ⟨B'', D'', hI'⟩ := step u B' D' hu hI
    have : u * 4 ≤ u ^ 5 := by
      calc u * 4 ≤ u * u ^ 4 := Nat.mul_le_mul_left _ ((show 4 ≤ u by omega).trans (Nat.le_self_pow (by norm_num) u))
        _ = u ^ 5 := by ring
    exact ⟨u ^ 5, B'', D'', by omega, hu.trans (Nat.le_self_pow (by norm_num) u), hI'⟩

set_option maxHeartbeats 2000000 in
/-- **Paper: Theorem thm:noacc.** "There are C and v₁ such that for all integers a ≥ 0 and v ≥ v₁ with (lg v)^(Ca) ≤ v no
nonzero commutative A-algebra has an accelerator of size v^a at scale v." -/
theorem thm_noacc {h : ℕ} (hh : 17 ≤ h) [Algebra.FiniteType ℤ A] {C₀ v₀ : ℕ} (hcut : CutHyp θ (16 * h) C₀ v₀) :
    ∃ C v₁ : ℕ, ∀ v, v₁ ≤ v → ∀ a, lg v ^ (C * a) ≤ v → ∀ (R : Type) [CommRing R] [Nontrivial R] [Algebra A R],
      ¬ HasAcc θ R (16 * h) v (v ^ a) := by
  obtain ⟨C, v₁, hall⟩ := thm_noacc_all_scales hh hcut
  obtain ⟨n9, hn9⟩ := poly_lg (1000 * (3 * (100000 * h ^ 3)) ^ 3) 9
  refine ⟨C, v₁, fun v hv a ha R _ _ _ hacc => ?_⟩
  obtain ⟨K, B, D, hD, hKn, hDs, hKh, hB⟩ := hacc
  obtain ⟨E, _, _, _, K', hD', hn', hh'⟩ := thm_noacc_finite_field hD
  obtain ⟨M, red, hM, hred⟩ := thm_noacc_periodic E
  obtain ⟨u, B', D', hu, hI⟩ := hall E v hv a ha K' B D hD' (hn'.trans_le hKn) hDs (hh'.trans_le hKh) hB
    (2 ^ (M + 2000 * h) + cst + n9)
  obtain ⟨cs, hcs⟩ : ∃ cs, cs = cst := ⟨_, rfl⟩
  rw [← hcs] at hu
  have hp : 1 ≤ 2 ^ (M + 2000 * h) := Nat.one_le_two_pow
  have hu1 : 1 ≤ u := by omega
  have hl : M + 2000 * h + 1 ≤ lg u := le_lg_of_two_pow_le (by omega)
  have hlt := lt_two_pow_lg u
  have hsmall := hn9 u (by omega)
  have a1 := hI.ht
  have a2 := hI.B_le
  obtain ⟨L, hL⟩ : ∃ L, L = lg u := ⟨_, rfl⟩
  rw [← hL] at hl hlt hsmall a1 a2
  refine thm_noacc_diagonal hh hI.acc (by omega) hI.nds hI.size hM hred (J := 16 * h * L)
    (X := K'.ht + max B' M + 16 * h * L + 10) ?_ (by omega) (by omega) ?_
  · rw [Nat.mul_comm (16 * h) L, pow_mul]
    calc u ^ (16 * h - 15) ≤ u ^ (16 * h) := pow_le_pow hu1 (by omega)
      _ < (2 ^ L) ^ (16 * h) := Nat.pow_lt_pow_left hlt (by omega)
  · refine le_trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (m := 3 * (100000 * h ^ 3) * L ^ 3) ?_ 3)) (le_trans (le_of_eq ?_) hsmall)
    · have h1 : 17 * (h * L) ≤ 100000 * (h ^ 3 * L ^ 3) :=
        Nat.mul_le_mul (by norm_num) (Nat.mul_le_mul (Nat.le_self_pow (by norm_num) h) (Nat.le_self_pow (by norm_num) L))
      have h2 : L ≤ h * L := Nat.le_mul_of_pos_left _ (by omega)
      have e1 : 16 * h * L = 16 * (h * L) := by ring
      have e2 : 3 * (100000 * h ^ 3) * L ^ 3 = 3 * (100000 * (h ^ 3 * L ^ 3)) := by ring
      have e3 : 100000 * h ^ 3 * L ^ 3 = 100000 * (h ^ 3 * L ^ 3) := by ring
      omega
    · ring

end Paper
