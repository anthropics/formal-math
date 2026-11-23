/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Paper.Postpone

/-!
# One round: guess exponents, postpone, cut, accelerate
-/

set_option linter.unusedSectionVars false

namespace NS1

open _root_.NS1.Tree

variable {A : Type} [CommRing A] {θ : List Bool → A} {R : Type} [CommRing R] [Algebra A R]

/-- The cut at the scale `v ^ H`, for times up to `v ^ (H * α)`. -/
def CutAt (θ : List Bool → A) (H v α : ℕ) : Prop :=
  ∀ τ s, v ^ H ≤ τ → τ ≤ v ^ (H * α) → s * v ^ 48 ≤ τ → ∃ G, CutProg θ H v τ s G

theorem CutHyp.at {H C₀ v₀ v α : ℕ} (h : CutHyp θ H C₀ v₀) (hv : v₀ ≤ v) (hl : lg v ^ (C₀ * α) ≤ v) : CutAt θ H v α :=
  fun τ s => h v hv α τ s hl

theorem Plain.of_le {T T' : ℕ} {z : Tree} (h : Plain θ T z) (hT : T ≤ T') : Plain θ T' z :=
  ⟨h.1, fun r hr => ⟨(h.2 r hr).1, (h.2 r hr).2.trans hT⟩⟩

/-- A constant: it bounds the sizes of the fixed programs. -/
def cst : ℕ := WF.code.size + UF.code.size + 2000

theorem cst_def : cst = WF.code.size + UF.code.size + 2000 := rfl

theorem size_LP (D : Tree) : (LP D).code.size ≤ D.size + 300 := by
  simp only [LP, Fm.code, Tree.size, size_num]
  omega

theorem size_stepF (D G p : Tree) (g : Fm) :
    (stepF D G p g).code.size ≤ 2 * D.size + G.size + p.size + g.code.size + WF.code.size + 1500 := by
  have := size_LP D
  simp only [stepF, app, ZE, Fm.code, Tree.size, size_num]
  omega

theorem pow_le_pow {u a b : ℕ} (hu : 1 ≤ u) (h : a ≤ b) : u ^ a ≤ u ^ b := Nat.pow_le_pow_right hu h

/-- **One round.** `τ'` bounds the time of the plain instances; `s` their size. -/
theorem round {H u v : ℕ} {K : KT R} {B' : ℕ} {D : Tree} (hD : IsAccT θ H u (u ^ (H - 16)) K B' D)
    {p : Tree} {B τ : ℕ} (hp : IsPre θ H v τ K B p) {J : ℕ} (hJ : τ < 2 ^ J) {τ' s t tG Ln : ℕ} {G : Tree}
    (hG : CutProg θ H u τ' s G)
    (hτ' : MM (K.ht + B + J + 1) * τ + 40 * ((K.expand B).nds * (J + 1)) + 40 ≤ τ')
    (hs : WF.code.size + p.size + v ^ (H - 32) + 4 * ((K.expand B).nds * (J + 1)) + 3 ≤ s)
    (htG : ∀ k, k * u ^ 24 ≤ τ' → k ≤ tG) (hLn : ∀ k, k * u ^ H ≤ τ' * u ^ 2 → k ≤ Ln)
    (ht : (8 * J + 10) * (K.expand B).nds + tG + (u ^ (H - 16) + 30) * Ln + 30 ≤ t) :
    IsAccT θ H v t K (max (B + J) B') (stepF D G p (gt id J B K [])).code := by
  have hg : ∀ z : Tree, ∃ l, Ev θ (gt id J B K []) z l ∧ List.Forall₂
      (RelG K.lk (K.InB (max (B + J) B')) ((8 * J + 10) * (K.expand B).nds)) l ((K.expand B).budg J) := by
    intro z
    refine gt_ev z K [] fun q hq i hi => ⟨?_, ?_⟩
    · rfl
    · exact hq.inB (lt_of_lt_of_le hi (le_max_left _ _))
  have hqs : ∀ q ∈ (K.expand B).budg J, q.1.ht ≤ K.ht + B + J + 1 ∧ q.1.nds ≤ (K.expand B).nds * (J + 1) := by
    intro q hq
    have h1 := KT.ht_budg hq
    have h2 := KT.ht_expand B K
    exact ⟨by omega, KT.nds_budg hq⟩
  have hsz : ∀ z : Tree, z.size ≤ v ^ (H - 32) → ∀ q ∈ (K.expand B).budg J, (zq p z q.1).size ≤ s := by
    intro z hz q hq
    have h1 := Bt.size_enc q.1
    have h2 := (hqs q hq).2
    simp only [zq, Tree.size]
    omega
  have key : ∀ z : Tree, z.size ≤ v ^ (H - 32) → ∀ q ∈ (K.expand B).budg J,
      Hl θ (Fm.ofTree G) (zq p z q.1) ∧ ∀ r ∈ evl θ (Fm.ofTree G) (zq p z q.1), r.bill = [] ∧
      r.cost ≤ tG ∧ r.out.toList.length ≤ Ln ∧ ∀ y ∈ r.out.toList, Hl θ (Fm.ofTree D) y ∧
        ∀ r ∈ evl θ (Fm.ofTree D) y, r.cost ≤ u ^ (H - 16) ∧ ∀ n ∈ r.bill, K.InB (max (B + J) B') n := by
    intro z hz q hq
    obtain ⟨h1, h2⟩ := hG.list _ (hsz z hz q hq)
    refine ⟨h1, fun r hr => ?_⟩
    obtain ⟨a1, a2, a3, a4⟩ := h2 r hr
    refine ⟨a1, htG _ a2, hLn _ a3, fun y hy => ?_⟩
    obtain ⟨b1, b2⟩ := hD.run y (a4 y hy)
    exact ⟨b1, fun r hr => ⟨(b2 r hr).1, fun n hn => ((b2 r hr).2 n hn).mono (le_max_right _ _)⟩⟩
  constructor
  · intro z hz
    obtain ⟨lg, eg, rg⟩ := hg z
    obtain ⟨l, e, h1, -⟩ := stepF_ev (p := p) eg rg (key z hz)
    rw [Fm.ofTree_code]
    refine ⟨e.hl, fun r hr => ?_⟩
    rw [e.evl] at hr
    obtain ⟨c1, c2⟩ := h1 r hr
    exact ⟨c1.trans ht, c2⟩
  · intro z hz hpl
    obtain ⟨lg, eg, rg⟩ := hg z
    obtain ⟨l, e, -, h2⟩ := stepF_ev (p := p) eg rg (key z hz)
    rw [Fm.ofTree_code, e.evl, h2, ← hp.val z hz hpl]
    obtain ⟨hp1, hp2⟩ := hp.run z hz hpl
    -- Lemma lem:postpone: the value of p, by the exponent vectors
    obtain ⟨hsum, hze⟩ := Paper.lem_postpone p z hJ hp1 (fun r hr => (hp2 r hr).1) (K.expand B) K.lk
      fun r hr n hn => KT.lookup_expand ((hp2 r hr).2 n hn)
    rw [hsum]
    refine congrArg List.sum (List.map_congr_left fun q hq => congrArg (q.2 * ·) ?_)
    obtain ⟨pl, -, -⟩ := hze q hq
    have hht := KT.ht_expand B K
    have pl' : Plain θ τ' (zq p z q.1) := Plain.of_le pl ((Nat.add_le_add_right (Nat.add_le_add_right
      (Nat.mul_le_mul_right _ (show 1000 + 100 * ((K.expand B).ht + J + 1) ≤ MM (K.ht + B + J + 1) by
        unfold MM; omega)) _) _).trans hτ')
    obtain ⟨v1, v2⟩ := hG.val _ (hsz z hz q hq) pl'
    show sumF K.lk _ _ = algebraMap A R (pv θ (zq p z q.1))
    rw [v2, map_list_sum, List.map_map, sumF]
    congr 1
    refine List.map_congr_left fun r hr => ?_
    obtain ⟨a1, a2, a3, a4⟩ := (hG.list _ (hsz z hz q hq)).2 r hr
    simp only [Function.comp_apply, map_mul, map_list_prod, List.map_map]
    congr 1
    · simp [wt, a1]
    · congr 1
      refine List.map_congr_left fun y hy => ?_
      exact hD.val y (a4 y hy) (v1 r hr y hy)

end NS1
