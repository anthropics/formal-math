/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import NS1.ApproxScale
import NS1.ApproxBack

/-!
# The paper, appendix "Approximate computation": one round, and back to exact values
-/

set_option linter.unusedSectionVars false

namespace Paper

open NS1
open _root_.NS1.Tree LaurentPolynomial

variable {A : Type} [CommRing A] {θ : List Bool → A} {E : Type} [CommRing E] [Algebra A E]

/-- **Paper: proof of Proposition prop:approx-acc, one round.** "So the new value lies in ∑_e λ^e(pv(z_e) + ε^r E[ε]) ⊆
(value of p) + εE[ε] ⊆ pv(z) + εE[ε]": the new program guesses e, cuts z_e, and lets the interpreter run D on all
pieces with the constants σ_r(κ′), where r exceeds the exponents of all λ^e. -/
theorem prop_approx_acc_round {H u v : ℕ} {K' : KT E[T;T⁻¹]} {B' : ℕ} {D : Tree}
    (hD : IsAccA θ H u (u ^ (H - 16)) K' B' D) {K : KT E[T;T⁻¹]} {p : Tree} {B τ : ℕ} (hp : IsPreA θ H v τ K B p)
    {J n : ℕ} (hJ : τ < 2 ^ J) (hn : ∀ q ∈ (K.expand B).budg J, Span n q.2)
    {τ' s t tG Ln : ℕ} {G : Tree} (hG : CutProg θ H u τ' s G)
    (hτ' : MM (K.ht + B + J + 1) * τ + 40 * ((K.expand B).nds * (J + 1)) + 40 ≤ τ')
    (hs : WF.code.size + p.size + v ^ (H - 32) + 4 * ((K.expand B).nds * (J + 1)) + 3 ≤ s)
    (htG : ∀ k, k * u ^ 24 ≤ τ' → k ≤ tG) (hLn : ∀ k, k * u ^ H ≤ τ' * u ^ 2 → k ≤ Ln)
    (hJ' : (u ^ (H - 16) + 30) * Ln + 10 < 2 ^ J)
    (ht : (8 * J + 10) * (K.expand B).nds + tG + ((8 * J + 10) * (K'.expand B').nds +
      MM (K'.ht + B' + J + 1) * ((u ^ (H - 16) + 30) * Ln + 10) + 40 * ((K'.expand B').nds * (J + 1)) + 60) + 20 ≤ t) :
    IsAccA θ H v t (.node K (K'.map (rescale A (n + 1)))) (max B B' + J) (roundA K B K' B' J D G p).code := by
  obtain ⟨f, hf⟩ : ∃ f, f = rescale A (E := E) (n + 1) := ⟨_, rfl⟩
  rw [← hf]
  obtain ⟨K2, hK2⟩ : ∃ K2, K2 = KT.node K (K'.map f) := ⟨_, rfl⟩
  rw [← hK2]
  have hl : ∀ q, K.InB (B + J) q → K2.lk ([false] ++ q) = K.lk q ∧ K2.InB (max B B' + J) ([false] ++ q) := by
    intro q hq
    subst hK2
    exact ⟨rfl, hq.mono (Nat.add_le_add_right (le_max_left _ _) _)⟩
  have hr : ∀ q, K'.InB (B' + J) q → K2.lk ([true] ++ q) = f (K'.lk q) ∧ K2.InB (max B B' + J) ([true] ++ q) := by
    intro q hq
    subst hK2
    exact ⟨KT.lk_map (f : E[T;T⁻¹] →+* E[T;T⁻¹]) K' q,
      (KT.inB_map f _ K' q).2 (hq.mono (Nat.add_le_add_right (le_max_right _ _) _))⟩
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
  have inner : ∀ z : Tree, z.size ≤ v ^ (H - 32) → ∀ q ∈ (K.expand B).budg J,
      Hl θ (Fm.ofTree G) (zq p z q.1) ∧ ∀ r ∈ evl θ (Fm.ofTree G) (zq p z q.1), r.bill = [] ∧ r.cost ≤ tG ∧
        KV θ K2.lk {m | K2.InB (max B B' + J) m} (rebF (gt id J B' K' [true]) (LP D).code) (.cons (LP D).code r.out)
          (f (r.out.toList.map fun y => val K'.lk (evl θ (Fm.ofTree D) y)).prod)
          ((8 * J + 10) * (K'.expand B').nds + MM (K'.ht + B' + J + 1) * ((u ^ (H - 16) + 30) * Ln + 10) +
            40 * ((K'.expand B').nds * (J + 1)) + 60) := by
    intro z hz q hq
    obtain ⟨h1, h2⟩ := hG.list _ (hsz z hz q hq)
    refine ⟨h1, fun r hr' => ?_⟩
    obtain ⟨a1, a2, a3, a4⟩ := h2 r hr'
    refine ⟨a1, htG _ a2, ?_⟩
    obtain ⟨l, e, e1, e2⟩ := LP_ev (θ := θ) (κ := K'.lk) (T := u ^ (H - 16)) (P := fun m => K'.InB B' m) r.out
      fun y hy => hD.run y (a4 y hy)
    rw [← e2]
    refine rebill_kv f (by rw [Fm.ofTree_code]; exact e) (fun x hx => ⟨(e1 x hx).1.trans ?_, (e1 x hx).2⟩) hJ' hr
    have := Nat.mul_le_mul_left (u ^ (H - 16) + 30) (hLn _ a3)
    omega
  have key : ∀ z : Tree, z.size ≤ v ^ (H - 32) → KV θ K2.lk {m | K2.InB (max B B' + J) m}
      (roundA K B K' B' J D G p) z (((K.expand B).budg J).map fun q => q.2 *
        sumF K2.lk (evl θ (Fm.ofTree G) (zq p z q.1))
          (fun o => f (o.toList.map fun y => val K'.lk (evl θ (Fm.ofTree D) y)).prod)).sum t := by
    intro z hz
    obtain ⟨lg, eg, rg⟩ := gt_ev (θ := θ) (ν := id) (J := J) (B := B) (κ := K2.lk)
      (P := fun m => K2.InB (max B B' + J) m) z K [false] fun q hq i hi => hl _ (hq.inB hi)
    exact (stepA_kv eg rg (inner z hz)).mono ht
  constructor
  · intro z hz
    rw [Fm.ofTree_code]
    exact ⟨(key z hz).hl, fun r hr' => (key z hz).evl.1 r hr'⟩
  · intro z hz hpl
    rw [Fm.ofTree_code, (key z hz).evl.2]
    obtain ⟨hp1, hp2⟩ := hp.run z hz hpl
    obtain ⟨L, hL⟩ : ∃ L, L = (K.expand B).budg J := ⟨_, rfl⟩
    rw [← hL]
    have hval := hp.val z hz hpl
    obtain ⟨hsum, hze⟩ := lem_postpone p z hJ hp1 (fun r hr' => (hp2 r hr').1) (K.expand B) K.lk
      fun r hr' m hm => KT.lookup_expand ((hp2 r hr').2 m hm)
    rw [hsum, ← hL] at hval
    obtain ⟨S1, hS1⟩ : ∃ S1 : Bt × E[T;T⁻¹] → E[T;T⁻¹], S1 = fun q => q.2 * sumF K2.lk
        (evl θ (Fm.ofTree G) (zq p z q.1))
        (fun o => f (o.toList.map fun y => val K'.lk (evl θ (Fm.ofTree D) y)).prod) := ⟨_, rfl⟩
    obtain ⟨S2, hS2⟩ : ∃ S2 : Bt × E[T;T⁻¹] → E[T;T⁻¹], S2 = fun q => q.2 * algebraMap A E[T;T⁻¹]
        (pv θ (postponed p z q.1)) := ⟨_, rfl⟩
    rw [← hS2] at hval
    rw [← hS1]
    have diff : ∀ q ∈ L, OrdGE 1 (S1 q - S2 q) := by
      intro q hq
      rw [hL] at hq
      obtain ⟨q1, q2⟩ := hqs q hq
      have pl : Plain θ τ' (zq p z q.1) := Plain.of_le (hze q hq).1 ((Nat.add_le_add_right (Nat.add_le_add_right
        (Nat.mul_le_mul_right _ (show 1000 + 100 * ((K.expand B).ht + J + 1) ≤ MM (K.ht + B + J + 1) by
          have := KT.ht_expand B K
          unfold MM; omega)) _) _).trans hτ')
      obtain ⟨v1, v2⟩ := hG.val _ (hsz z hz q hq) pl
      rw [hS1, hS2]
      simp only
      simp only [postponed]
      rw [v2, ← mul_sub, map_list_sum, List.map_map, sumF]
      refine ((hn q hq).ordGE.mul (s := ((n : ℤ) + 1)) ?_).mono (by omega)
      have e : ∀ (l : List (Run A)) (a b : Run A → E[T;T⁻¹]),
          (∀ r ∈ l, OrdGE ((n : ℤ) + 1) (a r - b r)) → OrdGE ((n : ℤ) + 1) ((l.map a).sum - (l.map b).sum) := by
        intro l a b hab
        induction l with
        | nil => simpa using OrdGE.zero _
        | cons x l ih =>
          simp only [List.map_cons, List.sum_cons]
          rw [add_sub_add_comm]
          exact (hab x List.mem_cons_self).add (ih fun r hr' => hab r (List.mem_cons_of_mem _ hr'))
      refine e _ _ _ fun r hr' => ?_
      obtain ⟨a1, a2, a3, a4⟩ := (hG.list _ (hsz z hz q hq)).2 r hr'
      have h1 := OrdGE.prod_sub (E := E) (r := 1) zero_le_one r.out.toList
        (fun y => val K'.lk (evl θ (Fm.ofTree D) y)) (pv θ) fun y hy => hD.val y (a4 y hy) (v1 r hr' y hy)
      have h2 := h1.rescale (A := A) (r := n + 1)
      rw [← hf, map_sub, AlgHom.commutes] at h2
      have h3 := (OrdGE.of_algebraMap (E := E) r.th).mul h2
      simp only [Function.comp_apply, map_mul, wt, a1, List.map_nil, List.prod_nil, mul_one, ← mul_sub]
      exact h3.mono (by omega)
    have e : (L.map S1).sum - algebraMap A E[T;T⁻¹] (pv θ z) =
        (L.map fun q => S1 q - S2 q).sum + ((L.map S2).sum - algebraMap A E[T;T⁻¹] (pv θ z)) := by
      have : ∀ l : List (Bt × E[T;T⁻¹]), (l.map fun q => S1 q - S2 q).sum = (l.map S1).sum - (l.map S2).sum := by
        intro l
        induction l with
        | nil => simp
        | cons x l ih => simp only [List.map_cons, List.sum_cons, ih]; ring
      rw [this]
      ring
    rw [e]
    refine (OrdGE.list_sum ?_).add hval
    intro P hP
    rw [List.mem_map] at hP
    obtain ⟨q, hq, rfl⟩ := hP
    exact diff q hq

set_option maxHeartbeats 1000000 in
/-- **Paper: proof of Proposition prop:approx-acc, one round with numbers.** -/
theorem prop_approx_acc_round_num {h : ℕ} (hh : 17 ≤ h) {u α : ℕ} (hα : 5 ≤ α) (hC : CutAt θ (16 * h) u (2 * α)) (hcst : cst ≤ u)
    {K' : KT E[T;T⁻¹]} {B' : ℕ} {D : Tree} (hD : IsAccA θ (16 * h) u (u ^ (16 * h - 16)) K' B' D)
    (hK' : K'.nds ≤ u ^ (h * α)) (hDs : D.size ≤ u ^ (h * α)) {K : KT E[T;T⁻¹]} {p : Tree} {B J X e M : ℕ}
    (hp : IsPreA θ (16 * h) (u ^ α) (u ^ (e + 8)) K B p) (hK : K.nds ≤ u ^ (h * α)) (hM : K.All (Span M)) (hM1 : 1 ≤ M)
    (hps : p.size ≤ u ^ (4 * h * α))
    (hJ : u ^ (e + 8) < 2 ^ J) (hX : K.ht + K'.ht + max B B' + J + 1 ≤ X) (hX10 : 10 ≤ X) (hXu : 1000 * X ^ 3 ≤ u)
    (he1 : α * (16 * h - 32) + 40 ≤ e) (he2 : e + 9 ≤ 16 * h * (2 * α)) :
    ∃ r p', r ≤ 2 ^ (3 * X) * M ∧
      IsAccA θ (16 * h) (u ^ α) (u ^ e) (.node K (K'.map (rescale A r))) (max B B' + J) p' ∧
      p'.size ≤ p.size + (u ^ (h * α + 2) + u ^ (16 * h + 1)) := by
  have hB1 := le_max_left B B'
  have hB2 := le_max_right B B'
  -- basic inequalities
  have hX3 : 10 * X ^ 2 ≤ X ^ 3 := by
    have : X ^ 3 = X * X ^ 2 := by ring
    rw [this]
    exact Nat.mul_le_mul_right _ hX10
  have hX2 : 10 * X ≤ X ^ 2 := by rw [pow_two]; exact Nat.mul_le_mul_right _ hX10
  rw [cst_def] at hcst
  obtain ⟨sU, hsU⟩ : ∃ n, n = UF.code.size := ⟨_, rfl⟩
  obtain ⟨sW, hsW⟩ : ∃ n, n = WF.code.size := ⟨_, rfl⟩
  rw [← hsU, ← hsW] at hcst
  have hu4 : 2000 ≤ u := by omega
  have hu1 : 1 ≤ u := by omega
  have hh1 : 5 * h ≤ h * α := by rw [Nat.mul_comm h α]; exact Nat.mul_le_mul_right _ hα
  have hα32 : α * (16 * h - 32) = 16 * (h * α) - 32 * α := by
    rw [Nat.mul_sub]
    congr 1
    · ring
    · ring
  have hαh : 17 * α ≤ h * α := Nat.mul_le_mul_right _ hh
  have he3 : h * α + 3 ≤ e := by omega
  have he4 : 16 * h ≤ e := by omega
  have hH : 16 * h ≤ e + 9 := by omega
  have pu : ∀ a, u ^ (a + 1) = u * u ^ a := fun a => by rw [pow_succ]; ring
  have pbig : ∀ a, 2000 * u ^ a ≤ u ^ (a + 1) := fun a => by rw [pu]; exact Nat.mul_le_mul_right _ hu4
  have ppos : ∀ a, 1 ≤ u ^ a := fun a => Nat.one_le_pow _ _ (by omega)
  -- the tries of powers
  have hnBX : ∀ (K₀ : KT E[T;T⁻¹]) (B₀ : ℕ), K₀.nds ≤ u ^ (h * α) → B₀ + 1 ≤ X → ∀ c, c * X ^ 2 ≤ 1000 * X ^ 3 →
      (K₀.expand B₀).nds * (c * X) ≤ 2 * u ^ (h * α + 1) := by
    intro K₀ B₀ h0 h1 c hc
    calc (K₀.expand B₀).nds * (c * X) ≤ K₀.nds * (2 * X) * (c * X) :=
          Nat.mul_le_mul_right _ ((KT.nds_expand B₀ K₀).trans (Nat.mul_le_mul_left _ (by omega)))
      _ = K₀.nds * (2 * (c * X ^ 2)) := by ring
      _ ≤ u ^ (h * α) * (2 * u) := Nat.mul_le_mul h0 (by omega)
      _ = 2 * u ^ (h * α + 1) := by rw [pow_succ]; ring
  obtain ⟨nB, hnB⟩ : ∃ n, n = (K.expand B).nds := ⟨_, rfl⟩
  obtain ⟨nB', hnB'⟩ : ∃ n, n = (K'.expand B').nds := ⟨_, rfl⟩
  have hb : ∀ c, c * X ^ 2 ≤ 1000 * X ^ 3 → nB * (c * X) ≤ 2 * u ^ (h * α + 1) ∧ nB' * (c * X) ≤ 2 * u ^ (h * α + 1) :=
    fun c hc => ⟨hnB ▸ hnBX K B hK (by omega) c hc, hnB' ▸ hnBX K' B' hK' (by omega) c hc⟩
  -- the cut
  obtain ⟨G, hG⟩ := hC (u ^ (e + 9)) (u ^ (α * (16 * h - 32) + 1)) (pow_le_pow hu1 hH)
    (pow_le_pow hu1 he2) (by
      rw [← pow_add]
      exact pow_le_pow hu1 (by omega))
  obtain ⟨f, hf⟩ : ∃ f, e = f + 15 := ⟨e - 15, by omega⟩
  obtain ⟨g, hg⟩ : ∃ g, e + 11 = g + 16 * h := ⟨e + 11 - 16 * h, by omega⟩
  have hJX : J + 1 ≤ X := by omega
  obtain ⟨e', he'⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
  have hpos := ppos (16 * h - 16)
  have hLP : (u ^ (16 * h - 16) + 30) * u ^ g + 10 ≤ u ^ (e - 4) := by
    have h1 : (u ^ (16 * h - 16) + 30) * u ^ g ≤ 31 * u ^ (e - 5) := by
      calc (u ^ (16 * h - 16) + 30) * u ^ g ≤ (31 * u ^ (16 * h - 16)) * u ^ g := Nat.mul_le_mul_right _ (by omega)
        _ = 31 * u ^ (16 * h - 16 + g) := by rw [pow_add]; ring
        _ = _ := by congr 2; omega
    have h2 := pbig (e - 5)
    have h3 := ppos (e - 5)
    rw [show e - 5 + 1 = e - 4 by omega] at h2
    omega
  have hn : ∀ q ∈ (K.expand B).budg J, Span (nB * 2 ^ J * (2 ^ B * M)) q.2 :=
    fun q hq => hnB ▸ span_expand_budg hM hq
  refine ⟨_, _, ?_, prop_approx_acc_round hD hp hJ hn hG (tG := u ^ f) (Ln := u ^ g) (t := u ^ e) ?_ ?_ ?_ ?_ ?_ ?_, ?_⟩
  · -- the exponent of the rescaling
    have h1 : nB ≤ 2 ^ J := by
      calc nB ≤ nB * (1 * X) := Nat.le_mul_of_pos_right _ (by omega)
        _ ≤ 2 * u ^ (h * α + 1) := (hb 1 (by omega)).1
        _ ≤ u ^ (h * α + 1 + 1) := by have := pbig (h * α + 1); omega
        _ ≤ u ^ (e + 8) := pow_le_pow hu1 (by omega)
        _ ≤ 2 ^ J := hJ.le
    calc nB * 2 ^ J * (2 ^ B * M) + 1 ≤ 2 ^ J * 2 ^ J * (2 ^ B * M) + 2 ^ J * 2 ^ J * (2 ^ B * M) := by
          refine Nat.add_le_add (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ h1)) ?_
          exact Nat.mul_pos (Nat.mul_pos (Nat.two_pow_pos J) (Nat.two_pow_pos J))
            (Nat.mul_pos (Nat.two_pow_pos B) (by omega))
      _ = 2 ^ (J + J + B + 1) * M := by rw [pow_succ, pow_add, pow_add]; ring
      _ ≤ _ := Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) (by omega))
  · -- time of the plain instances
    rw [← hnB]
    have m1 : MM (K.ht + B + J + 1) + 2 ≤ u := by
      unfold MM
      omega
    have m2 : 40 * (nB * (J + 1)) ≤ u ^ (e + 8) := by
      calc 40 * (nB * (J + 1)) ≤ 40 * (nB * X) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hJX)
        _ = nB * (40 * X) := by ring
        _ ≤ 2 * u ^ (h * α + 1) := (hb 40 (by omega)).1
        _ ≤ u ^ (h * α + 1 + 1) := by have := pbig (h * α + 1); omega
        _ ≤ u ^ (e + 8) := pow_le_pow hu1 (by omega)
    have m3 : 40 ≤ u ^ (e + 8) := by
      have h7 : 2000 * u ^ (e + 7) ≤ u ^ (e + 8) := pbig (e + 7)
      have := ppos (e + 7)
      omega
    calc MM (K.ht + B + J + 1) * u ^ (e + 8) + 40 * (nB * (J + 1)) + 40
        ≤ (MM (K.ht + B + J + 1) + 2) * u ^ (e + 8) := by rw [add_mul]; omega
      _ ≤ u * u ^ (e + 8) := Nat.mul_le_mul_right _ m1
      _ = u ^ (e + 9) := (pu (e + 8)).symm
  · -- size of the plain instances
    rw [← hnB, ← hsW]
    have m1 : sW + 3 ≤ u ^ (α * (16 * h - 32)) := by
      calc sW + 3 ≤ u ^ 1 := by rw [pow_one]; omega
        _ ≤ _ := pow_le_pow hu1 (by omega)
    have m2 : p.size ≤ u ^ (α * (16 * h - 32)) := hps.trans (pow_le_pow hu1 (by
      have : 4 * h * α = 4 * (h * α) := by ring
      omega))
    have m3 : (u ^ α) ^ (16 * h - 32) = u ^ (α * (16 * h - 32)) := by rw [← pow_mul]
    have m4 : 4 * (nB * (J + 1)) ≤ u ^ (α * (16 * h - 32)) := by
      calc 4 * (nB * (J + 1)) ≤ 4 * (nB * X) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hJX)
        _ = nB * (4 * X) := by ring
        _ ≤ 2 * u ^ (h * α + 1) := (hb 4 (by omega)).1
        _ ≤ u ^ (h * α + 1 + 1) := by have := pbig (h * α + 1); omega
        _ ≤ _ := pow_le_pow hu1 (by omega)
    have := pbig (α * (16 * h - 32))
    rw [m3]
    omega
  · intro k hk
    rw [show e + 9 = f + 24 by omega, pow_add] at hk
    exact Nat.le_of_mul_le_mul_right hk (ppos 24)
  · intro k hk
    rw [← pow_add, show e + 9 + 2 = g + 16 * h by omega, pow_add] at hk
    exact Nat.le_of_mul_le_mul_right hk (ppos _)
  · -- the run of the list fits into the digits
    exact lt_of_le_of_lt (hLP.trans (pow_le_pow hu1 (by omega))) hJ
  · -- time
    rw [← hnB, ← hnB']
    have m1 : (8 * J + 10) * nB ≤ u ^ e' ∧ (8 * J + 10) * nB' ≤ u ^ e' ∧ 40 * (nB' * (J + 1)) ≤ u ^ e' := by
      have h9 := hb 9 (by omega)
      have h40 := (hb 40 (by omega)).2
      have h3 : 2 * u ^ (h * α + 1) ≤ u ^ e' := by
        have := pbig (h * α + 1)
        exact le_trans (by omega : _ ≤ u ^ (h * α + 1 + 1)) (pow_le_pow hu1 (by omega))
      have e8 : (8 * J + 10) ≤ 9 * X := by omega
      refine ⟨?_, ?_, ?_⟩
      · refine (Nat.mul_le_mul_right _ e8).trans ?_
        rw [Nat.mul_comm]
        exact h9.1.trans h3
      · refine (Nat.mul_le_mul_right _ e8).trans ?_
        rw [Nat.mul_comm]
        exact h9.2.trans h3
      · refine le_trans ?_ (h40.trans h3)
        calc 40 * (nB' * (J + 1)) ≤ 40 * (nB' * X) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hJX)
          _ = nB' * (40 * X) := by ring
    have m2 : u ^ f ≤ u ^ e' := pow_le_pow hu1 (by omega)
    have m3 : MM (K'.ht + B' + J + 1) * ((u ^ (16 * h - 16) + 30) * u ^ g + 10) ≤ u ^ e' := by
      calc MM (K'.ht + B' + J + 1) * ((u ^ (16 * h - 16) + 30) * u ^ g + 10) ≤ u * u ^ (e - 4) := by
            refine Nat.mul_le_mul ?_ hLP
            unfold MM
            omega
        _ = u ^ (e - 4 + 1) := (pu _).symm
        _ ≤ u ^ e' := pow_le_pow hu1 (by omega)
    have m4 : 80 ≤ u ^ e' := by
      obtain ⟨e'', he''⟩ : ∃ e'', e' = e'' + 1 := ⟨e' - 1, by omega⟩
      have := pbig e''
      have := ppos e''
      rw [he'']
      omega
    have := pbig e'
    rw [he']
    omega
  · -- size
    have s1 := size_roundA K K' B B' J D G p
    rw [← hsW, ← hsU] at s1
    have s2 := hG.size
    have s3 : ∀ (K₀ : KT E[T;T⁻¹]) (B₀ : ℕ) (pre : List Bool), K₀.nds ≤ u ^ (h * α) → pre.length ≤ 1 →
        K₀.ht + B₀ + J + 1 ≤ X → (gt id J B₀ K₀ pre).code.size ≤ 2 * u ^ (h * α + 1) := by
      intro K₀ B₀ pre h0 h1 h2
      have s4 := hnBX K₀ B₀ h0 (by omega) (18 * X) (by
        rw [show 18 * X * X ^ 2 = 18 * X ^ 3 by ring]
        omega)
      refine (size_gt id J B₀ K₀ pre (B₀ + J) (fun i hi => (show id i ≤ B₀ + J from hi.le))).trans ?_
      refine le_trans (Nat.mul_le_mul_left _ (Nat.mul_le_mul (show J + 1 ≤ X by omega)
        (show 4 * (pre.length + K₀.ht + (B₀ + J)) + 100 ≤ 18 * X by omega))) ?_
      calc (K₀.expand B₀).nds * (X * (18 * X)) = (K₀.expand B₀).nds * (18 * X * X) := by ring
        _ ≤ _ := s4
    have sg := s3 K B [false] hK (by simp) (by omega)
    have sg' := s3 K' B' [true] hK' (by simp) (by omega)
    have s5 : 2 * D.size ≤ 2 * u ^ (h * α) := Nat.mul_le_mul_left _ hDs
    have s6 : 2 * sW + sU + 2000 ≤ 3 * u ^ (16 * h) := by
      have : u ^ 1 ≤ u ^ (16 * h) := pow_le_pow hu1 (by omega)
      rw [pow_one] at this
      omega
    have s7 := pbig (16 * h)
    have s8 : 2000 * u ^ (h * α + 1) ≤ u ^ (h * α + 2) := pbig (h * α + 1)
    have s9 : u ^ (h * α) ≤ u ^ (h * α + 1) := pow_le_pow hu1 (Nat.le_succ _)
    omega

set_option maxHeartbeats 1000000 in
/-- **Paper: proof of Proposition prop:approx-acc, from one scale to the next.** An approximate accelerator at the scale `u ^ H` gives
one at the scale `(u ^ α) ^ H`; its constants are rescaled copies of the given ones. -/
theorem prop_approx_acc_next {h : ℕ} (hh : 17 ≤ h) {u α : ℕ} (hα : 5 ≤ α) (hC : CutAt θ (16 * h) u (2 * α)) (hcst : cst ≤ u)
    {K' : KT E[T;T⁻¹]} {B' : ℕ} {D : Tree} (hD : IsAccA θ (16 * h) u (u ^ (16 * h - 16)) K' B' D)
    (hK : K'.nds * (4 * α + 5) ≤ u ^ (h * α)) (hDs : D.size ≤ u ^ (h * α))
    {M' Δ : ℕ} (hM : K'.All (Span M')) (hM1 : 1 ≤ M') (hT : K'.All (Thin Δ))
    {J : ℕ} (hJ : u ^ (16 * h * α + 1) < 2 ^ J) {X : ℕ} (hX : B' + (2 * α + 2) * (J + 1) + K'.ht + K'.ht + 10 ≤ X)
    (hXu : 1000 * X ^ 3 ≤ u) :
    ∃ (K : KT E[T;T⁻¹]) (p : Tree), IsAccA θ (16 * h) (u ^ α) (u ^ (16 * h * α + 1 - 8 * (2 * α + 1))) K (B' + (2 * α + 1) * J) p ∧
      p.size ≤ (u ^ α) ^ (4 * h) ∧ K.nds ≤ K'.nds * (4 * α + 5) ∧ K.ht ≤ K'.ht + (2 * α + 1) ∧
      K.All (Span ((2 ^ (3 * X) * M') ^ (2 * α + 1))) ∧ K.All (Thin Δ) := by
  have hX10 : 10 ≤ X := by omega
  have hXu' : X ≤ u := by
    have : X ≤ X ^ 3 := Nat.le_self_pow (by norm_num) X
    omega
  have hu4 : 2000 ≤ u := by
    rw [cst_def] at hcst
    exact (Nat.le_add_left _ _).trans hcst
  have hUF : UF.code.size ≤ u := by
    rw [cst_def] at hcst
    exact ((Nat.le_add_left _ _).trans (Nat.le_add_right _ 2000)).trans hcst
  have hu1 : 1 ≤ u := by omega
  have pu : ∀ a, u ^ (a + 1) = u * u ^ a := fun a => by rw [pow_succ]; ring
  have pbig : ∀ a, 2000 * u ^ a ≤ u ^ (a + 1) := fun a => by rw [pu]; exact Nat.mul_le_mul_right _ hu4
  have hαX : 2 * α + 2 ≤ X := by
    have : (2 * α + 2) * 1 ≤ (2 * α + 2) * (J + 1) := Nat.mul_le_mul_left _ (by omega)
    omega
  have hh1 : 5 * h ≤ h * α := by rw [Nat.mul_comm h α]; exact Nat.mul_le_mul_right _ hα
  have hαh : 17 * α ≤ h * α := Nat.mul_le_mul_right _ hh
  have hα32 : α * (16 * h - 32) = 16 * (h * α) - 32 * α := by
    rw [Nat.mul_sub]
    congr 1
    · ring
    · ring
  have e16 : 16 * h * α = 16 * (h * α) := by ring
  have e4 : 4 * h * α = 4 * (h * α) := by ring
  have e17 : 16 * h * (2 * α) = 32 * (h * α) := by ring
  have hsize : ∀ n ≤ 2 * α + 1, u + n * (u ^ (h * α + 2) + u ^ (16 * h + 1)) ≤ u ^ (4 * h * α) := by
    intro n hn
    obtain ⟨a, ha⟩ : ∃ a, 4 * h * α = a + 1 := ⟨4 * h * α - 1, by omega⟩
    have t1 : n * (u ^ (h * α + 2) + u ^ (16 * h + 1)) ≤ u * (u ^ (h * α + 2) + u ^ (16 * h + 1)) :=
      Nat.mul_le_mul_right _ (by omega)
    have t2 : u * (u ^ (h * α + 2) + u ^ (16 * h + 1)) = u ^ (h * α + 3) + u ^ (16 * h + 2) := by
      rw [mul_add, ← pu, ← pu]
    have t3 : u ^ (h * α + 3) ≤ u ^ a := pow_le_pow hu1 (by omega)
    have t4 : u ^ (16 * h + 2) ≤ u ^ a := pow_le_pow hu1 (by omega)
    have t5 : u ^ 1 ≤ u ^ a := pow_le_pow hu1 (by omega)
    have t6 := pbig a
    rw [pow_one] at t5
    rw [ha]
    omega
  have hnds : ∀ n ≤ 2 * α + 1, n * (K'.nds + 1) + 1 ≤ K'.nds * (4 * α + 5) := by
    intro n hn
    have h1 := KT.nds_pos K'
    calc n * (K'.nds + 1) + 1 ≤ (2 * α + 1) * (K'.nds + K'.nds) + K'.nds :=
          Nat.add_le_add (Nat.mul_le_mul hn (by omega)) h1
      _ = K'.nds * (4 * α + 3) := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ (by omega)
  have hK' : K'.nds ≤ u ^ (h * α) := (Nat.le_mul_of_pos_right _ (by omega)).trans hK
  obtain ⟨Γ, hΓ⟩ : ∃ Γ, Γ = 2 ^ (3 * X) * M' := ⟨_, rfl⟩
  rw [← hΓ]
  have hΓ1 : 1 ≤ Γ := hΓ ▸ Nat.mul_pos (Nat.two_pow_pos _) hM1
  have rounds : ∀ n ≤ 2 * α + 1, ∃ (K : KT E[T;T⁻¹]) (p : Tree), IsPreA θ (16 * h) (u ^ α) (u ^ (16 * h * α + 1 - 8 * n)) K (B' + n * J) p ∧
      p.size ≤ u + n * (u ^ (h * α + 2) + u ^ (16 * h + 1)) ∧ K.nds ≤ n * (K'.nds + 1) + 1 ∧ K.ht ≤ K'.ht + n ∧
      K.All (Span (Γ ^ n)) ∧ K.All (Thin Δ) ∧
      (1 ≤ n → IsAccA θ (16 * h) (u ^ α) (u ^ (16 * h * α + 1 - 8 * n)) K (B' + n * J) p) := by
    intro n
    induction n with
    | zero =>
      intro _
      refine ⟨KT.none, UF.code, ?_, ?_, by simp [KT.nds], by simp [KT.ht], trivial, trivial,
        fun h => absurd h (by norm_num)⟩
      · have h0 := UF_preA (E := E) θ (16 * h) (u ^ α) (B' + 0 * J)
        refine ⟨fun z hz hp => ⟨(h0.run z hz hp).1, fun r hr => ⟨((h0.run z hz hp).2 r hr).1.trans ?_,
          ((h0.run z hz hp).2 r hr).2⟩⟩, h0.val⟩
        rw [← pow_mul, Nat.mul_comm α (16 * h), Nat.mul_zero, Nat.sub_zero]
        have := pbig (16 * h * α)
        have : 1 ≤ u ^ (16 * h * α) := Nat.one_le_pow _ _ (by omega)
        omega
      · rw [Nat.zero_mul, Nat.add_zero]
        exact hUF
    | succ n ih =>
      intro hn
      have hn' : n ≤ 2 * α + 1 := by omega
      obtain ⟨K, p, hp, hps, hk1, hk2, hk3, hk4, -⟩ := ih hn'
      clear ih
      have hnJ : n * J ≤ 2 * α * J := Nat.mul_le_mul_right _ (by omega)
      have e1 : (2 * α + 2) * (J + 1) = 2 * α * J + 2 * J + 2 * α + 2 := by ring
      have e2 : (n + 1) * J = n * J + J := by ring
      have hmax : max (B' + n * J) B' = B' + n * J := max_eq_left (Nat.le_add_right _ _)
      have hp8 : IsPreA θ (16 * h) (u ^ α) (u ^ (16 * h * α + 1 - 8 * (n + 1) + 8)) K (B' + n * J) p := by
        rw [show 16 * h * α + 1 - 8 * (n + 1) + 8 = 16 * h * α + 1 - 8 * n by omega]
        exact hp
      have g1 : 16 * h * α + 1 - 8 * (n + 1) + 8 ≤ 16 * h * α + 1 := by omega
      have g2 : K.ht + K'.ht + max (B' + n * J) B' + J + 1 ≤ X := by omega
      have g3 : α * (16 * h - 32) + 40 ≤ 16 * h * α + 1 - 8 * (n + 1) := by omega
      have g4 : 16 * h * α + 1 - 8 * (n + 1) + 9 ≤ 16 * h * (2 * α) := by omega
      have hn2 : n ≤ 2 * α + 1 := hn'
      have hres := prop_approx_acc_round_num hh hα hC hcst hD hK' hDs (K := K) (p := p) (B := B' + n * J)
        (J := J) (X := X) (M := Γ ^ n) (e := 16 * h * α + 1 - 8 * (n + 1)) hp8
        ((hk1.trans (hnds n hn')).trans hK) hk3 (Nat.one_le_pow _ _ hΓ1) (hps.trans (hsize n hn'))
        (lt_of_le_of_lt (pow_le_pow hu1 g1) hJ) g2 hX10 hXu g3 g4
      obtain ⟨r, p', hr, hp', hps'⟩ := hres
      rw [hmax, show B' + n * J + J = B' + (n + 1) * J by omega] at hp'
      refine ⟨_, p', hp'.pre, ?_, ?_, ?_, ⟨?_, ?_⟩, ⟨hk4, hT.map fun c hc => hc.rescale r⟩, fun _ => hp'⟩
      · have e3 : (n + 1) * (u ^ (h * α + 2) + u ^ (16 * h + 1)) = n * (u ^ (h * α + 2) + u ^ (16 * h + 1)) +
            (u ^ (h * α + 2) + u ^ (16 * h + 1)) := by ring
        omega
      · rw [KT.nds, KT.nds_map]
        have : (n + 1) * (K'.nds + 1) = n * (K'.nds + 1) + K'.nds + 1 := by ring
        omega
      · rw [KT.ht, KT.ht_map]
        omega
      · exact hk3.imp fun c hc => hc.mono (Nat.pow_le_pow_right hΓ1 (Nat.le_succ n))
      · refine hM.map fun c hc => (hc.rescale r).mono ?_
        calc r * M' ≤ 2 ^ (3 * X) * Γ ^ n * M' := Nat.mul_le_mul_right _ hr
          _ = Γ ^ (n + 1) := by rw [pow_succ, hΓ]; ring
  obtain ⟨K, p, -, hps, hk1, hk2, hk3, hk4, hp⟩ := rounds (2 * α + 1) le_rfl
  refine ⟨K, p, hp (by omega), ?_, hk1.trans (hnds _ le_rfl), hk2, hk3, hk4⟩
  rw [← pow_mul, show α * (4 * h) = 4 * h * α by ring]
  exact hps.trans (hsize _ le_rfl)

/-- **Paper: proof of Proposition prop:approx-acc, back to exact values.** "Its value is the coefficient of ε⁰ in the
value of D, that is, pv(z) on plain instances": the coefficients of the powers are new constants with B = 1. -/
theorem prop_approx_acc_exact {H v t t' : ℕ} {K : KT E[T;T⁻¹]} {B : ℕ} {D : Tree} (hD : IsAccA θ H v t K B D)
    {J m W Δ M : ℕ} (hJ : t < 2 ^ J) (hT : K.All (Thin Δ)) (hM : K.All (Span M))
    (hm : 2 * (2 ^ (B + J) * Δ) + 1 ≤ 2 ^ m) (hW : (K.expand B).nds * 2 ^ J * (2 ^ B * M) < 2 ^ W)
    (ht : (K.expand B).nds * (60 * W + 3 * (J + m) + 100) + MM (K.ht + B + J + 1) * t +
      40 * ((K.expand B).nds * (J + 1)) + 40 * (W + 1) + 120 ≤ t') :
    ∃ (K' : KT E) (D' : Tree), IsAccT θ H v t' K' 1 D' ∧ K'.nds ≤ (K.expand B).nds * 2 ^ (J + m + 1) ∧
      K'.ht ≤ K.ht + B + J + m ∧
      D'.size ≤ (K.expand B).nds * (2 ^ (J + m) * (8 * (K.ht + B + J + m + W) + xcst + 31)) + D.size + xcst := by
  classical
  obtain ⟨K₂, hK₂⟩ : ∃ K₂, K₂ = K.expand B := ⟨_, rfl⟩
  rw [← hK₂] at hW ht ⊢
  have hh2 : K₂.ht ≤ K.ht + B := hK₂ ▸ KT.ht_expand B K
  have hsupp : K₂.All fun c => ∀ n < 2 ^ J, (c ^ n).coeff.support.card ≤ 2 ^ m := by
    rw [hK₂]
    refine hT.expand fun c hc b hb n hn => ?_
    rw [← pow_mul]
    refine (hc _).trans (le_trans ?_ hm)
    have : 2 ^ b * n ≤ 2 ^ (B + J) := by
      rw [pow_add]
      exact Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) hb.le) hn.le
    have := Nat.mul_le_mul_right Δ this
    omega
  obtain ⟨K', hK'⟩ : ∃ K', K' = coefK J m K₂ := ⟨_, rfl⟩
  obtain ⟨g, hg⟩ : ∃ g, g = xF J m W K₂ [] := ⟨_, rfl⟩
  refine ⟨K', (extF D g).code, ⟨?_, ?_⟩, hK' ▸ nds_coefK J m K₂,
    hK' ▸ (ht_coefK J m K₂).trans (by omega), ?_⟩
  rotate_left 2
  · have h1 := size_xF J m W K₂ []
    rw [← hg, List.length_nil] at h1
    have h2 : K₂.nds * (2 ^ (J + m) * (4 * (0 + K₂.ht) + 8 * (J + m + W) + xcst + 31)) ≤
        K₂.nds * (2 ^ (J + m) * (8 * (K.ht + B + J + m + W) + xcst + 31)) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (by omega))
    have h3 := size_extF D g
    omega
  all_goals
    have key : ∀ z : Tree, z.size ≤ v ^ (H - 32) → KV θ K'.lk {p | K'.InB 1 p} (extF D g) z
        ((xL J m W K₂).map fun q => q.2.1 * ((if KT.val q.2.2 = 0 then 1 else 0) *
          algebraMap A E ((evl θ (Fm.ofTree D) z).map fun r => if ok q.1 r.bill = true then r.th else 0).sum)).sum t' := by
      intro z hz
      obtain ⟨hD1, hD2⟩ := hD.run z hz
      obtain ⟨lx, ex, rx⟩ := xF_ev (θ := θ) (κ := K'.lk) (S := {p | K'.InB 1 p}) (J := J) (m := m) (W := W) z K₂ []
        fun p hp => by subst hK'; exact ⟨rfl, hp⟩
      rw [← hg] at ex
      refine (extF_kv ex rx hD1.ev (fun r hr => (hD2 r hr).1) (H := K.ht + B + J + 1) (n := K₂.nds * (J + 1))
        fun q hq => ⟨(bt_xL q hq).1.trans (by omega), (bt_xL q hq).2, length_xL q hq⟩).mono ?_
      omega
  · intro z hz
    rw [Fm.ofTree_code]
    exact ⟨(key z hz).hl, fun r hr => (key z hz).evl.1 r hr⟩
  · intro z hz hpl
    rw [Fm.ofTree_code, (key z hz).evl.2]
    obtain ⟨hD1, hD2⟩ := hD.run z hz
    have hv := hD.val z hz hpl
    obtain ⟨l, hl⟩ : ∃ l, l = evl θ (Fm.ofTree D) z := ⟨_, rfl⟩
    rw [← hl] at hD2 hv ⊢
    obtain ⟨hsum₀, hze⟩ := lem_postpone D z hJ hD1 (fun r hr => (hD2 r (hl ▸ hr)).1) (K.expand B) K.lk
      fun r hr p hp => KT.lookup_expand ((hD2 r (hl ▸ hr)).2 p hp)
    have hbud : NS1.val K.lk l = (((K.expand B).budg J).map fun q => q.2 *
        algebraMap A E[T;T⁻¹] (l.map fun r => if ok q.1 r.bill = true then r.th else 0).sum).sum := by
      rw [hl, hsum₀]
      exact congrArg List.sum (List.map_congr_left fun q hq => by rw [(hze q hq).2.2.1])
    rw [← hK₂] at hbud
    obtain ⟨s, hs⟩ : ∃ s : Bt → A, s = fun b => (l.map fun r => if ok b r.bill = true then r.th else 0).sum := ⟨_, rfl⟩
    have hs' : ∀ b, (l.map fun r => if ok b r.bill = true then r.th else 0).sum = s b := fun b => by rw [hs]
    simp only [hs'] at hbud ⊢
    have hsum := sum_xL (A := A) (W := W) hsupp fun b => algebraMap A (AddMonoidAlgebra E (ZMod (2 ^ W))) (s b)
    -- the right side is the image of the approximate value
    have hR : ((K₂.budg J).map fun q => algebraMap A (AddMonoidAlgebra E (ZMod (2 ^ W))) (s q.1) * wrap A W q.2).sum =
        wrap A W (NS1.val K.lk l) := by
      rw [hbud, map_list_sum, List.map_map]
      congr 1
      refine List.map_congr_left fun q _ => ?_
      rw [Function.comp_apply, map_mul, AlgHom.commutes, mul_comm]
    -- the left side at 0 is the value of the program
    have hL : ∀ L : List (Bt × E × List Bool), (∀ q ∈ L, q.2.2.length = W) →
        (L.map fun q : Bt × E × List Bool => algebraMap A (AddMonoidAlgebra E (ZMod (2 ^ W))) (s q.1) *
          mark W q.2.2 q.2.1).sum.coeff 0 =
          (L.map fun q => q.2.1 * ((if KT.val q.2.2 = 0 then 1 else 0) * algebraMap A E (s q.1))).sum := by
      intro L hL
      induction L with
      | nil => simp
      | cons q L ih =>
        have h0 : (((KT.val q.2.2 : ℕ) : ZMod (2 ^ W)) = 0) ↔ KT.val q.2.2 = 0 := by
          rw [ZMod.natCast_eq_zero_iff]
          exact ⟨fun h => Nat.eq_zero_of_dvd_of_lt h (val_lt_of_length (hL q List.mem_cons_self)), fun h => h ▸ dvd_zero _⟩
        simp only [List.map_cons, List.sum_cons, AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
          ih fun x hx => hL x (List.mem_cons_of_mem _ hx)]
        congr 1
        rw [mark, AddMonoidAlgebra.coe_algebraMap, Function.comp_apply, AddMonoidAlgebra.single_mul_single, zero_add,
          AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
        by_cases h : KT.val q.2.2 = 0
        · rw [if_pos (h0.2 h), if_pos h, one_mul, mul_comm]
        · rw [if_neg (mt h0.1 h), if_neg h, zero_mul, mul_zero]
    rw [← hL _ length_xL, hsum, hR]
    have hspan : Span (K₂.nds * 2 ^ J * (2 ^ B * M)) (NS1.val K.lk l) := by
      rw [hbud]
      have hq : ∀ q ∈ K₂.budg J, Span (K₂.nds * 2 ^ J * (2 ^ B * M)) q.2 := by
        subst hK₂
        exact fun q hq => span_expand_budg hM hq
      revert hq
      generalize K₂.budg J = L
      intro hq
      induction L with
      | nil => simpa using Span.zero _
      | cons q L ih =>
        rw [List.map_cons, List.sum_cons]
        refine Span.add ?_ (ih fun x hx => hq x (List.mem_cons_of_mem _ hx))
        simpa using (hq q List.mem_cons_self).mul (Span.of_algebraMap (E := E) (s q.1) 0)
    rw [coeff_wrap_zero hspan hW]
    have := hv 0 zero_lt_one
    simp only [AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply, sub_eq_zero, coeff_algebraMap, if_true] at this
    exact this

end Paper
