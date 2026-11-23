/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Paper.Laws
import Paper.Pieces
import Paper.Universal
import Nc.Dl.Last
import Nc.Dl.GrpCost
import NS1.OneCut

/-!
# The paper, section "Cutting computations"

Programs, instances, plain instances and sums are those of NS1.Machine and NS1.Accel: an instance is a tree whose
first part is a program and whose second part is its argument. The generators of the ring are a table θ.
-/

namespace Paper

open Finset NS1 Nc.Vp Nc.Tow
open Nc.Tower (U ee)
open _root_.NS1.Tree

variable {A : Type} [CommRing A]

/-- The table θ lists finitely many generators of A: every element is a fixed sum of products of them. -/
def Generates (θ : List Bool → A) : Prop := (Function.support θ).Finite ∧ ∀ a, ∃ w : WE, w.val θ = a

theorem exists_generates (A : Type) [CommRing A] [Algebra.FiniteType ℤ A] : ∃ θ : List Bool → A, Generates θ :=
  Nc.Dl.exists_theta A

/-- **Paper: Definition def:cut.** "A program G cuts (τ,s) into (τ′,s′) with P pieces in t steps if for every instance
z with |z| ≤ s: all runs of G on z halt, and the accepting ones take at most t steps, have empty bills and output lists
of at most P instances of size at most s′; and if z is τ-plain, then all these instances are τ′-plain and
sum(z) = ∑ weight · ∏ sum(y)." -/
theorem def_cut (θ : List Bool → A) (τ s τ' s' P t : ℕ) (G : Tree) :
    CutD θ τ s τ' s' P t G ↔ ∀ z, z.size ≤ s →
      Hl θ (Fm.ofTree G) z ∧
      (∀ r ∈ evl θ (Fm.ofTree G) z, r.bill = [] ∧ r.cost ≤ t ∧ r.out.toList.length ≤ P ∧
        ∀ y ∈ r.out.toList, y.size ≤ s') ∧
      (Plain θ τ z → (∀ r ∈ evl θ (Fm.ofTree G) z, ∀ y ∈ r.out.toList, Plain θ τ' y) ∧
        pv θ z = ((evl θ (Fm.ofTree G) z).map fun r => r.th * (r.out.toList.map (pv θ)).prod).sum) := by
  constructor
  · intro h z hz
    obtain ⟨Q, hD, hQ, hv⟩ := h z hz
    refine ⟨hD.hl, fun r hr => ?_, fun hp => ⟨fun r hr y hy => ?_, ?_⟩⟩
    · obtain ⟨h1, h2, q, hq, h3⟩ := hD.evl.1 r hr
      rw [← h3]
      exact ⟨h1, h2, hQ q hq⟩
    · obtain ⟨-, -, q, hq, h3⟩ := hD.evl.1 r hr
      rw [← h3] at hy
      exact (hv hp).1 q hq y hy
    · rw [(hv hp).2, ← hD.evl.2 (pvs θ)]
      rfl
  · intro h z hz
    obtain ⟨h1, h2, h3⟩ := h z hz
    refine ⟨(evl θ (Fm.ofTree G) z).map fun r => (r.th, r.out), ⟨_, h1.ev, fun r hr => ⟨(h2 r hr).1, (h2 r hr).2.1,
      _, List.mem_map.2 ⟨r, hr, rfl⟩, rfl⟩, fun φ => ?_⟩, fun q hq => ?_, fun hp => ⟨fun q hq => ?_, ?_⟩⟩
    · simp [wsum, Function.comp_def]
    · obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hq
      exact (h2 r hr).2.2
    · obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hq
      exact (h3 hp).1 r hr
    · rw [(h3 hp).2]
      simp [wsum, pvs, Function.comp_def]

/-- **Paper: Theorem thm:onecut, the evaluator.** "The sum of the evaluator on a script is the value of the piece", all
its runs halt, within (#blocks · T + #bits of units + #instructions · v^O(1))(lg v)^O(1) steps: GROUP and κ are the
evaluator and its step cost, GroupOK says halting, value and cost, GrpTimeOK bounds the cost by the bits of the piece. -/
theorem thm_onecut_evaluator {θ : List Bool → A} (hθ : Generates θ) {Γ S Q : Type} [Fintype Γ] [DecidableEq Γ]
    [Fintype S] [DecidableEq S] [Fintype Q] [DecidableEq Q] (mu : Nc.Letter S Unit Γ → Matrix Q Q A) {c : ℕ}
    (cb : Option Γ → Fin c → Bool) (kinds : List (Σ L : Nc.G.Law A, L.Ro)) :
    ∃ (GROUP : Fm) (κ : ℕ), Nc.Dl.GroupOK θ mu cb kinds (fun z => (Nc.Grp.qn Q z : ℕ)) GROUP κ ∧
      Nc.Dl.GrpTimeOK (S := S) A cb (fun z => (Nc.Grp.qn Q z : ℕ)) := by
  classical
  obtain ⟨GROUP, κ, hG⟩ := Nc.Grp.exists_group (θ := θ) mu cb kinds (fun z q q' => hθ.2 _) (fun z _ i y h => hθ.2 _)
  refine ⟨GROUP, κ, ?_, Nc.Dl.grpTimeOK cb _⟩
  intro A' K E U0 U1 cap Gr _ _ M P q x ρ n o grp g key dkey tg bT bub b h1 h2 h3 h4 h5 h6
  exact hG P q x ρ n o grp g key dkey tg bT bub b h1 h2 h3 h4 h5 h6

theorem lg_mul_sq_le {τ v : ℕ} : lg (τ * v ^ 2) ≤ lg τ + 2 * lg v + 1 := by
  have h1 : τ * v ^ 2 < 2 ^ (lg τ + 2 * lg v) := by
    rw [pow_add, Nat.mul_comm 2, pow_mul]
    exact Nat.mul_lt_mul'' (lt_two_pow_lg τ) (Nat.pow_lt_pow_left (lt_two_pow_lg v) (by norm_num))
  unfold lg at h1 ⊢
  rcases Nat.eq_zero_or_pos (τ * v ^ 2) with h | h
  · rw [h, Nat.log_zero_right]
    omega
  · have := Nat.log_lt_of_lt_pow (by omega) h1
    omega

set_option maxHeartbeats 1200000 in
/-- **Paper: Theorem thm:onecut.** "There are constants a₀, C, v₀ such that for all v ≥ v₀, all τ ≥ v^a₀ with
4 lg τ ≤ (lg v)², all s ≤ τ and 2 ≤ k ≤ v^64, with Λ = (lg v)^C, a program of size at most v^a₀ cuts (τ,s) into
(τΛ/k, (s/k + τ/v^256)Λ) with at most kΛ pieces, in (s + τk/v^256)Λ steps." The laws and the generators θ are the
standing hypothesis "Fix the ring A and the laws". The proof takes the automaton from Proposition prop:universal and
the formula and the bounds of the pieces from Proposition prop:pieces, and puts the evaluator and the program G on
them. -/
theorem thm_onecut {θ : List Bool → A} (hθ : Generates θ) {h : ℕ} [NeZero h]
    (VL : VLaws A (cNear (h := h)) (dNear (h := h)) 1 (2 ^ ee h)) (h3 : 3 ≤ h)
    (hgain : 1 + 8 * VL.C₁ ≤ (h : ℝ) / 4) :
    ∃ a₀ C v₀ : ℕ, ∀ v, v₀ ≤ v → ∀ τ s k, v ^ a₀ ≤ τ → 4 * lg τ ≤ lg v ^ 2 → s ≤ τ → 2 ≤ k → k ≤ v ^ 64 →
      ∃ G : Tree, G.size ≤ v ^ a₀ ∧ CutD θ τ s (τ * lg v ^ C / k) ((s / k + τ / v ^ 256) * lg v ^ C)
        (k * lg v ^ C) ((s + τ * k / v ^ 256) * lg v ^ C) G := by
  classical
  obtain ⟨S, Γ, Q, i1, i2, i3, i4, i5, i6, mu, i, e', b0, b1, CU, hCU⟩ := prop_universal θ hθ.1
  obtain ⟨a, e, he, hpieces⟩ := prop_pieces VL h3 hgain
  obtain ⟨Cp, v₁, hP⟩ := hpieces Γ S Q mu
  obtain ⟨kinds, hkinds⟩ : ∃ l, l = Nc.Tow.kindList A ((univ : Finset VL.Di).toList.map VL.L) := ⟨_, rfl⟩
  rw [← hkinds] at hP
  -- one evaluator for each code of symbols
  choose GR κ hGR hGT using fun (c : Fin (Cp + 1)) (cb : Option Γ → Fin c.1 → Bool) =>
    thm_onecut_evaluator hθ mu cb kinds
  obtain ⟨Zg, hZg⟩ : ∃ Z, Z = ∑ c : Fin (Cp + 1), ∑ cb : Option Γ → Fin c.1 → Bool, ((GR c cb).code.size + κ c cb) :=
    ⟨_, rfl⟩
  obtain ⟨ml, hml⟩ : ∃ m, m = (kinds.map fun L : (Σ L : Nc.G.Law A, L.Ro) =>
      Fintype.card L.1.Ro + Fintype.card L.1.Sl + Fintype.card L.1.Cn).sum := ⟨_, rfl⟩
  obtain ⟨cq, hcq⟩ : ∃ cq, ∀ q, (Nc.Grp.qn Q q : ℕ) ≤ cq :=
    ⟨univ.sup fun q => (Nc.Grp.qn Q q : ℕ), fun q => Finset.le_sup (f := fun q => (Nc.Grp.qn Q q : ℕ)) (Finset.mem_univ q)⟩
  obtain ⟨b₁, hb₁⟩ : ∃ b, b = 3 * Cp + 3 * e + a + 8 := ⟨_, rfl⟩
  obtain ⟨C1, hC1⟩ : ∃ C, C = Cp + 10 := ⟨_, rfl⟩
  obtain ⟨Z, hZ⟩ : ∃ Z, Z = 20000 + Cp + Zg + ml + cq + Fintype.card S + Fintype.card Q + kinds.length + Nc.Dl.dealC +
      16 * (CU + 1) + 3 * b₁ + 4 * Cp + 8 := ⟨_, rfl⟩
  obtain ⟨n1, hn1⟩ := poly_lg 1 C1
  refine ⟨a + e + 6 * b₁ + 400, 10 * C1, 2 ^ (Z + 1) + v₁ + n1, fun v hv τ s k hτ hlτ hsτ hk hkv => ?_⟩
  -- logarithms
  obtain ⟨l, hl⟩ : ∃ l, l = lg v := ⟨_, rfl⟩
  have hlbig : Z + 1 < l := by
    rw [hl]; exact le_lg_of_two_pow_le (le_trans (by omega) hv)
  have hl1 : 1 ≤ l := by omega
  have hpow1 := Nat.one_le_two_pow (n := Z + 1)
  have hv0 : v ≠ 0 := by omega
  have hv1 : 1 ≤ v := by omega
  have hlv : l ≤ v := by
    rw [hl]
    unfold lg
    exact Nat.log_lt_self 2 hv0
  obtain ⟨m, hm⟩ : ∃ m, m = l ^ C1 := ⟨_, rfl⟩
  have hml' : ∀ p, p ≤ C1 → l ^ p ≤ m := fun p hp => hm ▸ Nat.pow_le_pow_right hl1 hp
  have hlm : l ≤ m := by
    have := hml' 1 (by omega)
    rwa [pow_one] at this
  have hmv : m ≤ v := by
    have := hn1 v (by omega)
    rw [one_mul, ← hl, ← hm] at this
    exact this
  have hm1 : 1 ≤ m := hl1.trans hlm
  have vpow : ∀ {p q}, p ≤ q → v ^ p ≤ v ^ q := fun h => Nat.pow_le_pow_right hv1 h
  have vpos : ∀ p, 0 < v ^ p := fun p => Nat.pow_pos (by omega)
  have vone : v ≤ v ^ 1 := (pow_one v).ge
  -- the number of blocks
  obtain ⟨K, hKv, hKv', hP⟩ := hP v (by omega)
  have hK0 : 0 < K := lt_of_lt_of_le (vpos e) hKv
  have hvK : v ^ 300 ≤ K := (vpow he).trans hKv
  have hKe : K ≤ v ^ (e + 1) := by
    calc K ≤ Cp * v ^ e := hKv'
      _ ≤ v * v ^ e := Nat.mul_le_mul_right _ (by omega)
      _ = v ^ (e + 1) := (pow_succ' v e).symm
  obtain ⟨X, hX⟩ : ∃ X, X = v ^ b₁ := ⟨_, rfl⟩
  have vX : ∀ p, p ≤ b₁ → v ^ p ≤ X := fun p hp => hX ▸ vpow hp
  have hX1 : 1 ≤ X := hX ▸ Nat.pow_pos hv1
  have hvX : v ≤ X := vone.trans (vX 1 (by omega))
  have hKX : K ≤ X := hKe.trans (vX _ (by omega))
  have hsmall : X ^ 6 * m ^ 20 * v ^ 300 ≤ τ := by
    calc X ^ 6 * m ^ 20 * v ^ 300 ≤ X ^ 6 * v ^ 20 * v ^ 300 :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hmv 20))
      _ = v ^ (b₁ * 6 + 20 + 300) := by rw [hX, ← pow_mul, ← pow_add, ← pow_add]
      _ ≤ v ^ (a + e + 6 * b₁ + 400) := vpow (by omega)
      _ ≤ τ := hτ
  have hXτ : X ≤ τ := by
    calc X = X ^ 1 * 1 * 1 := by ring
      _ ≤ X ^ 6 * m ^ 20 * v ^ 300 := Nat.mul_le_mul (Nat.mul_le_mul (Nat.pow_le_pow_right hX1 (by norm_num))
          (Nat.pow_pos hm1)) (vpos 300)
      _ ≤ τ := hsmall
  have hτ1 : 1 ≤ τ := hX1.trans hXτ
  -- the steps: a plain instance is the value of the universal automaton in KT steps
  obtain ⟨tU, htU⟩ : ∃ t, t = (CU + 1) * (2 * τ + 2) * lg (2 * τ + 2) ^ 2 := ⟨_, rfl⟩
  have hl2 : lg τ + 3 ≤ 2 * l ^ 2 := by
    have : l ≤ l ^ 2 := Nat.le_self_pow (by norm_num) l
    rw [← hl] at hlτ
    omega
  have hlgτ : lg (2 * τ + 2) ≤ 2 * l ^ 2 := by
    have h1 : 2 * τ + 2 < 2 ^ (lg τ + 2) := by
      have := lt_two_pow_lg τ
      rw [pow_add]
      omega
    have h2 : Nat.log 2 (2 * τ + 2) < lg τ + 2 := Nat.log_lt_of_lt_pow (by omega) h1
    have e1 : lg (2 * τ + 2) = Nat.log 2 (2 * τ + 2) + 1 := rfl
    omega
  have htUle : tU ≤ τ * l ^ 5 := by
    calc tU ≤ (CU + 1) * (4 * τ) * (2 * l ^ 2) ^ 2 := by
          rw [htU]
          exact Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (Nat.pow_le_pow_left hlgτ 2)
      _ = τ * (16 * (CU + 1) * l ^ 4) := by ring
      _ ≤ τ * (l * l ^ 4) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (by omega))
      _ = τ * l ^ 5 := by ring
  obtain ⟨T, hT⟩ : ∃ T, T = tU / K + 1 := ⟨_, rfl⟩
  have hKTge : tU ≤ K * T := by
    have h1 := Nat.div_add_mod tU K
    have h2 := Nat.mod_lt tU hK0
    rw [hT, Nat.mul_add, Nat.mul_one]
    omega
  have hKT : K * T ≤ τ * m := by
    calc K * T = K * (tU / K) + K := by rw [hT]; ring
      _ ≤ tU + τ := Nat.add_le_add (Nat.mul_div_le _ _) (hKX.trans hXτ)
      _ ≤ τ * l ^ 5 + τ * l ^ 5 := Nat.add_le_add htUle (Nat.le_mul_of_pos_right _ (Nat.pow_pos hl1))
      _ = τ * (2 * l ^ 5) := by ring
      _ ≤ τ * (l * l ^ 5) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (by omega))
      _ = τ * l ^ 6 := by ring
      _ ≤ τ * m := Nat.mul_le_mul_left _ (hml' 6 (by omega))
  have hτtU : τ ≤ tU := by
    rw [htU]
    have h1 : 1 ≤ lg (2 * τ + 2) ^ 2 := Nat.pow_pos (by unfold lg; omega)
    calc τ ≤ 1 * (2 * τ + 2) * 1 := by omega
      _ ≤ (CU + 1) * (2 * τ + 2) * lg (2 * τ + 2) ^ 2 := Nat.mul_le_mul (Nat.mul_le_mul_right _ (by omega)) h1
  have hTa : v ^ a ≤ T := by
    refine Nat.le_of_mul_le_mul_left (?_ : v ^ (e + 1) * v ^ a ≤ v ^ (e + 1) * T) (vpos _)
    calc v ^ (e + 1) * v ^ a = v ^ (e + 1 + a) := (pow_add _ _ _).symm
      _ ≤ v ^ (a + e + 6 * b₁ + 400) := vpow (by omega)
      _ ≤ K * T := hτ.trans (hτtU.trans hKTge)
      _ ≤ v ^ (e + 1) * T := Nat.mul_le_mul_right _ hKe
  obtain ⟨pc⟩ := hP T k hTa hk hkv
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ, ℓ = s / K + 1 := ⟨_, rfl⟩
  have hℓT : ℓ ≤ T := by
    rw [hℓ, hT]
    exact Nat.add_le_add_right (Nat.div_le_div_right (hsτ.trans hτtU)) 1
  have hsK : s ≤ K * ℓ := by
    have h1 := Nat.div_add_mod s K
    have h2 := Nat.mod_lt s hK0
    rw [hℓ, Nat.mul_add, Nat.mul_one]
    omega
  -- numbers below X
  obtain ⟨hD, hst, hA', hE, hU0, hU1⟩ := pc.steps_le
  have hCX : v ^ Cp + 1 ≤ X := by
    calc v ^ Cp + 1 ≤ v ^ Cp * v := by
          have : 1 ≤ v ^ Cp := vpos Cp
          have : v ^ Cp * 2 ≤ v ^ Cp * v := Nat.mul_le_mul_left _ (by omega)
          omega
      _ = v ^ (Cp + 1) := (pow_succ v Cp).symm
      _ ≤ X := vX _ (by omega)
  have h3K : 3 * K ≤ v * K := Nat.mul_le_mul_right _ (by omega)
  have hK2 : K + K + 1 ≤ X := by
    calc K + K + 1 ≤ v * K := by omega
      _ ≤ v * v ^ (e + 1) := Nat.mul_le_mul_left _ hKe
      _ = v ^ (e + 2) := (pow_succ' v (e + 1)).symm
      _ ≤ X := vX _ (by omega)
  have hcId : Fintype.card (Nc.G.Uid (K + K) pc.U0 pc.sys.N pc.U1) ≤ X := by
    refine Nc.Dl.card_uid_le.trans ?_
    have g1 : (K + K) * (K + K) * pc.U0 ≤ v ^ (b₁ - 1) := by
      calc (K + K) * (K + K) * pc.U0 ≤ (v * K) * (v * K) * v ^ Cp :=
          Nat.mul_le_mul (Nat.mul_le_mul (by omega) (by omega)) hU0
        _ ≤ (v * v ^ (e + 1)) * (v * v ^ (e + 1)) * v ^ Cp := by gcongr
        _ = v ^ (2 * e + 4 + Cp) := by ring
        _ ≤ _ := vpow (by omega)
    have g2 : Fintype.card pc.sys.N * pc.U1 ≤ v ^ (b₁ - 1) := by
      calc _ ≤ v ^ Cp * v ^ Cp := Nat.mul_le_mul pc.outcomes_le hU1
        _ = v ^ (Cp + Cp) := (pow_add _ _ _).symm
        _ ≤ _ := vpow (by omega)
    calc _ ≤ v ^ (b₁ - 1) + v ^ (b₁ - 1) := Nat.add_le_add g1 g2
      _ ≤ v * v ^ (b₁ - 1) := by rw [← Nat.two_mul]; exact Nat.mul_le_mul_right _ (by omega)
      _ = X := by rw [hX, ← pow_succ']; congr 1; omega
  have hkind : ∀ r : pc.sys.R, ∃ t : ℕ, kinds[t]? = some ⟨pc.sys.kind r.1, r.2⟩ := fun r =>
    List.mem_iff_getElem?.1 (pc.kinds_mem r)
  choose tg htg using hkind
  have hlaw : ∀ r : pc.sys.R, Fintype.card (pc.sys.kind r.1).Ro + Fintype.card (pc.sys.kind r.1).Sl +
      Fintype.card (pc.sys.kind r.1).Cn ≤ ml := fun r => by
    rw [hml]
    exact List.single_le_sum (fun _ _ => Nat.zero_le _) _ (List.mem_map.2 ⟨_, pc.kinds_mem r, rfl⟩)
  have hrole : ∀ x, Fintype.card (pc.sys.kind x).Ro = 0 → Fintype.card (pc.sys.kind x).Sl = 0 ∧
      Fintype.card (pc.sys.kind x).Cn = 0 := fun x h0 => by
    have := Fintype.card_eq_zero_iff.1 h0
    exact ⟨Fintype.card_eq_zero_iff.2 ⟨fun z => this.false ((pc.sys.kind x).a z)⟩,
      Fintype.card_eq_zero_iff.2 ⟨fun z => this.false ((pc.sys.kind x).c z)⟩⟩
  have hlaw' : ∀ x, Fintype.card (pc.sys.kind x).Ro + Fintype.card (pc.sys.kind x).Sl +
      Fintype.card (pc.sys.kind x).Cn ≤ ml := fun x => by
    rcases Nat.eq_zero_or_pos (Fintype.card (pc.sys.kind x).Ro) with h0 | h0
    · obtain ⟨h1, h2⟩ := hrole x h0
      omega
    · exact hlaw ⟨x, (Fintype.card_pos_iff.1 h0).some⟩
  have hcR : Fintype.card pc.sys.R ≤ X := by
    calc Fintype.card pc.sys.R = ∑ x, Fintype.card (pc.sys.kind x).Ro := Fintype.card_sigma
      _ ≤ ∑ _x : Fin pc.E, ml := Finset.sum_le_sum fun x _ => le_trans (by omega) (hlaw' x)
      _ = pc.E * ml := by simp
      _ ≤ v ^ Cp * v := Nat.mul_le_mul hE (by omega)
      _ = v ^ (Cp + 1) := (pow_succ v Cp).symm
      _ ≤ X := vX _ (by omega)
  have hrow : Fintype.card (Nc.Cut.RowData (K + K)) ≤ X := by
    rw [Nc.Dl.card_row]
    calc 2 * ((K + K) * (K + K)) = 8 * (K * K) := by ring
      _ ≤ v * (v ^ (e + 1) * v ^ (e + 1)) := Nat.mul_le_mul (by omega) (Nat.mul_le_mul hKe hKe)
      _ = v ^ (2 * e + 3) := by ring
      _ ≤ X := vX _ (by omega)
  have hSX : Fintype.card (Option S) ≤ X := by
    rw [Fintype.card_option]
    omega
  -- bits
  obtain ⟨Lc, hLc⟩ : ∃ L, L = lg (X ^ 3) + lg (τ * v ^ 2) + 1 := ⟨_, rfl⟩
  have hX3Lc : X ^ 3 ≤ 2 ^ Lc := (lt_two_pow_lg _).le.trans (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hTLc : T < 2 ^ Lc := by
    refine lt_of_le_of_lt ?_ (lt_of_lt_of_le (lt_two_pow_lg (τ * v ^ 2)) (Nat.pow_le_pow_right (by norm_num) (by omega)))
    calc T ≤ K * T := Nat.le_mul_of_pos_left _ hK0
      _ ≤ τ * m := hKT
      _ ≤ τ * v ^ 2 := Nat.mul_le_mul_left _ (hmv.trans (Nat.le_self_pow (by norm_num) v))
  obtain ⟨t1, t2, t3, t4⟩ := Nc.Dl.exists_bits T (L := Lc) hTLc
  obtain ⟨u1, u2, u3, u4⟩ := Nc.Dl.exists_bits pc.ub (L := Lc) (lt_of_le_of_lt pc.unit_le.1 hTLc)
  obtain ⟨l1, l2, -, -⟩ := Nc.Dl.exists_bits ℓ (L := Lc) (lt_of_le_of_lt hℓT hTLc)
  have hLcm : Lc + 1 ≤ m := by
    have h1 : lg (X ^ 3) ≤ 3 * b₁ * l := by
      rw [hX, ← pow_mul, hl, Nat.mul_comm b₁ 3]
      exact lg_pow_le (by omega)
    have h2 := lg_mul_sq_le (τ := τ) (v := v)
    rw [← hl] at h2 hlτ
    calc Lc + 1 ≤ 3 * b₁ * l + (l ^ 2 + 2 * l + 3) := by omega
      _ ≤ l * l + (l * l + l * l + l * l) := by
          have : 3 * b₁ * l ≤ l * l := Nat.mul_le_mul_right _ (by omega)
          have : 2 * l ≤ l * l := Nat.mul_le_mul_right _ (by omega)
          have : 3 ≤ l * l := le_trans (by omega : 3 ≤ l) (Nat.le_mul_self l)
          rw [pow_two]
          omega
      _ = 4 * (l * l) := by ring
      _ ≤ l * (l * l) := Nat.mul_le_mul_right _ (by omega)
      _ = l ^ 3 := by ring
      _ ≤ m := hml' 3 (by omega)
  have hX30 : 60 ≤ X := by omega
  have hX32 : ∀ n, n ≤ 60 * (X * X) → n ≤ 2 ^ Lc := by
    intro n hn
    refine hn.trans (le_trans ?_ hX3Lc)
    calc 60 * (X * X) ≤ X * (X * X) := Nat.mul_le_mul_right _ hX30
      _ = X ^ 3 := by ring
  have hXX : X ≤ X * X := Nat.le_mul_of_pos_left _ hX1
  have hN := pc.outcomes_le
  obtain ⟨Cd, hCd⟩ := Nc.Dl.exists_codes (A' := pc.A') (E := pc.E) (U0 := pc.U0) (U1 := pc.U1) (D := pc.D)
    (pS := pc.steps) (S := S) (M := pc.sys) (Lc := Lc)
    (hX32 _ ((Nc.Dl.card_nm hK2 hSX (by omega) (by omega) (by omega) hcId).trans (by omega))) (hX32 _ (by omega))
    (hX32 _ (by omega)) (hX32 _ (by
      rw [Fintype.card_sum, Fintype.card_prod, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, Fintype.card_fin]
      have g1 : (K + K + pc.A') * Fintype.card (Nc.G.Uid (K + K) pc.U0 pc.sys.N pc.U1) ≤ X * X :=
        Nat.mul_le_mul (by omega) hcId
      have g2 : (K + K) * pc.U0 ≤ X * X := Nat.mul_le_mul (by omega) (by omega)
      omega))
  -- the bounds of the pieces, in units
  obtain ⟨L, hL⟩ : ∃ L, L = lg v ^ Cp := ⟨_, rfl⟩
  have hLm : L ≤ m := hL ▸ hl ▸ hml' Cp (by omega)
  obtain ⟨bd, hbd⟩ : ∃ b, b = K * T * L / (pc.ub * v ^ 300) := ⟨_, rfl⟩
  obtain ⟨ev, hev⟩ : ∃ b, b = K * T * L / (pc.ub * k) := ⟨_, rfl⟩
  obtain ⟨ιb, hιb⟩ : ∃ b, b = Cp * K / k := ⟨_, rfl⟩
  have hbits : ∀ d, K * T * L / (pc.ub * d) * pc.ub * d ≤ τ * m ^ 2 := fun d => by
    rw [Nat.mul_assoc _ pc.ub d]
    refine (Nat.div_mul_le_self _ _).trans ((Nat.mul_le_mul hKT hLm).trans (le_of_eq ?_))
    ring
  have hιK : ιb * k ≤ Cp * K := hιb ▸ Nat.div_mul_le_self _ _
  have hnums : Nc.Dl.CutNums v K τ s k T ℓ pc.ub pc.load X Lc m pc.c ιb bd ev pc.num :=
    { v_pos := hv1, m_ge := by omega, m_le := hmv, k_pos := hk, kK := hkv.trans ((vpow (by norm_num)).trans hvK),
      vK := hvK, KT := hKT, ℓeq := hℓ, ub_pos := pc.ub_pos, ub_le := pc.unit_le.1.trans (Nat.le_succ T),
      lhub := by
        refine pc.unit_le.2.trans ?_
        rw [← hL, Nat.mul_comm]
        exact Nat.mul_le_mul_right _ hLm
      Lc_le := hLcm, c_le := by have := pc.c_le; omega, K_X := hKX, X_ge := hX1,
      ιb_le := hιK.trans (Nat.mul_le_mul_right _ (by omega)),
      ιbX := by
        calc ιb ≤ Cp * K := hιb ▸ Nat.div_le_self _ _
          _ ≤ v * v ^ (e + 1) := Nat.mul_le_mul (by omega) hKe
          _ = v ^ (e + 2) := (pow_succ' v (e + 1)).symm
          _ ≤ X := vX _ (by omega)
      bd_le := hbd ▸ hbits _, ev_le := hev ▸ hbits _,
      mm_le := by
        refine pc.num_le.trans ?_
        rw [← hL]
        exact Nat.mul_le_mul_left _ hLm
      mmX := by have := pc.digits.2.2.1; omega
      small := hsmall }
  have hubk : 0 < pc.ub * k := Nat.mul_pos pc.ub_pos (by omega)
  have hbdle : ∀ n o, pc.tab.valid n → (∀ x, pc.plan.good n o x) → ∀ g,
      ((pc.plan.cur n o pc.E).filter (Nc.Plus.OneIn (Nc.G.hold0 pc.sys.np) (Nc.G.hold1 pc.sys.np) (pc.grp n o) g)).card ≤
        bd := fun n o hn hg g => by
    rw [hbd, Nat.le_div_iff_mul_le (Nat.mul_pos pc.ub_pos (vpos 300)), ← Nat.mul_assoc, hL]
    exact pc.cut_le n o ((pc.tab_valid n).1 hn) hg g
  have hevle : ∀ n o, pc.tab.valid n → (∀ x, pc.plan.good n o x) → ∀ g,
      Nc.Dl.evG pc.grp n o g + Nc.Dl.pdG pc.plan pc.grp n o g ≤ ev := fun n o hn hg g => by
    rw [hev, Nat.le_div_iff_mul_le hubk, ← Nat.mul_assoc, hL]
    exact pc.all_le n o ((pc.tab_valid n).1 hn) hg g
  have hbase : ∀ n o, pc.tab.valid n → (∀ x, pc.plan.good n o x) → ∀ g,
      (univ.filter fun p : Fin (K + K) => pc.grp n o (Fin.castAdd pc.A' p) = g).card ≤ ιb := fun n o hn hg g => by
    rw [hιb, Nat.le_div_iff_mul_le (by omega)]
    exact pc.blocks_le n o ((pc.tab_valid n).1 hn) hg g
  have hnum : ∀ n o y, pc.plan.num n o y ≤ X := fun n o y => by
    have h1 := pc.tab.hnum y (n, o)
    have h2 := (pc.tab.fn (pc.tab.knum y) (n, o)).2
    simp only at h1
    omega
  -- the evaluator of this code
  obtain ⟨ci, hci⟩ : ∃ ci : Fin (Cp + 1), ci.1 = pc.c := ⟨⟨pc.c, Nat.lt_succ_of_le pc.c_le⟩, rfl⟩
  obtain ⟨cb, hcb⟩ : ∃ cb : Option Γ → Fin ci.1 → Bool, cb = fun z j => pc.cb z (Fin.cast hci j) := ⟨_, rfl⟩
  obtain ⟨GROUP, κ', hG, hGtime, hsize⟩ : ∃ (GROUP : Fm) (κ' : ℕ),
      Nc.Dl.GroupOK θ mu pc.cb kinds (fun z => (Nc.Grp.qn Q z : ℕ)) GROUP κ' ∧
      Nc.Dl.GrpTimeOK (S := S) A pc.cb (fun z => (Nc.Grp.qn Q z : ℕ)) ∧ GROUP.code.size + κ' ≤ Zg := by
    obtain ⟨cn, hcn⟩ := ci
    simp only at hci
    subst hci
    refine ⟨GR ⟨pc.c, hcn⟩ pc.cb, κ ⟨pc.c, hcn⟩ pc.cb, hGR ⟨pc.c, hcn⟩ pc.cb, hGT ⟨pc.c, hcn⟩ pc.cb, ?_⟩
    rw [hZg]
    exact le_trans (Finset.single_le_sum (f := fun cb => (GR ⟨pc.c, hcn⟩ cb).code.size + κ ⟨pc.c, hcn⟩ cb)
      (fun _ _ => Nat.zero_le _) (mem_univ pc.cb))
      (Finset.single_le_sum (f := fun c : Fin (Cp + 1) => ∑ cb : Option Γ → Fin c.1 → Bool,
        ((GR c cb).code.size + κ c cb)) (fun _ _ => Nat.zero_le _) (mem_univ (⟨pc.c, hcn⟩ : Fin (Cp + 1))))
  -- the program G
  have : Nonempty Q := ⟨i⟩
  obtain ⟨G, hGs, hcut⟩ := thm_onecut_program (θ := θ) (mu := mu) (i := i) (e := e') (b0 := b0) (b1 := b1) (τ := τ) (s := s)
    (X := X) (Lc := Lc) (bT := (Nc.Dl.bitsN Lc T).reverse) (bub := (Nc.Dl.bitsN Lc pc.ub).reverse)
    (nub := Nc.Dl.bitsN Lc pc.ub) (nl := Nc.Dl.bitsN Lc ℓ) (ℓ := ℓ) (cb := pc.cb) (bd := bd) (ιb := ιb)
    (tB := 2 * (Lc + 1) * (T + pc.ub + 2) + ιb * T + 1000 * (ev + ιb * pc.load) * (pc.ub + Lc + 1) +
      X ^ 4 * 1000 * (Lc + 1))
    hK0 hG (fun z hz hpl => by
      rw [t4]
      refine hCU τ z (K * T) hpl (le_trans ?_ hKTge)
      rw [htU]
      exact Nat.mul_le_mul (Nat.mul_le_mul (by omega) (by omega)) (Nat.pow_le_pow_left (lg_mono (by omega)) 2))
    htg pc.tab pc.ok (by rw [u4]; exact pc.ub_pos) (by rw [u2, u4]) l2 pc.U1_pos (by rw [t4]; exact hℓT)
    (fun z hz => by
      rw [t4, u4]
      rw [pc.value i e' (fun _ => Nc.Dl.wordG b0 b1 z) ℓ hℓT (by rw [Nc.Dl.length_wordG]; exact hz.trans hsK)]
      refine Finset.sum_congr rfl fun q _ => if_congr Iff.rfl ?_ rfl
      refine Finset.sum_congr rfl fun ρ _ => if_congr Iff.rfl ?_ rfl
      exact Finset.sum_congr rfl fun n _ => if_congr (pc.tab_valid n).symm rfl rfl)
    hbdle hbase hnum pc.digits.1 pc.digits.2.1 pc.digits.2.2.2 pc.digits.2.2.1 Cd hCd (by omega)
    t3.le u3.le u1.le l1.le hK2 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hcId hSX (by omega) hrow hcR
    (fun y => le_trans (by have := hlaw' y; omega : Fintype.card (pc.sys.kind y).Sl ≤ ml) (by omega))
    (fun y => le_trans (by have := hlaw' y; omega : Fintype.card (pc.sys.kind y).Cn ≤ ml) (by omega))
    (fun q => (hcq q).trans (by omega)) (fun r => by
      have h1 := htg r
      have h2 : tg r < kinds.length := by
        by_contra hlt
        rw [List.getElem?_eq_none (not_lt.1 hlt)] at h1
        simp at h1
      omega) (by omega) hnums.mmX (by have := pc.c_le; omega) (fun q x ρ n o b g hx hn ho => by
        have := hGtime pc.plan pc.ok q x ρ n o (pc.grp n o) g Cd.key Cd.dkey tg (Nc.Dl.bitsN Lc T).reverse
          (Nc.Dl.bitsN Lc pc.ub).reverse b (Lc := Lc) (X := X) (ιb := ιb) (lh := pc.load) (ev := ev) hx hCd.key hCd.dkey
          t3.le u3.le hSX hK2 hcR hcId (fun y => by have := hlaw' y; omega) (fun y => by have := hlaw' y; omega)
          (hbase n o hn ho g) hnums.ιbX (fun p _ => (pc.tab_valid n).1 hn p) (hevle n o hn ho g)
        refine this.trans (le_of_eq ?_)
        rw [t4, u4])
  have hm10 : lg v ^ (10 * C1) = m ^ 10 := by rw [← hl, hm, ← pow_mul, Nat.mul_comm]
  refine ⟨G, ?_, ?_⟩
  · calc G.size ≤ (Nc.Dl.dealC + 3000) * (X * Lc) ^ 4 := hGs
      _ ≤ v * (X * v) ^ 4 := Nat.mul_le_mul (by omega) (Nat.pow_le_pow_left (Nat.mul_le_mul_left _ (by omega)) 4)
      _ = v ^ ((b₁ + 1) * 4 + 1) := by rw [hX, ← pow_succ, ← pow_mul, ← pow_succ']
      _ ≤ v ^ (a + e + 6 * b₁ + 400) := vpow (by omega)
  · rw [hm10]
    rw [u4] at hcut
    refine hcut.mono (hnums.time (by omega)) hnums.size
      (hnums.mm_le.trans (Nat.mul_le_mul_left _ (Nat.le_self_pow (by norm_num) m))) hnums.deal

/-- **Paper: Theorem thm:cut.** "There are a multiple H ≥ 272 of 16 and constants C₀, v₀ such that the following holds
whenever v ≥ v₀ and (lg v)^(C₀α) ≤ v. For v^H ≤ τ ≤ v^(Hα) and sv^48 ≤ τ some program of size at most v^H cuts (τ,s)
into (v^H, v^(H−32)) with at most τv²/v^H pieces in at most τ/v^24 steps." The proof composes the cuts of Theorem
thm:onecut. -/
theorem thm_cut {θ : List Bool → A} (hθ : Generates θ) {h' : ℕ} [NeZero h']
    (VL : VLaws A (cNear (h := h')) (dNear (h := h')) 1 (2 ^ ee h')) (h3 : 3 ≤ h')
    (hgain : 1 + 8 * VL.C₁ ≤ (h' : ℝ) / 4) :
    ∃ H C₀ v₀ : ℕ, 272 ≤ H ∧ 16 ∣ H ∧ ∀ v, v₀ ≤ v → ∀ α τ s, lg v ^ (C₀ * α) ≤ v → v ^ H ≤ τ → τ ≤ v ^ (H * α) →
      s * v ^ 48 ≤ τ → ∃ G : Tree, G.size ≤ v ^ H ∧
        CutD θ τ s (v ^ H) (v ^ (H - 32)) (τ * v ^ 2 / v ^ H) (τ / v ^ 24) G := by
  obtain ⟨a₀, C, v₀, hv₀⟩ := thm_onecut hθ VL h3 hgain
  obtain ⟨h, hhdef⟩ : ∃ h, h = a₀ + 217 := ⟨_, rfl⟩
  have hh : a₀ + 200 ≤ 16 * h := by omega
  refine ⟨16 * h, (3 * C + 4) * (32 * h + 2), v₀ + 2 ^ 100 + 4000, by omega, dvd_mul_right 16 h,
    fun v hv α τ s hlog hτ hτα hs => ?_⟩
  obtain ⟨r, hr⟩ : ∃ r, r = 16 * h * α := ⟨_, rfl⟩
  have hv1 : 4000 ≤ v := by omega
  have hv0 : 1 ≤ v := by omega
  have hl100 : 100 ≤ lg v := (Nat.le_succ _).trans (le_lg_of_two_pow_le (by omega))
  have hα : 1 ≤ α := by
    by_contra hne
    have h0 : α = 0 := by omega
    rw [h0, Nat.mul_zero, pow_zero] at hτα
    have : v ≤ v ^ (16 * h) := Nat.le_self_pow (by omega) v
    omega
  have hαl : 2 * r ≤ lg v := by
    refine le_trans ?_ (le_lg_of_lg_pow_le (by omega) hlog)
    rw [hr, Nat.mul_assoc (3 * C + 4), ← Nat.mul_assoc 2]
    refine le_trans (Nat.mul_le_mul_right _ (?_ : 2 * (16 * h) ≤ 32 * h + 2)) (Nat.le_mul_of_pos_left _ (by omega))
    omega
  obtain ⟨q4, hq4⟩ : ∃ n, n = 4 ^ (r + 1) := ⟨_, rfl⟩
  obtain ⟨Λ, hΛ⟩ : ∃ n, n = lg v ^ (C + 1) := ⟨_, rfl⟩
  have hl2 := lg_ge_two (show 4 ≤ v by omega)
  have hΛ2 : 2 ≤ Λ := by
    rw [hΛ]
    exact hl2.trans (Nat.le_self_pow (by omega) _)
  have hΛ1 : 1 ≤ Λ := by omega
  have hX : (100 * Λ ^ 3) ^ (r + 1) ≤ v := hΛ ▸ hr ▸ polylog_loss_le hl100 hα hlog
  have hq4v : q4 ≤ v := by
    refine hq4 ▸ le_trans (Nat.pow_le_pow_left ?_ _) hX
    exact le_trans (by norm_num) (Nat.le_mul_of_pos_right 100 (Nat.pow_pos (show 0 < Λ by omega)))
  have hX1 : 100 * Λ ^ 3 ≤ v := (Nat.le_self_pow (by omega) _).trans hX
  have hL3 : Λ ≤ Λ ^ 3 := Nat.le_self_pow (by norm_num) Λ
  have hL2 : Λ ^ 2 ≤ Λ ^ 3 := Nat.pow_le_pow_right hΛ1 (by norm_num)
  have hat0 : OneCutAt θ v a₀ (16 * h * α) (lg v ^ C) := by
    intro τ' s' k' h1 h2 h3' h4 h5
    refine hv₀ v (by omega) τ' s' k' h1 ?_ h3' h4 h5
    have h6 : lg τ' ≤ 16 * h * α * lg v := (lg_mono h2).trans (lg_pow_le (Nat.mul_pos (by omega) hα))
    have h7 : 4 * (16 * h * α) ≤ lg v := by
      refine le_trans ?_ (le_lg_of_lg_pow_le (by omega) hlog)
      have h8 : 4 * (16 * h) * α ≤ (3 * C + 4) * (32 * h + 2) * α := by
        refine Nat.mul_le_mul_right _ ?_
        calc 4 * (16 * h) ≤ 4 * (32 * h + 2) := by omega
          _ ≤ _ := Nat.mul_le_mul_right _ (by omega)
      calc 4 * (16 * h * α) = 4 * (16 * h) * α := by ring
        _ ≤ _ := h8
    calc 4 * lg τ' ≤ 4 * (16 * h * α * lg v) := Nat.mul_le_mul_left _ h6
      _ = 4 * (16 * h * α) * lg v := by ring
      _ ≤ lg v * lg v := Nat.mul_le_mul_right _ h7
      _ = lg v ^ 2 := by ring
  have hat : OneCutAt θ v a₀ (16 * h * α) Λ := OneCutAt.mono (Λ := lg v ^ C) hat0 (by
    rw [hΛ]
    exact Nat.pow_le_pow_right (by omega) (Nat.le_succ C))
  have pmono : ∀ {a b}, a ≤ b → v ^ a ≤ v ^ b := fun h => Nat.pow_le_pow_right hv0 h
  have ppos : ∀ a, 0 < v ^ a := fun a => Nat.pow_pos (by omega)
  obtain ⟨G, P, t, s', hcut, hP, ht, hs', hG⟩ := thm_cut_iterate hat (by omega) hΛ2 (by omega) (H := 16 * h) (by omega) (by omega)
    r τ s 1 hτ hτα (by
      calc τ * Λ < τ * v := Nat.mul_lt_mul_of_pos_left (by omega) (lt_of_lt_of_le (ppos _) hτ)
        _ ≤ v ^ (16 * h * α) * v := Nat.mul_le_mul_right _ hτα
        _ = v ^ (r + 1) := by rw [hr, pow_succ]
        _ ≤ v ^ (16 * h + (64 + 62 * r)) := pmono (by omega)
        _ = _ := pow_add _ _ _) (by simpa using hs) le_rfl (by rw [one_mul, ← hq4]; omega)
  have e8 : (8 * Λ) ^ (r + 1) ≤ v := (Nat.pow_le_pow_left (by omega) _).trans hX
  have e4 : (4 * Λ ^ 2) ^ (r + 1) ≤ v := (Nat.pow_le_pow_left (by omega) _).trans hX
  refine ⟨G, ?_, hcut.mono le_rfl ?_ ((Nat.le_div_iff_mul_le (ppos _)).2 ?_) ((Nat.le_div_iff_mul_le (ppos _)).2 ?_)⟩
  · have hq : 4 ^ r ≤ v := (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ r)).trans (by rw [← hq4]; omega)
    calc G.size ≤ 4 ^ r * (v ^ a₀ + 3000) := hG
      _ ≤ v * (v ^ a₀ + v) := Nat.mul_le_mul hq (by omega)
      _ ≤ v * (v ^ (a₀ + 1) + v ^ (a₀ + 1)) := Nat.mul_le_mul_left _ (Nat.add_le_add (pmono (Nat.le_succ _)) (by
          calc v = v ^ 1 := (pow_one v).symm
            _ ≤ _ := pmono (by omega)))
      _ = 2 * v ^ (a₀ + 2) := by rw [pow_succ v (a₀ + 1)]; ring
      _ ≤ v * v ^ (a₀ + 2) := Nat.mul_le_mul_right _ (by omega)
      _ = v ^ (a₀ + 3) := by rw [pow_succ v (a₀ + 2)]; ring
      _ ≤ v ^ (16 * h) := pmono (by omega)
  · have h1 : s' * v ^ 48 ≤ v ^ (16 * h - 32) * v ^ 48 := by
      calc s' * v ^ 48 ≤ 1 * v ^ (16 * h) * (8 * Λ) ^ (r + 1) := hs'
        _ ≤ 1 * v ^ (16 * h) * v := Nat.mul_le_mul_left _ e8
        _ = v ^ (16 * h + 1) := by rw [one_mul, pow_succ]
        _ ≤ v ^ (16 * h - 32 + 48) := pmono (by omega)
        _ = _ := pow_add _ _ _
    exact Nat.le_of_mul_le_mul_right h1 (ppos 48)
  · calc P * v ^ (16 * h) ≤ τ * (4 * Λ ^ 2) ^ (r + 1) := hP
      _ ≤ τ * v := Nat.mul_le_mul_left _ e4
      _ ≤ τ * v ^ 2 := Nat.mul_le_mul_left _ (Nat.le_self_pow (by norm_num) v)

  · have h1 : t * v ^ 24 * v ^ 24 ≤ τ * v ^ 24 := by
      calc t * v ^ 24 * v ^ 24 = t * v ^ 48 := by rw [Nat.mul_assoc, ← pow_add]
        _ ≤ 1 * τ * (100 * Λ ^ 3) ^ (r + 1) := ht
        _ ≤ τ * v := by rw [one_mul]; exact Nat.mul_le_mul_left _ hX
        _ ≤ τ * v ^ 24 := Nat.mul_le_mul_left _ (Nat.le_self_pow (by norm_num) v)
    exact Nat.le_of_mul_le_mul_right h1 (ppos 24)

/-- What the next section starts from, in the form NS1.CutHyp: the conclusion of Theorem thm:cut multiplied out. -/
theorem cutHyp_of_laws {θ : List Bool → A} (hθ : Generates θ) {h' : ℕ} [NeZero h']
    (VL : VLaws A (cNear (h := h')) (dNear (h := h')) 1 (2 ^ ee h')) (h3 : 3 ≤ h')
    (hgain : 1 + 8 * VL.C₁ ≤ (h' : ℝ) / 4) : ∃ h C₀ v₀ : ℕ, 17 ≤ h ∧ CutHyp θ (16 * h) C₀ v₀ := by
  obtain ⟨H, C₀, v₀, hH, ⟨h, rfl⟩, hcut⟩ := thm_cut hθ VL h3 hgain
  refine ⟨h, C₀, v₀ + 1, by omega, fun v hv α τ s hl h1 h2 h4 => ?_⟩
  obtain ⟨G, hsize, hG⟩ := hcut v (by omega) α τ s hl h1 h2 h4
  have hp : ∀ a, 0 < v ^ a := fun a => Nat.pow_pos (by omega)
  exact ⟨G, hG.cutProg hsize ((Nat.le_div_iff_mul_le (hp _)).1 le_rfl) ((Nat.le_div_iff_mul_le (hp _)).1 le_rfl)⟩

/-- "We keep A, H and C₀ of the theorem on cuts at all scales": what the next section starts from. -/
theorem exists_setting {K : Type} [Field K] (hK : Contracting K) :
    ∃ (A : Subring K) (_ : Algebra.FiniteType ℤ A) (θ : List Bool → A) (h C₀ v₀ : ℕ),
      Generates θ ∧ 17 ≤ h ∧ CutHyp θ (16 * h) C₀ v₀ := by
  obtain ⟨h', hne, h3, A, hA, VL, hgain, -⟩ := exists_laws hK
  obtain ⟨θ, hθ⟩ := exists_generates A
  obtain ⟨h, C₀, v₀, hh, hcut⟩ := cutHyp_of_laws hθ VL h3 hgain
  exact ⟨A, hA, θ, h, C₀, v₀, hθ, hh, hcut⟩

end Paper
