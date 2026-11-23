/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Dl.Does
import Nc.Dl.SizeDeal
import Nc.Dl.SizeScript
import Nc.Dl.Cost
import Nc.Grp.GroupProg

/-!
# One cut, with numbers
-/

set_option linter.unusedSectionVars false

namespace Nc.Dl

open NS1 NS1.Tree Finset Nc.G Nc.Cut Codes

/-- The time of GROUP at a script. -/
def grpT (bT bub : List Bool) (l : List Grp.Ins) : ℕ :=
  (bT.length + 1) * (Grp.bval bT + 1) + (bub.length + 1) * (Grp.bval bub + 1) +
    (l.map (Grp.insCost (Grp.bval bT) (Grp.bval bub))).sum + l.length

/-- **What GROUP does** (the conclusion of `Nc.Grp.exists_group`). -/
def GroupOK {A : Type} [CommRing A] (θ : List Bool → A) {Γ S Q : Type} [Fintype Γ] [DecidableEq Γ] [Fintype S]
    [DecidableEq S] [Fintype Q] [DecidableEq Q] {c : ℕ} (mu : Letter S Unit Γ → Matrix Q Q A)
    (cb : Option Γ → Fin c → Bool) (kinds : List (Σ L : G.Law A, L.Ro)) (qn : Q → ℕ) (GROUP : Fm) (κ : ℕ) : Prop :=
  ∀ {A' K E U0 U1 cap : ℕ} {Gr : Type} [DecidableEq Gr] [Fintype Gr]
    {M : Sys A (K + K + A') E} (P : G.Plan M U0 U1) (q : Fin (K + 1) → Q) (x : Fin K → List Γ)
    (ρ : Option S → Fin (K + K) → RowData (K + K)) (n : Fin (K + K) → Fin (K + K) → Fin (U0 + 1))
    (o : M.N → Fin U1) (grp : Fin (K + K + A') → Gr) (g : Gr) (key : Grp.Cell M U0 U1 → List Bool)
    (dkey : Fin (K + K) × Fin U0 → List Bool) (tg : M.R → ℕ) (bT bub : List Bool)
    (b : G.Uid (K + K) U0 M.N U1 → UW (Grp.bval bub)),
    Function.Injective (Sum.elim key dkey) → 0 < Grp.bval bub → P.Ok cap → (∀ κ, (x κ).length ≤ Grp.bval bT) →
    (∀ s p, (ρ s p).1 = false → (ρ s p).2.1 ≤ (ρ s p).2.2) → (∀ r, kinds[tg r]? = some ⟨M.kind r.1, r.2⟩) →
    Plain θ (κ * grpT bT bub (Grp.script qn cb P q x ρ n o grp g key dkey tg b))
      (.cons GROUP.code (Grp.scriptT bT bub (Grp.script qn cb P q x ρ n o grp g key dkey tg b))) ∧
    pv θ (.cons GROUP.code (Grp.scriptT bT bub (Grp.script qn cb P q x ρ n o grp g key dkey tg b))) =
      G.grpVal mu (Grp.bval bT) cb P q x ρ n o grp g b ∧
    (evl θ GROUP (Grp.scriptT bT bub (Grp.script qn cb P q x ρ n o grp g key dkey tg b)) ≠ [] →
      (∀ p, grp (Fin.castAdd A' p) = g → ∑ b, ((n p b : ℕ) + n b p) ≤
        2 * ((Grp.bval bT + (K + K) * (Fintype.card S + 1)) * c / Grp.bval bub + (K + K))) ∧
      ∀ r : M.R, grp (M.rp r) = g → ∃ ι : Fin (P.num n o r.1 * Grp.bval bub) → (M.kind r.1).I,
        ∀ ν : (M.kind r.1).CnAt r.2,
          (o ⟨r.1, ν.1⟩ : ℕ) = (∑ k, ((M.kind r.1).lam + (M.kind r.1).len (ι k) ν.1)) / Grp.bval bub)

/-- The number of all names, digits, keys. -/
structure CodesLe {A : Type} [CommRing A] {S : Type} [Fintype S] {K A' E U0 U1 D pS : ℕ} {M : Sys A (K + K + A') E}
    (C : Codes S M U0 U1 D pS) (Lc : ℕ) : Prop where
  nm : ∀ y, (C.nm y).length ≤ Lc
  dc : ∀ d, (C.dc d).length ≤ Lc
  rc : ∀ d, (C.rc d).length ≤ Lc
  key : ∀ a, (C.key a).length ≤ Lc
  dkey : ∀ a, (C.dkey a).length ≤ Lc
  inj : Function.Injective (Sum.elim C.key C.dkey)

theorem exists_codes {A : Type} [CommRing A] {S : Type} [Fintype S] [DecidableEq S] {K A' E U0 U1 D pS : ℕ}
    {M : Sys A (K + K + A') E} {Lc : ℕ}
    (h1 : Fintype.card (Nm K E pS S M.N (G.Uid (K + K) U0 M.N U1)) ≤ 2 ^ Lc) (h2 : D ≤ 2 ^ Lc)
    (h3 : Fintype.card (RowData (K + K)) ≤ 2 ^ Lc)
    (h4 : Fintype.card (Grp.Cell M U0 U1 ⊕ Fin (K + K) × Fin U0) ≤ 2 ^ Lc) :
    ∃ C : Codes S M U0 U1 D pS, CodesLe C Lc := by
  obtain ⟨f1, i1, l1⟩ := exists_code _ h1
  obtain ⟨f2, i2, l2⟩ := exists_code (Fin D) (by rwa [Fintype.card_fin])
  obtain ⟨f3, i3, l3⟩ := exists_code _ h3
  obtain ⟨f4, i4, l4⟩ := exists_code _ h4
  refine ⟨⟨f1, i1, f2, i2, f3, i3, fun a => f4 (.inl a), fun a => f4 (.inr a)⟩, fun y => (l1 y).le, fun y => (l2 y).le,
    fun y => (l3 y).le, fun y => (l4 _).le, fun y => (l4 _).le, ?_⟩
  intro x y hxy
  apply i4
  cases x <;> cases y <;> exact hxy

variable {A : Type} [CommRing A] {Γ S Q : Type} [Fintype Γ] [DecidableEq Γ] [Fintype S] [DecidableEq S] [Fintype Q]
  [DecidableEq Q] {θ : List Bool → A} {K A' E U0 U1 mm D pS c ℓ : ℕ} {M : Sys A (K + K + A') E} {P : G.Plan M U0 U1}
  {grp : NN K U0 → (M.N → Fin U1) → Fin (K + K + A') → Fin mm} {mu : Letter S Unit Γ → Matrix Q Q A}
  {cb : Option Γ → Fin c → Bool} {kinds : List (Σ L : G.Law A, L.Ro)} {qn : Q → ℕ} {GROUP : Fm} {κ : ℕ}

/-- The cut units: at most `bd` for every group. -/
theorem card_cutUnits_le {n : NN K U0} {o : M.N → Fin U1} {bd : ℕ}
    (h : ∀ g, ((P.cur n o E).filter (Nc.Plus.OneIn (G.hold0 M.np) (G.hold1 M.np) (grp n o) g)).card ≤ bd) :
    (cutUnits (G.hold0 M.np) (G.hold1 M.np) (grp n o) (P.cur n o E)).card ≤ mm * bd := by
  classical
  have hsub : cutUnits (G.hold0 M.np) (G.hold1 M.np) (grp n o) (P.cur n o E) ⊆ (univ : Finset (Fin mm)).biUnion fun g =>
      (P.cur n o E).filter (Nc.Plus.OneIn (G.hold0 M.np) (G.hold1 M.np) (grp n o) g) := by
    intro id hid
    obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hid
    rw [Finset.mem_biUnion]
    exact ⟨grp n o (G.hold0 M.np id), Finset.mem_univ _, Finset.mem_filter.2 ⟨h1, Or.inl ⟨rfl, Ne.symm h2⟩⟩⟩
  refine (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans ?_)
  refine (Finset.sum_le_sum fun g _ => h g).trans ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

theorem card_cutAt_le {n : NN K U0} {o : M.N → Fin U1} {bd : ℕ} {g : Fin mm}
    (h : ((P.cur n o E).filter (Nc.Plus.OneIn (G.hold0 M.np) (G.hold1 M.np) (grp n o) g)).card ≤ bd) :
    (cutAt P n o (grp n o) g).card ≤ bd := by
  classical
  refine (Finset.card_le_card fun id hid => ?_).trans h
  unfold cutAt at hid
  obtain ⟨-, h1, h2, h3⟩ := Finset.mem_filter.1 hid
  refine Finset.mem_filter.2 ⟨h1, ?_⟩
  rcases h3 with h3 | h3
  · exact Or.inl ⟨h3, fun h4 => h2 (h3.trans h4.symm)⟩
  · exact Or.inr ⟨fun h4 => h2 (h4.trans h3.symm), h3⟩

open Classical in
/-- **Paper: Theorem thm:onecut, the program G.** "Every choice in the formula is guessed exactly once"; script
size and time: G cuts, with numbers. -/
theorem _root_.Paper.thm_onecut_program {i e : Q} {b0 b1 : Γ} {τ s cap bd ιb X Lc tB : ℕ} {tg : M.R → ℕ} {bT bub nub nl : List Bool}
    -- the automaton and GROUP
    (hK : 0 < K) [Nonempty Q] (hGR : GroupOK θ mu cb kinds qn GROUP κ)
    (hU : ∀ z, z.size ≤ s → Plain θ τ z → runVal mu i e (K * Grp.bval bT) (fun _ => wordG b0 b1 z) = pv θ z)
    (hkind : ∀ r, kinds[tg r]? = some ⟨M.kind r.1, r.2⟩)
    -- the plan, the formula and the bounds of the pieces
    (tab : SlpTab P grp D pS) (hP : P.Ok cap) (hub : 0 < Grp.bval bub) (hnub : KT.val nub = Grp.bval bub)
    (hnl : KT.val nl = ℓ) (hU1p : 0 < U1) (hℓ : ℓ ≤ Grp.bval bT)
    (hval : ∀ z, z.size ≤ s → runVal mu i e (K * Grp.bval bT) (fun _ => wordG b0 b1 z) =
      ∑ q : Fin (K + 1) → Q, if q 0 = i ∧ q (Fin.last K) = e then
        ∑ ρ : Option S → Fin (K + K) → RowData (K + K), if ValidRows ρ then
          ∑ n : NN K U0, if tab.valid n then
            ∑ o : M.N → Fin U1, if ∀ x, P.good n o x then
              ∑ b ∈ Common (none : UW (Grp.bval bub)) (cutUnits (G.hold0 M.np) (G.hold1 M.np) (grp n o) (P.cur n o E)),
                ∏ g, G.grpVal mu (Grp.bval bT) cb P q (parts ℓ (wordG b0 b1 z)) ρ n o (grp n o) g b
            else 0
          else 0
        else 0
      else 0)
    (hbdle : ∀ n o, tab.valid n → (∀ x, P.good n o x) → ∀ g,
      ((P.cur n o E).filter (Nc.Plus.OneIn (G.hold0 M.np) (G.hold1 M.np) (grp n o) g)).card ≤ bd)
    (hbase : ∀ n o, tab.valid n → (∀ x, P.good n o x) → ∀ g,
      (univ.filter fun p : Fin (K + K) => grp n o (Fin.castAdd A' p) = g).card ≤ ιb)
    (hnum : ∀ n o y, P.num n o y ≤ X)
    -- digits
    (hU0D : U0 < D) (hU1D : U1 ≤ D) (hD1 : 1 < D) (hmmD : mm ≤ D)
    -- sizes
    (C : Codes S M U0 U1 D pS) (hC : CodesLe C Lc) (hLc : 1 ≤ Lc) (hbT : bT.length ≤ Lc) (hbub : bub.length ≤ Lc)
    (hnubl : nub.length ≤ Lc) (hnll : nl.length ≤ Lc) (hK1 : K + K + 1 ≤ X) (hU0X : U0 + 1 ≤ X) (hU1X : U1 ≤ X) (hE : E + 1 ≤ X)
    (hDX : D ≤ X) (hpS : pS ≤ X) (hN : Fintype.card M.N ≤ X) (hId : Fintype.card (G.Uid (K + K) U0 M.N U1) ≤ X)
    (hS : Fintype.card (Option S) ≤ X) (hQ : Fintype.card Q + 1 ≤ X) (hrow : Fintype.card (RowData (K + K)) ≤ X)
    (hR : Fintype.card M.R ≤ X) (hSl : ∀ y, Fintype.card (M.kind y).Sl ≤ X) (hCn : ∀ y, Fintype.card (M.kind y).Cn ≤ X)
    (hqn : ∀ q, qn q ≤ X) (htg : ∀ r, tg r + 4 ≤ X) (hgp : GROUP.code.size ≤ X) (hmm : mm ≤ X) (hcX : c ≤ X)
    -- time of GROUP
    (htB : ∀ (q : Fin (K + 1) → Q) (x : Fin K → List Γ) (ρ : Option S → Fin (K + K) → RowData (K + K)) (n : NN K U0)
      (o : M.N → Fin U1) (b : G.Uid (K + K) U0 M.N U1 → UW (Grp.bval bub)) (g : Fin mm), (∀ κ, (x κ).length ≤ Grp.bval bT) →
      tab.valid n → (∀ x, P.good n o x) →
      grpT bT bub (Grp.script qn cb P q x ρ n o (grp n o) g C.key C.dkey tg b) ≤ tB) :
    ∃ G : Tree, G.size ≤ (dealC + 3000) * (X * Lc) ^ 4 ∧ CutD θ τ s (κ * tB)
      (X + 1 + (200 * X ^ 3 * Lc + ιb * ℓ * (4 * c + 2) + bd * (4 * Grp.bval bub))) mm
      (dealB Lc X K mm (Grp.bval bub) (mm * bd) (4 * (X * X) + 10 * X) s) G := by
  classical
  have : Nonempty (Fin U1) := ⟨⟨0, hU1p⟩⟩
  have hSlAt : ∀ r : M.R, Fintype.card ((M.kind r.1).SlAt r.2) ≤ X := fun r => (Fintype.card_subtype_le _).trans (hSl _)
  have hCnAt : ∀ r : M.R, Fintype.card ((M.kind r.1).CnAt r.2) ≤ X := fun r => (Fintype.card_subtype_le _).trans (hCn _)
  let gt : Fin mm → Tree := fun g => C.dt ⟨g, lt_of_lt_of_le g.2 hmmD⟩
  let d1 : Tree := C.dt ⟨1, hD1⟩
  have hd1 : ∀ d : Fin D, C.dt d = d1 ↔ d.1 = 1 := fun d => by
    rw [show d1 = C.dt ⟨1, hD1⟩ from rfl, dt_inj.eq_iff, Fin.ext_iff]
  have hgt : ∀ (d : Fin D) (g : Fin mm), C.dt d = gt g ↔ d.1 = g.1 := fun d g => by
    rw [show gt g = C.dt ⟨g, lt_of_lt_of_le g.2 hmmD⟩ from rfl, dt_inj.eq_iff, Fin.ext_iff]
  have hdts : ∀ d, (C.dt d).size ≤ 4 * Lc + 1 := fun d => by
    have h1 := size_ofBits (C.dc d)
    have h2 := hC.dc d
    rw [dt]
    omega
  have hH : SizeHyp C qn tg X Lc := by
    refine { hLc := hLc, nm := hC.nm, dc := hC.dc, rc := hC.rc, key := hC.key, dkey := hC.dkey, hK1 := by omega,
             hK2 := by omega, hU0 := hU0X, hU1 := hU1X, hE := hE, hD := hDX, hpS := hpS, hN := hN, hId := hId, hS := hS,
             hQ := hQ, row := hrow, hR := hR, Sl := ?_, Cn := ?_, hqn := hqn, htg := htg }
    · exact hSlAt
    · exact hCnAt
  refine ⟨(dealProg C tab qn tg bT bub nl nub gt d1 GROUP.code cb b0 b1 i e hU0D hU1D).code,
    size_dealProg (tab := tab) (H := hH) (hd1 := hdts _) (hgt := fun g => hdts _) (hbT := hbT) (hbub := hbub) (hgp := hgp)
      (hmm := hmm) (hnl := hnll) (hnub := hnubl) (hc := hcX) .., ?_⟩
  refine deal_cut C tab qn tg bT bub nl nub gt d1 GROUP.code cb b0 b1 i e hU0D hU1D hK hnl hnub hd1 hgt hU
    hval ?_ ?_
  · intro z hz
    exact deal_does hK hnl hnub hnll hnubl hC.nm hC.dc hC.rc hLc hQ hrow hU0X hU1X hS (by omega) hId hSlAt hCnAt hR
      (length_steps18_le hQ hS hK1 hN hpS hE hId) (fun n o hn ho => card_cutUnits_le (hbdle n o hn ho)) z hz
  · intro z hz q ρ n o b g hρ hn ho hb
    have hx : ∀ κ : Fin K, (parts ℓ (wordG b0 b1 z) κ).length ≤ Grp.bval bT := fun κ => (length_parts_le _ _ _).trans hℓ
    have hρ' : ∀ s p, (ρ s p).1 = false → (ρ s p).2.1 ≤ (ρ s p).2.2 := by
      intro s p hf
      have := hρ s p
      rw [if_neg (by simp [hf])] at this
      exact this.2
    obtain ⟨h1, h2, h3⟩ := hGR P q (parts ℓ (wordG b0 b1 z)) ρ n o (grp n o) g C.key C.dkey tg bT bub b hC.inj hub hP hx hρ'
      hkind
    refine ⟨?_, ?_, h2⟩
    · have hsz := size_scriptT (qn := qn) (cb := cb) (P := P) (q := q) (x := parts ℓ (wordG b0 b1 z)) (ρ := ρ) (n := n)
        (o := o) (grp := grp n o) (g := g) (key := C.key) (dkey := C.dkey) (tg := tg) (X := X) (Lc := Lc) (by omega) hLc
        (by omega) (by omega) hU1X hS hId hR hSl hCn hC.key hC.dkey hqn (fun r => by have := htg r; omega) (hnum n o) hbT hbub b
      have hparts : (∑ κ ∈ univ.filter (fun κ : Fin K => grp n o (Fin.castAdd A' (Fin.natAdd K κ)) = g),
          (parts ℓ (wordG b0 b1 z) κ).length) ≤ ιb * ℓ := by
        refine (Finset.sum_le_card_nsmul _ _ ℓ fun κ _ => length_parts_le _ _ _).trans ?_
        rw [smul_eq_mul]
        refine Nat.mul_le_mul_right _ ?_
        refine le_trans ?_ (hbase n o hn ho g)
        refine Finset.card_le_card_of_injOn (Fin.natAdd K) ?_ ?_
        · intro κ hκ
          simpa using hκ
        · intro κ _ κ' _ h
          simpa using h
      have hcut := card_cutAt_le (hbdle n o hn ho g)
      have e1 := Nat.mul_le_mul_right (4 * c + 2) hparts
      have e2 := Nat.mul_le_mul_right (4 * Grp.bval bub) hcut
      simp only [Tree.size]
      omega
    · exact ⟨h1.1, fun r hr => ⟨(h1.2 r hr).1,
        (h1.2 r hr).2.trans (Nat.mul_le_mul_left κ (htB q _ ρ n o b g hx hn ho))⟩⟩

end Nc.Dl
