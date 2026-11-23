/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Uni.EvThm3

/-!
# The universal machine: input and result
-/

set_option linter.unusedSectionVars false

namespace Nc.Uni

open Finset NS1

variable {A : Type} [CommRing A] {θ : List Bool → A} {supp : Finset (List Bool)}

/-- The word of a tree: brackets in preorder. -/
def word : Tree → List Bool
  | .nil => [false]
  | .cons a b => true :: (word a ++ word b)

/-- What happens when a tree that has been read is returned to the frame k. -/
def PKS (θ : List Bool → A) (supp : Finset (List Bool)) (H : List (Rec Kd)) (k : ℕ) (inp : List Bool) (o : Tree) (S : A)
    (B : ℤ) : Prop :=
  ∀ (σ : St supp) (v : ℕ), OKs σ → σ.mode = .PR → σ.regs 1 = v → σ.regs 2 = k → H ⊆ σ.heap → σ.inp = inp →
    Rep σ.heap v o → Mach.SumTo (UM θ supp) σ S B

/-- A step after a tree has been read. -/
theorem pstep {σ : St supp} (hσ : OKs σ) (hm : σ.mode = .PR) {κ : Kd} {p q s : ℕ}
    (hrec : ((κ, ![σ.regs 2, p, q, s]) : Rec Kd) ∈ σ.heap) (r : Ra) (hr : nextR supp .PR κ = some (.inl r))
    (hs : (ruleA r : RD A (Nm supp)).src = .PR) (hk : (ruleA r : RD A (Nm supp)).lk = κ) {S : A} {B : ℤ}
    (h : Mach.SumTo (UM θ supp) (nx θ σ (.inl r) p q s) S (B - 1)) : Mach.SumTo (UM θ supp) σ S B := by
  have hrec' : ((κ, ![σ.regs (laM σ.mode), p, q, s]) : Rec Kd) ∈ σ.heap := by
    rw [hm]
    exact hrec
  exact (sumTo_ruleA hσ hrec' r (by rw [hm]; exact hr) (by rw [hm]; simp) (by rw [hm]; simp) (by rw [hm]; exact hs) hk
    h).mono (by omega)

/-- A step that reads a bracket. -/
theorem bstep {σ : St supp} (hσ : OKs σ) (hm : σ.mode = .P) (b : Bool) {rest : List Bool} (hi : σ.inp = b :: rest) {S : A}
    {B : ℤ} (h : Mach.SumTo (UM θ supp) (nx θ σ (.inl (if b then .pr1 else .pr0)) 0 0 0) S (B - 1)) :
    Mach.SumTo (UM θ supp) σ S B := by
  have hrec : ((.N, ![σ.regs (laM σ.mode), 0, 0, 0]) : Rec Kd) ∈ σ.heap := by
    rw [hm]
    change ((.N, ![σ.regs 0, 0, 0, 0]) : Rec Kd) ∈ σ.heap
    rw [hσ.r0]
    exact hσ.nil
  have hz : σ.mode ≠ (UM θ supp).mh := by
    rw [hm]
    change Md.P ≠ .Z
    simp
  have hfire : ∀ st' : (UM θ supp).Step, Mach.Fire σ st' ↔ st' = (.inl (if b then .pr1 else .pr0), envOf σ 0 0 0) := by
    intro st'
    rw [fire_iff hσ hrec, hm, hi]
    constructor
    · rintro ⟨h1, h2, h3, h4⟩
      refine Prod.ext ?_ h4
      have hsp : Sp st'.1 := by
        by_contra hsp
        have h6 := nextR_of (θ := θ) st'.1 hsp
        rw [h1, h2] at h6
        exact absurd h6 (by simp [nextR])
      rcases hsp with e | e | ⟨c, e⟩
      · rw [e] at h3
        cases b
        · exact e
        · exfalso
          simp [rule, ruleA, rl] at h3
      · rw [e] at h3
        cases b
        · exfalso
          simp [rule, ruleA, rl] at h3
        · exact e
      · exfalso
        rw [e] at h1
        cases c
        · exact absurd h1 (by simp [rule, ruleA, rl])
        · exact absurd h1 (by simp [rule, ruleA, rl])
    · rintro rfl
      cases b
      · refine ⟨rfl, rfl, ?_, rfl⟩
        simp [rule, ruleA, rl]
      · refine ⟨rfl, rfl, ?_, rfl⟩
        simp [rule, ruleA, rl]
  have h9 := Mach.SumTo.one hz _ hfire h
  have hw : (UM θ supp).wt (.inl (if b then .pr1 else .pr0)) = 1 := wtA _
  rw [hw, one_mul] at h9
  exact h9.mono (by omega)

/-- **Reading a tree.** -/
theorem parse {S : A} (a : Tree) : ∀ (B : ℤ) (σ : St supp) (k : ℕ) (rest : List Bool), OKs σ → σ.mode = .P → σ.regs 1 = k →
    σ.inp = word a ++ rest → PKS θ supp σ.heap k rest a S B → Mach.SumTo (UM θ supp) σ S (B + 3 * a.size) := by
  induction a with
  | nil =>
    intro B σ k rest hσ hm h1 hi hk
    refine bstep hσ hm false (rest := rest) hi ?_
    refine (hk (nx θ σ (.inl .pr0) 0 0 0) 0 (hσ.nx _ _ _ _) rfl hσ.r0 h1 (heap_nx _ _ _ _ _) ?_ rfl).mono ?_
    · rw [inp_nx, hi]
      rfl
    · simp only [Tree.size]
      push_cast
      linarith
  | cons a b iha ihb =>
    intro B σ k rest hσ hm h1 hi hk
    have hi' : σ.inp = true :: (word a ++ (word b ++ rest)) := by
      rw [hi]
      simp [word]
    refine bstep hσ hm true hi' ?_
    have ok1 := hσ.nx (θ := θ) (.inl .pr1) 0 0 0
    refine (iha (B + 3 * b.size + 2) (nx θ σ (.inl .pr1) 0 0 0) (σ.n + 1) (word b ++ rest) ok1 rfl rfl ?_ ?_).mono ?_
    · rw [inp_nx, hi']
      rfl
    · intro σ2 v ok2 hm2 h21 h22 hh2 hi2 hv
      have hfr : ((.PA, ![σ2.regs 2, σ.regs 1, σ.regs 0, σ.regs 0]) : Rec Kd) ∈ σ2.heap := by
        rw [h22]
        exact hh2 (new_nx (θ := θ) σ (.inl .pr1) 0 0 0)
      refine pstep ok2 hm2 hfr .pa rfl rfl rfl ?_
      subst h21
      have ok3 := ok2.nx (θ := θ) (.inl .pa) (σ.regs 1) (σ.regs 0) (σ.regs 0)
      refine (ihb (B + 1) (nx θ σ2 (.inl .pa) (σ.regs 1) (σ.regs 0) (σ.regs 0)) (σ2.n + 1) rest ok3 rfl rfl ?_ ?_).mono
        (by linarith)
      · rw [inpA _ _ (by simp) (by simp), hi2]
      · intro σ4 v' ok4 hm4 h41 h42 hh4 hi4 hv'
        have hfr' : ((.PB, ![σ4.regs 2, σ2.regs 1, σ.regs 1, σ2.regs 0]) : Rec Kd) ∈ σ4.heap := by
          rw [h42]
          exact hh4 (new_nx (θ := θ) σ2 (.inl .pa) (σ.regs 1) (σ.regs 0) (σ.regs 0))
        refine pstep ok4 hm4 hfr' .pb rfl rfl rfl ?_
        subst h41
        refine (hk (nx θ σ4 (.inl .pb) (σ2.regs 1) (σ.regs 1) (σ2.regs 0)) (σ4.n + 1) (ok4.nx _ _ _ _) rfl rfl h1
          (fun _ hc => heap_nx _ _ _ _ _ (hh4 (heap_nx _ _ _ _ _ (hh2 (heap_nx _ _ _ _ _ hc))))) ?_ ?_).mono (by linarith)
        · rw [inpA _ _ (by simp) (by simp), hi4]
        · refine ⟨σ2.regs 1, σ4.regs 1, σ4.regs 0, new_nx (θ := θ) σ4 (.inl .pb) (σ2.regs 1) (σ.regs 1) (σ2.regs 0), ?_, ?_⟩
          · exact ((hv.mono (heap_nx _ _ _ _ _)).mono hh4).mono (heap_nx _ _ _ _ _)
          · exact hv'.mono (heap_nx _ _ _ _ _)
    · simp only [Tree.size]
      push_cast
      linarith

variable (supp) in
/-- The first state. -/
def σ0 (z : Tree) : St supp := ⟨.S0, fun _ => 0, [(.N, ![0, 0, 0, 0])], 0, word z⟩

theorem ok_σ0 (z : Tree) : OKs (σ0 supp z) := by
  refine ⟨by simp [σ0], ?_, ?_, rfl⟩
  · intro c hc
    simp only [σ0, List.mem_singleton] at hc
    subst hc
    exact le_rfl
  · intro c hc c' hc' _
    simp only [σ0, List.mem_singleton] at hc hc'
    rw [hc, hc']

theorem closed_σ0 (z : Tree) : Mach.Closed (σ0 supp z) := by
  refine ⟨?_, ?_, fun _ => le_rfl⟩
  · intro c hc i
    simp only [σ0, List.mem_singleton] at hc
    subst hc
    fin_cases i <;> exact le_rfl
  · intro j hj
    have : j = 0 := Nat.le_zero.1 hj
    subst this
    exact ⟨(.N, ![0, 0, 0, 0]), by simp [σ0], rfl⟩

/-- A step that loads the record of register 0. -/
theorem zstep {σ : St supp} (hσ : OKs σ) {md : Md (Nm supp)} (hm : σ.mode = md) (hla : laM md = 0) (r : Ra)
    (hr : nextR supp md .N = some (.inl r)) (hP : md ≠ .P) (hD : md ≠ .D 7) (hs : (ruleA r : RD A (Nm supp)).src = md)
    (hk : (ruleA r : RD A (Nm supp)).lk = .N) {S : A} {B : ℤ}
    (h : Mach.SumTo (UM θ supp) (nx θ σ (.inl r) 0 0 0) S (B - 1)) : Mach.SumTo (UM θ supp) σ S B := by
  have hrec' : ((.N, ![σ.regs (laM σ.mode), 0, 0, 0]) : Rec Kd) ∈ σ.heap := by
    rw [hm, hla, hσ.r0]
    exact hσ.nil
  exact (sumTo_ruleA hσ hrec' r (by rw [hm]; exact hr) (by rw [hm]; exact hP) (by rw [hm]; exact fun e => hD e.1)
    (by rw [hm]; exact hs) hk h).mono (by omega)

/-- The end of a run. -/
theorem KS_halt {H : List (Rec Kd)} {k : ℕ} (hk : ((.HT, ![k, 0, 0, 0]) : Rec Kd) ∈ H) (o : Tree) :
    KS θ supp H k [] o 1 1 := by
  intro σ v ok hm h1 h2 hh hi hv
  have hht : ((.HT, ![σ.regs 2, 0, 0, 0]) : Rec Kd) ∈ σ.heap := by
    rw [h2]
    exact hh hk
  refine rstep ok hm hht .rht rfl rfl rfl ?_
  refine (Mach.SumTo.halt (P := UM θ supp) rfl ?_ (fun r => src_ne r)).mono (by norm_num)
  rw [inpA _ _ (by simp) (by simp), hi]

theorem pv_eq {τ : ℕ} {z : Tree} (h : Plain θ τ z) : pv θ z = tot (fun _ => 1) (evl θ (Fm.ofTree z.hd) z.tl) := by
  unfold pv tot pval
  congr 1
  refine List.map_congr_left fun r hr => ?_
  rw [if_pos (h.2 r hr).1, mul_one]

/-- After the tree has been read. -/
theorem PKS_eval (hθ : ∀ q, q ∉ supp → θ q = 0) {τ : ℕ} {z : Tree} (h : Plain θ τ z) {H : List (Rec Kd)} {k j s0 s1 : ℕ}
    (hj : ((.PE, ![j, k, s0, s1]) : Rec Kd) ∈ H) (hk : ((.HT, ![k, 0, 0, 0]) : Rec Kd) ∈ H) :
    PKS θ supp H j [] z (pv θ z) (Cc supp * τ + 3) := by
  intro σ3 v ok3 hm3 h31 h32 hh3 hi3 hv
  have hev := evOK (supp := supp) hθ h.1.ev
  have hfr : ((.PE, ![σ3.regs 2, k, s0, s1]) : Rec Kd) ∈ σ3.heap := by
    rw [h32]
    exact hh3 hj
  refine pstep ok3 hm3 hfr .pe rfl rfl rfl ?_
  subst h31
  have ok4 := ok3.nx (θ := θ) (.inl .pe) k s0 s1
  obtain ⟨p, q, s, hrec, hp', hq'⟩ := (hv.mono (heap_nx (θ := θ) σ3 (.inl .pe) k s0 s1)).load ok4
  have hi4 : (nx θ σ3 (.inl .pe) k s0 s1).inp = [] := (inpA _ _ (by simp) (by simp) _ _ _).trans hi3
  have hh4 : H ⊆ (nx θ σ3 (.inl .pe) k s0 s1).heap := fun _ hc => heap_nx _ _ _ _ _ (hh3 hc)
  have hr4 : (nx θ σ3 (.inl .pe) k s0 s1).regs 2 = k := rfl
  have hrec4 : ((kb (decide (z ≠ .nil)), ![(nx θ σ3 (.inl .pe) k s0 s1).regs 1, p, q, s]) : Rec Kd) ∈
    (nx θ σ3 (.inl .pe) k s0 s1).heap := hrec
  have hm4 : (nx θ σ3 (.inl .pe) k s0 s1).mode = .S2 := rfl
  generalize nx θ σ3 (.inl .pe) k s0 s1 = σ4 at *
  generalize decide (z ≠ .nil) = b at hrec4
  refine lstep ok4 hm4 rfl hrec4 (.s2 b) (by cases b <;> rfl) (by simp) (by simp) rfl rfl ?_
  rw [pv_eq h]
  refine (hev (nx θ σ4 (.inl (.s2 b)) p q s) ⟨ok4.nx _ _ _ _, rfl, ⟨z.hd, hp'.mono (heap_nx _ _ _ _ _), rfl⟩,
    hq'.mono (heap_nx _ _ _ _ _)⟩ (fun _ => 1) (fun _ => 1) (Cc supp * τ + 1) ?_).mono (by linarith)
  intro r hr hb
  refine ⟨?_, ?_⟩
  · have e1 : (nx θ σ4 (.inl (.s2 b)) p q s).regs 3 = k := hr4
    have e2 : (nx θ σ4 (.inl (.s2 b)) p q s).inp = [] := (inpA _ _ (by simp) (by simp) _ _ _).trans hi4
    rw [e1, e2]
    exact KS_halt (heap_nx _ _ _ _ _ (hh4 hk)) _
  · have hC := Cc_ge (supp := supp)
    have h9 : (r.cost : ℤ) ≤ τ := by exact_mod_cast (h.2 r hr).2
    have h10 : Cc supp * r.cost ≤ Cc supp * τ := mul_le_mul_of_nonneg_left h9 (by linarith)
    linarith

/-- The first step. -/
theorem start0 {σ : St supp} (ok : OKs σ) (hm : σ.mode = .S0) {S : A} {B : ℤ}
    (h : ∀ (σ' : St supp) (j : ℕ), OKs σ' → σ'.mode = .S1 → σ'.regs 1 = j → ((.HT, ![j, 0, 0, 0]) : Rec Kd) ∈ σ'.heap →
      σ'.inp = σ.inp → Mach.SumTo (UM θ supp) σ' S (B - 1)) : Mach.SumTo (UM θ supp) σ S B := by
  refine zstep ok hm rfl .s0 rfl (by simp) (by simp) rfl rfl ?_
  refine h (nx θ σ (.inl .s0) 0 0 0) (σ.n + 1) (ok.nx _ _ _ _) rfl rfl ?_ (inpA _ _ (by simp) (by simp) _ _ _)
  have h1 : ((.HT, ![σ.n + 1, σ.regs 0, σ.regs 0, σ.regs 0]) : Rec Kd) ∈ (nx θ σ (.inl .s0) 0 0 0).heap :=
    new_nx (θ := θ) σ (.inl .s0) 0 0 0
  rw [ok.r0] at h1
  exact h1

/-- The second step. -/
theorem start1 {σ : St supp} (ok : OKs σ) (hm : σ.mode = .S1) {S : A} {B : ℤ}
    (h : ∀ (σ' : St supp) (j s0 s1 : ℕ), OKs σ' → σ'.mode = .P → σ'.regs 1 = j →
      ((.PE, ![j, σ.regs 1, s0, s1]) : Rec Kd) ∈ σ'.heap → σ.heap ⊆ σ'.heap →
      σ'.inp = σ.inp → Mach.SumTo (UM θ supp) σ' S (B - 1)) : Mach.SumTo (UM θ supp) σ S B := by
  refine zstep ok hm rfl .s1 rfl (by simp) (by simp) rfl rfl ?_
  exact h (nx θ σ (.inl .s1) 0 0 0) (σ.n + 1) (σ.regs 0) (σ.regs 0) (ok.nx _ _ _ _) rfl rfl
    (new_nx (θ := θ) σ (.inl .s1) 0 0 0) (heap_nx _ _ _ _ _) (inpA _ _ (by simp) (by simp) _ _ _)

/-- From the first state. -/
theorem start (hθ : ∀ q, q ∉ supp → θ q = 0) {τ : ℕ} {z : Tree} (h : Plain θ τ z) {σ : St supp} (ok : OKs σ)
    (hm : σ.mode = .S0) (hi : σ.inp = word z) :
    Mach.SumTo (UM θ supp) σ (pv θ z) (3 * z.size + Cc supp * τ + 10) := by
  refine start0 ok hm fun σ1 j ok1 hm1 hr1 hht hi1 => ?_
  refine start1 ok1 hm1 fun σ2 k s0 s1 ok2 hm2 hr2 hpe hh2 hi2 => ?_
  rw [hr1] at hpe
  refine (parse z (Cc supp * τ + 3) σ2 k [] ok2 hm2 hr2 (by rw [hi2, hi1, hi, List.append_nil])
    (PKS_eval hθ h hpe (hh2 hht))).mono (by linarith)

/-- **The universal machine.** -/
theorem sum_machine (hθ : ∀ q, q ∉ supp → θ q = 0) {τ : ℕ} {z : Tree} (h : Plain θ τ z) :
    Mach.SumTo (UM θ supp) (σ0 supp z) (pv θ z) (3 * z.size + Cc supp * τ + 10) :=
  start hθ h (ok_σ0 z) rfl rfl

end Nc.Uni
