/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Uni.Det

/-!
# Trees in the heap, opcodes, names
-/

set_option linter.unusedSectionVars false

namespace Nc.Uni

open Finset NS1

variable {A : Type} [CommRing A] {θ : List Bool → A} {supp : Finset (List Bool)}

/-- The address a represents the tree. -/
def Rep (H : List (Rec Kd)) : ℕ → Tree → Prop
  | a, .nil => a = 0
  | a, .cons t1 t2 => ∃ p q s, ((.C, ![a, p, q, s]) : Rec Kd) ∈ H ∧ Rep H p t1 ∧ Rep H q t2

theorem Rep.mono {H H' : List (Rec Kd)} (hH : H ⊆ H') {a : ℕ} {t : Tree} (h : Rep H a t) : Rep H' a t := by
  induction t generalizing a with
  | nil => exact h
  | cons t1 t2 ih1 ih2 =>
    obtain ⟨p, q, s, h1, h2, h3⟩ := h
    exact ⟨p, q, s, hH h1, ih1 h2, ih2 h3⟩

/-- The record at an address that represents a tree. -/
theorem Rep.load {σ : St supp} (hσ : OKs σ) {a : ℕ} {t : Tree} (h : Rep σ.heap a t) :
    ∃ p q s, ((kb (decide (t ≠ .nil)), ![a, p, q, s]) : Rec Kd) ∈ σ.heap ∧ Rep σ.heap p t.hd ∧ Rep σ.heap q t.tl := by
  cases t with
  | nil =>
    have h0 : a = 0 := h
    subst h0
    exact ⟨0, 0, 0, hσ.nil, rfl, rfl⟩
  | cons t1 t2 =>
    obtain ⟨p, q, s, h1, h2, h3⟩ := h
    exact ⟨p, q, s, h1, h2, h3⟩

/-- What happens when the value o is returned to the frame k. -/
def KS (θ : List Bool → A) (supp : Finset (List Bool)) (H : List (Rec Kd)) (k : ℕ) (inp : List Bool) (o : Tree) (S : A)
    (B : ℤ) : Prop :=
  ∀ (σ : St supp) (v : ℕ), OKs σ → σ.mode = .R → σ.regs 1 = v → σ.regs 2 = k → H ⊆ σ.heap → σ.inp = inp →
    Rep σ.heap v o → Mach.SumTo (UM θ supp) σ S B

theorem KS.heap {H H' : List (Rec Kd)} (hH : H ⊆ H') {k : ℕ} {inp : List Bool} {o : Tree} {S : A} {B : ℤ}
    (h : KS θ supp H k inp o S B) : KS θ supp H' k inp o S B :=
  fun σ v h1 h2 h3 h4 h5 h6 h7 => h σ v h1 h2 h3 h4 (fun _ hc => h5 (hH hc)) h6 h7

theorem wtA (r : Ra) : (ruleA r : RD A (Nm supp)).wt = 1 := by
  cases r with
  | d7 b => cases b <;> rfl
  | _ => rfl

/-- A forced step with a rule without names. -/
theorem sumTo_ruleA {σ : St supp} (hσ : OKs σ) {κ : Kd} {p q s : ℕ}
    (hrec : (κ, ![σ.regs (laM σ.mode), p, q, s]) ∈ σ.heap) (r : Ra) (hr : nextR supp σ.mode κ = some (.inl r))
    (hm : σ.mode ≠ .P) (hd : ¬ (σ.mode = .D 7 ∧ κ = .N)) (hs : (ruleA r : RD A (Nm supp)).src = σ.mode)
    (hk : (ruleA r : RD A (Nm supp)).lk = κ)
    {S : A} {B : ℤ} (h : Mach.SumTo (UM θ supp) (nx θ σ (.inl r) p q s) S B) :
    Mach.SumTo (UM θ supp) σ S (B + 1) := by
  have h1 := sumTo_rule hσ hrec (.inl r) hr hm hd hs hk h
  have h2 : (rule θ supp (.inl r)).wt = 1 := wtA r
  rw [h2, one_mul] at h1
  exact h1

theorem rdA (r : Ra) (h : r ≠ .pr0) (h' : r ≠ .pr1) : (rule θ supp (.inl r)).rd = none := by
  cases r with
  | pr0 => exact absurd rfl h
  | pr1 => exact absurd rfl h'
  | d7 b => cases b <;> rfl
  | _ => rfl

theorem inpA (σ : St supp) (r : Ra) (h : r ≠ .pr0) (h' : r ≠ .pr1) (p q s : ℕ) : (nx θ σ (.inl r) p q s).inp = σ.inp := by
  rw [inp_nx, rdA r h h']
  rfl

/-- Reading the number of an opcode. -/
theorem dchain {S : A} {B : ℤ} (o : Tree) : ∀ (j : ℕ) (hj : j < 11) (σ : St supp) (po : ℕ), OKs σ → σ.mode = .D ⟨j, hj⟩ →
    σ.regs 1 = po → Rep σ.heap po o → ∀ (hl : j + o.len < 11),
    (∀ σ' : St supp, OKs σ' → σ'.mode = .D ⟨j + o.len, hl⟩ → σ'.regs 1 = 0 → σ'.regs 2 = σ.regs 2 →
      σ'.regs 3 = σ.regs 3 → σ'.regs 4 = σ.regs 4 → σ.heap ⊆ σ'.heap → σ'.inp = σ.inp → Mach.SumTo (UM θ supp) σ' S B) →
    Mach.SumTo (UM θ supp) σ S (B + o.len) := by
  induction o with
  | nil =>
    intro j hj σ po hσ hm h1 hr hl h
    have h0 : po = 0 := hr
    subst h0
    have := h σ hσ hm h1 rfl rfl rfl (fun _ hc => hc) rfl
    simpa [Tree.len] using this
  | cons a b _ ih =>
    intro j hj σ po hσ hm h1 hr hl h
    obtain ⟨p, q, s, hrec, -, hq⟩ := hr
    have hl' : j + 1 + b.len < 11 := by
      simp only [Tree.len] at hl
      omega
    have hj' : j < 10 := by omega
    have hrec' : ((.C, ![σ.regs (laM σ.mode), p, q, s]) : Rec Kd) ∈ σ.heap := by
      rw [hm]
      change ((.C, ![σ.regs 1, p, q, s]) : Rec Kd) ∈ σ.heap
      rw [h1]
      exact hrec
    have h2 := ih (j + 1) (by omega) (nx θ σ (.inl (.dc ⟨j, hj'⟩)) p q s) q (hσ.nx _ _ _ _) rfl rfl
      (hq.mono (heap_nx σ _ _ _ _)) hl' (fun σ' a1 a2 a3 a4 a5 a6 a7 a8 => h σ' a1 (by
        rw [a2]
        congr 2
        simp only [Tree.len]
        omega) a3 (a4.trans rfl) (a5.trans rfl) (a6.trans rfl) (fun _ hc => a7 (heap_nx σ _ _ _ _ hc))
        (a8.trans (inpA σ _ (by simp) (by simp) _ _ _)))
    have h3 := sumTo_ruleA hσ hrec' (.dc ⟨j, hj'⟩) (by rw [hm]; exact dif_pos hj') (by rw [hm]; simp) (by simp)
      (by rw [hm]; rfl) rfl h2
    refine h3.mono ?_
    simp only [Tree.len]
    push_cast
    omega

/-- Numbers that are no opcodes. -/
theorem dstuck {B : ℤ} (o : Tree) : ∀ (j : ℕ) (hj : j < 11) (σ : St supp) (po : ℕ), OKs σ → σ.mode = .D ⟨j, hj⟩ →
    σ.regs 1 = po → Rep σ.heap po o → 11 ≤ j + o.len → Mach.SumTo (UM θ supp) σ 0 B := by
  induction o generalizing B with
  | nil =>
    intro j hj σ po hσ hm h1 hr hl
    simp only [Tree.len] at hl
    omega
  | cons a b _ ih =>
    intro j hj σ po hσ hm h1 hr hl
    obtain ⟨p, q, s, hrec, -, hq⟩ := hr
    simp only [Tree.len] at hl
    have hrec' : ((.C, ![σ.regs (laM σ.mode), p, q, s]) : Rec Kd) ∈ σ.heap := by
      rw [hm]
      change ((.C, ![σ.regs 1, p, q, s]) : Rec Kd) ∈ σ.heap
      rw [h1]
      exact hrec
    by_cases hj' : j < 10
    · have h2 := ih (B := B - 1) (j + 1) (by omega) (nx θ σ (.inl (.dc ⟨j, hj'⟩)) p q s) q (hσ.nx _ _ _ _) rfl rfl
        (hq.mono (heap_nx σ _ _ _ _)) (by omega)
      have h3 := sumTo_ruleA hσ hrec' (.dc ⟨j, hj'⟩) (by rw [hm]; exact dif_pos hj') (by rw [hm]; simp) (by simp)
        (by rw [hm]; rfl) rfl h2
      exact h3.mono (by omega)
    · refine sumTo_stuck hσ hrec' ?_ (by rw [hm]; simp) (by simp) (by rw [hm]; simp) B
      rw [hm]
      exact dif_neg hj'

/-- From a formula to its opcode. -/
theorem toOp {S : A} {B : ℤ} {σ : St supp} (hσ : OKs σ) (hm : σ.mode = .E) {o a : Tree}
    (hr : Rep σ.heap (σ.regs 1) (.cons o a)) (hl : o.len < 11)
    (h : ∀ σ' : St supp, OKs σ' → σ'.mode = .D ⟨o.len, hl⟩ → σ'.regs 1 = 0 → Rep σ'.heap (σ'.regs 2) a →
      σ'.regs 3 = σ.regs 2 → σ'.regs 4 = σ.regs 3 → σ.heap ⊆ σ'.heap → σ'.inp = σ.inp →
      Mach.SumTo (UM θ supp) σ' S B) : Mach.SumTo (UM θ supp) σ S (B + 11) := by
  obtain ⟨p, q, s, hrec, hp, hq⟩ := hr
  have hrec' : ((.C, ![σ.regs (laM σ.mode), p, q, s]) : Rec Kd) ∈ σ.heap := by
    rw [hm]
    exact hrec
  have h2 := dchain (θ := θ) (S := S) (B := B) o 0 (by omega) (nx θ σ (.inl .ec) p q s) p (hσ.nx _ _ _ _) rfl rfl
    (hp.mono (heap_nx σ _ _ _ _)) (by omega) (fun σ' a1 a2 a3 a4 a5 a6 a7 a8 => by
      refine h σ' a1 (by rw [a2]; congr 2; omega) a3 ?_ (a5.trans rfl) (a6.trans rfl)
        (fun _ hc => a7 (heap_nx σ _ _ _ _ hc)) (a8.trans (inpA σ _ (by simp) (by simp) _ _ _))
      rw [a4]
      exact (hq.mono (heap_nx σ _ _ _ _)).mono a7)
  have h3 := sumTo_ruleA hσ hrec' .ec (by rw [hm]; rfl) (by rw [hm]; simp) (by simp) (by rw [hm]; rfl) rfl h2
  refine h3.mono ?_
  have : (o.len : ℤ) ≤ 10 := by exact_mod_cast Nat.le_of_lt_succ hl
  linarith

theorem noOp {B : ℤ} {σ : St supp} (hσ : OKs σ) (hm : σ.mode = .E) {o a : Tree}
    (hr : Rep σ.heap (σ.regs 1) (.cons o a)) (hl : 11 ≤ o.len) : Mach.SumTo (UM θ supp) σ 0 B := by
  obtain ⟨p, q, s, hrec, hp, hq⟩ := hr
  have hrec' : ((.C, ![σ.regs (laM σ.mode), p, q, s]) : Rec Kd) ∈ σ.heap := by
    rw [hm]
    exact hrec
  have h2 := dstuck (θ := θ) (B := B - 1) o 0 (by omega) (nx θ σ (.inl .ec) p q s) p (hσ.nx _ _ _ _) rfl rfl
    (hp.mono (heap_nx σ _ _ _ _)) (by omega)
  have h3 := sumTo_ruleA hσ hrec' .ec (by rw [hm]; rfl) (by rw [hm]; simp) (by simp) (by rw [hm]; rfl) rfl h2
  exact h3.mono (by omega)

/-- The bound for the lengths of names. -/
def Lm (supp : Finset (List Bool)) : ℕ := supp.sup List.length

theorem length_pre {p : List Bool} (hp : p ∈ pre supp) : p.length ≤ Lm supp := by
  obtain ⟨q, hq, h⟩ := mem_pre.1 hp
  exact h.length_le.trans (Finset.le_sup (f := List.length) hq)

theorem not_pre {p : List Bool} (hp : p ∉ pre supp) (hθ : ∀ q, q ∉ supp → θ q = 0) (w : List Bool) : θ (p ++ w) = 0 := by
  refine hθ _ fun h => hp (mem_pre.2 ⟨_, h, List.prefix_append _ _⟩)

/-- Reading a name. -/
theorem readName (hθ : ∀ q, q ∉ supp → θ q = 0) {S : A} {B : ℤ} (w : Tree) : ∀ (p : Nm supp) (σ : St supp), OKs σ →
    σ.mode = .TH p → Rep σ.heap (σ.regs 1) w → KS θ supp σ.heap (σ.regs 2) σ.inp .nil S B →
    Mach.SumTo (UM θ supp) σ (θ (p.1 ++ w.path) * S) (B + 1 + 2 * (Lm supp - p.1.length : ℕ)) := by
  induction w with
  | nil =>
    intro p σ hσ hm hr hk
    have h0 : σ.regs 1 = 0 := hr
    have hrec' : ((.N, ![σ.regs (laM σ.mode), 0, 0, 0]) : Rec Kd) ∈ σ.heap := by
      rw [hm]
      change ((.N, ![σ.regs 1, 0, 0, 0]) : Rec Kd) ∈ σ.heap
      rw [h0]
      exact hσ.nil
    have h2 := hk (nx θ σ (.inr (.inr (.inl p))) 0 0 0) 0 (hσ.nx _ _ _ _) rfl hσ.r0 rfl (heap_nx σ _ _ _ _) rfl rfl
    have h3 := sumTo_rule hσ hrec' (.inr (.inr (.inl p))) (by rw [hm]; rfl) (by rw [hm]; simp) (by rw [hm]; simp)
      (by rw [hm]; rfl) rfl h2
    have hw : (rule θ supp (.inr (.inr (.inl p)))).wt = θ p.1 := rfl
    rw [hw] at h3
    simp only [Tree.path, List.append_nil]
    refine h3.mono ?_
    have : (0 : ℤ) ≤ ((Lm supp - p.1.length : ℕ) : ℤ) := Int.natCast_nonneg _
    linarith
  | cons a b _ ih =>
    intro p σ hσ hm hr hk
    obtain ⟨pa, pb, s, hrec, ha, hb⟩ := hr
    have hrec' : ((.C, ![σ.regs (laM σ.mode), pa, pb, s]) : Rec Kd) ∈ σ.heap := by
      rw [hm]
      exact hrec
    let σ1 := nx θ σ (.inr (.inr (.inr (.inl p)))) pa pb s
    have hσ1 : OKs σ1 := hσ.nx _ _ _ _
    have ha1 : Rep σ1.heap pa a := ha.mono (heap_nx σ _ _ _ _)
    have hb1 : Rep σ1.heap pb b := hb.mono (heap_nx σ _ _ _ _)
    obtain ⟨x1, x2, x3, hx, -, -⟩ := ha1.load hσ1
    have hrec1 : ((kb (decide (a ≠ .nil)), ![σ1.regs (laM σ1.mode), x1, x2, x3]) : Rec Kd) ∈ σ1.heap := hx
    have hpath : (Tree.cons a b).path = decide (a ≠ .nil) :: b.path := rfl
    rw [hpath]
    have key : Mach.SumTo (UM θ supp) σ1 (θ (p.1 ++ decide (a ≠ .nil) :: b.path) * S)
        (B + 2 * (Lm supp - p.1.length : ℕ)) := by
      generalize decide (a ≠ .nil) = bt at hrec1 ⊢
      have hsplit : p.1 ++ bt :: b.path = (p.1 ++ [bt]) ++ b.path := by simp
      by_cases hp : p.1 ++ [bt] ∈ pre supp
      · have hnext : nextR supp σ1.mode (kb bt) = some (.inr (.inr (.inr (.inr ⟨(p, ⟨_, hp⟩, bt), rfl⟩)))) := by
          change nextR supp (.TB p) (kb bt) = _
          cases bt
          · exact dif_pos hp
          · exact dif_pos hp
        have h2 := ih ⟨_, hp⟩ (nx θ σ1 (.inr (.inr (.inr (.inr ⟨(p, ⟨_, hp⟩, bt), rfl⟩)))) x1 x2 x3) (hσ1.nx _ _ _ _) rfl
          (hb1.mono (heap_nx σ1 _ _ _ _)) (KS.heap (fun _ hc => heap_nx σ1 _ _ _ _ (heap_nx σ _ _ _ _ hc)) hk)
        have h3 := sumTo_rule hσ1 hrec1 _ hnext (by change Md.TB p ≠ .P; simp)
          (by rintro ⟨h, -⟩; exact absurd h (by change Md.TB p ≠ .D 7; simp)) rfl rfl h2
        have hw : (rule θ supp (.inr (.inr (.inr (.inr ⟨(p, ⟨_, hp⟩, bt), rfl⟩))))).wt = 1 := rfl
        rw [hw, one_mul] at h3
        rw [hsplit]
        refine h3.mono ?_
        have h5 := length_pre hp
        simp only [List.length_append, List.length_singleton] at h5 ⊢
        have h6 : ((Lm supp - p.1.length : ℕ) : ℤ) = ((Lm supp - (p.1.length + 1) : ℕ) : ℤ) + 1 := by
          have : Lm supp - p.1.length = Lm supp - (p.1.length + 1) + 1 := by omega
          rw [this]
          push_cast
          ring
        rw [h6]
        linarith
      · have hz : θ (p.1 ++ bt :: b.path) = 0 := by rw [hsplit]; exact not_pre hp hθ _
        rw [hz, zero_mul]
        refine sumTo_stuck hσ1 hrec1 ?_ (by change Md.TB p ≠ .P; simp)
          (by rintro ⟨h, -⟩; exact absurd h (by change Md.TB p ≠ .D 7; simp)) (by change Md.TB p ≠ .Z; simp) _
        change nextR supp (.TB p) (kb bt) = none
        cases bt
        · exact dif_neg hp
        · exact dif_neg hp
    have h3 := sumTo_rule hσ hrec' (.inr (.inr (.inr (.inl p)))) (by rw [hm]; rfl) (by rw [hm]; simp) (by simp)
      (by rw [hm]; rfl) rfl key
    have hw : (rule θ supp (.inr (.inr (.inr (.inl p))))).wt = 1 := rfl
    rw [hw, one_mul] at h3
    exact h3.mono (by linarith)

end Nc.Uni
