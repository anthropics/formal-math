/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Uni.EvalU

/-!
# The universal machine evaluates formulas
-/

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false

namespace Nc.Uni

open Finset NS1

variable {A : Type} [CommRing A] {θ : List Bool → A} {supp : Finset (List Bool)}

section Inv

theorem inv_quote {c c0 : Tree} (h : Fm.ofTree c = .quote c0) :
    (c = .nil ∧ c0 = .nil) ∨ ∃ o, c = .cons o c0 ∧ o.len = 0 := by
  cases c with
  | nil => rw [Fm.ofTree] at h; injection h with h; exact Or.inl ⟨rfl, h.symm⟩
  | cons o a =>
    rw [Fm.ofTree] at h
    split at h <;> first | (exfalso; simp only [reduceCtorEq] at h; done) | skip
    injection h with h
    subst h
    exact Or.inr ⟨o, rfl, by assumption⟩

theorem inv_id {c : Tree} (h : Fm.ofTree c = .id) : ∃ o a, c = .cons o a ∧ o.len = 1 := by
  cases c with
  | nil => rw [Fm.ofTree] at h; cases h
  | cons o a =>
    rw [Fm.ofTree] at h
    split at h <;> first | (exfalso; simp only [reduceCtorEq] at h; done) | skip
    exact ⟨o, a, rfl, by assumption⟩

theorem inv_hd {c : Tree} {a0 : Fm} (h : Fm.ofTree c = .hd a0) :
    ∃ o a, c = .cons o a ∧ o.len = 2 ∧ Fm.ofTree a = a0 := by
  cases c with
  | nil => rw [Fm.ofTree] at h; cases h
  | cons o a =>
    rw [Fm.ofTree] at h
    split at h <;> first | (exfalso; simp only [reduceCtorEq] at h; done) | skip
    injection h with h
    exact ⟨o, a, rfl, by assumption, h⟩

theorem inv_tl {c : Tree} {a0 : Fm} (h : Fm.ofTree c = .tl a0) :
    ∃ o a, c = .cons o a ∧ o.len = 3 ∧ Fm.ofTree a = a0 := by
  cases c with
  | nil => rw [Fm.ofTree] at h; cases h
  | cons o a =>
    rw [Fm.ofTree] at h
    split at h <;> first | (exfalso; simp only [reduceCtorEq] at h; done) | skip
    injection h with h
    exact ⟨o, a, rfl, by assumption, h⟩

theorem inv_cons {c : Tree} {a0 b0 : Fm} (h : Fm.ofTree c = .cons a0 b0) :
    ∃ o a, c = .cons o a ∧ o.len = 4 ∧ Fm.ofTree a.hd = a0 ∧ Fm.ofTree a.tl = b0 := by
  cases c with
  | nil => rw [Fm.ofTree] at h; cases h
  | cons o a =>
    rw [Fm.ofTree] at h
    split at h <;> first | (exfalso; simp only [reduceCtorEq] at h; done) | skip
    injection h with h h'
    exact ⟨o, a, rfl, by assumption, h, h'⟩

theorem inv_ite {c : Tree} {a0 b0 c0 : Fm} (h : Fm.ofTree c = .ite a0 b0 c0) :
    ∃ o a, c = .cons o a ∧ o.len = 5 ∧ Fm.ofTree a.hd = a0 ∧ Fm.ofTree a.tl.hd = b0 ∧ Fm.ofTree a.tl.tl = c0 := by
  cases c with
  | nil => rw [Fm.ofTree] at h; cases h
  | cons o a =>
    rw [Fm.ofTree] at h
    split at h <;> first | (exfalso; simp only [reduceCtorEq] at h; done) | skip
    injection h with h h' h''
    exact ⟨o, a, rfl, by assumption, h, h', h''⟩

theorem inv_run {c : Tree} {a0 b0 : Fm} (h : Fm.ofTree c = .run a0 b0) :
    ∃ o a, c = .cons o a ∧ o.len = 6 ∧ Fm.ofTree a.hd = a0 ∧ Fm.ofTree a.tl = b0 := by
  cases c with
  | nil => rw [Fm.ofTree] at h; cases h
  | cons o a =>
    rw [Fm.ofTree] at h
    split at h <;> first | (exfalso; simp only [reduceCtorEq] at h; done) | skip
    injection h with h h'
    exact ⟨o, a, rfl, by assumption, h, h'⟩

theorem inv_guess {c : Tree} (h : Fm.ofTree c = .guess) : ∃ o a, c = .cons o a ∧ o.len = 7 := by
  cases c with
  | nil => rw [Fm.ofTree] at h; cases h
  | cons o a =>
    rw [Fm.ofTree] at h
    split at h <;> first | (exfalso; simp only [reduceCtorEq] at h; done) | skip
    exact ⟨o, a, rfl, by assumption⟩

theorem inv_fail {c : Tree} (h : Fm.ofTree c = .fail) : ∃ o a, c = .cons o a ∧ (o.len = 8 ∨ 11 ≤ o.len) := by
  cases c with
  | nil => rw [Fm.ofTree] at h; cases h
  | cons o a =>
    refine ⟨o, a, rfl, ?_⟩
    rw [Fm.ofTree] at h
    split at h <;> first | (exfalso; simp only [reduceCtorEq] at h; done) | skip
    · left; assumption
    · right
      by_contra hc
      push Not at hc
      generalize o.len = k at *
      interval_cases k <;> simp_all

theorem inv_theta {c : Tree} {a0 : Fm} (h : Fm.ofTree c = .theta a0) :
    ∃ o a, c = .cons o a ∧ o.len = 9 ∧ Fm.ofTree a = a0 := by
  cases c with
  | nil => rw [Fm.ofTree] at h; cases h
  | cons o a =>
    rw [Fm.ofTree] at h
    split at h <;> first | (exfalso; simp only [reduceCtorEq] at h; done) | skip
    injection h with h
    exact ⟨o, a, rfl, by assumption, h⟩

theorem inv_mul {c : Tree} {a0 : Fm} (h : Fm.ofTree c = .mul a0) : ∃ o a, c = .cons o a ∧ o.len = 10 := by
  cases c with
  | nil => rw [Fm.ofTree] at h; cases h
  | cons o a =>
    rw [Fm.ofTree] at h
    split at h <;> first | (exfalso; simp only [reduceCtorEq] at h; done) | skip
    exact ⟨o, a, rfl, by assumption⟩

end Inv

/-- The sum over the runs without named constants. -/
def tot (m : Run A → A) (l : List (Run A)) : A := (l.map fun r => if r.bill = [] then r.th * m r else 0).sum

theorem tot_nil (m : Run A → A) : tot m [] = 0 := rfl

theorem tot_append (m : Run A → A) (l l' : List (Run A)) : tot m (l ++ l') = tot m l + tot m l' := by simp [tot]

theorem tot_flatMap (m : Run A → A) {ι : Type*} (l : List ι) (f : ι → List (Run A)) :
    tot m (l.flatMap f) = (l.map fun i => tot m (f i)).sum := by
  induction l with
  | nil => rfl
  | cons i l ih => rw [List.flatMap_cons, tot_append, ih, List.map_cons, List.sum_cons]

/-- One run after the other. -/
theorem tot_seq (m : Run A → A) (la : List (Run A)) (L : Run A → List (Run A)) (o : Run A → Run A → Tree) :
    tot m (la.flatMap fun r => (L r).map fun s => (r.seq s).tick (o r s)) =
      tot (fun r => tot (fun s => m ((r.seq s).tick (o r s))) (L r)) la := by
  rw [tot_flatMap]
  unfold tot
  congr 1
  refine List.map_congr_left fun r _ => ?_
  rw [List.map_map]
  by_cases hr : r.bill = []
  · rw [if_pos hr, ← List.sum_map_mul_left]
    congr 1
    refine List.map_congr_left fun s _ => ?_
    simp only [Function.comp, Run.tick, Run.seq, hr, List.nil_append]
    split_ifs
    · ring
    · ring
  · rw [if_neg hr]
    refine List.sum_eq_zero fun y hy => ?_
    rw [List.mem_map] at hy
    obtain ⟨s, -, rfl⟩ := hy
    exact if_neg fun h => hr (List.append_eq_nil_iff.1 h).1

variable (supp) in
/-- Steps of the machine for one step of the evaluation. -/
def Cc : ℤ := 40 + 2 * (Lm supp : ℤ)

theorem Cc_ge : 40 ≤ Cc supp := by
  unfold Cc
  have : (0 : ℤ) ≤ (Lm supp : ℤ) := Int.natCast_nonneg _
  linarith

/-- The machine is about to evaluate the formula F at the tree x. -/
structure ES (σ : St supp) (F : Fm) (x : Tree) : Prop where
  ok : OKs σ
  mode : σ.mode = .E
  fm : ∃ c, Rep σ.heap (σ.regs 1) c ∧ Fm.ofTree c = F
  arg : Rep σ.heap (σ.regs 2) x

variable (θ supp) in
/-- The machine evaluates the formula correctly. -/
def EvOK (F : Fm) (x : Tree) (l : List (Run A)) : Prop :=
  ∀ σ : St supp, ES σ F x → ∀ (m : Run A → A) (Bd : Run A → ℤ) (B : ℤ),
    (∀ r ∈ l, r.bill = [] → KS θ supp σ.heap (σ.regs 3) σ.inp r.out (m r) (Bd r) ∧ Cc supp * r.cost + Bd r ≤ B) →
    Mach.SumTo (UM θ supp) σ (tot m l) B

/-- A step from an opcode. -/
theorem dstep {σ : St supp} (hσ : OKs σ) {c : Fin 11} (hm : σ.mode = .D c) (h1 : σ.regs 1 = 0) (r : Ra)
    (hr : nextR supp (.D c) .N = some (.inl r)) (hc : c ≠ 7) (hs : (ruleA r : RD A (Nm supp)).src = .D c)
    (hk : (ruleA r : RD A (Nm supp)).lk = .N) {S : A} {B : ℤ}
    (h : Mach.SumTo (UM θ supp) (nx θ σ (.inl r) 0 0 0) S (B - 1)) : Mach.SumTo (UM θ supp) σ S B := by
  have hrec : ((.N, ![σ.regs (laM σ.mode), 0, 0, 0]) : Rec Kd) ∈ σ.heap := by
    rw [hm]
    change ((.N, ![σ.regs 1, 0, 0, 0]) : Rec Kd) ∈ σ.heap
    rw [h1]
    exact hσ.nil
  have h2 := sumTo_ruleA hσ hrec r (by rw [hm]; exact hr) (by rw [hm]; simp) (by rw [hm]; simp [hc]) (by rw [hm]; exact hs)
    hk h
  exact h2.mono (by omega)

theorem EvOK.quote (c0 x : Tree) : EvOK θ supp (.quote c0) x [.det 1 c0] := by
  intro σ hσ m Bd B h
  obtain ⟨ok, hm, ⟨c, hc, hF⟩, hx⟩ := hσ
  obtain ⟨hk, hB⟩ := h (.det 1 c0) (by simp) rfl
  have ht : tot m [.det 1 c0] = m (.det 1 c0) := by simp [tot, Run.det]
  rw [ht]
  have hC := Cc_ge (supp := supp)
  have hB' : Cc supp + Bd (.det 1 c0) ≤ B := by
    have : ((Run.det 1 c0 : Run A).cost : ℤ) = 1 := rfl
    rw [this] at hB
    linarith
  rcases inv_quote hF with ⟨rfl, rfl⟩ | ⟨o, rfl, hl⟩
  · have h0 : σ.regs 1 = 0 := hc
    have hrec : ((.N, ![σ.regs (laM σ.mode), 0, 0, 0]) : Rec Kd) ∈ σ.heap := by
      rw [hm]
      change ((.N, ![σ.regs 1, 0, 0, 0]) : Rec Kd) ∈ σ.heap
      rw [h0]
      exact ok.nil
    have h2 := hk (nx θ σ (.inl .en) 0 0 0) 0 (ok.nx _ _ _ _) rfl h0 rfl (heap_nx σ _ _ _ _)
      (inpA σ _ (by simp) (by simp) _ _ _) rfl
    exact (sumTo_ruleA ok hrec .en (by rw [hm]; rfl) (by rw [hm]; simp) (by rw [hm]; simp) (by rw [hm]; rfl) rfl h2).mono
      (by linarith)
  · refine (toOp (B := B - 11) ok hm hc (by omega) fun σ1 ok1 hm1 h11 h12 h13 h14 hh1 hi1 => ?_).mono (by omega)
    have hm1' : σ1.mode = .D 0 := by rw [hm1]; congr 1; exact Fin.ext hl
    refine dstep ok1 hm1' h11 .d0 rfl (by decide) rfl rfl ?_
    refine (hk (nx θ σ1 (.inl .d0) 0 0 0) (σ1.regs 2) (ok1.nx _ _ _ _) rfl rfl h14
      (fun _ h => heap_nx σ1 _ _ _ _ (hh1 h)) ((inpA σ1 _ (by simp) (by simp) _ _ _).trans hi1)
      (h12.mono (heap_nx σ1 _ _ _ _))).mono (by linarith)

theorem EvOK.id (x : Tree) : EvOK θ supp .id x [.det 1 x] := by
  intro σ hσ m Bd B h
  obtain ⟨ok, hm, ⟨c, hc, hF⟩, hx⟩ := hσ
  obtain ⟨hk, hB⟩ := h (.det 1 x) (by simp) rfl
  have ht : tot m [.det 1 x] = m (.det 1 x) := by simp [tot, Run.det]
  rw [ht]
  have hC := Cc_ge (supp := supp)
  have hB' : Cc supp + Bd (.det 1 x) ≤ B := by
    have : ((Run.det 1 x : Run A).cost : ℤ) = 1 := rfl
    rw [this] at hB
    linarith
  obtain ⟨o, a, rfl, hl⟩ := inv_id hF
  refine (toOp (B := B - 11) ok hm hc (by omega) fun σ1 ok1 hm1 h11 h12 h13 h14 hh1 hi1 => ?_).mono (by omega)
  have hm1' : σ1.mode = .D 1 := by rw [hm1]; congr 1; exact Fin.ext hl
  refine dstep ok1 hm1' h11 .d1 rfl (by decide) rfl rfl ?_
  refine (hk (nx θ σ1 (.inl .d1) 0 0 0) (σ1.regs 3) (ok1.nx _ _ _ _) rfl rfl h14
    (fun _ h => heap_nx σ1 _ _ _ _ (hh1 h)) ((inpA σ1 _ (by simp) (by simp) _ _ _).trans hi1) ?_).mono (by linarith)
  rw [h13]
  exact hx.mono fun _ h => heap_nx σ1 _ _ _ _ (hh1 h)

theorem EvOK.fail (x : Tree) : EvOK θ supp .fail x [] := by
  intro σ hσ m Bd B h
  obtain ⟨ok, hm, ⟨c, hc, hF⟩, hx⟩ := hσ
  rw [tot_nil]
  obtain ⟨o, a, rfl, hl | hl⟩ := inv_fail hF
  · refine (toOp (B := B - 11) ok hm hc (by omega) fun σ1 ok1 hm1 h11 h12 h13 h14 hh1 hi1 => ?_).mono (by omega)
    have hm1' : σ1.mode = .D 8 := by rw [hm1]; congr 1; exact Fin.ext hl
    have hrec : ((.N, ![σ1.regs (laM σ1.mode), 0, 0, 0]) : Rec Kd) ∈ σ1.heap := by
      rw [hm1']
      change ((.N, ![σ1.regs 1, 0, 0, 0]) : Rec Kd) ∈ σ1.heap
      rw [h11]
      exact ok1.nil
    exact sumTo_stuck ok1 hrec (by rw [hm1']; rfl) (by rw [hm1']; simp) (by
      rw [hm1']
      rintro ⟨h, -⟩
      injection h with h
      exact absurd h (by decide)) (by rw [hm1']; simp) _
  · exact noOp ok hm hc hl

end Nc.Uni
