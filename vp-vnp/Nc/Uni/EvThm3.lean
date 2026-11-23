/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Uni.EvThm2

/-!
# The universal machine evaluates formulas: the other cases, and the input
-/

set_option linter.unusedSectionVars false

namespace Nc.Uni

open Finset NS1

variable {A : Type} [CommRing A] {θ : List Bool → A} {supp : Finset (List Bool)}

theorem tot_seq3 (m : Run A → A) (la lb : List (Run A)) (L : Run A → Run A → List (Run A)) :
    tot m (la.flatMap fun r => lb.flatMap fun s => (L r s).map fun t => ((r.seq s).seq t).tick t.out) =
      tot (fun r => tot (fun s => tot (fun t => m (((r.seq s).seq t).tick t.out)) (L r s)) lb) la := by
  rw [tot_flatMap]
  unfold tot
  congr 1
  refine List.map_congr_left fun r _ => ?_
  have h1 := tot_flatMap m lb fun s => (L r s).map fun t => ((r.seq s).seq t).tick t.out
  unfold tot at h1
  rw [h1]
  by_cases hr : r.bill = []
  · rw [if_pos hr, ← List.sum_map_mul_left]
    congr 1
    refine List.map_congr_left fun s _ => ?_
    rw [List.map_map]
    by_cases hs : s.bill = []
    · rw [if_pos hs, ← List.sum_map_mul_left, ← List.sum_map_mul_left]
      congr 1
      refine List.map_congr_left fun t _ => ?_
      simp only [Function.comp, Run.tick, Run.seq, hr, hs, List.nil_append]
      split_ifs
      · ring
      · ring
    · rw [if_neg hs, mul_zero]
      refine List.sum_eq_zero fun y hy => ?_
      rw [List.mem_map] at hy
      obtain ⟨t, -, rfl⟩ := hy
      exact if_neg fun h => hs (List.append_eq_nil_iff.1 (List.append_eq_nil_iff.1 h).1).2
  · rw [if_neg hr]
    refine List.sum_eq_zero fun y hy => ?_
    rw [List.mem_map] at hy
    obtain ⟨s, -, rfl⟩ := hy
    refine List.sum_eq_zero fun y hy => ?_
    rw [List.map_map, List.mem_map] at hy
    obtain ⟨t, -, rfl⟩ := hy
    exact if_neg fun h => hr (List.append_eq_nil_iff.1 (List.append_eq_nil_iff.1 h).1).1

theorem EvOK.run {a b : Fm} {x : Tree} {la lb : List (Run A)} {L : Run A → Run A → List (Run A)}
    (iha : EvOK θ supp a x la) (ihb : EvOK θ supp b x lb)
    (ihc : ∀ r ∈ la, ∀ s ∈ lb, EvOK θ supp (Fm.ofTree r.out) s.out (L r s)) :
    EvOK θ supp (.run a b) x (la.flatMap fun r => lb.flatMap fun s => (L r s).map fun t =>
      ((r.seq s).seq t).tick t.out) := by
  intro σ hσ m Bd B h
  obtain ⟨ok, hm, ⟨c, hc, hF⟩, hx⟩ := hσ
  obtain ⟨o, a', rfl, hl, rfl, rfl⟩ := inv_run hF
  have hC := Cc_ge (supp := supp)
  rw [tot_seq3]
  refine (toOp (B := B - 11) ok hm hc (by omega) fun σ1 ok1 hm1 h11 h12 h13 h14 hh1 hi1 => ?_).mono (by omega)
  have hm1' : σ1.mode = .D 6 := by rw [hm1]; congr 1; exact Fin.ext hl
  refine dstep ok1 hm1' h11 .d6 rfl (by decide) rfl rfl ?_
  have ok2 := ok1.nx (θ := θ) (.inl .d6) 0 0 0
  obtain ⟨p, q, s, hrec, hp, hq⟩ := (h12.mono (heap_nx (θ := θ) σ1 (.inl .d6) 0 0 0)).load ok2
  generalize decide (a' ≠ .nil) = bt at hrec
  refine lstep ok2 (md := .K6) rfl rfl hrec (.k6 bt) (by cases bt <;> rfl) (by simp) (by simp) rfl rfl ?_
  set σ2 := nx θ σ1 (.inl .d6) 0 0 0 with hσ2
  have hh2 : σ.heap ⊆ (nx θ σ2 (.inl (.k6 bt)) p q s).heap := fun _ hc => heap_nx _ _ _ _ _ (heap_nx _ _ _ _ _ (hh1 hc))
  have hr2 : σ2.regs 2 = σ.regs 2 := h13
  have hr3 : σ2.regs 3 = σ.regs 3 := h14
  refine iha (nx θ σ2 (.inl (.k6 bt)) p q s) ⟨ok2.nx _ _ _ _, rfl, ⟨a'.hd, hp.mono (heap_nx _ _ _ _ _), rfl⟩, ?_⟩ _
    (fun r => B - Cc supp * r.cost - Cc supp + 2) _ ?_
  · change Rep _ (σ2.regs 2) x
    rw [hr2]
    exact hx.mono hh2
  · intro r hr hb
    refine ⟨fun σ3 v ok3 hm3 h31 h32 hh3 hi3 hv => ?_, by linarith⟩
    have hfr : ((.RU1, ![σ3.regs 2, q, σ2.regs 2, σ2.regs 3]) : Rec Kd) ∈ σ3.heap := by
      rw [h32]
      exact hh3 (new_nx (θ := θ) σ2 (.inl (.k6 bt)) p q s)
    refine rstep ok3 hm3 hfr .rru1 rfl rfl rfl ?_
    subst h31
    have ok4 := ok3.nx (θ := θ) (.inl .rru1) q (σ2.regs 2) (σ2.regs 3)
    set σ4 := nx θ σ3 (.inl .rru1) q (σ2.regs 2) (σ2.regs 3) with hσ4
    have hh4 : σ.heap ⊆ σ4.heap := fun _ hc => heap_nx _ _ _ _ _ (hh3 (hh2 hc))
    refine (ihb σ4 ⟨ok4, rfl, ⟨a'.tl, ?_, rfl⟩, ?_⟩ (fun s => tot (fun t => m (((r.seq s).seq t).tick t.out)) (L r s))
      (fun s => B - Cc supp * r.cost - Cc supp * s.cost - Cc supp + 1) (B - Cc supp * r.cost - Cc supp + 1) ?_).mono
      (by linarith)
    · change Rep σ4.heap q a'.tl
      exact ((hq.mono (heap_nx _ _ _ _ _)).mono hh3).mono (heap_nx _ _ _ _ _)
    · change Rep σ4.heap (σ2.regs 2) x
      rw [hr2]
      exact hx.mono hh4
    · intro s' hs' hb'
      refine ⟨fun σ5 v' ok5 hm5 h51 h52 hh5 hi5 hv' => ?_, by linarith⟩
      have hfr' : ((.RU2, ![σ5.regs 2, σ3.regs 1, σ2.regs 3, σ3.regs 0]) : Rec Kd) ∈ σ5.heap := by
        rw [h52]
        exact hh5 (new_nx (θ := θ) σ3 (.inl .rru1) q (σ2.regs 2) (σ2.regs 3))
      refine rstep ok5 hm5 hfr' .rru2 rfl rfl rfl ?_
      subst h51
      have hh6 : σ.heap ⊆ (nx θ σ5 (.inl .rru2) (σ3.regs 1) (σ2.regs 3) (σ3.regs 0)).heap :=
        fun _ hc => heap_nx _ _ _ _ _ (hh5 (hh4 hc))
      refine (ihc r hr s' hs' (nx θ σ5 (.inl .rru2) (σ3.regs 1) (σ2.regs 3) (σ3.regs 0)) ⟨ok5.nx _ _ _ _, rfl,
        ⟨r.out, ?_, rfl⟩, hv'.mono (heap_nx _ _ _ _ _)⟩ (fun t => m (((r.seq s').seq t).tick t.out))
        (fun t => Bd (((r.seq s').seq t).tick t.out)) (B - Cc supp * r.cost - Cc supp * s'.cost - Cc supp) ?_).mono
        (by linarith)
      · exact ((hv.mono (heap_nx _ _ _ _ _)).mono hh5).mono (heap_nx _ _ _ _ _)
      · intro t ht hbt
        obtain ⟨k1, k2⟩ := h (((r.seq s').seq t).tick t.out)
          (List.mem_flatMap.2 ⟨r, hr, List.mem_flatMap.2 ⟨s', hs', List.mem_map.2 ⟨t, ht, rfl⟩⟩⟩)
          (by simp [Run.tick, Run.seq, hb, hb', hbt])
        rw [cost_tick, cost_seq, cost_seq] at k2
        refine ⟨?_, by linarith⟩
        have e1 : (nx θ σ5 (.inl .rru2) (σ3.regs 1) (σ2.regs 3) (σ3.regs 0)).regs 3 = σ.regs 3 := hr3
        have e2 : (nx θ σ5 (.inl .rru2) (σ3.regs 1) (σ2.regs 3) (σ3.regs 0)).inp = σ.inp := by
          rw [inpA _ _ (by simp) (by simp), hi5, inpA _ _ (by simp) (by simp), hi3, inpA _ _ (by simp) (by simp),
            inpA _ _ (by simp) (by simp), hi1]
        rw [e1, e2]
        exact k1.heap hh6

theorem EvOK.guess (x : Tree) : EvOK θ supp .guess x [.det 1 .nil, .det 1 Tree.one] := by
  intro σ hσ m Bd B h
  obtain ⟨ok, hm, ⟨c, hc, hF⟩, hx⟩ := hσ
  obtain ⟨hk0, hB0⟩ := h (.det 1 .nil) (by simp) rfl
  obtain ⟨hk1, hB1⟩ := h (.det 1 Tree.one) (by simp) rfl
  have ht : tot m [.det 1 .nil, .det 1 Tree.one] = 1 * m (.det 1 .nil) + 1 * m (.det 1 Tree.one) := by
    simp [tot, Run.det]
  rw [ht]
  have hC := Cc_ge (supp := supp)
  have hB0' : Cc supp + Bd (.det 1 .nil) ≤ B := by
    have : ((Run.det 1 .nil : Run A).cost : ℤ) = 1 := rfl
    rw [this] at hB0
    linarith
  have hB1' : Cc supp + Bd (.det 1 Tree.one) ≤ B := by
    have : ((Run.det 1 Tree.one : Run A).cost : ℤ) = 1 := rfl
    rw [this] at hB1
    linarith
  obtain ⟨o, a, rfl, hl⟩ := inv_guess hF
  refine (toOp (B := B - 11) ok hm hc (by omega) fun σ1 ok1 hm1 h11 h12 h13 h14 hh1 hi1 => ?_).mono (by omega)
  have hm1' : σ1.mode = .D 7 := by rw [hm1]; congr 1; exact Fin.ext hl
  have hrec : ((.N, ![σ1.regs (laM σ1.mode), 0, 0, 0]) : Rec Kd) ∈ σ1.heap := by
    rw [hm1']
    change ((.N, ![σ1.regs 1, 0, 0, 0]) : Rec Kd) ∈ σ1.heap
    rw [h11]
    exact ok1.nil
  have hz : σ1.mode ≠ (UM θ supp).mh := by
    rw [hm1']
    change Md.D 7 ≠ .Z
    simp
  have g0 := hk0 (nx θ σ1 (.inl (.d7 false)) 0 0 0) 0 (ok1.nx _ _ _ _) rfl ok1.r0 h14
    (fun _ h => heap_nx σ1 _ _ _ _ (hh1 h)) ((inpA σ1 _ (by simp) (by simp) _ _ _).trans hi1) rfl
  have g1 := hk1 (nx θ σ1 (.inl (.d7 true)) 0 0 0) (σ1.n + 1) (ok1.nx _ _ _ _) rfl rfl h14
    (fun _ h => heap_nx σ1 _ _ _ _ (hh1 h)) ((inpA σ1 _ (by simp) (by simp) _ _ _).trans hi1)
    ⟨σ1.regs 0, σ1.regs 0, σ1.regs 0, new_nx (θ := θ) σ1 (.inl (.d7 true)) 0 0 0, ok1.r0, ok1.r0⟩
  have hfire : ∀ st' : (UM θ supp).Step, Mach.Fire σ1 st' ↔ st' = (.inl (.d7 false), envOf σ1 0 0 0) ∨
      st' = (.inl (.d7 true), envOf σ1 0 0 0) := by
    intro st'
    rw [fire_iff ok1 hrec, hm1']
    constructor
    · rintro ⟨h1, h2, -, h4⟩
      have h5 : ∃ b, st'.1 = .inl (.d7 b) := by
        by_contra hne
        have hsp : ¬ Sp st'.1 := by
          rintro (e | e | e)
          · rw [e] at h1; exact absurd h1 (by simp [rule, ruleA, rl])
          · rw [e] at h1; exact absurd h1 (by simp [rule, ruleA, rl])
          · exact hne e
        have h6 := nextR_of (θ := θ) st'.1 hsp
        rw [h1, h2] at h6
        exact absurd h6 (by simp [nextR])
      obtain ⟨b, hb⟩ := h5
      cases b
      · exact Or.inl (Prod.ext hb h4)
      · exact Or.inr (Prod.ext hb h4)
    · rintro (rfl | rfl)
      · exact ⟨rfl, rfl, List.nil_prefix, rfl⟩
      · exact ⟨rfl, rfl, List.nil_prefix, rfl⟩
  have h9 := Mach.SumTo.two hz _ _ (fun e => by
    have h8 : (Sum.inl (Ra.d7 false) : Ru supp) = Sum.inl (Ra.d7 true) := congrArg Prod.fst e
    exact absurd h8 (by simp)) hfire (g0.mono (B' := B - 12) (by linarith)) (g1.mono (B' := B - 12) (by linarith))
  exact h9.mono (by omega)

theorem EvOK.mul {a : Fm} {x : Tree} {l : List (Run A)} :
    EvOK θ supp (.mul a) x (l.map fun r => ⟨r.cost + 1, r.th, r.bill ++ [r.out.path], .nil⟩) := by
  intro σ hσ m Bd B h
  obtain ⟨ok, hm, ⟨c, hc, hF⟩, hx⟩ := hσ
  have ht : tot m (l.map fun r => (⟨r.cost + 1, r.th, r.bill ++ [r.out.path], .nil⟩ : Run A)) = 0 := by
    unfold tot
    refine List.sum_eq_zero fun y hy => ?_
    rw [List.map_map, List.mem_map] at hy
    obtain ⟨r, -, rfl⟩ := hy
    simp
  rw [ht]
  obtain ⟨o, a', rfl, hl⟩ := inv_mul hF
  refine (toOp (B := B - 11) ok hm hc (by omega) fun σ1 ok1 hm1 h11 h12 h13 h14 hh1 hi1 => ?_).mono (by omega)
  have hm1' : σ1.mode = .D 10 := by rw [hm1]; congr 1; exact Fin.ext hl
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

theorem EvOK.theta (hθ : ∀ q, q ∉ supp → θ q = 0) {a : Fm} {x : Tree} {l : List (Run A)} (ih : EvOK θ supp a x l) :
    EvOK θ supp (.theta a) x (l.map fun r => ⟨r.cost + 1, r.th * θ r.out.path, r.bill, .nil⟩) := by
  intro σ hσ m Bd B h
  obtain ⟨ok, hm, ⟨c, hc, hF⟩, hx⟩ := hσ
  obtain ⟨o, a', rfl, hl, rfl⟩ := inv_theta hF
  have hC := Cc_ge (supp := supp)
  let f : Run A → Run A := fun r => ⟨r.cost + 1, r.th * θ r.out.path, r.bill, .nil⟩
  have ht : tot m (l.map f) = tot (fun r => θ r.out.path * m (f r)) l := by
    unfold tot
    rw [List.map_map]
    congr 1
    refine List.map_congr_left fun r _ => ?_
    simp only [Function.comp, f]
    split_ifs
    · ring
    · rfl
  change Mach.SumTo (UM θ supp) σ (tot m (l.map f)) B
  rw [ht]
  refine (toOp (B := B - 11) ok hm hc (by omega) fun σ1 ok1 hm1 h11 h12 h13 h14 hh1 hi1 => ?_).mono (by omega)
  have hm1' : σ1.mode = .D 9 := by rw [hm1]; congr 1; exact Fin.ext hl
  refine dstep ok1 hm1' h11 .d9 rfl (by decide) rfl rfl ?_
  have hh2 : σ.heap ⊆ (nx θ σ1 (.inl .d9) 0 0 0).heap := fun _ hc => heap_nx σ1 _ _ _ _ (hh1 hc)
  refine ih (nx θ σ1 (.inl .d9) 0 0 0) ⟨ok1.nx _ _ _ _, rfl, ⟨a', h12.mono (heap_nx σ1 _ _ _ _), rfl⟩, ?_⟩ _
    (fun r => Bd (f r) + 2 + 2 * (Lm supp : ℤ)) _ ?_
  · change Rep _ (σ1.regs 3) x
    rw [h13]
    exact hx.mono hh2
  · intro r hr hb
    obtain ⟨k1, k2⟩ := h (f r) (List.mem_map.2 ⟨r, hr, rfl⟩) hb
    have hcost : ((f r).cost : ℤ) = r.cost + 1 := by simp [f]
    rw [hcost] at k2
    refine ⟨fun σ3 v ok3 hm3 h31 h32 hh3 hi3 hv => ?_, by unfold Cc at *; linarith⟩
    have hfr : ((.TH, ![σ3.regs (laM σ3.mode), σ1.regs 4, σ1.regs 0, σ1.regs 0]) : Rec Kd) ∈ σ3.heap := by
      rw [hm3]
      change ((.TH, ![σ3.regs 2, σ1.regs 4, σ1.regs 0, σ1.regs 0]) : Rec Kd) ∈ σ3.heap
      rw [h32]
      exact hh3 (new_nx (θ := θ) σ1 (.inl .d9) 0 0 0)
    by_cases hp : ([] : List Bool) ∈ pre supp
    · have ok4 := ok3.nx (θ := θ) (.inr (.inl ⟨(), hp⟩)) (σ1.regs 4) (σ1.regs 0) (σ1.regs 0)
      have h4 := readName (θ := θ) hθ (S := m (f r)) (B := Bd (f r)) r.out ⟨[], hp⟩
        (nx θ σ3 (.inr (.inl ⟨(), hp⟩)) (σ1.regs 4) (σ1.regs 0) (σ1.regs 0)) ok4 rfl ?_ ?_
      · have h5 := sumTo_rule ok3 hfr (.inr (.inl ⟨(), hp⟩)) (by rw [hm3]; exact dif_pos hp) (by rw [hm3]; simp)
          (by rw [hm3]; simp) (by rw [hm3]; rfl) rfl h4
        have hw : (rule θ supp (.inr (.inl ⟨(), hp⟩))).wt = 1 := rfl
        rw [hw, one_mul] at h5
        refine h5.mono ?_
        simp only [List.length_nil, Nat.sub_zero]
        linarith
      · change Rep _ (σ3.regs 1) r.out
        rw [h31]
        exact hv.mono (heap_nx _ _ _ _ _)
      · have e1 : (nx θ σ3 (.inr (.inl ⟨(), hp⟩)) (σ1.regs 4) (σ1.regs 0) (σ1.regs 0)).regs 2 = σ.regs 3 := h14
        have e2 : (nx θ σ3 (.inr (.inl ⟨(), hp⟩)) (σ1.regs 4) (σ1.regs 0) (σ1.regs 0)).inp = σ.inp := by
          have e3 : (nx θ σ3 (.inr (.inl ⟨(), hp⟩)) (σ1.regs 4) (σ1.regs 0) (σ1.regs 0)).inp = σ3.inp := rfl
          rw [e3, hi3, inpA _ _ (by simp) (by simp), hi1]
        rw [e1, e2]
        exact k1.heap fun _ hc => heap_nx _ _ _ _ _ (hh3 (hh2 hc))
    · have hz : θ r.out.path = 0 := by
        have := not_pre hp hθ r.out.path
        simpa using this
      rw [hz, zero_mul]
      exact sumTo_stuck ok3 hfr (by rw [hm3]; exact dif_neg hp) (by rw [hm3]; simp) (by rw [hm3]; simp)
        (by rw [hm3]; simp) _

/-- **The machine evaluates all formulas.** -/
theorem evOK (hθ : ∀ q, q ∉ supp → θ q = 0) {F : Fm} {x : Tree} {l : List (Run A)} (h : Ev θ F x l) : EvOK θ supp F x l := by
  induction h with
  | quote c x => exact EvOK.quote c x
  | id x => exact EvOK.id x
  | hd _ ih => exact EvOK.hd ih
  | tl _ ih => exact EvOK.tl ih
  | cons _ _ iha ihb => exact EvOK.cons iha ihb
  | ite _ _ _ iha ihb ihc => exact EvOK.ite iha ihb ihc
  | run _ _ _ iha ihb ih => exact EvOK.run iha ihb ih
  | guess x => exact EvOK.guess x
  | fail x => exact EvOK.fail x
  | theta _ ih => exact EvOK.theta hθ ih
  | mul _ _ => exact EvOK.mul

end Nc.Uni
