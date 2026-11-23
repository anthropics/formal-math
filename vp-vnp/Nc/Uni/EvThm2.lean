/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Uni.EvThm

/-!
# The universal machine evaluates formulas: the cases with subformulas
-/

set_option linter.unusedSectionVars false

namespace Nc.Uni

open Finset NS1

variable {A : Type} [CommRing A] {θ : List Bool → A} {supp : Finset (List Bool)}

theorem tot_map (m : Run A → A) (l : List (Run A)) (f : Run A → Tree) :
    tot m (l.map fun r => r.tick (f r)) = tot (fun r => m (r.tick (f r))) l := by
  unfold tot
  rw [List.map_map]
  rfl

/-- A step from a returned value; the frame is in the heap. -/
theorem rstep {σ : St supp} (hσ : OKs σ) (hm : σ.mode = .R) {κ : Kd} {p q s : ℕ}
    (hrec : ((κ, ![σ.regs 2, p, q, s]) : Rec Kd) ∈ σ.heap) (r : Ra) (hr : nextR supp .R κ = some (.inl r))
    (hs : (ruleA r : RD A (Nm supp)).src = .R) (hk : (ruleA r : RD A (Nm supp)).lk = κ) {S : A} {B : ℤ}
    (h : Mach.SumTo (UM θ supp) (nx θ σ (.inl r) p q s) S (B - 1)) : Mach.SumTo (UM θ supp) σ S B := by
  have hrec' : ((κ, ![σ.regs (laM σ.mode), p, q, s]) : Rec Kd) ∈ σ.heap := by
    rw [hm]
    exact hrec
  exact (sumTo_ruleA hσ hrec' r (by rw [hm]; exact hr) (by rw [hm]; simp) (by rw [hm]; simp) (by rw [hm]; exact hs) hk
    h).mono (by omega)

/-- A step that loads the record of register 1. -/
theorem lstep {σ : St supp} (hσ : OKs σ) {md : Md (Nm supp)} (hm : σ.mode = md) (hla : laM md = 1) {κ : Kd} {p q s : ℕ}
    (hrec : ((κ, ![σ.regs 1, p, q, s]) : Rec Kd) ∈ σ.heap) (r : Ra) (hr : nextR supp md κ = some (.inl r))
    (hP : md ≠ .P) (hD : md ≠ .D 7) (hs : (ruleA r : RD A (Nm supp)).src = md)
    (hk : (ruleA r : RD A (Nm supp)).lk = κ) {S : A} {B : ℤ}
    (h : Mach.SumTo (UM θ supp) (nx θ σ (.inl r) p q s) S (B - 1)) : Mach.SumTo (UM θ supp) σ S B := by
  have hrec' : ((κ, ![σ.regs (laM σ.mode), p, q, s]) : Rec Kd) ∈ σ.heap := by
    rw [hm, hla]
    exact hrec
  exact (sumTo_ruleA hσ hrec' r (by rw [hm]; exact hr) (by rw [hm]; exact hP) (by rw [hm]; exact fun e => hD e.1)
    (by rw [hm]; exact hs) hk h).mono (by omega)

theorem cost_tick (r : Run A) (o : Tree) : ((r.tick o).cost : ℤ) = r.cost + 1 := by
  simp [Run.tick]

theorem cost_seq (r s : Run A) : ((r.seq s).cost : ℤ) = r.cost + s.cost := by
  simp [Run.seq]

theorem EvOK.hd {a : Fm} {x : Tree} {l : List (Run A)} (ih : EvOK θ supp a x l) :
    EvOK θ supp (.hd a) x (l.map fun r => r.tick r.out.hd) := by
  intro σ hσ m Bd B h
  obtain ⟨ok, hm, ⟨c, hc, hF⟩, hx⟩ := hσ
  obtain ⟨o, a', rfl, hl, rfl⟩ := inv_hd hF
  have hC := Cc_ge (supp := supp)
  rw [tot_map]
  refine (toOp (B := B - 11) ok hm hc (by omega) fun σ1 ok1 hm1 h11 h12 h13 h14 hh1 hi1 => ?_).mono (by omega)
  have hm1' : σ1.mode = .D 2 := by rw [hm1]; congr 1; exact Fin.ext hl
  refine dstep ok1 hm1' h11 .d2 rfl (by decide) rfl rfl ?_
  have hh2 : σ.heap ⊆ (nx θ σ1 (.inl .d2) 0 0 0).heap := fun _ hc => heap_nx σ1 _ _ _ _ (hh1 hc)
  refine ih (nx θ σ1 (.inl .d2) 0 0 0) ⟨ok1.nx _ _ _ _, rfl, ⟨a', h12.mono (heap_nx σ1 _ _ _ _), rfl⟩, ?_⟩ _
    (fun r => Bd (r.tick r.out.hd) + 2) _ ?_
  · change Rep _ (σ1.regs 3) x
    rw [h13]
    exact hx.mono hh2
  · intro r hr hb
    obtain ⟨k1, k2⟩ := h (r.tick r.out.hd) (List.mem_map.2 ⟨r, hr, rfl⟩) hb
    rw [cost_tick] at k2
    refine ⟨fun σ3 v ok3 hm3 h31 h32 hh3 hi3 hv => ?_, by linarith⟩
    have hfr : ((.HD, ![σ3.regs 2, σ1.regs 4, σ1.regs 0, σ1.regs 0]) : Rec Kd) ∈ σ3.heap := by
      rw [h32]
      exact hh3 (new_nx (θ := θ) σ1 (.inl .d2) 0 0 0)
    refine rstep ok3 hm3 hfr .rhd rfl rfl rfl ?_
    have ok4 := ok3.nx (θ := θ) (.inl .rhd) (σ1.regs 4) (σ1.regs 0) (σ1.regs 0)
    subst h31
    obtain ⟨p, q, s, hrec, hp, hq⟩ := (hv.mono (heap_nx (θ := θ) σ3 (.inl .rhd) (σ1.regs 4) (σ1.regs 0) (σ1.regs 0))).load ok4
    generalize decide (r.out ≠ .nil) = b at hrec
    refine lstep ok4 (md := .H) rfl rfl hrec (.h b) (by cases b <;> rfl) (by simp) (by simp) rfl rfl ?_
    refine (k1 (nx θ (nx θ σ3 (.inl .rhd) (σ1.regs 4) (σ1.regs 0) (σ1.regs 0)) (.inl (.h b)) p q s) p
      (ok4.nx _ _ _ _) rfl rfl h14 (fun _ hc => heap_nx _ _ _ _ _ (heap_nx _ _ _ _ _ (hh3 (hh2 hc)))) ?_
      (hp.mono (heap_nx _ _ _ _ _))).mono (by linarith)
    rw [inpA _ _ (by simp) (by simp), inpA _ _ (by simp) (by simp), hi3, inpA _ _ (by simp) (by simp), hi1]

theorem EvOK.tl {a : Fm} {x : Tree} {l : List (Run A)} (ih : EvOK θ supp a x l) :
    EvOK θ supp (.tl a) x (l.map fun r => r.tick r.out.tl) := by
  intro σ hσ m Bd B h
  obtain ⟨ok, hm, ⟨c, hc, hF⟩, hx⟩ := hσ
  obtain ⟨o, a', rfl, hl, rfl⟩ := inv_tl hF
  have hC := Cc_ge (supp := supp)
  rw [tot_map]
  refine (toOp (B := B - 11) ok hm hc (by omega) fun σ1 ok1 hm1 h11 h12 h13 h14 hh1 hi1 => ?_).mono (by omega)
  have hm1' : σ1.mode = .D 3 := by rw [hm1]; congr 1; exact Fin.ext hl
  refine dstep ok1 hm1' h11 .d3 rfl (by decide) rfl rfl ?_
  have hh2 : σ.heap ⊆ (nx θ σ1 (.inl .d3) 0 0 0).heap := fun _ hc => heap_nx σ1 _ _ _ _ (hh1 hc)
  refine ih (nx θ σ1 (.inl .d3) 0 0 0) ⟨ok1.nx _ _ _ _, rfl, ⟨a', h12.mono (heap_nx σ1 _ _ _ _), rfl⟩, ?_⟩ _
    (fun r => Bd (r.tick r.out.tl) + 2) _ ?_
  · change Rep _ (σ1.regs 3) x
    rw [h13]
    exact hx.mono hh2
  · intro r hr hb
    obtain ⟨k1, k2⟩ := h (r.tick r.out.tl) (List.mem_map.2 ⟨r, hr, rfl⟩) hb
    rw [cost_tick] at k2
    refine ⟨fun σ3 v ok3 hm3 h31 h32 hh3 hi3 hv => ?_, by linarith⟩
    have hfr : ((.TL, ![σ3.regs 2, σ1.regs 4, σ1.regs 0, σ1.regs 0]) : Rec Kd) ∈ σ3.heap := by
      rw [h32]
      exact hh3 (new_nx (θ := θ) σ1 (.inl .d3) 0 0 0)
    refine rstep ok3 hm3 hfr .rtl rfl rfl rfl ?_
    have ok4 := ok3.nx (θ := θ) (.inl .rtl) (σ1.regs 4) (σ1.regs 0) (σ1.regs 0)
    subst h31
    obtain ⟨p, q, s, hrec, hp, hq⟩ := (hv.mono (heap_nx (θ := θ) σ3 (.inl .rtl) (σ1.regs 4) (σ1.regs 0) (σ1.regs 0))).load ok4
    generalize decide (r.out ≠ .nil) = b at hrec
    refine lstep ok4 (md := .T) rfl rfl hrec (.t b) (by cases b <;> rfl) (by simp) (by simp) rfl rfl ?_
    refine (k1 (nx θ (nx θ σ3 (.inl .rtl) (σ1.regs 4) (σ1.regs 0) (σ1.regs 0)) (.inl (.t b)) p q s) q
      (ok4.nx _ _ _ _) rfl rfl h14 (fun _ hc => heap_nx _ _ _ _ _ (heap_nx _ _ _ _ _ (hh3 (hh2 hc)))) ?_
      (hq.mono (heap_nx _ _ _ _ _))).mono (by linarith)
    rw [inpA _ _ (by simp) (by simp), inpA _ _ (by simp) (by simp), hi3, inpA _ _ (by simp) (by simp), hi1]

theorem EvOK.cons {a b : Fm} {x : Tree} {la lb : List (Run A)} (iha : EvOK θ supp a x la) (ihb : EvOK θ supp b x lb) :
    EvOK θ supp (.cons a b) x (la.flatMap fun r => lb.map fun s => (r.seq s).tick (.cons r.out s.out)) := by
  intro σ hσ m Bd B h
  obtain ⟨ok, hm, ⟨c, hc, hF⟩, hx⟩ := hσ
  obtain ⟨o, a', rfl, hl, rfl, rfl⟩ := inv_cons hF
  have hC := Cc_ge (supp := supp)
  rw [tot_seq m la (fun _ => lb) fun r s => .cons r.out s.out]
  refine (toOp (B := B - 11) ok hm hc (by omega) fun σ1 ok1 hm1 h11 h12 h13 h14 hh1 hi1 => ?_).mono (by omega)
  have hm1' : σ1.mode = .D 4 := by rw [hm1]; congr 1; exact Fin.ext hl
  refine dstep ok1 hm1' h11 .d4 rfl (by decide) rfl rfl ?_
  have ok2 := ok1.nx (θ := θ) (.inl .d4) 0 0 0
  obtain ⟨p, q, s, hrec, hp, hq⟩ := (h12.mono (heap_nx (θ := θ) σ1 (.inl .d4) 0 0 0)).load ok2
  generalize decide (a' ≠ .nil) = bt at hrec
  refine lstep ok2 (md := .K4) rfl rfl hrec (.k4 bt) (by cases bt <;> rfl) (by simp) (by simp) rfl rfl ?_
  set σ2 := nx θ σ1 (.inl .d4) 0 0 0 with hσ2
  have hh2 : σ.heap ⊆ (nx θ σ2 (.inl (.k4 bt)) p q s).heap := fun _ hc => heap_nx _ _ _ _ _ (heap_nx _ _ _ _ _ (hh1 hc))
  have hr2 : σ2.regs 2 = σ.regs 2 := h13
  have hr3 : σ2.regs 3 = σ.regs 3 := h14
  refine iha (nx θ σ2 (.inl (.k4 bt)) p q s) ⟨ok2.nx _ _ _ _, rfl, ⟨a'.hd, hp.mono (heap_nx _ _ _ _ _), rfl⟩, ?_⟩ _
    (fun r => B - Cc supp * r.cost - Cc supp + 2) _ ?_
  · change Rep _ (σ2.regs 2) x
    rw [hr2]
    exact hx.mono hh2
  · intro r hr hb
    refine ⟨fun σ3 v ok3 hm3 h31 h32 hh3 hi3 hv => ?_, by linarith⟩
    have hfr : ((.CO1, ![σ3.regs 2, q, σ2.regs 2, σ2.regs 3]) : Rec Kd) ∈ σ3.heap := by
      rw [h32]
      exact hh3 (new_nx (θ := θ) σ2 (.inl (.k4 bt)) p q s)
    refine rstep ok3 hm3 hfr .rco1 rfl rfl rfl ?_
    subst h31
    have ok4 := ok3.nx (θ := θ) (.inl .rco1) q (σ2.regs 2) (σ2.regs 3)
    set σ4 := nx θ σ3 (.inl .rco1) q (σ2.regs 2) (σ2.regs 3) with hσ4
    have hh4 : σ.heap ⊆ σ4.heap := fun _ hc => heap_nx _ _ _ _ _ (hh3 (hh2 hc))
    refine (ihb σ4 ⟨ok4, rfl, ⟨a'.tl, ?_, rfl⟩, ?_⟩ (fun s => m ((r.seq s).tick (.cons r.out s.out)))
      (fun s => Bd ((r.seq s).tick (.cons r.out s.out)) + 1) (B - Cc supp * r.cost - Cc supp + 1) ?_).mono (by linarith)
    · change Rep σ4.heap q a'.tl
      exact ((hq.mono (heap_nx _ _ _ _ _)).mono hh3).mono (heap_nx _ _ _ _ _)
    · change Rep σ4.heap (σ2.regs 2) x
      rw [hr2]
      exact hx.mono hh4
    · intro s' hs' hb'
      obtain ⟨k1, k2⟩ := h ((r.seq s').tick (.cons r.out s'.out))
        (List.mem_flatMap.2 ⟨r, hr, List.mem_map.2 ⟨s', hs', rfl⟩⟩) (by simp [Run.tick, Run.seq, hb, hb'])
      rw [cost_tick, cost_seq] at k2
      refine ⟨fun σ5 v' ok5 hm5 h51 h52 hh5 hi5 hv' => ?_, by linarith⟩
      have hfr' : ((.CO2, ![σ5.regs 2, σ3.regs 1, σ2.regs 3, σ3.regs 0]) : Rec Kd) ∈ σ5.heap := by
        rw [h52]
        exact hh5 (new_nx (θ := θ) σ3 (.inl .rco1) q (σ2.regs 2) (σ2.regs 3))
      refine rstep ok5 hm5 hfr' .rco2 rfl rfl rfl ?_
      subst h51
      refine (k1 _ (σ5.n + 1) (ok5.nx _ _ _ _) rfl rfl hr3 (fun _ hc => heap_nx _ _ _ _ _ (hh5 (hh4 hc))) ?_ ?_).mono
        (by linarith)
      · rw [inpA _ _ (by simp) (by simp), hi5, inpA _ _ (by simp) (by simp), hi3, inpA _ _ (by simp) (by simp),
          inpA _ _ (by simp) (by simp), hi1]
      · refine ⟨σ3.regs 1, σ5.regs 1, σ5.regs 0, new_nx (θ := θ) σ5 (.inl .rco2) (σ3.regs 1) (σ2.regs 3) (σ3.regs 0), ?_, ?_⟩
        · exact ((hv.mono (heap_nx _ _ _ _ _)).mono hh5).mono (heap_nx _ _ _ _ _)
        · exact hv'.mono (heap_nx _ _ _ _ _)

theorem EvOK.ite {a b c : Fm} {x : Tree} {la : List (Run A)} {L : Run A → List (Run A)} (iha : EvOK θ supp a x la)
    (ihb : ∀ r ∈ la, r.out ≠ .nil → EvOK θ supp b x (L r)) (ihc : ∀ r ∈ la, r.out = .nil → EvOK θ supp c x (L r)) :
    EvOK θ supp (.ite a b c) x (la.flatMap fun r => (L r).map fun s => (r.seq s).tick s.out) := by
  intro σ hσ m Bd B h
  obtain ⟨ok, hm, ⟨c', hc, hF⟩, hx⟩ := hσ
  obtain ⟨o, a', rfl, hl, rfl, rfl, rfl⟩ := inv_ite hF
  have hC := Cc_ge (supp := supp)
  rw [tot_seq m la L fun r s => s.out]
  refine (toOp (B := B - 11) ok hm hc (by omega) fun σ1 ok1 hm1 h11 h12 h13 h14 hh1 hi1 => ?_).mono (by omega)
  have hm1' : σ1.mode = .D 5 := by rw [hm1]; congr 1; exact Fin.ext hl
  refine dstep ok1 hm1' h11 .d5 rfl (by decide) rfl rfl ?_
  have ok2 := ok1.nx (θ := θ) (.inl .d5) 0 0 0
  obtain ⟨p, q, s, hrec, hp, hq⟩ := (h12.mono (heap_nx (θ := θ) σ1 (.inl .d5) 0 0 0)).load ok2
  generalize decide (a' ≠ .nil) = bt at hrec
  refine lstep ok2 (md := .K5) rfl rfl hrec (.k5 bt) (by cases bt <;> rfl) (by simp) (by simp) rfl rfl ?_
  set σ2 := nx θ σ1 (.inl .d5) 0 0 0 with hσ2
  have hh2 : σ.heap ⊆ (nx θ σ2 (.inl (.k5 bt)) p q s).heap := fun _ hc => heap_nx _ _ _ _ _ (heap_nx _ _ _ _ _ (hh1 hc))
  have hr2 : σ2.regs 2 = σ.regs 2 := h13
  have hr3 : σ2.regs 3 = σ.regs 3 := h14
  refine iha (nx θ σ2 (.inl (.k5 bt)) p q s) ⟨ok2.nx _ _ _ _, rfl, ⟨a'.hd, hp.mono (heap_nx _ _ _ _ _), rfl⟩, ?_⟩ _
    (fun r => B - Cc supp * r.cost - Cc supp + 3) _ ?_
  · change Rep _ (σ2.regs 2) x
    rw [hr2]
    exact hx.mono hh2
  · intro r hr hb
    refine ⟨fun σ3 v ok3 hm3 h31 h32 hh3 hi3 hv => ?_, by linarith⟩
    have hfr : ((.IT, ![σ3.regs 2, q, σ2.regs 2, σ2.regs 3]) : Rec Kd) ∈ σ3.heap := by
      rw [h32]
      exact hh3 (new_nx (θ := θ) σ2 (.inl (.k5 bt)) p q s)
    refine rstep ok3 hm3 hfr .rit rfl rfl rfl ?_
    subst h31
    have ok4 := ok3.nx (θ := θ) (.inl .rit) q (σ2.regs 2) (σ2.regs 3)
    have hv4 := hv.mono (heap_nx (θ := θ) σ3 (.inl .rit) q (σ2.regs 2) (σ2.regs 3))
    set σ4 := nx θ σ3 (.inl .rit) q (σ2.regs 2) (σ2.regs 3) with hσ4
    have hh4 : σ.heap ⊆ σ4.heap := fun _ hc => heap_nx _ _ _ _ _ (hh3 (hh2 hc))
    have hq4 : Rep σ4.heap q a'.tl := ((hq.mono (heap_nx _ _ _ _ _)).mono hh3).mono (heap_nx _ _ _ _ _)
    have hi4 : σ4.inp = σ.inp := by
      rw [inpA _ _ (by simp) (by simp), hi3, inpA _ _ (by simp) (by simp), inpA _ _ (by simp) (by simp), hi1]
    obtain ⟨y1, y2, y3, hrec4, -, -⟩ := hv4.load ok4
    have hrec4' : ((kb (decide (r.out ≠ .nil)), ![σ4.regs 1, y1, y2, y3]) : Rec Kd) ∈ σ4.heap := hrec4
    have hks : ∀ s' ∈ L r, s'.bill = [] → KS θ supp σ.heap (σ.regs 3) σ.inp s'.out (m ((r.seq s').tick s'.out))
        (Bd ((r.seq s').tick s'.out)) ∧ Cc supp * s'.cost + Bd ((r.seq s').tick s'.out) ≤
          B - Cc supp * r.cost - Cc supp := by
      intro s' hs' hb'
      obtain ⟨k1, k2⟩ := h ((r.seq s').tick s'.out)
        (List.mem_flatMap.2 ⟨r, hr, List.mem_map.2 ⟨s', hs', rfl⟩⟩) (by simp [Run.tick, Run.seq, hb, hb'])
      rw [cost_tick, cost_seq] at k2
      exact ⟨k1, by linarith⟩
    by_cases ho : r.out = .nil
    · have hkb : kb (decide (r.out ≠ .nil)) = .N := by simp [kb, ho]
      rw [hkb] at hrec4'
      refine lstep ok4 (md := .I) rfl rfl hrec4' .inn rfl (by simp) (by simp) rfl rfl ?_
      have ok5 := ok4.nx (θ := θ) (.inl .inn) y1 y2 y3
      have hq5 := hq4.mono (heap_nx (θ := θ) σ4 (.inl .inn) y1 y2 y3)
      set σ5 := nx θ σ4 (.inl .inn) y1 y2 y3 with hσ5
      obtain ⟨z1, z2, z3, hrec5, hz1, hz2⟩ := hq5.load ok5
      generalize decide (a'.tl ≠ .nil) = bu at hrec5
      have hrec5' : ((kb bu, ![σ5.regs 1, z1, z2, z3]) : Rec Kd) ∈ σ5.heap := hrec5
      refine lstep ok5 (md := .I2) rfl rfl hrec5' (.i2 bu) (by cases bu <;> rfl) (by simp) (by simp) rfl rfl ?_
      have hh6 : σ.heap ⊆ (nx θ σ5 (.inl (.i2 bu)) z1 z2 z3).heap :=
        fun _ hc => heap_nx _ _ _ _ _ (heap_nx _ _ _ _ _ (hh4 hc))
      refine (ihc r hr ho (nx θ σ5 (.inl (.i2 bu)) z1 z2 z3) ⟨ok5.nx _ _ _ _, rfl,
        ⟨a'.tl.tl, hz2.mono (heap_nx _ _ _ _ _), rfl⟩, ?_⟩ (fun s' => m ((r.seq s').tick s'.out))
        (fun s' => Bd ((r.seq s').tick s'.out)) (B - Cc supp * r.cost - Cc supp) ?_).mono (by linarith)
      · change Rep _ (σ2.regs 2) x
        rw [hr2]
        exact hx.mono hh6
      · intro s' hs' hb'
        obtain ⟨k1, k2⟩ := hks s' hs' hb'
        refine ⟨?_, k2⟩
        have e1 : (nx θ σ5 (.inl (.i2 bu)) z1 z2 z3).regs 3 = σ.regs 3 := hr3
        have e2 : (nx θ σ5 (.inl (.i2 bu)) z1 z2 z3).inp = σ.inp := by
          rw [inpA _ _ (by simp) (by simp), inpA _ _ (by simp) (by simp), hi4]
        rw [e1, e2]
        exact k1.heap hh6
    · have hkb : kb (decide (r.out ≠ .nil)) = .C := by simp [kb, ho]
      rw [hkb] at hrec4'
      refine lstep ok4 (md := .I) rfl rfl hrec4' .ic rfl (by simp) (by simp) rfl rfl ?_
      have ok5 := ok4.nx (θ := θ) (.inl .ic) y1 y2 y3
      have hq5 := hq4.mono (heap_nx (θ := θ) σ4 (.inl .ic) y1 y2 y3)
      set σ5 := nx θ σ4 (.inl .ic) y1 y2 y3 with hσ5
      obtain ⟨z1, z2, z3, hrec5, hz1, hz2⟩ := hq5.load ok5
      generalize decide (a'.tl ≠ .nil) = bu at hrec5
      have hrec5' : ((kb bu, ![σ5.regs 1, z1, z2, z3]) : Rec Kd) ∈ σ5.heap := hrec5
      refine lstep ok5 (md := .I1) rfl rfl hrec5' (.i1 bu) (by cases bu <;> rfl) (by simp) (by simp) rfl rfl ?_
      have hh6 : σ.heap ⊆ (nx θ σ5 (.inl (.i1 bu)) z1 z2 z3).heap :=
        fun _ hc => heap_nx _ _ _ _ _ (heap_nx _ _ _ _ _ (hh4 hc))
      refine (ihb r hr ho (nx θ σ5 (.inl (.i1 bu)) z1 z2 z3) ⟨ok5.nx _ _ _ _, rfl,
        ⟨a'.tl.hd, hz1.mono (heap_nx _ _ _ _ _), rfl⟩, ?_⟩ (fun s' => m ((r.seq s').tick s'.out))
        (fun s' => Bd ((r.seq s').tick s'.out)) (B - Cc supp * r.cost - Cc supp) ?_).mono (by linarith)
      · change Rep _ (σ2.regs 2) x
        rw [hr2]
        exact hx.mono hh6
      · intro s' hs' hb'
        obtain ⟨k1, k2⟩ := hks s' hs' hb'
        refine ⟨?_, k2⟩
        have e1 : (nx θ σ5 (.inl (.i1 bu)) z1 z2 z3).regs 3 = σ.regs 3 := hr3
        have e2 : (nx θ σ5 (.inl (.i1 bu)) z1 z2 z3).inp = σ.inp := by
          rw [inpA _ _ (by simp) (by simp), inpA _ _ (by simp) (by simp), hi4]
        rw [e1, e2]
        exact k1.heap hh6

end Nc.Uni
