/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Uni.Vals

/-!
# Matched runs are runs of the pointer machine
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Nc.Uni

open Finset

section Columns

theorem cols_ext {q : ℕ} {c c' : List (Fin (q + 1) → Bool)} (h : ∀ j, c.map (fun v => v j) = c'.map fun v => v j) : c = c' := by
  have hl : c.length = c'.length := by simpa using congrArg List.length (h 0)
  refine List.ext_getElem hl fun i h1 h2 => ?_
  funext j
  have := h j
  have h3 : (c.map fun v => v j)[i]'(by simpa using h1) = (c'.map fun v => v j)[i]'(by simpa using h2) := by
    simp only [this]
  simpa using h3

/-- The columns of numbers of L bits. -/
def unb (L : ℕ) {q : ℕ} (a : Fin q → ℕ) : List (Fin q → Bool) :=
  List.ofFn fun t : Fin L => fun j => (bin L (a j)).get (t.cast (length_bin L (a j)).symm)

theorem length_unb (L : ℕ) {q : ℕ} (a : Fin q → ℕ) : (unb L a).length = L := by simp [unb]

theorem unb_proj (L : ℕ) {q : ℕ} (a : Fin q → ℕ) (j : Fin q) : (unb L a).map (fun v => v j) = bin L (a j) := by
  refine List.ext_getElem (by simp [length_unb, length_bin]) fun i h1 h2 => ?_
  simp [unb]

/-- A list of columns is given by numbers. -/
theorem unb_bv {q : ℕ} (w : List (Fin (q + 1) → Bool)) : unb w.length (fun j => bv (w.map fun v => v j)) = w := by
  refine cols_ext fun j => ?_
  rw [unb_proj]
  have := bin_bv (w.map fun v => v j)
  rwa [List.length_map] at this

theorem bin_zero (L : ℕ) : bin L 0 = List.replicate L false := by
  have := bin_bv (List.replicate L false)
  rwa [List.length_replicate, bv_false] at this

end Columns

section Chains

theorem chain_len {ι : Type*} (l : List ι) (f g : ι → List Bool) (a b : List Bool) (h : a :: l.map f = l.map g ++ [b])
    (hfg : ∀ r ∈ l, (f r).length = (g r).length) : (∀ r ∈ l, (g r).length = a.length) ∧ b.length = a.length := by
  induction l generalizing a with
  | nil =>
    simp only [List.map_nil, List.nil_append, List.cons.injEq, and_true] at h
    exact ⟨by simp, by rw [h]⟩
  | cons r l ih =>
    simp only [List.map_cons, List.cons_append, List.cons.injEq] at h
    obtain ⟨h1, h2⟩ := ih (f r) h.2 fun r hr => hfg r (by simp [hr])
    have h3 : (f r).length = a.length := by rw [hfg r (by simp), h.1]
    refine ⟨fun r' hr' => ?_, by rw [h2, h3]⟩
    rw [List.mem_cons] at hr'
    rcases hr' with rfl | hr'
    · rw [h.1]
    · rw [h1 r' hr', h3]

theorem chain_val {ι : Type*} (l : List ι) (f g : ι → List Bool) (a b : List Bool) (h : a :: l.map f = l.map g ++ [b])
    (hfg : ∀ r ∈ l, bv (f r) = bv (g r) + 1) :
    l.map (fun r => bv (g r)) = (List.range l.length).map (fun j => bv a + j) ∧ bv b = bv a + l.length := by
  induction l generalizing a with
  | nil =>
    simp only [List.map_nil, List.nil_append, List.cons.injEq, and_true] at h
    exact ⟨rfl, by rw [h]; rfl⟩
  | cons r l ih =>
    simp only [List.map_cons, List.cons_append, List.cons.injEq] at h
    obtain ⟨h1, h2⟩ := ih (f r) h.2 fun r hr => hfg r (by simp [hr])
    have h3 : bv (f r) = bv a + 1 := by rw [hfg r (by simp), h.1]
    rw [List.map_cons, List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map, h1, h2, h3, h.1]
    refine ⟨?_, by omega⟩
    congr 1
    refine List.map_congr_left fun j _ => ?_
    simp only [Function.comp]
    omega

end Chains

variable {A : Type} [CommRing A] {M K : Type} [Fintype M] [DecidableEq M] [Fintype K] [DecidableEq K] {P : Mach A M K}

/-- A step with numbers. -/
def nst (s : P.Rl × List (Fin 9 → Bool)) : P.Step := (s.1, fun i => bv (cw s.2 i))

variable (P) in
/-- The first state. -/
def σi (bits : List Bool) : Mach.State (M := M) (K := K) := ⟨P.m0, fun _ => 0, [(P.kN, ![0, 0, 0, 0])], 0, bits⟩

/-- The content of a record of numbers. -/
def cN (L : ℕ) (ρ : Rec K) : List (Bl K) := cont ρ.1 (unb L ρ.2)

theorem length_cN (L : ℕ) (ρ : Rec K) : (cN L ρ).length = L + 1 := by simp [cN, cont, length_unb]

/-- The key of a record of numbers. -/
def kyN (L : ℕ) (ρ : Rec K) : Fin (L + 1) → Bl K := fun i => (cN L ρ).get (i.cast (length_cN L ρ).symm)

theorem ofFn_kyN (L : ℕ) (ρ : Rec K) : List.ofFn (kyN L ρ) = cN L ρ := by
  refine List.ext_getElem (by rw [List.length_ofFn, length_cN]) fun i h1 h2 => ?_
  rw [List.getElem_ofFn]
  rfl

theorem kyN_inj {L : ℕ} {ρ ρ' : Rec K} (h : ∀ j, ρ.2 j < 2 ^ L) (h' : ∀ j, ρ'.2 j < 2 ^ L) (e : kyN L ρ = kyN L ρ') :
    ρ = ρ' := by
  have h1 : cN L ρ = cN L ρ' := by rw [← ofFn_kyN, ← ofFn_kyN, e]
  simp only [cN, cont, List.cons.injEq, Sum.inl.injEq] at h1
  have h2 := List.map_injective_iff.2 Sum.inr_injective h1.2
  refine Prod.ext h1.1 ?_
  funext j
  have h3 := congrArg (List.map fun v : Fin 4 → Bool => v j) h2
  rw [unb_proj, unb_proj] at h3
  rw [← bv_bin (h j), ← bv_bin (h' j), h3]

theorem length_cn (r : List Bool × List Unit) : (cn1 r).length = (cn r).length := by simp [cn, cn1]

theorem bv_cn (r : List Bool × List Unit) : bv (cn1 r) = bv (cn r) + 1 := bv_succ _ _

theorem bv_i1 (l : List Unit) : bv (i1 l) = 1 := by
  rw [i1, bv_append, bv_false]
  simp [bv]

theorem length_i1 (l : List Unit) : (i1 l).length = l.length + 1 := by simp [i1]

theorem length_i0 (l : List Unit) : (i0 l).length = l.length + 1 := by simp [i0]

theorem bv_i0 (l : List Unit) : bv (i0 l) = 0 := bv_false _

theorem alc_eq {L : ℕ} {s : P.Rl × List (Fin 9 → Bool)} (hl : s.2.length = L) :
    alc P s.1 s.2 = unb L (Mach.al (nst s)).2 := by
  have key : ∀ i, cw s.2 i = bin L (bv (cw s.2 i)) := by
    intro i
    have := bin_bv (cw s.2 i)
    rw [cw, List.length_map, hl] at this
    exact this.symm
  refine cols_ext fun j => ?_
  rw [unb_proj, alc, List.map_map]
  fin_cases j
  · exact key 8
  · exact key _
  · exact key _
  · exact key _

theorem ldc_eq {L : ℕ} {s : P.Rl × List (Fin 9 → Bool)} (hl : s.2.length = L) :
    ldc P s.1 s.2 = unb L (Mach.ld (nst s)).2 := by
  have key : ∀ i, cw s.2 i = bin L (bv (cw s.2 i)) := by
    intro i
    have := bin_bv (cw s.2 i)
    rw [cw, List.length_map, hl] at this
    exact this.symm
  refine cols_ext fun j => ?_
  rw [unb_proj, ldc, List.map_map]
  fin_cases j
  · exact key _
  · exact key 5
  · exact key 6
  · exact key 7

section Facts

variable {x : XP P} {bits : List Bool} (hx : MX x bits)

include hx

theorem MX.len_cn : (∀ r ∈ x.2.1, (cn r).length = x.1.length + 1) ∧ x.2.2.2.1.2.length + 1 = x.1.length + 1 := by
  have := chain_len x.2.1 cn1 cn _ _ hx.cp fun r _ => length_cn r
  rw [length_i1] at this
  exact ⟨this.1, by simpa using this.2⟩

theorem MX.len : ∀ s ∈ x.2.2.1, s.2.length = x.1.length + 1 := by
  intro s hs
  have h1 : cw s.2 8 ∈ x.2.1.map cn := by
    rw [hx.fr]
    exact List.mem_map.2 ⟨s, hs, rfl⟩
  obtain ⟨r, hr, e⟩ := List.mem_map.1 h1
  have h2 := hx.len_cn.1 r hr
  rw [e] at h2
  simpa [cw] using h2

theorem MX.length_eq : x.2.1.length = x.2.2.1.length := by
  have := congrArg List.length hx.fr
  simpa using this

theorem MX.vals : x.2.2.1.map (fun s => bv (cw s.2 8)) = (List.range x.2.2.1.length).map (fun j => 1 + j) ∧
    bv (true :: x.2.2.2.1.2) = 1 + x.2.2.1.length := by
  have h1 := chain_val x.2.1 cn1 cn _ _ hx.cp fun r _ => bv_cn r
  rw [bv_i1, hx.length_eq] at h1
  refine ⟨?_, h1.2⟩
  rw [← h1.1]
  have h2 := congrArg (List.map bv) hx.fr
  rw [List.map_map, List.map_map] at h2
  exact h2.symm

theorem MX.size_eq : Nat.size (x.2.2.1.length + 1) = x.1.length + 1 := by
  have h1 := hx.vals.2
  have h2 := hx.len_cn.2
  have h3 := bv_lt x.2.2.2.1.2
  simp only [bv, if_true] at h1
  have e : x.2.2.2.1.2.length = x.1.length := by omega
  rw [e] at h1 h3
  refine le_antisymm ?_ ?_
  · rw [Nat.size_le, pow_succ]
    omega
  · rw [Nat.succ_le_iff, Nat.lt_size]
    omega

end Facts

/-- The records of numbers that are defined. -/
def dfN (tr : List P.Step) : List (Rec K) := (P.kN, ![0, 0, 0, 0]) :: tr.map Mach.al

/-- The list that is sorted. -/
def lsN (L : ℕ) (tr : List P.Step) : List (Sort.Rc (L + 1) (Bl K)) :=
  ((dfN tr).map (kyN L)).map (fun k => (false, k)) ++ ((tr.map Mach.ld).map (kyN L)).map fun k => (true, k)

theorem recs_lsN (L : ℕ) (tr : List P.Step) : recs 0 (lsN L tr) =
    ((dfN tr).map (cN L)).map (fun c => (false, oc c)) ++ ((tr.map Mach.ld).map (cN L)).map fun c => (true, oc c) := by
  simp only [recs, lsN, List.map_append, List.map_map, Function.comp_def, rot_zero, ofFn_kyN, oc]

theorem lsN_ne (L : ℕ) (tr : List P.Step) : lsN L tr ≠ [] := by simp [lsN, dfN]

theorem unb_zero (L : ℕ) : unb L ![0, 0, 0, 0] = List.replicate L fun _ : Fin 4 => false := by
  refine cols_ext fun j => ?_
  rw [unb_proj, List.map_replicate]
  have : (![0, 0, 0, 0] : Fin 4 → ℕ) j = 0 := by fin_cases j <;> rfl
  rw [this, bin_zero]

theorem block_of {x : XP P} (hx : ∀ s ∈ x.2.2.1, s.2.length = x.1.length + 1) :
    (dfs x).map (fun c => (false, oc c)) ++ (lks x).map (fun c => (true, oc c)) =
      recs 0 (lsN (x.1.length + 1) (x.2.2.1.map nst)) := by
  rw [recs_lsN]
  congr 1
  · congr 1
    rw [dfs, dfN, List.map_cons, List.map_map, List.map_map]
    congr 1
    · rw [cN, unb_zero]
    · refine List.map_congr_left fun s hs => ?_
      simp only [Function.comp, cN]
      rw [← alc_eq (hx s hs)]
      rfl
  · congr 1
    rw [lks, List.map_map, List.map_map]
    refine List.map_congr_left fun s hs => ?_
    simp only [Function.comp, cN]
    rw [← ldc_eq (hx s hs)]
    rfl

theorem MX.block {x : XP P} {bits : List Bool} (hx : MX x bits) :
    (dfs x).map (fun c => (false, oc c)) ++ (lks x).map (fun c => (true, oc c)) =
      recs 0 (lsN (x.1.length + 1) (x.2.2.1.map nst)) := block_of hx.len

theorem nst_lt {x : XP P} {bits : List Bool} (hx : MX x bits) {s : P.Rl × List (Fin 9 → Bool)} (hs : s ∈ x.2.2.1) (i : Fin 9) :
    (nst s).2 i < 2 ^ (x.1.length + 1) := by
  have := bv_lt (cw s.2 i)
  rw [cw, List.length_map, hx.len s hs] at this
  exact this

theorem four_lt {a b c d n : ℕ} (ha : a < n) (hb : b < n) (hc : c < n) (hd : d < n) (j : Fin 4) : (![a, b, c, d] : Fin 4 → ℕ) j < n := by
  fin_cases j <;> assumption

/-- **A matched run is a run of the machine.** -/
theorem MX.gv {x : XP P} {bits : List Bool} (hx : MX x bits) : Mach.GV (σi P bits) (x.2.2.1.map nst) := by
  refine ⟨?_, fun i => ⟨bv (x.2.2.2.1.1.map fun v => v i), ?_⟩, ?_, ?_, ?_⟩
  · rw [List.map_map, List.map_map]
    exact hx.md
  · have := congrArg (List.map bv) (hx.rg i)
    rw [List.map_cons, List.map_append, List.map_map, List.map_map, bv_i0] at this
    rw [List.map_map, List.map_map]
    exact this
  · rw [List.map_map, List.length_map]
    refine hx.vals.1.trans ?_
    exact List.map_congr_left fun j _ => by simp [σi]
  · rw [List.flatMap_map]
    exact hx.inp
  · have h1 := hx.ls
    rw [hx.block] at h1
    have h2 := (imu_table (M := M) ((dfN (x.2.2.1.map nst)).map (kyN (x.1.length + 1)))
      (((x.2.2.1.map nst).map Mach.ld).map (kyN (x.1.length + 1))) (by simp [dfN])).1 ⟨_, h1⟩
    intro st hst
    have h3 := h2 (kyN (x.1.length + 1) (Mach.ld st)) (List.mem_map.2 ⟨_, List.mem_map.2 ⟨st, hst, rfl⟩, rfl⟩)
    obtain ⟨ρ, hρ, e⟩ := List.mem_map.1 h3
    have hst' := hst
    obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hst'
    have hb1 : ∀ j, (Mach.ld (nst s)).2 j < 2 ^ (x.1.length + 1) :=
      four_lt (nst_lt hx hs _) (nst_lt hx hs _) (nst_lt hx hs _) (nst_lt hx hs _)
    have hb2 : ∀ j, ρ.2 j < 2 ^ (x.1.length + 1) := by
      rw [dfN, List.mem_cons, List.mem_map] at hρ
      rcases hρ with rfl | ⟨st', hst', rfl⟩
      · exact four_lt (by positivity) (by positivity) (by positivity) (by positivity)
      · obtain ⟨s', hs', rfl⟩ := List.mem_map.1 hst'
        exact four_lt (nst_lt hx hs' _) (nst_lt hx hs' _) (nst_lt hx hs' _) (nst_lt hx hs' _)
    rw [← kyN_inj hb2 hb1 e]
    exact hρ

theorem unit_list {l l' : List Unit} (h : l.length = l'.length) : l = l' :=
  List.ext_getElem h fun _ _ _ => rfl

/-- The run is determined by the run of the machine. -/
theorem MX.unique {x x' : XP P} {bits : List Bool} (hx : MX x bits) (hx' : MX x' bits)
    (e : x.2.2.1.map nst = x'.2.2.1.map nst) : x = x' := by
  have hT : x.2.2.1.length = x'.2.2.1.length := by simpa using congrArg List.length e
  have hL : x.1.length = x'.1.length := by
    have h1 := hx.size_eq
    have h2 := hx'.size_eq
    rw [hT] at h1
    omega
  have e1 : x.1 = x'.1 := unit_list hL
  have e3 : x.2.2.1 = x'.2.2.1 := by
    refine List.ext_getElem hT fun i h1 h2 => ?_
    have h3 : (x.2.2.1.map nst)[i]'(by simpa using h1) = (x'.2.2.1.map nst)[i]'(by simpa using h2) := by
      simp only [e]
    simp only [List.getElem_map] at h3
    have l1 := hx.len _ (List.getElem_mem h1)
    have l2 := hx'.len _ (List.getElem_mem h2)
    have h4 := congrArg Prod.fst h3
    have h5 := congrArg Prod.snd h3
    refine Prod.ext h4 ?_
    have h6 := unb_bv (x.2.2.1[i]).2
    have h7 := unb_bv (x'.2.2.1[i]).2
    rw [← h6, ← h7, l1, l2, hL]
    congr 1
  have e2 : x.2.1 = x'.2.1 := by
    have h1 : x.2.1.map cn = x'.2.1.map cn := by rw [hx.fr, hx'.fr, e3]
    refine List.map_injective_iff.2 ?_ h1
    rintro ⟨u, k⟩ ⟨u', k'⟩ h
    obtain ⟨a1, a2⟩ := cut_unique h
    exact Prod.ext a1 (unit_list a2)
  have e4 : x.2.2.2.1 = x'.2.2.2.1 := by
    refine Prod.ext (cols_ext fun i => ?_) ?_
    · have h1 := hx.rg i
      have h2 := hx'.rg i
      rw [e1, e3] at h1
      have h3 := h1.symm.trans h2
      simpa using List.append_cancel_left h3
    · have h1 := hx.cp
      have h2 := hx'.cp
      rw [e1, e2] at h1
      have h3 := h1.symm.trans h2
      simpa using List.append_cancel_left h3
  have e5 : x.2.2.2.2.1 = x'.2.2.2.2.1 := by
    rw [hx.lk, hx'.lk, lks, lks, e3]
  have e6 : x.2.2.2.2.2 = x'.2.2.2.2.2 := by
    have h1 := hx.ls
    have h2 := hx'.ls
    rw [hx.block] at h1
    rw [hx'.block] at h2
    rw [e1, e3] at h1
    exact imu_unique (lsN_ne _ _) h1 h2
  exact Prod.ext e1 (Prod.ext e2 (Prod.ext e3 (Prod.ext e4 (Prod.ext e5 e6))))

end Nc.Uni
