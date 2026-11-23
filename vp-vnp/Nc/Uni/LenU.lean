/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Uni.Trace

/-!
# The lengths of the tapes
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Nc.Uni

open Finset Nc.Sort

variable {A : Type} [CommRing A] {M K : Type} [Fintype M] [DecidableEq M] [Fintype K] [DecidableEq K]

theorem sum_Tp (f : Tp K → ℕ) : ∑ s, f s = (∑ i, f (.rg i)) + f .md + f .cp + f .fr + f .lk + f .ls + (∑ b, f (.bk b)) +
    ∑ k, f (.cm k) := by
  let e : Tp K ≃ (Fin 5 ⊕ (Bl K ⊕ Bool)) ⊕ Fin 5 :=
    { toFun := fun s => match s with
        | .rg i => .inl (.inl i)
        | .bk b => .inl (.inr (.inl b))
        | .cm k => .inl (.inr (.inr k))
        | .md => .inr 0
        | .cp => .inr 1
        | .fr => .inr 2
        | .lk => .inr 3
        | .ls => .inr 4
      invFun := fun y => match y with
        | .inl (.inl i) => .rg i
        | .inl (.inr (.inl b)) => .bk b
        | .inl (.inr (.inr k)) => .cm k
        | .inr 0 => .md
        | .inr 1 => .cp
        | .inr 2 => .fr
        | .inr 3 => .lk
        | .inr 4 => .ls
      left_inv := fun s => by cases s <;> rfl
      right_inv := fun y => by
        rcases y with (i | b | k) | j
        · rfl
        · rfl
        · rfl
        · fin_cases j <;> rfl }
  rw [← e.symm.sum_comp, Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type, Fin.sum_univ_five (fun j => f (e.symm (.inr j)))]
  change (∑ i, f (.rg i)) + ((∑ b, f (.bk b)) + ∑ k, f (.cm k)) + (f .md + f .cp + f .fr + f .lk + f .ls) = _
  ring

theorem length_rw' (f : Bool) (w : List (Option (Bl K))) : (rw' f w : List (Sy M K)).length = w.length + 2 := by
  simp [rw']

theorem length_encW {l : List (Bool × List (Option (Bl K)))} {n : ℕ} (h : ∀ r ∈ l, r.2.length = n) :
    (encW l : List (Sy M K)).length = l.length * (n + 2) := by
  induction l with
  | nil => simp [encW]
  | cons r l ih =>
    rw [encW_cons, List.length_append, length_rw', h r (by simp), ih fun r hr => h r (by simp [hr]), List.length_cons]
    ring

theorem length_rot {n : ℕ} {j : ℕ} (hj : j ≤ n) (x : Fin n → Bl K) : (rot j x).length = n + 1 := by
  simp [rot]
  omega

theorem length_encW_recs {n : ℕ} {j : ℕ} (hj : j ≤ n) (l : List (Rc n (Bl K))) :
    (encW (recs j l) : List (Sy M K)).length = l.length * (n + 3) := by
  rw [length_encW (n := n + 1)]
  · simp [recs]
  · intro r hr
    obtain ⟨r', -, rfl⟩ := List.mem_map.1 hr
    exact length_rot hj _

theorem canon_length {n : ℕ} (l : List (Rc n (Bl K))) (k j : ℕ) (hjk : j + k = n) :
    (canon l k j : List (Ps M K)).length = k ∧ ∀ p ∈ (canon l k j : List (Ps M K)),
      (encW (dIn p.1) : List (Sy M K)).length = l.length * (n + 3) ∧
        ∑ b, ((p.2 b).map (Subtype.val : NB M K → Sy M K)).length = l.length * (n + 3) := by
  induction k generalizing j with
  | zero => simp [canon]
  | succ k ih =>
    have hj : j < n := by omega
    obtain ⟨h1, h2⟩ := ih (j + 1) (by omega)
    have hl : (srt (bsl K) l j).length = l.length := length_srt mem_bsl bsl_nodup l j
    rw [canon, dif_pos hj]
    refine ⟨by rw [List.length_cons, h1], ?_⟩
    intro p hp
    rw [List.mem_cons] at hp
    rcases hp with rfl | hp
    · constructor
      · rw [cps, dIn_dl, length_encW_recs hj.le, hl]
      · have h3 : ∀ b, (((cps j hj (srt (bsl K) l j) : Ps M K).2 b).map (Subtype.val : NB M K → Sy M K)).length =
            ((srt (bsl K) l j).filter fun r => r.2 ⟨j, hj⟩ = b).length * (n + 3) := by
          intro b
          have e : ((cps j hj (srt (bsl K) l j) : Ps M K).2 b).map (Subtype.val : NB M K → Sy M K) =
              encW (dOut b (dl j hj (srt (bsl K) l j))) := toNB_val _ (bar_encW _)
          rw [e, dOut_dl, length_encW_recs (by omega)]
        rw [Finset.sum_congr rfl fun b _ => h3 b, ← Finset.sum_mul, Sort.sum_filter, hl]
    · exact h2 p hp

theorem sum_const_map {ι : Type*} (l : List ι) (f : ι → ℕ) (c : ℕ) (h : ∀ i ∈ l, f i = c) : (l.map f).sum = l.length * c := by
  induction l with
  | nil => simp
  | cons i l ih =>
    rw [List.map_cons, List.sum_cons, h i (by simp), ih fun i hi => h i (by simp [hi]), List.length_cons]
    ring

/-- The lengths of the tapes of the sort. -/
theorem imu_length {n : ℕ} {l : List (Rc n (Bl K))} (hl : l ≠ []) {x : XU M K} (h : IMU x (encW (recs 0 l))) :
    (emU x lsT).length + ∑ b, (emU x (.tp (.bk b) true)).length + ∑ k, (emU x (.tp (.cm k) true)).length =
      (n + 1) * (l.length * (n + 3) + 1) + (n * (l.length * (n + 3)) + Fintype.card (Bl K) * n) + 2 * (l.length * (n + 2)) := by
  rw [imu_iff hl] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  obtain ⟨c1, c2⟩ := canon_length (M := M) l n 0 (by omega)
  have hfin : (finL l).length = l.length := by
    rw [finL, List.length_map]
    exact length_srt mem_bsl bsl_nodup l n
  have hfin2 : ∀ r ∈ finL l, r.2.length = n := by
    intro r hr
    obtain ⟨r', -, rfl⟩ := List.mem_map.1 hr
    simp
  have hsum := sum_const_map (canon l n 0 : List (Ps M K))
    (List.length ∘ fun p : Ps M K => (encW (dIn p.1) : List (Sy M K))) (l.length * (n + 3)) (fun p hp => (c2 p hp).1)
  have e1 : (emU x lsT).length = (n + 1) * (l.length * (n + 3) + 1) := by
    rw [emU_lsT, length_blocks, h1, h2, ← recs_last, List.map_append, List.sum_append, List.map_map,
      hsum, c1, List.length_append, List.length_map, c1]
    simp only [List.map_cons, List.map_nil, List.sum_singleton, List.length_singleton]
    rw [length_encW_recs le_rfl]
    have : (srt (bsl K) l n).length = l.length := length_srt mem_bsl bsl_nodup l n
    rw [this]
    ring
  have e2 : ∑ b, (emU x (.tp (.bk b) true)).length = n * (l.length * (n + 3)) + Fintype.card (Bl K) * n := by
    have h5 : ∀ b, (emU x (.tp (.bk b) true)).length =
        (x.1.map fun p => ((p.2 b).map (Subtype.val : NB M K → Sy M K)).length).sum + n := by
      intro b
      rw [emU_bk_true, length_blocks, List.map_map, List.length_map, h1, c1]
      rfl
    rw [Finset.sum_congr rfl fun b _ => h5 b, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, smul_eq_mul]
    congr 1
    have h6 : ∀ ps : List (Ps M K), ∑ b, (ps.map fun p => ((p.2 b).map (Subtype.val : NB M K → Sy M K)).length).sum =
        (ps.map fun p => ∑ b, ((p.2 b).map (Subtype.val : NB M K → Sy M K)).length).sum := by
      intro ps
      induction ps with
      | nil => simp
      | cons p ps ih =>
        simp only [List.map_cons, List.sum_cons]
        rw [Finset.sum_add_distrib, ih]
    rw [h6, h1, sum_const_map _ _ (l.length * (n + 3)) (fun p hp => (c2 p hp).2), c1]
  have e3 : ∀ k, (emU x (.tp (.cm k) true)).length = l.length * (n + 2) := by
    intro k
    rw [emU_cm_true]
    have h7 : (if k then QlG x.2.2 else PlG x.2.2) = finL l := by
      cases k
      · simpa using h3
      · simpa using h4
    rw [h7, length_encW (n := n)]
    · rw [fOut, List.length_map, hfin]
    · intro r hr
      obtain ⟨r', hr', rfl⟩ := List.mem_map.1 hr
      simpa using hfin2 r' hr'
  rw [e1, e2, Finset.sum_congr rfl fun k _ => e3 k]
  simp

variable {P : Mach A M K}

theorem length_bws {ws : List (List Bool)} {n : ℕ} (h : ∀ w ∈ ws, w.length = n) :
    (bws ws : List (Sy M K)).length = ws.length * (n + 1) := by
  induction ws with
  | nil => simp [bws]
  | cons w ws ih =>
    rw [bws_cons, List.length_append, ih fun w hw => h w (by simp [hw]), List.length_cons]
    simp only [bw, List.length_append, List.length_map, List.length_singleton, h w (by simp)]
    ring

/-- The total length for T steps and L bits; b letters of records. -/
def tU (b T L : ℕ) : ℕ := 5 * ((T + 1) * (L + 1)) + (T + 1) + (T + 1) * (L + 1) + T * (L + 1) + T * (L + 4) +
  ((L + 2) * ((2 * T + 1) * (L + 4) + 1) + ((L + 1) * ((2 * T + 1) * (L + 4)) + b * (L + 1)) + 2 * ((2 * T + 1) * (L + 3)))

theorem MX.total {x : XP P} {bits : List Bool} (hx : MX x bits) :
    ∑ s, (emX P x (.tp s true)).length = tU (Fintype.card (Bl K)) x.2.2.1.length (x.1.length + 1) := by
  have hcw : ∀ s ∈ x.2.2.1, ∀ i, (cw s.2 i).length = x.1.length + 1 := by
    intro s hs i
    rw [cw, List.length_map, hx.len s hs]
  have hend : ∀ i : Fin 5, (x.2.2.2.1.1.map fun v => v i).length = x.1.length + 1 := by
    intro i
    have h1 := hx.rg i
    have h2 : ∀ w ∈ x.2.2.1.map (fun s => cw s.2 (rv i)) ++ [x.2.2.2.1.1.map fun v => v i], w.length = x.1.length + 1 := by
      rw [← h1]
      intro w hw
      rw [List.mem_cons, List.mem_map] at hw
      rcases hw with rfl | ⟨s, hs, rfl⟩
      · exact length_i0 _
      · exact hcw s hs _
    exact h2 _ (by simp)
  have e1 : ∀ i, (emX P x (.tp (.rg i) true)).length = (x.2.2.1.length + 1) * (x.1.length + 2) := by
    intro i
    rw [emX_rg_true, length_bws (n := x.1.length + 1)]
    · simp
    · intro w hw
      rw [List.mem_append, List.mem_map, List.mem_singleton] at hw
      rcases hw with ⟨s, hs, rfl⟩ | rfl
      · exact hcw s hs _
      · exact hend i
  have e2 : (emX P x (.tp .md true)).length = x.2.2.1.length + 1 := by
    rw [emX_md_true]
    simp
  have e3 : (emX P x (.tp .cp true)).length = (x.2.2.1.length + 1) * (x.1.length + 2) := by
    rw [emX_cp_true, length_bws (n := x.1.length + 1)]
    · simp [hx.length_eq]
    · intro w hw
      rw [List.mem_append, List.mem_map, List.mem_singleton] at hw
      rcases hw with ⟨r, hr, rfl⟩ | rfl
      · exact hx.len_cn.1 r hr
      · simpa using hx.len_cn.2
  have e4 : (emX P x (.tp .fr true)).length = x.2.2.1.length * (x.1.length + 2) := by
    rw [emX_fr_true, length_bws (n := x.1.length + 1)]
    · simp
    · intro w hw
      rw [List.mem_map] at hw
      obtain ⟨s, hs, rfl⟩ := hw
      exact hcw s hs _
  have e5 : (emX P x (.tp .lk true)).length = x.2.2.1.length * (x.1.length + 5) := by
    rw [emX_lk_true, hx.lk, length_encW (n := x.1.length + 3)]
    · simp [lks]
    · intro r hr
      obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hr
      obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hc
      simp [oc, cont, ldc, hx.len s hs]
  have hls := hx.ls
  rw [hx.block] at hls
  have e6 := imu_length (lsN_ne _ _) hls
  have hN : (lsN (x.1.length + 1) (x.2.2.1.map nst)).length = 2 * x.2.2.1.length + 1 := by
    simp [lsN, dfN]
    ring
  rw [hN] at e6
  have e7 : (emX P x (.tp .ls true)).length = (emU x.2.2.2.2.2 lsT).length := by rw [← emX_ls_true]
  have e8 : ∀ b, (emX P x (.tp (.bk b) true)).length = (emU x.2.2.2.2.2 (.tp (.bk b) true)).length := by
    intro b; rw [← emX_bk]
  have e9 : ∀ k, (emX P x (.tp (.cm k) true)).length = (emU x.2.2.2.2.2 (.tp (.cm k) true)).length := by
    intro k; rw [← emX_cm]
  rw [sum_Tp (fun s => (emX P x (.tp s true)).length), Finset.sum_congr rfl fun i _ => e1 i, e2, e3, e4, e5, e7,
    Finset.sum_congr rfl fun b _ => e8 b, Finset.sum_congr rfl fun k _ => e9 k]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  unfold tU
  have e10 : ∀ a b c d e f g h' : ℕ, a + b + c + d + e + f + g + h' = a + b + c + d + e + (f + g + h') := by
    intros; omega
  rw [e10, e6]

end Nc.Uni
