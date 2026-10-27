/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import PaddedDescent.F.Table
public import StepMachines.Prog.NetRun
public import StepMachines.Prog.NetVal
public import StepMachines.Prog.GridDefs
public import Groundwork.Net.Net

/-! # The rebalancing on explicit data (mergedF = mergedVal, StR)

`mergedF` computes the same numbers as the value specification `NetE.mergedVal`, on well-formed
queries. The equality follows from uniqueness of results: the program `mergedM` over
the cost-free procedures `freeM` halts with the plain value on every input (by the run lemmas of the
combinators), `mergedM_runs` says
that it halts with `mergedVal` on well-formed queries, and results are unique. -/

public section

namespace PaddedDescent.F.RebalF

open Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Stepped Finset

theorem freeM_runs {α β : Type} (f : α → β) (a : α) : (freeM f).Runs a 0 0 (f a) :=
  .halt rfl (Nat.le_refl 0)

/-- How to show that a network of plain functions presents a network. -/
theorem presents {C : Type} (F : FNet C) (c : C) {g : ℕ} (N : Network (Fin g) (List Bool) (List Bool))
    (hS : ∀ a : Fin g, N.S a = words (F.n c a))
    (hc : ∀ a b : Fin g, a ≠ b → N.c a b = F.cap c a b)
    (hl : ∀ a b : Fin g, a ≠ b → N.lab a b = words (F.cap c a b))
    (hW : ∀ (a : Fin g) (z : List Bool), z.length = F.n c a → F.W (c, (a.val, z)) = N.W a z)
    (hf : ∀ (a b : Fin g) (z θ : List Bool), a ≠ b → z.length = F.n c a → θ.length = F.cap c a b →
      F.f (c, ((a.val, b.val), (z, θ))) = N.f a b z θ) :
    F.toP.Presents c N 0 0 where
  S_eq := hS
  c_eq := hc
  lab_eq := hl
  W_runs a z hz := by rw [← hW a z hz]; exact freeM_runs _ _
  f_runs a b z θ hab hz hθ := by rw [← hf a b z θ hab hz hθ]; exact freeM_runs _ _

/-! ### The programs over cost-free procedures halt with the plain value -/

/-- M halts on a with the result b. -/
def Halts {α β : Type} (M : Stepped α β) (a : α) (b : β) : Prop := ∃ T S, M.Runs a T S b

section hcalc
variable {α β : Type}

theorem halts_sumRange [HasSize α] {N : α → ℕ} {M : Stepped (α × ℕ) ℤ} {a : α} {v : ℕ → ℤ}
    (h : ∀ y, y < N a → Halts M (a, y) (v y)) : Halts (sumRange N M) a (∑ y ∈ range (N a), v y) := by
  choose! t S hr using h
  exact ⟨_, _, sumRange_runs t v ((range (N a)).sup fun y => (v y).natAbs) ((range (N a)).sup S)
    (fun y hy => (hr y hy).mono le_rfl (Finset.le_sup (f := S) (mem_range.2 hy)))
    (fun y hy => Finset.le_sup (f := fun y => (v y).natAbs) (mem_range.2 hy))⟩

theorem halts_prodRange [HasSize α] {N : α → ℕ} {M : Stepped (α × ℕ) ℤ} {a : α} {v : ℕ → ℤ}
    (h : ∀ y, y < N a → Halts M (a, y) (v y)) : Halts (prodRange N M) a (∏ y ∈ range (N a), v y) := by
  choose! t S hr using h
  exact ⟨_, _, prodRange_runs t v (((range (N a)).sup fun y => (v y).natAbs) + 1) ((range (N a)).sup S) (by omega)
    (fun y hy => (hr y hy).mono le_rfl (Finset.le_sup (f := S) (mem_range.2 hy)))
    (fun y hy => (Finset.le_sup (f := fun y => (v y).natAbs) (mem_range.2 hy)).trans (Nat.le_succ _))⟩

theorem halts_ite {p : α → Bool} {M N : Stepped α β} {a : α} {b c : β} (h1 : Halts M a b) (h2 : Halts N a c) :
    Halts (Stepped.ite p M N) a (bif p a then b else c) := by
  obtain ⟨T, S, h1⟩ := h1
  obtain ⟨T', S', h2⟩ := h2
  cases hp : p a with
  | true => exact ⟨_, _, ite_runs_true hp h1⟩
  | false => exact ⟨_, _, ite_runs_false hp h2⟩

theorem halts_free {γ : Type} (q : α → γ) (f : γ → β) (a : α) : Halts (mapIn q (freeM f)) a (f (q a)) :=
  ⟨_, _, mapIn_runs (freeM_runs f (q a))⟩

end hcalc

variable {C : Type}

/-- `termF` without fuel. -/
def termP (K g : ℕ) (F : FNet C) (u : (X0 C × ℕ) × ℕ) : ℤ :=
  bif isOne K g u then 1
  else bif isW g u then F.W (qW K g F.toP u)
  else bif isPsi K g u then ∑ y ∈ range (nLab g F.toP u), F.f (qP1 K g F.toP (u, y)) * F.f (qP2 K g F.toP (u, y))
  else F.f (qF K g F.toP u)

/-- `mergedF` without fuel. -/
def mergedP (K g : ℕ) (F : FNet C) (u : X0 C) : ℤ :=
  bif validB K g F.toP u then ∑ y ∈ range (nStates K g F.toP u), ∏ i ∈ range (g * g), termP K g F ((u, y), i) else 0

section
variable [HasSize C]

theorem termM_halts (K g : ℕ) (F : FNet C) (u : (X0 C × ℕ) × ℕ) : Halts (termM K g F.toP) u (termP K g F u) := by
  unfold termM termP psiM
  refine halts_ite ⟨_, _, const_runs _ _⟩ (halts_ite (halts_free _ _ _) (halts_ite (halts_sumRange fun y _ => ?_)
    (halts_free _ _ _)))
  exact ⟨_, _, mul2_runs (mapIn_runs (freeM_runs F.f _)) (mapIn_runs (freeM_runs F.f _))⟩

theorem mergedM_halts (K g : ℕ) (F : FNet C) (u : X0 C) : Halts (mergedM K g F.toP) u (mergedP K g F u) := by
  unfold mergedM mergedP
  exact halts_ite (halts_sumRange fun y _ => halts_prodRange fun i _ => termM_halts K g F ((u, y), i)) ⟨_, _, const_runs _ _⟩

end

/-- The plain value is the specification `mergedVal`, on well-formed queries. -/
theorem mergedP_eq {K g : ℕ} {F : FNet C} {c : C} {N : Network (Fin g) (List Bool) (List Bool)} {P B : ℕ}
    (hN : F.toP.Presents c N 0 0) (hS : N.Sized P B) (x β m : ℕ)
    (hm : ∀ G < K, (members K g x G).length ≤ m)
    (hβ : ∀ G < K, ∀ G' < K, G ≠ G' → lbLen K g F.toP c x G G' ≤ β)
    (G : Fin K) (θ : Fin K → List Bool) (hθ : ∀ G', G' ≠ G → (θ G').length = β) (hG : θ G = []) :
    mergedP K g F ((c, x), (G.val, List.ofFn θ)) = mergedVal K g F.toP N ((c, x), (G.val, List.ofFn θ)) := by
  let _ : HasSize C := ⟨fun _ => 0⟩
  obtain ⟨T, S, h⟩ := mergedM_halts K g F ((c, x), (G.val, List.ofFn θ))
  exact h.unique (mergedM_runs K g F.toP (hN.mono (Nat.zero_le 1) le_rfl) hS le_rfl x β m hm hβ G θ hθ hG)

/-- The fuelled `termF` equals the plain `termP`; the bound of the number of labels by the padding
length is needed only in the cases where the sum is evaluated. -/
theorem termF_eq {pad : U} {K g : ℕ} {F : FNet C} {u : (X0 C × ℕ) × ℕ}
    (h : isW g u = false → nLab g F.toP u ≤ pad.length) : termF pad K g F u = termP K g F u := by
  unfold termF termP
  cases h2 : isW g u with
  | true => rfl
  | false => rw [sumF_eq (h h2)]

theorem mergedF_eq {pad : U} {K g : ℕ} {F : FNet C} {u : X0 C} (h1 : nStates K g F.toP u ≤ pad.length)
    (h2 : ∀ y, ∀ i < g * g, isW g ((u, y), i) = false → nLab g F.toP ((u, y), i) ≤ pad.length) :
    mergedF pad K g F u = mergedP K g F u := by
  unfold mergedF mergedP
  rw [sumF_eq h1]
  simp only [prodL_eq]
  congr 1
  exact Finset.sum_congr rfl fun y _ => Finset.prod_congr rfl fun i hi => termF_eq (h2 y i (Finset.mem_range.1 hi))

/-! ### `StR` -/

theorem n_le {F : FNet C} {c : C} {g : ℕ} {N : Network (Fin g) (List Bool) (List Bool)} {P B : ℕ}
    (hN : F.toP.Presents c N 0 0) (hS : N.Sized P B) (a : Fin g) : F.toP.n c a ≤ P := by
  have := hS.card_S a
  rw [hN.S_eq, card_words] at this
  exact (Nat.pow_le_pow_iff_right (by norm_num)).1 this

theorem cap_le {F : FNet C} {c : C} {g : ℕ} {N : Network (Fin g) (List Bool) (List Bool)} {P B : ℕ}
    (hN : F.toP.Presents c N 0 0) (hS : N.Sized P B) {a b : Fin g} (hab : a ≠ b) : F.toP.cap c a b ≤ P := by
  rw [← hN.c_eq a b hab]
  exact (Finset.single_le_sum (f := fun b => N.c a b) (fun _ _ => Nat.zero_le _)
    (Finset.mem_erase.2 ⟨hab.symm, mem_univ b⟩)).trans (hS.sum_c a)

theorem stLen_le {F : FNet C} {c : C} {K g : ℕ} {N : Network (Fin g) (List Bool) (List Bool)} {P B : ℕ}
    (hN : F.toP.Presents c N 0 0) (hS : N.Sized P B) {x G m : ℕ} (hm : (members K g x G).length ≤ m) :
    stLen K g F.toP c x G ≤ P * m := by
  unfold stLen stLens
  have h1 := List.sum_le_card_nsmul ((members K g x G).map (F.toP.n c)) P (by
    intro y hy
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hy
    exact n_le hN hS ⟨a, List.mem_range.1 (List.mem_filter.1 ha).1⟩)
  rw [List.length_map, smul_eq_mul] at h1
  calc _ ≤ (members K g x G).length * P := h1
    _ ≤ m * P := Nat.mul_le_mul_right _ hm
    _ = P * m := Nat.mul_comm _ _

/-- The bound on the new label length, for any colouring. -/
theorem betaC_le {F : FNet C} {c : C} {K g : ℕ} {N : Network (Fin g) (List Bool) (List Bool)} {P B : ℕ}
    (hN : F.toP.Presents c N 0 0) (hS : N.Sized P B) : K ^ 3 * betaC K g F.toP c ≤ K ^ 3 + K * N.U + g * P := by
  have h1 := Colouring.beta_le K g (Uc g F.toP c) (Pc g F.toP c)
  rw [Uc_eq F.toP hN] at h1
  have h2 : g * Pc g F.toP c ≤ g * P := Nat.mul_le_mul_left _ (Pc_le F.toP hN hS)
  rw [betaC, Uc_eq F.toP hN]
  omega

/-- `StR`: the rebalancing `rebalF` picks the first good grouping and returns a table whose value is
that of the merged network, with bounds on the new label length and on the entries. -/
theorem stR : StR := by
  intro C pad K g F c N P B hK hg hN hS f1 f2 f3 f4
  have hK0 : 0 < K := by omega
  obtain ⟨x', hx', hgood'⟩ := exists_goodB F.toP hK hg hN hS
  obtain ⟨x, hfind⟩ : ∃ x, (List.range (K ^ g)).find? (fun x => goodB K g F.toP (c, x)) = some x := by
    rw [← Option.isSome_iff_exists, List.find?_isSome]
    exact ⟨x', List.mem_range.2 hx', hgood'⟩
  have hgood : goodB K g F.toP (c, x) = true := List.find?_some (p := fun x => goodB K g F.toP (c, x)) hfind
  obtain ⟨hg1, hg2⟩ := (goodB_iff F.toP hK0 hN x).1 hgood
  have hβ3 := betaC_le (K := K) hN hS
  obtain ⟨β, hβdef⟩ : ∃ β, β = betaC K g F.toP c := ⟨_, rfl⟩
  rw [← hβdef] at hg2 f4 hβ3
  obtain ⟨m, hmdef⟩ : ∃ m, m = 2 * g / K := ⟨_, rfl⟩
  rw [← hmdef] at f2 ⊢
  have hm : ∀ G, #{a : Fin g | chi hK0 x a = G} ≤ m := fun G => by
    rw [hmdef, Nat.le_div_iff_mul_le hK0, Nat.mul_comm]
    exact (hg1 G).le
  have hβ1 : 1 ≤ β := hβdef ▸ Colouring.one_le_beta _ _ _ _
  have hSm := Network.merge_sized N (chi hK0 x) [] [] hS hm
  have hm' : ∀ G < K, (members K g x G).length ≤ m := fun G hG => by
    rw [length_members hK0 x ⟨G, hG⟩]; exact hm _
  have hβ' : ∀ G < K, ∀ G' < K, G ≠ G' → lbLen K g F.toP c x G G' ≤ β := fun G hG G' hG' hne => by
    have hne' : (⟨G, hG⟩ : Fin K) ≠ ⟨G', hG'⟩ := fun e => hne (congrArg Fin.val e)
    rw [lbLen_eq F.toP hK0 hN x hne']
    exact hg2 _ _ hne'
  have hg0 : 0 < g := by
    have : 0 < K ^ 8 := Nat.pow_pos hK0
    omega
  have hentry : ∀ (G : Fin K) (θ : Fin K → List Bool), WFQ β G θ →
      mergedF pad K g F ((c, x), (G.1, List.ofFn θ)) =
        (N.merge (chi hK0 x) [] []).toInst (mD K g F.toP c x β) (mdec K g F.toP c x) G θ := by
    rintro G θ ⟨hθ, hG⟩
    rw [toInst_eq_mergedVal F.toP hK0 hN x β G θ hθ, ← mergedP_eq hN hS x β m hm' hβ' G θ hθ hG]
    refine mergedF_eq ?_ fun y i hi hW => ?_
    · exact (Nat.pow_le_pow_right (by norm_num) (stLen_le hN hS (hm' G G.2))).trans f2
    · have ha : i / g < g := Nat.div_lt_of_lt_mul hi
      have hb : i % g < g := Nat.mod_lt _ hg0
      have hab : (⟨i / g, ha⟩ : Fin g) ≠ ⟨i % g, hb⟩ := by
        intro e
        have e' : i / g = i % g := congrArg Fin.val e
        simp [isW, e'] at hW
      exact (Nat.pow_le_pow_right (by norm_num) (cap_le hN hS hab)).trans f3
  have habs : ∀ (G : Fin K) (θ : Fin K → List Bool), WFQ β G θ →
      (mergedF pad K g F ((c, x), (G.1, List.ofFn θ))).natAbs ≤ 2 ^ (P * m + B * (m + m * m) * K) := by
    intro G θ hq
    rw [hentry G θ hq]
    have h : |(N.merge (chi hK0 x) [] []).toInst (mD K g F.toP c x β) (mdec K g F.toP c x) G θ| ≤
        2 ^ (P * m + B * (m + m * m) * K) := by
      simpa only [Fintype.card_fin] using Network.abs_toInst_le _ _ _ hSm G θ
    rw [Int.abs_eq_natAbs] at h
    exact_mod_cast h
  refine ⟨(List.replicate β (), tabulate pad K β fun q => mergedF pad K g F ((c, x), q)), ?_, ?_, by simpa using hβ3, ?_⟩
  · unfold rebalF
    rw [rng_eq f1, hfind, ← hβdef]
    rfl
  · unfold zval
    simp only [List.length_replicate]
    rw [Table.stT1 K β _ ((N.merge (chi hK0 x) [] []).toInst (mD K g F.toP c x β) (mdec K g F.toP c x))
      fun G θ hq => by rw [instOf, Table.stT2 pad K β _ f4 G θ hq, hentry G θ hq]]
    exact ZW_merged F.toP hK0 hN x β fun G G' hlt => by
      rw [lbLen_eq F.toP hK0 hN x hlt.ne]; exact hg2 _ _ hlt.ne
  · simp only [List.length_replicate]
    exact Table.stT3a pad K β β _ _ f4 hβ1 le_rfl habs

end PaddedDescent.F.RebalF
