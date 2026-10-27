/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import PaddedDescent.F.Interfaces
import PaddedDescent.F.LenList
import StepMachines.Prog.NetVal
import ToTuring.EncLemmas

/-! # One evaluation, and the count for one sparse formula

`stValF`: the top rebalancing, the descent through the levels and exhaustive search at the bottom
compute the value of every network with entries 0, 1, −1 that is
given by plain functions, if the pad is long enough. `stEval`: hence one evaluation, the sum over
the admissible profiles of the values of the networks of marks, is
the cut-off sum `Mark.trunc`. `stCountM`: hence the choice of the layers by the program is the
choice of the layers with exact evaluations, no cut-off by the pad
is active, and `countM` is the number of satisfying assignments. The hypotheses are interface
statements of `proof/rates/PaddedDescent/F/Interfaces.lean`. -/

namespace PaddedDescent.F.Eval

open Groundwork Groundwork.Prog Groundwork.Prog.NetE
open PaddedDescent.F.Mark (Cl trunc Good nSat occ placeAt placeE layersE Asked MCtx markF markN adm nProf cls WfL)

/-! ### The value of a network -/

/-- x ≤ lamG K g Ub₀ P if K³·x ≤ K³ + K·U + g·P' with U ≤ Ub₀ and P' ≤ P. -/
theorem le_lamG {K g x Uv Pv Ub₀ P : ℕ} (hK : 0 < K) (h : K ^ 3 * x ≤ K ^ 3 + K * Uv + g * Pv) (hU : Uv ≤ Ub₀) (hP : Pv ≤ P) :
    x ≤ lamG K g Ub₀ P := by
  unfold lamG
  rw [Nat.le_div_iff_mul_le (Nat.pow_pos hK), Nat.mul_comm]
  have h1 : K * Uv ≤ K * Ub₀ := Nat.mul_le_mul_left _ hU
  have h2 : g * Pv ≤ g * P := Nat.mul_le_mul_left _ hP
  omega

/-- `StValF` with the numbers K and g of nodes as free variables. -/
theorem val_core (hR : StR) (hD : StD) {C : Type} (F : FNet C) (c : C) (pad : U) (sched : List Lvl) (K g Ub₀ P : ℕ) (hg : g = 3 * K ^ 8)
    (N : Network (Fin g) (List Bool) (List Bool)) (hK : 2 ≤ K) (chain : Chain K sched) (col : K ^ g ≤ pad.length)
    (st : 2 ^ (P * (2 * g / K)) ≤ pad.length) (lab : 2 ^ P ≤ pad.length) (tab : 2 ^ ((K - 1) * lamG K g Ub₀ P) ≤ pad.length)
    (fits : Fits pad.length K (lamG K g Ub₀ P) (P * (2 * g / K)) 1 sched) (hN : F.toP.Presents c N 0 0) (hS : N.Sized P 0)
    (hU : N.U ≤ Ub₀) : ((rebalF pad K g F c).elim 0 fun I => ((descend pad sched I).map (bruteF pad 256)).sum) = N.value := by
  have hK0 : 0 < K := by omega
  have hβ : betaC K g F.toP c ≤ lamG K g Ub₀ P := by
    have h1 := Colouring.beta_le K g (Uc g F.toP c) (Pc g F.toP c)
    exact le_lamG hK0 h1 (by rw [Uc_eq F.toP hN]; exact hU) (Pc_le F.toP hN hS)
  obtain ⟨J, hJ, hz, hlen, hWF⟩ := hR _ pad K g F c N P 0 hK hg.ge hN hS col st lab
    ((Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left _ hβ)).trans tab)
  have hWF' : WF K (lamG K g Ub₀ P) (P * (2 * g / K)) J :=
    ⟨hWF.lam_pos, le_lamG hK0 hlen hU le_rfl, hWF.rows, hWF.row_len, by simpa using hWF.abs_le⟩
  rw [hJ]
  simp only [Option.elim]
  rw [hD pad sched K _ _ J chain fits hWF', hz]

/-- The number of nodes at the top. -/
theorem length_gU (Ku : U) : (gU Ku).length = 3 * Ku.length ^ 8 := by simp [gU]

/-- `valF` computes the value of every network that F presents, if its entries are 0, 1, −1 and the
pad is long enough. -/
public theorem stValF (hR : StR) (hD : StD) : StValF := by
  intro C F c pad S Ub₀ P N hT hN hS hU
  have hg := length_gU S.2
  unfold valF
  refine val_core hR hD F c pad S.1 S.2.length (gU S.2).length Ub₀ P hg N hT.two_le hT.chain ?_ ?_ hT.lab ?_ ?_ hN hS hU
  · rw [hg]; exact hT.col
  · rw [hg]; exact hT.st
  · rw [hg]; exact hT.tab
  · rw [hg]; exact hT.fits

/-! ### One evaluation -/

/-- A function of the members of a list, listed by position. -/
theorem map_range_getD {α β : Type} (l : List α) (d : α) (f : α → β) : (List.range l.length).map (fun i => f (l.getD i d)) = l.map f := by
  refine List.ext_getElem (by simp) fun i h1 h2 => ?_
  have hi : i < l.length := by simpa using h1
  simp [List.getElem?_eq_getElem hi]

/-- The list of all clauses with the index of their layer has as many members as the layers have
clauses. -/
theorem length_cls (Ls : List Fml) : (cls Ls).length = Ls.flatten.length := by
  have h := map_range_getD Ls [] List.length
  simp only [cls, List.length_flatMap, List.length_map, List.length_flatten]
  rw [h]

/-- The number of profile numbers grows with the number of clauses and of layers. -/
theorem nProf_le (g : ℕ) {M M' R R' : ℕ} (hM : M ≤ M') (hR : R ≤ R') : nProf g M R ≤ nProf g M' R' := by
  unfold nProf
  exact (Nat.pow_le_pow_left (by omega) _).trans (Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_left _ hR))

/-- One evaluation is exact if the pad is long enough. -/
public theorem stEval (hV : StValF) (hP : StMarkPresents) (hSum : StMarkSum) (hSz : StMarkSized) : StEval := by
  intro k pad S p Ls R₁ Δ m hNet hProf hb0 hb hm hW hocc hlen hR₁
  obtain ⟨nu, wu, βu, bu⟩ := p
  simp only at hNet hb0 hb hm hW ⊢
  have hg := length_gU S.2
  have hg0 : 0 < (gU S.2).length := by
    have : 0 < S.2.length ^ 8 := Nat.pow_pos (by have := hNet.two_le; omega)
    omega
  unfold evalF
  rw [sumF_eq ((nProf_le _ ((length_cls Ls).le.trans hlen) hR₁).trans (by rw [hg]; exact hProf)),
    ← hSum k (gU S.2) nu βu bu wu.length Ls hg0 hb0 hb hW]
  refine Finset.sum_congr rfl fun y _ => ?_
  cases hy : adm k (gU S.2).length nu.length wu.length Ls y with
  | false => simp
  | true =>
    obtain ⟨s1, s2⟩ := hSz k (gU S.2) nu βu bu wu.length Δ Ls y hg0 hb0 hb hW hocc (hlen.trans hm) hy
    have hUb : Ub k (gU S.2).length nu.length wu.length βu.length Ls.length ≤ Ub k (gU S.2).length nu.length wu.length βu.length R₁ :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 hR₁)
    rw [← hg] at hNet
    simpa using hV _ markF ((gU S.2, nu, βu, bu), (Ls, y)) pad S _ _ (markN (gU S.2).length ((gU S.2, nu, βu, bu), (Ls, y))) hNet
      (hP _) s1 (s2.trans hUb)

/-! ### The layers: their form does not depend on the evaluation function -/

/-- A list is its first i members, its member number i, and the rest. -/
theorem take_getD_drop {Ls : List Fml} {i : ℕ} (h : i < Ls.length) : Ls.take i ++ Ls.getD i [] :: Ls.drop (i + 1) = Ls := by
  rw [List.getD_eq_getElem _ _ h, ← List.drop_eq_getElem_cons h, List.take_append_drop]

/-- R + 1 layers that hold c clauses, all of 1 to k literals on variables below n. -/
structure Form (k n R c : ℕ) (Ls : List Fml) : Prop where
  layers : Ls.length = R + 1
  wf : WfL k n Ls
  card : Ls.flatten.length = c

/-- Adding a clause to a layer keeps the form. -/
theorem Form.placeAt {k n R c : ℕ} {Ls : List Fml} (h : Form k n R c Ls) {C : Cl} (hC : C ≠ [] ∧ C.length ≤ k ∧ ∀ l ∈ C, l.1 < n) {i : ℕ}
    (hi : i < Ls.length) : Form k n R (c + 1) (placeAt Ls C i) := by
  have e := take_getD_drop hi
  refine ⟨?_, ?_, ?_⟩
  · rw [← h.layers]
    conv_rhs => rw [← e]
    simp [Mark.placeAt]
  · intro L hL D hD
    have hmem : ∀ L' ∈ Ls.take i ++ Ls.getD i [] :: Ls.drop (i + 1), ∀ D ∈ L', D ≠ [] ∧ D.length ≤ k ∧ ∀ l ∈ D, l.1 < n := by
      rw [e]; exact h.wf
    simp only [Mark.placeAt, List.mem_append, List.mem_cons] at hL
    rcases hL with hL | rfl | hL
    · exact hmem L (by simp [hL]) D hD
    · rcases List.mem_cons.1 hD with rfl | hD
      · exact hC
      · exact hmem _ (by simp) D hD
    · exact hmem L (by simp [hL]) D hD
  · rw [← h.card]
    conv_rhs => rw [← e]
    simp [Mark.placeAt]
    omega

/-- Placing a clause keeps the form, whatever the evaluation function. -/
theorem Form.placeE {k n R c : ℕ} {Ls : List Fml} (h : Form k n R c Ls) (ev : List Fml → ℤ) (w : ℕ) {C : Cl}
    (hC : C ≠ [] ∧ C.length ≤ k ∧ ∀ l ∈ C, l.1 < n) : Form k n R (c + 1) (placeE ev w Ls C) := by
  refine h.placeAt hC ?_
  have hl := h.layers
  cases hf : (List.range (Ls.length - 1)).find? (Mark.dropE ev w Ls C) with
  | none => simp only [Option.getD_none]; omega
  | some i =>
    have := List.mem_range.1 (List.mem_of_find?_eq_some hf)
    simp only [Option.getD_some]
    omega

/-- The empty layers. -/
theorem form_replicate (k n R : ℕ) : Form k n R 0 (List.replicate (R + 1) []) := by
  refine ⟨by simp, ?_, by simp⟩
  intro L hL D hD
  rw [List.eq_of_mem_replicate hL] at hD
  simp at hD

/-- A bound on the length of the word of a literal with variable below n. -/
theorem len_lit_le {l : ℕ × Bool} {n : ℕ} (h : l.1 < n) : len l + 2 ≤ 3 * n + 5 := by
  have : l.1.size ≤ l.1 := Nat.size_le.2 Nat.lt_two_pow_self
  obtain ⟨a, b⟩ := l
  rw [len_pair, len_nat, len_bool]
  simp only at this h
  omega

/-- A bound on the length of the word of layers, by the number of their clauses. -/
theorem len_layers_le {k n : ℕ} (Ls : List Fml) (h : WfL k n Ls) : len Ls ≤ Ls.flatten.length * (k * (3 * n + 5) + 10) + 4 * Ls.length + 2 := by
  induction Ls with
  | nil => simp [len_nil]
  | cons L Ls ih =>
    have h1 := ih fun L' hL' => h L' (by simp [hL'])
    have h2 : len L ≤ L.length * (k * (3 * n + 5) + 10) + 2 := Lists.len_list_le L _ fun C hC => by
      have h3 := Lists.len_list_le' C (3 * n + 5) (h L (by simp) C hC).2.1 fun l hl => len_lit_le ((h L (by simp) C hC).2.2 l hl)
      omega
    rw [len_cons, List.flatten_cons, List.length_append, List.length_cons, Nat.add_mul]
    omega

/-- The word of layers of the given form fits under a pad of length layLen k n m R, if they hold at
most m clauses. -/
theorem Form.len_le {k n R c m : ℕ} {Ls : List Fml} (h : Form k n R c Ls) (hc : c ≤ m) : len Ls ≤ layLen k n m R := by
  have h1 := len_layers_le Ls h.wf
  rw [h.layers, h.card] at h1
  have h2 : c * (k * (3 * n + 5) + 10) ≤ m * (k * (3 * n + 5) + 10) := Nat.mul_le_mul_right _ hc
  unfold layLen
  omega

/-- No cut-off by the pad is active in the loop that places the clauses. -/
theorem foldl_cap_eq {k n R m : ℕ} {pad : U} (hpad : layLen k n m R ≤ pad.length) (ev : List Fml → ℤ) (w : ℕ) (ψ : Fml) :
    ∀ (Ls : List Fml) (c : ℕ), Form k n R c Ls → (∀ C ∈ ψ, C ≠ [] ∧ C.length ≤ k ∧ ∀ l ∈ C, l.1 < n) → c + ψ.length ≤ m →
      ψ.foldl (fun Ls C => cap pad [] (placeE ev w Ls C)) Ls = ψ.foldl (placeE ev w) Ls := by
  induction ψ with
  | nil => intros; rfl
  | cons C ψ ih =>
    intro Ls c hF hψ hc
    have hF' := hF.placeE ev w (hψ C (by simp))
    rw [List.length_cons] at hc
    rw [List.foldl_cons, List.foldl_cons, cap_eq ((hF'.len_le (by omega)).trans hpad)]
    exact ih _ (c + 1) hF' (fun D hD => hψ D (by simp [hD])) (by omega)

/-- The layers that the program chooses are those of the generic choice with the program's
evaluation function. -/
theorem layersF_eq {k n R m : ℕ} {pad : U} (hpad : layLen k n m R ≤ pad.length) (S : List Lvl × U) (p : U × U × U × U) (ψ : Fml)
    (hψ : ∀ C ∈ ψ, C ≠ [] ∧ C.length ≤ k ∧ ∀ l ∈ C, l.1 < n) (hm : ψ.length ≤ m) :
    layersF k pad S p R ψ = layersE (evalF k pad S p) p.2.1.length R ψ := by
  unfold layersF layersE
  rw [cap_eq (((form_replicate k n R).len_le (Nat.zero_le m)).trans hpad)]
  exact foldl_cap_eq hpad _ _ ψ _ 0 (form_replicate k n R) hψ (by omega)

/-! ### The count -/

/-- `countM k` counts the satisfying assignments of a formula with clauses of 1 to k literals, if
the pad is long enough. -/
public theorem stCountM (hE : StEval) (hL : StLayersE) : StCountM := by
  intro k pad S p R Δ m ψ hT hw hW hocc hm
  have hψ : ∀ C ∈ ψ, C ≠ [] ∧ C.length ≤ k ∧ ∀ l ∈ C, l.1 < p.1.length := hW ψ (by simp)
  unfold countM
  rw [layersF_eq hT.lay S p ψ hψ hm]
  refine hL p.1.length p.2.1.length R (evalF k pad S p) ψ hw.ge ?_ fun Ls hA => ?_
  · have h1 : 2 ^ R * ψ.length ≤ 2 ^ R * m := Nat.mul_le_mul_left _ hm
    have h2 := hT.last
    rw [hw]
    omega
  · obtain ⟨-, hA2, hA3⟩ := hA
    refine hE k pad S p Ls (R + 2) Δ m (by rw [hw]; exact hT.net) hT.prof hT.b_pos hT.b_le hT.m_le ?_ ?_ (hA3.length_le.trans hm) hA2
    · intro L hL' C hC
      exact hψ C (hA3.subset (List.mem_flatten.2 ⟨L, hL', hC⟩))
    · intro v
      exact ((hA3.filter _).length_le).trans (hocc v)

end PaddedDescent.F.Eval
