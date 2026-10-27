/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Eight.ViaGrouping.Defs
public import Eight.SecNetworks_Grouping
import Mathlib.Tactic

/-! # Proof of Lemma 1, «The algorithm», first three sentences: the search for a good grouping

«Being good depends only on the numbers c_{a,b}. Go through all K^g groupings (a constant) and fix
the first good one. Let L = max{1, ⌊(U + gP/K)/K²⌋}, so that Y_{γ,γ'} ≤ L.»
* `goodP_iff`: on a network in the sense of Definition 2 the test `goodP` of the program says yes to
  the number x exactly if the grouping number x is good as printed (`SecNetworks.Good`: (G1) at most
  2g/K nodes in a group, (G2) with the given P).
* `exists_goodP`: for g = 3K⁸ the test says yes to some x < K^g. The good grouping comes from the
  paragraph «A good grouping exists» (`SecNetworks.groupingFacts`,
  proof/networks/Eight/SecNetworks_Grouping.lean).
* `stSearch : StSearch`: so the first x < K^g to which the test says yes exists, and the grouping
  number x is good.
* `lamP_eq`, `Y_le_of_good`: the number `lamP` of the program is L; «so that Y_{γ,γ'} ≤ L».
* `searchP_runs`: the search takes 2·K^g steps (one step for a test, one to go on), on states of
  size at most 4·(size of the context + size of K^g) + 10. So the search through the groupings is
  counted: «(a constant)».

Different from the paper: one test of a grouping counts as one step of the step machine; the search
runs through all K^g numbers and keeps the first good one. -/

public section

namespace Eight.ViaGrouping

open Groundwork Groundwork.Prog Groundwork.Prog.NetE Finset Stepped Eight.SecNetworks

variable {C : Type} [HasSize C] {Np : Procs C} {c : C} {g K : ℕ} {N : Net g} {P B τ S : ℕ}

/-! ## The numbers of the program are the numbers of the network -/

/-- The procedures `Np.toPaperNetwork` present the network `N.toPaperNetwork`; that the algorithm of
Definition 2 (iii) receives B is not needed for this. From `SecNetworks.presents_toPaperNetwork`,
applied to Np with the number B put in. -/
theorem presentsP (h : IsNetworkP Np c N P B τ S) : Np.toPaperNetwork.Presents c N.toPaperNetwork (2 * τ + 1) (S + (size c + 2 * size g + 4 * P + 6)) :=
  presents_toPaperNetwork (Np := { Np with B := fun _ => B }) (c := c) (N := N) (P := P) (B := B) (τ := τ) (S := S)
    ⟨h.is, h.τ_pos, ⟨h.given.P_eq, rfl, h.given.len_eq, h.given.cap_eq, h.given.mem_runs, h.given.W_runs, h.given.Ψ_runs, h.given.f_runs⟩⟩

/-- The sum of the given numbers c_{a,b} that the program forms is the total U. -/
theorem Uc_eq_U (h : IsNetworkP Np c N P B τ S) : Uc g Np.toPaperNetwork c = N.U := Uc_eq _ (presentsP h)

/-- The number of bits between two groups that the program forms is Y_{γ,γ'}. -/
theorem lbLen_eq_Y (hK0 : 0 < K) (h : IsNetworkP Np c N P B τ S) (x : ℕ) {γ γ' : Fin K} (hne : γ ≠ γ') :
    lbLen K g Np.toPaperNetwork c x γ.val γ'.val = Y N.c (Paper.grouping hK0 x) γ γ' := by
  rw [lbLen_eq _ hK0 (presentsP h) x hne, Groundwork.Network.merge_c]
  rfl

/-- «Being good depends only on the numbers c_{a,b}»: the test of the program says yes to x exactly
if the grouping number x is good as printed, with (G1) as printed and with the given P in (G2). -/
theorem goodP_iff (hK0 : 0 < K) (h : IsNetworkP Np c N P B τ S) (x : ℕ) : goodP K g Np (c, x) = true ↔ Good N.c P (Paper.grouping hK0 x) := by
  simp only [goodP, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq]
  rw [Uc_eq_U h, h.given.P_eq]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun γ => ?_, fun γ γ' hne => ?_⟩
    · have := h1 γ.val γ.2
      rwa [length_members hK0 x γ] at this
    · rw [← lbLen_eq_Y hK0 h x hne]
      exact (h2 γ.val γ.2 γ'.val γ'.2).resolve_left fun e => hne (Fin.ext e)
  · rintro ⟨h1, h2⟩
    refine ⟨fun G hG => ?_, fun G hG G' hG' => ?_⟩
    · rw [length_members hK0 x ⟨G, hG⟩]
      exact h1 _
    · by_cases e : G = G'
      · exact .inl e
      · right
        have hne : (⟨G, hG⟩ : Fin K) ≠ ⟨G', hG'⟩ := fun e' => e (congrArg Fin.val e')
        have := h2 _ _ hne
        rwa [← lbLen_eq_Y hK0 h x hne] at this

/-! ## The first good grouping -/

/-- Every grouping has a number below K^g: its values are the digits in base K. -/
theorem grouping_number (hK0 : 0 < K) (χ : Fin g → Fin K) : ∃ x < K ^ g, Paper.grouping hK0 x = χ := by
  refine ⟨(finFunctionFinEquiv χ).val, (finFunctionFinEquiv χ).2, ?_⟩
  funext a
  have := congrFun (finFunctionFinEquiv.symm_apply_apply χ) a
  rw [← this]
  rfl

/-- For g = 3K⁸ the test says yes to some number below K^g: «a good grouping exists»
(`SecNetworks.groupingFacts`), from c_{a,b} = c_{b,a} and (i) of Definition 2. -/
theorem exists_goodP (hK : 2 ≤ K) {N : Net (3 * K ^ 8)} (h : IsNetworkP Np c N P B τ S) : ∃ x < K ^ (3 * K ^ 8), goodP K (3 * K ^ 8) Np (c, x) = true := by
  have hK0 : 0 < K := by omega
  obtain ⟨χ, hχ⟩ := groupingFacts.exists_good K P N.c hK h.is.c_symm h.is.i
  obtain ⟨x, hx, rfl⟩ := grouping_number hK0 χ
  exact ⟨x, hx, (goodP_iff hK0 h x).2 hχ⟩

/-- **«Go through all K^g groupings and fix the first good one.»** For g = 3K⁸ there is a first
number x < K^g to which the test says yes, and the grouping number x is good as printed. -/
theorem stSearch : StSearch := by
  intro K hK C _ Np c N P B τ S h
  obtain ⟨x', hx', hgood'⟩ := exists_goodP hK h
  obtain ⟨x, hfind⟩ : ∃ x, (List.range (K ^ (3 * K ^ 8))).find? (fun x => goodP K (3 * K ^ 8) Np (c, x)) = some x := by
    rw [← Option.isSome_iff_exists, List.find?_isSome]
    exact ⟨x', List.mem_range.2 hx', hgood'⟩
  have hgood : goodP K (3 * K ^ 8) Np (c, x) = true := List.find?_some (p := fun x => goodP K (3 * K ^ 8) Np (c, x)) hfind
  exact ⟨x, List.mem_range.1 (List.mem_of_find?_eq_some hfind), hfind, (goodP_iff _ h x).1 hgood⟩

/-! ## The number L -/

/-- The number that the program passes to the algorithm for cliques is L = max{1, ⌊(U + gP/K)/K²⌋},
written max{1, ⌊(KU + gP)/K³⌋}. -/
theorem lamP_eq (h : IsNetworkP Np c N P B τ S) (x : ℕ) : lamP K g Np (c, x) = Paper.groupedLength K g N.U P := by
  unfold lamP
  rw [Uc_eq_U h, h.given.P_eq]

/-- «… so that Y_{γ,γ'} ≤ L», for a good grouping. -/
theorem Y_le_of_good (hK0 : 0 < K) {χ : Fin g → Fin K} (hχ : Good N.c P χ) {γ γ' : Fin K} (hne : γ ≠ γ') : Y N.c χ γ γ' ≤ Paper.groupedLength K g N.U P :=
  Colouring.le_beta hK0 (hχ.G2 γ γ' hne)

/-! ## The run of the search -/

/-- The search, for any procedures and any context: 2·K^g steps, on states of size at most 4·(size
of c + size of K^g) + 10; the result is the first x < K^g to which the test says yes, if there is
one. Both bounds but for the size of c depend on K and g only: «(a constant)». -/
theorem searchP_runs (K g : ℕ) (Np : Procs C) (c : C) :
    (searchP K g Np).Runs c (2 * K ^ g) (4 * (size c + size (K ^ g)) + 10) ((List.range (K ^ g)).find? fun x => goodP K g Np (c, x)) := by
  have := firstRange_runs (N := nCol K g) (M := ofFun (goodP K g Np)) (p := id) (a := c) (fun _ => 1) (fun x => goodP K g Np (c, x)) (size c + size (K ^ g) + 1)
    (fun y hy => (ofFun_runs (goodP K g Np) (c, y)).mono le_rfl (by
      have := Nat.size_le_size (Nat.le_of_lt hy)
      simp only [nCol] at this
      simp only [size_prod, size_nat, size_bool]
      omega))
  refine this.mono ?_ ?_
  · simp [nCol]; omega
  · simp only [nCol]; omega

end Eight.ViaGrouping
