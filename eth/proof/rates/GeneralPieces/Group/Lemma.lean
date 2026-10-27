/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import AppRunningTimeStatement
public import GeneralPieces.Group.CaseI
public import GeneralPieces.Group.CaseII
public import PaddedDescent.F.RebalG
public import PaddedDescent.Col.CertG
public import Mathlib.Algebra.Order.Floor.Ring

/-! # Lemma 8 (the grouping lemma with explicit cost): a good grouping, and the program that uses it

The order of the proof of Lemma 8 in Appendix A. First "some grouping has at most 2g/K nodes in
every group and Y ≤ L for all γ ≠ γ'" (`someGrouping`): case (i) is `GeneralPieces.caseI`, the
argument of the proof of Lemma 1, case (ii) is
`GeneralPieces.stCaseII`. Then the algorithm: the program `rebalG` goes through the K^g groupings,
takes the first that passes its test and writes out the tables of the (K, L)-clique.

What differs. The test of the program asks for fewer than 2g/K nodes in every group, where the paper
has "at most"; both proofs of existence give the strict bound (`exists_grouping_lt`).
The bound |W̃_γ| ≤ 2^{B'} with B' = ⌈2gP/K⌉ + g²B is proved as in the paper, "a sum of at most
2^{2gP/K} terms, each a product of at most g² values" (`abs_toInst_merge_le`); values are bounded by
2^B and 2^{B'} with "at most" throughout this development, where the paper has "below". -/

public section

namespace GeneralPieces.Group

open Finset Groundwork

/-! ### Some grouping is good -/

/-- "Some grouping has at most 2g/K nodes in every group and Y ≤ L for all γ ≠ γ'", in both cases,
with fewer than 2g/K nodes in every group. Here P = 0 is allowed: then no two nodes share a bit. -/
theorem exists_grouping_lt (K g : ℕ) (ζ : ℝ) (P : ℕ) (c : Fin g → Fin g → ℕ) (hK : 2 ≤ K) (hg : 2 ≤ g) (hζ0 : 0 < ζ) (hζ1 : ζ ≤ 1)
    (hs : ∀ a b, c a b = c b a) (hP : ∀ a, ∑ b ∈ univ.erase a, c a b ≤ P) (h : AppRunningTime.Cases K g ζ P c) :
    ∃ χ : Fin g → Fin K, (∀ γ, K * #{a | χ a = γ} < 2 * g) ∧
      ∀ γ γ', γ ≠ γ' → ∑ a with χ a = γ, ∑ b with χ b = γ', c a b ≤ AppRunningTime.Lof K g ζ P (∑ a, ∑ b ∈ univ.erase a, c a b) := by
  have key : ∃ χ : Fin g → Fin K, (∀ γ, K * #{a | χ a = γ} < 2 * g) ∧
      ∀ γ γ', γ ≠ γ' → (∑ a with χ a = γ, ∑ b with χ b = γ', (c a b : ℝ)) ≤
        ((∑ a, ∑ b ∈ univ.erase a, (c a b : ℝ)) + 2 * ζ * g * P) / (K : ℝ) ^ 2 := by
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
    · exact caseI K g c P ζ hK h1 h2 hs fun a => by exact_mod_cast hP a
    · rcases Nat.eq_zero_or_pos P with rfl | hP1
      · have hc0 : ∀ a b, a ≠ b → c a b = 0 := fun a b hab =>
          Finset.sum_eq_zero_iff.1 (Nat.le_zero.1 (hP a)) b (Finset.mem_erase.2 ⟨hab.symm, mem_univ b⟩)
        have hg0 : (0 : ℝ) < g := by exact_mod_cast (by omega : 0 < g)
        obtain ⟨χ, a1, -⟩ := stCaseII K g c 1 ζ hK hg h1 hζ0 hζ1 one_pos
          (fun a => by
            rw [Finset.sum_eq_zero fun b hb => by rw [hc0 a b (Finset.ne_of_mem_erase hb).symm, Nat.cast_zero]]
            exact zero_le_one)
          (fun a b hab => by rw [hc0 a b hab, Nat.cast_zero]; positivity) h3
        refine ⟨χ, fun γ => by rw [a1, Nat.mul_div_cancel' h1]; omega, fun γ γ' hne => ?_⟩
        rw [Finset.sum_eq_zero fun a ha => Finset.sum_eq_zero fun b hb => by
          have hab : a ≠ b := fun e => hne (by rw [← (Finset.mem_filter.1 ha).2, ← (Finset.mem_filter.1 hb).2, e])
          rw [hc0 a b hab, Nat.cast_zero]]
        positivity
      · obtain ⟨χ, a1, a2⟩ := stCaseII K g c P ζ hK hg h1 hζ0 hζ1 (by exact_mod_cast hP1) (fun a => by exact_mod_cast hP a) h2 h3
        refine ⟨χ, fun γ => ?_, fun γ γ' hne => (a2 γ γ' hne).le⟩
        rw [a1, Nat.mul_div_cancel' h1]
        omega
  obtain ⟨χ, a1, a2⟩ := key
  refine ⟨χ, a1, fun γ γ' hne => ?_⟩
  have := (a2 γ γ' hne).trans (Nat.le_ceil _)
  unfold AppRunningTime.Lof
  push_cast
  exact_mod_cast this

/-! ### The size of an entry -/

variable {J J' σ τ A : Type*}

/-- "Each a product of at most g² values": the nodes of a group, the pairs of nodes inside it, and
the pairs of one node inside and one outside, are at most g² in all. -/
theorem card_values_le [Fintype J] [LinearOrder J] [Fintype J'] [DecidableEq J'] (χ : J → J') (G : J') :
    #{a | χ a = G} + #{p ∈ pairs J | χ p.1 = G ∧ χ p.2 = G} + ∑ G' ∈ univ.erase G, #{p : J × J | χ p.1 = G ∧ χ p.2 = G'} ≤ Fintype.card J ^ 2 := by
  have hA : #{a | χ a = G} ≤ #{p : J × J | p.1 = p.2 ∧ χ p.1 = G} :=
    Finset.card_le_card_of_injOn (fun a => (a, a)) (by intro a ha; simpa using ha) (by intro a _ b _ e; exact (Prod.mk.inj e).1)
  have hB : #{p ∈ pairs J | χ p.1 = G ∧ χ p.2 = G} = #{p : J × J | p.1 < p.2 ∧ χ p.1 = G ∧ χ p.2 = G} := by
    rw [pairs, Finset.filter_filter]
  have hC : ∑ G' ∈ univ.erase G, #{p : J × J | χ p.1 = G ∧ χ p.2 = G'} = #{p : J × J | χ p.1 = G ∧ χ p.2 ≠ G} := by
    rw [Finset.card_eq_sum_card_fiberwise (f := fun p : J × J => χ p.2) (t := univ.erase G) (by intro p hp; simp at hp ⊢; exact hp.2)]
    refine Finset.sum_congr rfl fun G' hG' => ?_
    have hne : G' ≠ G := by simpa using hG'
    rw [Finset.filter_filter]
    congr 1
    ext p
    simp only [mem_filter, mem_univ, true_and]
    grind
  rw [hB, hC]
  calc _ ≤ #{p : J × J | p.1 = p.2 ∧ χ p.1 = G} + #{p : J × J | p.1 < p.2 ∧ χ p.1 = G ∧ χ p.2 = G} + #{p : J × J | χ p.1 = G ∧ χ p.2 ≠ G} := by omega
    _ = ∑ p : J × J, ((if p.1 = p.2 ∧ χ p.1 = G then 1 else 0) + (if p.1 < p.2 ∧ χ p.1 = G ∧ χ p.2 = G then 1 else 0) +
          (if χ p.1 = G ∧ χ p.2 ≠ G then 1 else 0)) := by simp only [Finset.card_filter, Finset.sum_add_distrib]
    _ ≤ ∑ _p : J × J, 1 := Finset.sum_le_sum fun p _ => by split_ifs <;> first | omega | (exfalso; grind)
    _ = Fintype.card J ^ 2 := by simp [sq]

/-- "The sum defining W̃_γ(Θ) has at most (2^P)^{2g/K} = 2^{2gP/K} terms, each a product of at most
g² values": if every group has at most m nodes, an entry of a table of the clique is at most
2^{Pm + g²B} in absolute value. -/
theorem abs_toInst_merge_le [Fintype J] [LinearOrder J] [Fintype J'] [LinearOrder J'] [DecidableEq A] (N : Network J σ τ) (χ : J → J') (s₀ : σ) (t₀ : τ)
    (D : J' → J' → Finset A) (dec : J' → J' → A → (J × J → τ)) {P B m : ℕ} (h : N.Sized P B) (hm : ∀ G, #{a | χ a = G} ≤ m) (G : J') (θ : J' → A) :
    |(N.merge χ s₀ t₀).toInst D dec G θ| ≤ 2 ^ (P * m + B * Fintype.card J ^ 2) := by
  have hSh := Network.merge_shaped N χ s₀ t₀ h.toShaped hm
  unfold Network.toInst
  have h1 : ∀ z, |(N.merge χ s₀ t₀).W G z * ∏ b ∈ univ.erase G, if θ b ∈ D (min G b) (max G b) then
      (N.merge χ s₀ t₀).f G b z (dec (min G b) (max G b) (θ b)) else 0| ≤ 2 ^ (B * Fintype.card J ^ 2) := by
    intro z
    have w1 : |(N.merge χ s₀ t₀).W G z| ≤ 2 ^ (B * #{a | χ a = G}) * 2 ^ (B * #{p ∈ pairs J | χ p.1 = G ∧ χ p.2 = G}) := by
      simp only [Network.merge]
      rw [abs_mul]
      refine mul_le_mul (abs_prod_le_two_pow _ _ (fun a _ => h.abs_W a _) le_rfl)
        (abs_prod_le_two_pow _ _ (fun p hp => h.abs_Ψ _ _ _ _ ?_) le_rfl) (abs_nonneg _) (pow_nonneg (by norm_num) _)
      have : p.1 < p.2 := by simpa [pairs] using (Finset.mem_filter.1 hp).1
      exact this.ne
    have w2 : |∏ b ∈ univ.erase G, if θ b ∈ D (min G b) (max G b) then
        (N.merge χ s₀ t₀).f G b z (dec (min G b) (max G b) (θ b)) else 0| ≤ 2 ^ (B * ∑ G' ∈ univ.erase G, #{p : J × J | χ p.1 = G ∧ χ p.2 = G'}) := by
      rw [Finset.abs_prod, Finset.mul_sum, ← Finset.prod_pow_eq_pow_sum]
      refine Finset.prod_le_prod (fun _ _ => abs_nonneg _) fun b _ => ?_
      split_ifs
      · simp only [Network.merge]
        exact abs_prod_le_two_pow _ _ (fun p _ => h.abs_f _ _ _ _) le_rfl
      · simp
    calc _ = |(N.merge χ s₀ t₀).W G z| * |∏ b ∈ univ.erase G, if θ b ∈ D (min G b) (max G b) then
          (N.merge χ s₀ t₀).f G b z (dec (min G b) (max G b) (θ b)) else 0| := abs_mul _ _
      _ ≤ 2 ^ (B * #{a | χ a = G}) * 2 ^ (B * #{p ∈ pairs J | χ p.1 = G ∧ χ p.2 = G}) *
          2 ^ (B * ∑ G' ∈ univ.erase G, #{p : J × J | χ p.1 = G ∧ χ p.2 = G'}) := mul_le_mul w1 w2 (abs_nonneg _) (by positivity)
      _ = 2 ^ (B * (#{a | χ a = G} + #{p ∈ pairs J | χ p.1 = G ∧ χ p.2 = G} + ∑ G' ∈ univ.erase G, #{p : J × J | χ p.1 = G ∧ χ p.2 = G'})) := by
          rw [← pow_add, ← pow_add, ← mul_add, ← mul_add]
      _ ≤ 2 ^ (B * Fintype.card J ^ 2) := pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_left _ (card_values_le χ G))
  calc _ ≤ ∑ z ∈ (N.merge χ s₀ t₀).S G, |(N.merge χ s₀ t₀).W G z * ∏ b ∈ univ.erase G, if θ b ∈ D (min G b) (max G b) then
      (N.merge χ s₀ t₀).f G b z (dec (min G b) (max G b) (θ b)) else 0| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ z ∈ (N.merge χ s₀ t₀).S G, (2 : ℤ) ^ (B * Fintype.card J ^ 2) := Finset.sum_le_sum fun z _ => h1 z
    _ = (#((N.merge χ s₀ t₀).S G) : ℤ) * 2 ^ (B * Fintype.card J ^ 2) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 2 ^ (P * m) * 2 ^ (B * Fintype.card J ^ 2) := by
          refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg (by norm_num) _)
          exact_mod_cast hSh.card_S G
    _ = 2 ^ (P * m + B * Fintype.card J ^ 2) := (pow_add _ _ _).symm

/-! ### The algorithm -/

open Groundwork.Prog Groundwork.Prog.NetE PaddedDescent.F PaddedDescent.F.RebalF PaddedDescent.Col

/-- "Find the first such grouping among all K^g, define the (K, L)-clique with the tables W̃_γ,
whose value is that of the network": if some grouping passes the test for the label length β and the
pad
is long enough, `rebalG` returns the clique on K nodes with labels of β bits, written out, with the
value of the network and entries of absolute value at most 2^{P·⌊2g/K⌋ + g²B}. This is
`PaddedDescent.F.RebalF.rebalG_spec` with the paper's bound on the entries. -/
theorem rebalG_spec' {C : Type} (pad : U) (K g β : ℕ) (F : FNet C) (c : C) (N : Network (Fin g) (List Bool) (List Bool)) (P B : ℕ)
    (hK : 2 ≤ K) (hg0 : 0 < g) (hβ1 : 1 ≤ β) (hN : F.toP.Presents c N 0 0) (hS : N.Sized P B)
    (hex : ∃ x < K ^ g, goodG K g F.toP β (c, x) = true)
    (f1 : K ^ g ≤ pad.length) (f2 : 2 ^ (P * (2 * g / K)) ≤ pad.length) (f3 : 2 ^ P ≤ pad.length)
    (f4 : 2 ^ ((K - 1) * β) ≤ pad.length) :
    ∃ J, rebalG pad K g β F c = some J ∧ zval K J = N.value ∧ J.1.length = β ∧ WF K β (P * (2 * g / K) + B * g ^ 2) J := by
  have hK0 : 0 < K := by omega
  obtain ⟨x', hx', hgood'⟩ := hex
  obtain ⟨x, hfind⟩ : ∃ x, (List.range (K ^ g)).find? (fun x => goodG K g F.toP β (c, x)) = some x := by
    rw [← Option.isSome_iff_exists, List.find?_isSome]
    exact ⟨x', List.mem_range.2 hx', hgood'⟩
  have hgood : goodG K g F.toP β (c, x) = true := List.find?_some (p := fun x => goodG K g F.toP β (c, x)) hfind
  obtain ⟨hg1, hg2⟩ := (goodG_iff F.toP hK0 hN β x).1 hgood
  obtain ⟨m, hmdef⟩ : ∃ m, m = 2 * g / K := ⟨_, rfl⟩
  rw [← hmdef] at f2 ⊢
  have hm : ∀ G, #{a : Fin g | chi hK0 x a = G} ≤ m := fun G => by
    rw [hmdef, Nat.le_div_iff_mul_le hK0, Nat.mul_comm]
    exact (hg1 G).le
  have hm' : ∀ G < K, (members K g x G).length ≤ m := fun G hG => by
    rw [length_members hK0 x ⟨G, hG⟩]; exact hm _
  have hβ' : ∀ G < K, ∀ G' < K, G ≠ G' → lbLen K g F.toP c x G G' ≤ β := fun G hG G' hG' hne => by
    have hne' : (⟨G, hG⟩ : Fin K) ≠ ⟨G', hG'⟩ := fun e => hne (congrArg Fin.val e)
    rw [lbLen_eq F.toP hK0 hN x hne']
    exact hg2 _ _ hne'
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
      (mergedF pad K g F ((c, x), (G.1, List.ofFn θ))).natAbs ≤ 2 ^ (P * m + B * g ^ 2) := by
    intro G θ hq
    rw [hentry G θ hq]
    have h : |(N.merge (chi hK0 x) [] []).toInst (mD K g F.toP c x β) (mdec K g F.toP c x) G θ| ≤ 2 ^ (P * m + B * g ^ 2) := by
      simpa only [Fintype.card_fin] using abs_toInst_merge_le N (chi hK0 x) [] [] _ _ hS hm G θ
    rw [Int.abs_eq_natAbs] at h
    exact_mod_cast h
  refine ⟨(List.replicate β (), tabulate pad K β fun q => mergedF pad K g F ((c, x), q)), ?_, ?_, by simp, ?_⟩
  · unfold rebalG
    rw [rng_eq f1, hfind]
    rfl
  · unfold zval
    simp only [List.length_replicate]
    rw [Table.stT1 K β _ ((N.merge (chi hK0 x) [] []).toInst (mD K g F.toP c x β) (mdec K g F.toP c x))
      fun G θ hq => by rw [instOf, Table.stT2 pad K β _ f4 G θ hq, hentry G θ hq]]
    exact ZW_merged F.toP hK0 hN x β fun G G' hlt => by
      rw [lbLen_eq F.toP hK0 hN x hlt.ne]; exact hg2 _ _ hlt.ne
  · exact Table.stT3a pad K β β _ _ f4 hβ1 le_rfl habs

/-- A grouping χ is the number x < K^g whose digits are its values; if χ has fewer than 2g/K nodes
in every group and Y ≤ β for any two groups, x passes the test of the program. -/
theorem goodG_of_grouping {C : Type} {K g β : ℕ} (Np : PNet C) {c : C} {N : Network (Fin g) (List Bool) (List Bool)} {t S : ℕ} (hK : 0 < K)
    (hN : Np.Presents c N t S) (χ : Fin g → Fin K) (h1 : ∀ γ, K * #{a | χ a = γ} < 2 * g)
    (h2 : ∀ γ γ', γ ≠ γ' → ∑ a with χ a = γ, ∑ b with χ b = γ', N.c a b ≤ β) : ∃ x < K ^ g, goodG K g Np β (c, x) = true := by
  have hχ : chi hK (finFunctionFinEquiv χ).val = χ := by
    funext a
    have := congrFun (finFunctionFinEquiv.symm_apply_apply χ) a
    rw [← this]
    rfl
  refine ⟨(finFunctionFinEquiv χ).val, (finFunctionFinEquiv χ).2, (goodG_iff Np hK hN β _).2 ?_⟩
  rw [hχ]
  exact ⟨h1, fun G G' hne => by rw [Network.merge_c]; exact h2 G G' hne⟩

/-- P·⌊2g/K⌋ + g²B ≤ B' = ⌈2gP/K⌉ + g²B. -/
theorem le_B'of (K g P B : ℕ) (hK : 0 < K) : P * (2 * g / K) + B * g ^ 2 ≤ AppRunningTime.B'of K g P B := by
  unfold AppRunningTime.B'of
  have h1 : P * (2 * g / K) ≤ (2 * g * P + K - 1) / K := by
    rw [Nat.le_div_iff_mul_le hK]
    calc P * (2 * g / K) * K = P * (2 * g / K * K) := by ring
      _ ≤ P * (2 * g) := Nat.mul_le_mul_left _ (Nat.div_mul_le_self _ _)
      _ ≤ 2 * g * P + K - 1 := by rw [Nat.mul_comm]; omega
  rw [Nat.mul_comm B]
  omega

end GeneralPieces.Group

namespace GeneralPieces

open Finset Groundwork PaddedDescent.F ClauseBound.Alg GeneralPieces.Group

/-- The first step of the proof of Lemma 8: "Some grouping has at most 2g/K nodes in every group and
Y ≤ L for all γ ≠ γ'." -/
theorem someGrouping : AppRunningTime.SomeGrouping := by
  intro K g ζ P c hK hg hζ0 hζ1 hP1 hs hP h
  obtain ⟨χ, h1, h2⟩ := exists_grouping_lt K g ζ P c hK hg hζ0 hζ1 hs hP h
  exact ⟨χ, fun γ => (h1 γ).le, h2⟩

/-- An instance whose entries are at most 2^B in absolute value has entries at most 2^{B'} for every
B' ≥ B. -/
theorem wfe_mono {K lam B B' : ℕ} {J : PInst} (h : WFe K lam B J) (hB : B ≤ B') : WFe K lam B' J :=
  ⟨⟨h.1.lam_pos, h.1.lam_le, h.1.rows, h.1.row_len, fun r hr z hz => (h.1.abs_le r hr z hz).trans (Nat.pow_le_pow_right (by norm_num) hB)⟩, h.2⟩

/-- Lemma 8 in the form in which the recursion and the top levels call it: in case (i) or (ii), for
every label length β ≥ L (in the recursion "the number L depends on ι";
the programs use one label length for all ι, an upper bound), `rebalG` returns the (K, β)-clique
with the value of the network. Two bounds hold for its entries: the paper's B' = ⌈2gP/K⌉ + g²B, and
P·G + B·(G + G²)·K with G = ⌊2g/K⌋, which is the smaller one once 4g/K + 2 < g and is the one that
the programs compute with. In place of P ≥ 1 only β ≥ 1 is needed. -/
theorem grouping_general (C : Type) (F : FNet C) (x : C) (K g : ℕ) (ζ : ℝ) (N : Network (Fin g) (List Bool) (List Bool)) (P B β : ℕ) (pad : U)
    (hK : 2 ≤ K) (hg : 2 ≤ g) (hζ0 : 0 < ζ) (hζ1 : ζ ≤ 1) (hN : F.toP.Presents x N 0 0) (hS : N.Sized P B) (hcase : AppRunningTime.Cases K g ζ P N.c)
    (hβ : AppRunningTime.Lof K g ζ P N.U ≤ β) (hβ1 : 1 ≤ β) (f1 : K ^ g ≤ pad.length) (f2 : 2 ^ (P * (2 * g / K)) ≤ pad.length) (f3 : 2 ^ P ≤ pad.length)
    (f4 : 2 ^ ((K - 1) * β) ≤ pad.length) :
    ∃ J, rebalG pad K g β F x = some J ∧ zval K J = N.value ∧
      WFe K β (min (AppRunningTime.B'of K g P B) (P * (2 * g / K) + B * (2 * g / K + 2 * g / K * (2 * g / K)) * K)) J := by
  obtain ⟨χ, h1, h2⟩ := exists_grouping_lt K g ζ P N.c hK hg hζ0 hζ1 hS.c_symm hS.sum_c hcase
  have hex := goodG_of_grouping F.toP (by omega) hN χ h1 fun γ γ' hne => (h2 γ γ' hne).trans hβ
  obtain ⟨J, a1, a2, a3, a4⟩ := rebalG_spec' pad K g β F x N P B hK (by omega) hβ1 hN hS hex f1 f2 f3 f4
  obtain ⟨J', b1, -, -, b4⟩ := RebalF.rebalG_spec pad K g β F x N P B hK (by omega) hβ1 hN hS hex f1 f2 f3 f4
  obtain rfl : J = J' := Option.some.inj (a1.symm.trans b1)
  refine ⟨J, a1, a2, ⟨a4.lam_pos, a4.lam_le, a4.rows, a4.row_len, fun r hr z hz => ?_⟩, a3⟩
  rcases le_total (AppRunningTime.B'of K g P B) (P * (2 * g / K) + B * (2 * g / K + 2 * g / K * (2 * g / K)) * K) with h | h
  · rw [min_eq_left h]
    exact (a4.abs_le r hr z hz).trans (Nat.pow_le_pow_right (by norm_num) (le_B'of K g P B (by omega)))
  · rw [min_eq_right h]
    exact b4.abs_le r hr z hz

end GeneralPieces
