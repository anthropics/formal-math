/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Printed.GroupingEntry
public import QueryMachines.CombRuns
public import Eight.ViaGrouping.Main
import Mathlib.Tactic

/-! # Lemma 1 for the algorithm of its proof

Proof of Lemma 1, «Cost»: run the algorithm for (K, e) with L, B' in the roles of λ, B, which is
legitimate because Definition 4 covers all integer tables; answer each of its at most C·2^{eK²L}(B' +
L)^C queries by computing the entry; since K²L ≤ K² + U + gP/K and L ≤ 2gP, the bound follows.
The machine is `groupingMachine K g M` (proof/threesat/Printed/Programs.lean), for ANY machine M
that does what Definition 4 asks (`AchievedBy`). A query of Definition 2(iii) costs τ operations
throughout.
* `subst_within_of`: answering each query by computing the entry: if M takes T operations, a query
  counted as one, and each entry costs at most E operations, the whole costs at most T·(E + 2) (from
  `QueryMachines.StSubst`);
* `optBind_within`, `mapIn_within`: the search first, then the run; the search asks nothing;
* `bitsOut_le_Bp`: B' as a quotient of natural numbers and as the ceiling of a real number;
* `groupingMachine_computes`: the steps put together, for every g ≥ K for which the search finds a
  good grouping; the arithmetic is that of proof/networks/Eight/ViaGrouping/Main.lean
  (`Cost.bound_follows`, `Cost.base_le`);
* `stGroupingTiedOf`: g = 3K⁸. -/

public section

namespace Printed

open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Eight Eight.SecNetworks Eight.ViaGrouping QueryMachines QueryMachines.QueryMachine

/-! ## The three steps on machines -/

/-- **Answering each query by computing the entry.** M takes at most T operations, a query counted
as one; N answers each query within E operations at the prices w'. Then M with its queries answered
by N takes at most T·(E + 2) operations at the prices w'. -/
theorem subst_within_of (hSub : StSubst) {Q A Q' A' C α β : Type} [HasSize C] (M : QueryMachine Q A α β) (N : QueryMachine Q' A' (C × Q) A) (O : Q → Option A) (O' : Q' → Option A') (w' : Q' → ℕ)
    (c : C) (a : α) (T S S' E : ℕ) (b : β) (hM : M.Within O unitCost a T S b) (hN : ∀ x v, O x = some v → N.Within O' w' (c, x) E S' v) :
    (M.subst N).Within O' w' (c, a) (T * (E + 2)) (size c + S + S' + 1) b := by
  obtain ⟨own, L, hr, hle⟩ := hM
  rw [sum_map_unitCost] at hle
  have H : ∀ x : Q, ∃ (t : ℕ) (L' : List Q'), (∀ v, O x = some v → N.Runs O' (c, x) t L' S' v) ∧ t + (L'.map w').sum ≤ E := by
    intro x
    cases hx : O x with
    | none => exact ⟨0, [], fun v hv => (by cases hv), (by simp)⟩
    | some v =>
      obtain ⟨t, L', h1, h2⟩ := hN x v hx
      exact ⟨t, L', fun v' hv' => by
        obtain rfl := Option.some.inj hv'
        exact h1, h2⟩
  choose t L' hH using H
  refine ⟨_, _, hSub _ _ _ _ _ _ _ M N O O' c a own S S' L b t L' hr (fun x _ v hv => (hH x).1 v hv), ?_⟩
  have key : ∀ l : List Q, (l.map fun x => t x + 2).sum + ((l.flatMap L').map w').sum ≤ l.length * (E + 2) := by
    intro l
    induction l with
    | nil => simp
    | cons x l ih =>
      have := (hH x).2
      simp only [List.map_cons, List.sum_cons, List.flatMap_cons, List.map_append, List.sum_append, List.length_cons, Nat.succ_mul]
      omega
  have h3 : (own + L.length) * (E + 2) ≤ T * (E + 2) := Nat.mul_le_mul_right _ hle
  have h4 : own ≤ own * (E + 2) := Nat.le_mul_of_pos_right _ (by omega)
  have h5 := key L
  rw [Nat.add_mul] at h3
  omega

/-- A function applied to the input. -/
theorem mapIn_within {Q A α β γ : Type} {f : α → β} {M : QueryMachine Q A β γ} {O : Q → Option A} {w : Q → ℕ} {a : α} {T S : ℕ} {c : γ} (h : M.Within O w (f a) T S c) :
    (QueryMachine.mapIn f M).Within O w a T S c :=
  let ⟨own, L, hr, hle⟩ := h
  ⟨own, L, stMapInRuns _ _ _ _ _ f M O a own S L c hr, hle⟩

/-- First a step machine R, which asks nothing; if its result is some i, then N on (a, i). -/
theorem optBind_within {Q A α ι β : Type} [HasSize α] [HasSize β] {R : Stepped α (Option ι)} {N : QueryMachine Q A (α × ι) β} {dflt : α → β} {O : Q → Option A} {w : Q → ℕ} {a : α} {i : ι}
    {t T S S' : ℕ} {b : β} (h : R.Runs a t S (some i)) (h' : N.Within O w (a, i) T S' b) :
    (QueryMachine.optBind (QueryMachine.lift R) N dflt).Within O w a (t + 1 + T) (max (size a + S) (S' + 1) + 1) b := by
  obtain ⟨own, L, hr, hle⟩ := h'
  unfold QueryMachine.optBind
  refine ⟨t + 1 + own, [] ++ L, stBindRuns _ _ _ _ _ _ _ O a t own S (S' + 1) [] L (some i) b (stLiftRuns _ _ _ _ R O a t S _ h)
    ((stBranchRuns _ _ _ _ _ _ Stepped.optSel N _ O (a, some i) own S' L b).1 (a, i) rfl hr), ?_⟩
  simp only [List.nil_append]
  omega

/-! ## Arithmetic -/

/-- B' = ⌈2gP/K⌉ + g²B, written with a quotient of natural numbers, is at most the same written with
the ceiling of a real number (they are equal). -/
theorem bitsOut_le_Bp {K : ℕ} (hK0 : 0 < K) (g P B : ℕ) : bitsOut K g P B ≤ Cost.Bp K g P B := by
  unfold bitsOut Cost.Bp
  refine Nat.add_le_add_right ?_ _
  obtain ⟨n, hn⟩ : ∃ n : ℕ, n = ⌈2 * ((g : ℝ) * P) / K⌉₊ := ⟨_, rfl⟩
  rw [← hn]
  have h1 : 2 * ((g : ℝ) * P) / K ≤ n := hn ▸ Nat.le_ceil _
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK0
  rw [div_le_iff₀ hKr] at h1
  have h2 : 2 * (g * P) ≤ n * K := by exact_mod_cast h1
  exact Nat.lt_succ_iff.1 (Nat.div_lt_of_lt_mul (calc 2 * (g * P) + (K - 1) < n * K + K := by omega
    _ = K * (n + 1) := by ring))

/-- D·X + M·X^k + M'·X^k' ≤ c·X^c. -/
theorem poly_le_three {D M M' k k' c X : ℕ} (hX : 1 ≤ X) (hk : k ≤ c) (hk' : k' ≤ c) (h1 : 1 ≤ c) (hc : D + M + M' ≤ c) : D * X + M * X ^ k + M' * X ^ k' ≤ c * X ^ c :=
  calc D * X + M * X ^ k + M' * X ^ k' ≤ D * X ^ c + M * X ^ c + M' * X ^ c :=
        Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_left _ (Nat.le_self_pow (by omega) X)) (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hX hk))) (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hX hk'))
    _ = (D + M + M') * X ^ c := by ring
    _ ≤ c * X ^ c := Nat.mul_le_mul_right _ hc

/-! ## Lemma 1 -/

/-- The tables W̃ of the clique of the groups, as Definition 4 takes tables: a function of the
number of the node and of the setting. -/
@[expose] def groupTables {g K : ℕ} (N : Net g) (P B : ℕ) (hK0 : 0 < K) (x L : ℕ) : ℕ → List Bool → ℤ :=
  fun w z => if h : w < K then (Value.groupClique (asked.close (netOracle N)) (netInput N P B) N hK0 x L).W ⟨w, h⟩ z else 0

/-- The clique with these tables is the clique of the groups. -/
theorem clique_groupTables {g K : ℕ} (N : Net g) (P B : ℕ) (hK0 : 0 < K) (x L : ℕ) :
    (clique K L fun w => groupTables N P B hK0 x L w.val) = Value.groupClique (asked.close (netOracle N)) (netInput N P B) N hK0 x L :=
  congrArg (clique K L) (funext fun w => funext fun _ => dif_pos w.2)

/-- **Running the algorithm for (K, e) with L, B' in the roles of λ, B, and answering each query by
computing the entry**: for a good grouping number x, the machine M, given (L, B'), with its queries
answered by `tableQ`, outputs the value of the network within T_M·(E + 2) operations, where T_M ≤
C·2^{eK²L}(B' + L)^C and
E = c₁·2^{P⌊2g/K⌋}·τ is the cost of one entry. -/
theorem run_clique_within (hV : Value.StValueEqualsZ) (hSub : StSubst) {K g : ℕ} {e : ℝ} {M : CliqueMachine} {Cc c₁ : ℕ} (hK0 : 0 < K) (hg : 0 < g) (hM : AchievedBy M Cc K e)
    {N : Net g} {P B τ x : ℕ} (hN : N.Is P B) (hgood : Good N.c P (Paper.grouping hK0 x))
    (hE : ∀ (γ : Fin K), ∀ Θ ∈ words ((K - 1) * Paper.groupedLength K g N.U P),
      (tableQ K g asked).Within (netOracle N) (fun _ => τ) ((netInput N P B, x), toLists K (Paper.groupedLength K g N.U P) (γ.val, Θ)) (c₁ * 2 ^ (P * (2 * g / K)) * τ) (c₁ * (P + B) ^ c₁)
        ((Value.groupClique (asked.close (netOracle N)) (netInput N P B) N hK0 x (Paper.groupedLength K g N.U P)).W γ Θ) ∧
      |(Value.groupClique (asked.close (netOracle N)) (netInput N P B) N hK0 x (Paper.groupedLength K g N.U P)).W γ Θ| < 2 ^ bitsOut K g P B) :
    ∃ TM : ℕ, (QueryMachine.mapIn (fun cx : NetInput × ℕ => (cx, (unary (lamP K g asked.under cx), unary (bitsOut K g (asked.P cx.1) (asked.B cx.1)))))
        (M.subst (QueryMachine.mapIn (fun y : (NetInput × ℕ) × TableQuery => (y.1, toLists K (lamP K g asked.under y.1) y.2)) (tableQ K g asked)))).Within (netOracle N) (fun _ => τ) (netInput N P B, x)
          (TM * (c₁ * 2 ^ (P * (2 * g / K)) * τ + 2))
          (size (netInput N P B, x) + Cc * (bitsOut K g P B + Paper.groupedLength K g N.U P) ^ Cc + c₁ * (P + B) ^ c₁ + 1) N.value ∧
      (TM : ℝ) ≤ Cc * (2 : ℝ) ^ (e * (K : ℝ) ^ 2 * (Paper.groupedLength K g N.U P : ℝ)) * ((bitsOut K g P B : ℝ) + (Paper.groupedLength K g N.U P : ℝ)) ^ Cc := by
  have hnet := asked_isNetworkP N hN
  obtain ⟨L, hL⟩ : ∃ L : ℕ, L = Paper.groupedLength K g N.U P := ⟨_, rfl⟩
  rw [← hL] at hE ⊢
  have hlam : lamP K g asked.under (netInput N P B, x) = L := (lamP_eq hnet x).trans hL.symm
  have hL1 : 1 ≤ L := hL ▸ Colouring.one_le_beta _ _ _ _
  have hY : ∀ γ γ' : Fin K, γ ≠ γ' → Y N.c (Paper.grouping hK0 x) γ γ' ≤ L := fun γ γ' hne => hL ▸ Y_le_of_good hK0 hgood hne
  have hB1 : 1 ≤ bitsOut K g P B := by
    have : 1 ≤ g ^ 2 * B := Nat.mul_pos (pow_pos hg 2) hN.B_pos
    exact this.trans (Nat.le_add_left _ _)
  obtain ⟨TM, hrun, hTM⟩ := hM L (bitsOut K g P B) (groupTables N P B hK0 x L) hL1 hB1 fun w hw z hz => by
    unfold groupTables
    rw [dif_pos hw]
    exact (hE ⟨w, hw⟩ z hz).2
  rw [clique_groupTables, hV NetInput g K hK0 _ _ N P B 1 _ hnet x L hY] at hrun
  refine ⟨TM, mapIn_within ?_, hTM⟩
  change (M.subst _).Within _ _ ((netInput N P B, x), (unary (lamP K g asked.under (netInput N P B, x)), unary (bitsOut K g (unary P).length (unary B).length))) _ _ _
  rw [hlam, length_unary, length_unary]
  refine subst_within_of hSub M _ (tables K L (groupTables N P B hK0 x L)) (netOracle N) (fun _ => τ) (netInput N P B, x) _ TM _ _ _ _ hrun fun q v hq => mapIn_within ?_
  simp only [tables] at hq
  split_ifs at hq with hc
  obtain rfl := Option.some.inj hq
  change (tableQ K g asked).Within (netOracle N) (fun _ => τ) ((netInput N P B, x), toLists K (lamP K g asked.under (netInput N P B, x)) q) _ _ _
  rw [hlam]
  unfold groupTables
  rw [dif_pos hc.1]
  exact (hE ⟨q.1, hc.1⟩ q.2 (mem_words.2 hc.2)).1

/-- The bound of Lemma 1 for the algorithm of its proof, on networks on [g], for every g ≥ K for
which the search finds a good grouping (hypothesis `hS`; for g = 3K⁸ this is
`Eight.ViaGrouping.StSearch`). -/
theorem groupingMachine_computes (hStops : Exits.StSearchStops) (hE : StEntryCost) (hV : Value.StValueEqualsZ) (hSub : StSubst) {K g : ℕ} {e : ℝ} {M : CliqueMachine} {Cc : ℕ} (hK0 : 0 < K) (hg : 0 < g) (h0 : 0 ≤ e)
    (hM : AchievedBy M Cc K e)
    (hS : ∀ (N : Net g) (P B : ℕ), N.Is P B → ∃ x < K ^ g, (List.range (K ^ g)).find? (fun x => goodP K g (asked.close (netOracle N)) (netInput N P B, x)) = some x ∧ Good N.c P (Paper.grouping (g := g) hK0 x)) :
    ∃ C₁ : ℕ, ComputesNetworks (groupingMachine K g M) C₁ g K e := by
  -- the constants
  obtain ⟨c₁, hc₁⟩ := hE K g
  obtain ⟨A1, hA1⟩ := Cost.bound_follows (K := K) (g := g) Cc (c₁ + 2) (2 * K ^ g + 1) hK0 hg h0
  obtain ⟨D, hD⟩ : ∃ D, D = 4 * g ^ 2 + 6 * g + 6 := ⟨_, rfl⟩
  obtain ⟨sx, hsx⟩ : ∃ sx, sx = size (K ^ g) := ⟨_, rfl⟩
  obtain ⟨G, hG⟩ : ∃ G, G = 4 * g + g ^ 2 := ⟨_, rfl⟩
  obtain ⟨A2, hA2⟩ : ∃ A2, A2 = (5 * D + 5 * sx + 13) + Cc * G ^ Cc + c₁ + Cc := ⟨_, rfl⟩
  refine ⟨max A1 A2, fun N P B τ hN hτ => ?_⟩
  have hP := hN.P_pos
  have hU := U_le hN
  -- fix the first good grouping, number x
  obtain ⟨x, hxlt, hfind, hgood⟩ := hS N P B hN
  have hsearch : (Exits.search K g asked.under).Runs (netInput N P B) (2 * (x + 1)) (4 * (size (netInput N P B) + size (K ^ g)) + 10) (some x) :=
    hStops K g NetInput (asked.close (netOracle N)) (netInput N P B) x hfind
  -- the cost of one entry; the run of the algorithm for (K, e)
  have hLle : Paper.groupedLength K g N.U P ≤ 2 * (g * P) := L_le hK0 hg hP hU
  obtain ⟨TM, hrun, hTM⟩ := run_clique_within hV hSub hK0 hg hM hN hgood
    (hc₁ hK0 hg N P B τ hN hτ x hxlt _ hLle hgood.G1 fun γ γ' hne => Y_le_of_good hK0 hgood hne)
  have hall := optBind_within (dflt := zeroOf) hsearch hrun
  obtain ⟨n, hn⟩ : ∃ n, n = 2 ^ (P * (2 * g / K)) := ⟨_, rfl⟩
  rw [← hn] at hall
  have hn1 : 1 ≤ n := hn ▸ Nat.one_le_two_pow
  have hBB := bitsOut_le_Bp hK0 g P B
  refine ⟨2 * (x + 1) + 1 + TM * (c₁ * n * τ + 2), hall.mono le_rfl ?_, ?_⟩
  · -- the sizes of the states
    have hs := size_netInput_le N hN
    rw [← hD] at hs
    have hbase := Cost.base_le N.U P B hK0 hg hP hU
    rw [← hG] at hbase
    obtain ⟨X, hX⟩ : ∃ X, X = P + B := ⟨_, rfl⟩
    rw [← hX] at hs hbase ⊢
    have hX1 : 1 ≤ X := by omega
    have hx : size x ≤ sx := by
      rw [hsx]
      simp only [size_nat]
      exact Nat.succ_le_succ (Nat.size_le_size hxlt.le)
    have a2 : Cc * (bitsOut K g P B + Paper.groupedLength K g N.U P) ^ Cc ≤ Cc * G ^ Cc * X ^ Cc := by
      rw [Nat.mul_assoc, ← Nat.mul_pow]
      exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
    have a3 : (5 * D + 5 * sx + 13) * X = 5 * (D * X) + (5 * sx + 13) * X := by ring
    have a4 : (5 * sx + 13) * 1 ≤ (5 * sx + 13) * X := Nat.mul_le_mul_left _ hX1
    have a5 := poly_le_three (D := 5 * D + 5 * sx + 13) (M := Cc * G ^ Cc) (M' := c₁) (k := Cc) (k' := c₁) (c := A2) hX1 (by omega) (by omega) (by omega) (by omega)
    have a6 : A2 * X ^ A2 ≤ max A1 A2 * X ^ max A1 A2 := Nat.mul_le_mul (le_max_right _ _) (Nat.pow_le_pow_right hX1 (le_max_right _ _))
    have e : size (netInput N P B, x) = size (netInput N P B) + size x := rfl
    rw [e, ← hsx]
    generalize size (netInput N P B) = sc at hs ⊢
    omega
  · -- the bound follows
    have hTE : ((TM * ((c₁ + 2) * 2 ^ (P * (2 * g / K)) * τ) : ℕ) : ℝ) ≤ Cc * (2 : ℝ) ^ (e * (K : ℝ) ^ 2 * (Paper.groupedLength K g N.U P : ℝ)) *
        ((Cost.Bp K g P B : ℝ) + (Paper.groupedLength K g N.U P : ℝ)) ^ Cc * (((c₁ + 2) * 2 ^ (P * (2 * g / K)) * τ : ℕ) : ℝ) := by
      rw [Nat.cast_mul]
      refine mul_le_mul_of_nonneg_right (hTM.trans ?_) (Nat.cast_nonneg _)
      have hBB' : (bitsOut K g P B : ℝ) ≤ (Cost.Bp K g P B : ℝ) := by exact_mod_cast hBB
      gcongr
    have hT : 2 * (x + 1) + 1 + TM * (c₁ * n * τ + 2) ≤ 2 * K ^ g + 1 + TM * ((c₁ + 2) * 2 ^ (P * (2 * g / K)) * τ) := by
      rw [← hn]
      have b1 : c₁ * n * τ + 2 ≤ (c₁ + 2) * n * τ := by
        have : (c₁ + 2) * n * τ = c₁ * n * τ + 2 * (n * τ) := by ring
        have : 1 ≤ n * τ := Nat.mul_pos hn1 hτ
        omega
      have b2 := Nat.mul_le_mul_left TM b1
      omega
    have hfin := hA1 P B τ N.U _ _ hP hτ hU hTE hT
    rw [exponent_eq] at hfin
    refine hfin.trans ?_
    have hY : (1 : ℝ) ≤ (P : ℝ) + B := by exact_mod_cast (by omega : 1 ≤ P + B)
    have hAm : (A1 : ℝ) ≤ ((max A1 A2 : ℕ) : ℝ) := by exact_mod_cast le_max_left _ _
    have hYp : ((P : ℝ) + B) ^ A1 ≤ ((P : ℝ) + B) ^ (max A1 A2) := pow_le_pow_right₀ hY (le_max_left _ _)
    gcongr

/-- **Lemma 1 for the algorithm of its proof, from ANY machine that does what Definition 4 asks**,
with the steps of the proof in its hypotheses. -/
theorem stGroupingTiedOf : StGroupingTiedOf := fun hS hStops hE hV hSub K _ _ _ hK h0 hM =>
  groupingMachine_computes hStops hE hV hSub (by omega) (by positivity) h0 hM fun N P B hN => hS K hK NetInput _ _ N P B 1 _ (asked_isNetworkP N hN)

end Printed
