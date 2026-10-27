/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import VariableBound.Net.Tests
public import VariableBound.Net.SizeB
import PaddedDescent.F.MarkDeg
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! # Step 3, «The parameters»

«At most Δ⌈n/g⌉ clauses have a variable at a; each gives z_a one mark of kind 0 and load(E) ≤ t̄ + 2
marks of kind 1; the checks with home a give at most ⌈r̄/g⌉·s̄ more. So z_a has at most P₀ bits.
An object has at most two tests at a, and ⌈log C(t, μ)⌉ ≤ t, so condition (i) of the definition of a
network holds with P = ⌈2P₀⌉.» One theorem for each of these sentences, then the network of a
profile
has size P (`sized_netDN`, `sized_PD`), and with the bound on |W_a| of
proof/variables/VariableBound/Net/SizeB.lean the statement `StSized`. Display (69) is proved in
SizeB.lean, the case m ≤ n̄ in SizeSmall.lean. Some counting lemmas come from
proof/rates/PaddedDescent/F/MarkDeg.lean. -/

public section

namespace VariableBound.Net.SizeP

open Groundwork Groundwork.Prog Finset
open PaddedDescent.F.Mark (Cl qv WfL occ)

variable {k g n Δ : ℕ} {D : Dat}

/-! ### The number of objects that touch a node -/

/-- A clause with a variable among a·q, …, a·q + q − 1 is counted at one of these variables (0 < q). -/
theorem countP_block_le {q : ℕ} (hq : 0 < q) (a : ℕ) (L : Fml) :
    L.countP (fun C => C.any fun l => l.1 / q == a) ≤ ∑ r ∈ range q, L.countP fun C => C.any fun l => l.1 == a * q + r := by
  induction L with
  | nil => simp
  | cons C L ih =>
    simp only [List.countP_cons, sum_add_distrib]
    refine Nat.add_le_add ih ?_
    by_cases h : (C.any fun l => l.1 / q == a) = true
    · obtain ⟨l, hl, hla⟩ := List.any_eq_true.1 h
      have hla' : l.1 / q = a := by simpa using hla
      have hr : l.1 % q ∈ range q := mem_range.2 (Nat.mod_lt _ hq)
      have h1 : (C.any fun l' => l'.1 == a * q + l.1 % q) = true :=
        List.any_eq_true.2 ⟨l, hl, by rw [← hla', Nat.div_add_mod']; simp⟩
      rw [if_pos h]
      refine le_trans ?_ (single_le_sum (f := fun r => if (C.any fun l' => l'.1 == a * q + r) = true then 1 else 0)
        (fun _ _ => Nat.zero_le _) hr)
      simp only [h1, if_true, le_refl]
    · rw [if_neg h]; exact Nat.zero_le _

/-- Step 3, «The parameters»: «at most Δ⌈n/g⌉ clauses have a variable at a», if 0 < g, the data are
well-formed (`WfD`) and every variable occurs in at most Δ clauses. -/
theorem card_clauses_at_le (hg : 0 < g) (hW : WfD k n D) (hΔ : ∀ v, (occ D.1 v).length ≤ Δ) (a : ℕ) :
    #((range D.1.length).filter fun e => ∃ l ∈ D.1.getD e [], l.1 / qv g n = a) ≤ qv g n * Δ := by
  have e1 : #((range D.1.length).filter fun e => ∃ l ∈ D.1.getD e [], l.1 / qv g n = a) = D.1.countP fun C => C.any fun l => l.1 / qv g n == a := by
    rw [← PaddedDescent.F.Mark.Deg.length_filter_range D.1 [] fun C => C.any fun l => l.1 / qv g n == a, Tests.length_filter_eq_card]
    congr 1
    ext e
    simp
  rw [e1]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h0 : D.1 = [] := by
      rw [List.eq_nil_iff_forall_not_mem]
      intro C hC
      obtain ⟨hne, -, hlt⟩ := hW.1 D.1 (by simp) C hC
      obtain ⟨l, hl⟩ := List.exists_mem_of_ne_nil C hne
      exact absurd (hlt l hl) (Nat.not_lt_zero _)
    rw [h0]
    simp
  · have hq : 0 < qv g n := Nat.div_pos (by omega) hg
    refine (countP_block_le hq a _).trans ?_
    refine (sum_le_card_nsmul _ _ Δ fun r _ => ?_).trans (by simp)
    refine le_trans ?_ (hΔ (a * qv g n + r))
    rw [occ, ← List.countP_eq_length_filter]

/-- load(E) as the number of the checks j < r that contain the clause number e. -/
theorem colD_eq (e : ℕ) : colD D e = #((range D.2.length).filter fun j => e ∈ D.2.getD j []) := by
  rw [colD, ← List.countP_eq_length_filter, ← PaddedDescent.F.Mark.Deg.length_filter_range D.2 [] fun L => L.contains e, Tests.length_filter_eq_card]
  congr 1
  ext j
  simp

/-- Step 3, «The parameters»: a clause E «gives one mark of kind 0 and load(E) marks of kind 1»: at
most 1 + load(E) objects have the clause number e (for well-formed data, `WfD`). -/
theorem card_objs_of_clause_le (hW : WfD k n D) (e : ℕ) : #((range (objs D).length).filter fun o => (obAt D o).2.1 = e) ≤ 1 + colD D e := by
  classical
  rw [colD_eq]
  have h := card_le_card_of_injOn (s := (range (objs D).length).filter fun o => (obAt D o).2.1 = e)
    (t := insert (0, 0) (((range D.2.length).filter fun j => e ∈ D.2.getD j []).image fun j => (1, j)))
    (fun o => ((obAt D o).1, (obAt D o).2.2)) ?_ ?_
  · refine h.trans ((card_insert_le _ _).trans ?_)
    have := card_image_le (s := (range D.2.length).filter fun j => e ∈ D.2.getD j []) (f := fun j => ((1 : ℕ), j))
    omega
  · intro o ho
    obtain ⟨ho1, ho2⟩ := mem_filter.1 (mem_coe.1 ho)
    rcases Basic.mem_objs.1 (Basic.obAt_mem (mem_range.1 ho1)) with ⟨h0, -, h2⟩ | ⟨h1, hj, he⟩
    · exact mem_coe.2 (mem_insert.2 (Or.inl (Prod.ext h0 h2)))
    · refine mem_coe.2 (mem_insert_of_mem (mem_image.2 ⟨(obAt D o).2.2, mem_filter.2 ⟨mem_range.2 hj, ho2 ▸ he⟩, Prod.ext h1.symm rfl⟩))
  · intro o ho o' ho' heq
    obtain ⟨ho1, ho2⟩ := mem_filter.1 (mem_coe.1 ho)
    obtain ⟨ho1', ho2'⟩ := mem_filter.1 (mem_coe.1 ho')
    simp only [Prod.mk.injEq] at heq
    exact Basic.obAt_inj hW (mem_range.1 ho1) (mem_range.1 ho1') (Prod.ext heq.1 (Prod.ext (ho2.trans ho2'.symm) heq.2))

/-- The objects whose clause has a variable at a: at most Δ⌈n/g⌉·(1 + c), if 0 < g, the data are
well-formed (`WfD`), every variable occurs in at most Δ clauses and load(E) ≤ c for every clause. -/
theorem card_var_at_le (hg : 0 < g) (hW : WfD k n D) (hΔ : ∀ v, (occ D.1 v).length ≤ Δ) {c : ℕ} (hc : ∀ e < D.1.length, colD D e ≤ c) (a : ℕ) :
    #((range (objs D).length).filter fun o => ∃ l ∈ clOf D o, l.1 / qv g n = a) ≤ qv g n * Δ * (1 + c) := by
  have h := card_le_mul_card_image_of_maps_to (s := (range (objs D).length).filter fun o => ∃ l ∈ clOf D o, l.1 / qv g n = a)
    (t := (range D.1.length).filter fun e => ∃ l ∈ D.1.getD e [], l.1 / qv g n = a) (f := fun o => (obAt D o).2.1) ?_ (1 + c) ?_
  · calc _ ≤ (1 + c) * _ := h
      _ ≤ (1 + c) * (qv g n * Δ) := Nat.mul_le_mul_left _ (card_clauses_at_le hg hW hΔ a)
      _ = qv g n * Δ * (1 + c) := Nat.mul_comm _ _
  · intro o ho
    obtain ⟨ho1, ho2⟩ := mem_filter.1 ho
    exact mem_filter.2 ⟨mem_range.2 (Basic.cl_lt hW (mem_range.1 ho1)), ho2⟩
  · intro e he
    have h1 := hc e (mem_range.1 (mem_filter.1 he).1)
    refine (card_le_card ?_).trans ((card_objs_of_clause_le hW e).trans (by omega))
    intro o ho
    obtain ⟨ho1, ho2⟩ := mem_filter.1 ho
    exact mem_filter.2 ⟨(mem_filter.1 ho1).1, ho2⟩

/-- The incidences of the checks with home a: at most the sum of the sizes of these checks (for
well-formed data, `WfD`). -/
theorem card_home_at_le (hW : WfD k n D) (a : ℕ) :
    #((range (objs D).length).filter fun o => (obAt D o).1 = 1 ∧ home g (obAt D o).2.2 = a) ≤
      ∑ j ∈ (range D.2.length).filter (fun j => home g j = a), (D.2.getD j []).length := by
  classical
  rw [card_eq_sum_card_fiberwise (f := fun o => (obAt D o).2.2) (t := (range D.2.length).filter fun j => home g j = a)]
  · refine sum_le_sum fun j _ => ?_
    refine (card_le_card_of_injOn (t := (D.2.getD j []).toFinset) (fun o => (obAt D o).2.1) ?_ ?_).trans (List.toFinset_card_le _)
    · intro o ho
      obtain ⟨ho1, ho2⟩ := mem_filter.1 (mem_coe.1 ho)
      obtain ⟨ho3, ho4⟩ := mem_filter.1 ho1
      exact mem_coe.2 (List.mem_toFinset.2 (ho2 ▸ (Basic.inc_mem (mem_range.1 ho3) ho4.1).2))
    · intro o ho o' ho' heq
      obtain ⟨ho1, ho2⟩ := mem_filter.1 (mem_coe.1 ho)
      obtain ⟨ho3, ho4⟩ := mem_filter.1 ho1
      obtain ⟨ho1', ho2'⟩ := mem_filter.1 (mem_coe.1 ho')
      obtain ⟨ho3', ho4'⟩ := mem_filter.1 ho1'
      exact Basic.obAt_inj hW (mem_range.1 ho3) (mem_range.1 ho3') (Prod.ext (ho4.1.trans ho4'.1.symm) (Prod.ext heq (ho2.trans ho2'.symm)))
  · intro o ho
    obtain ⟨ho1, ho2⟩ := mem_filter.1 (mem_coe.1 ho)
    exact mem_coe.2 (mem_filter.2 ⟨mem_range.2 (Basic.inc_mem (mem_range.1 ho1) ho2.1).1, ho2.2⟩)

/-- The number of objects that touch a: at most Δ⌈n/g⌉·(1 + c) plus the sizes of the checks with
home a, if 0 < g, the data are well-formed (`WfD`), every variable occurs in at most Δ clauses and
load(E) ≤ c for every clause. -/
theorem length_tch_le (hg : 0 < g) (hW : WfD k n D) (hΔ : ∀ v, (occ D.1 v).length ≤ Δ) {c : ℕ} (hc : ∀ e < D.1.length, colD D e ≤ c) (a : ℕ) :
    (tch g n D a).length ≤ qv g n * Δ * (1 + c) + ∑ j ∈ (range D.2.length).filter (fun j => home g j = a), (D.2.getD j []).length := by
  classical
  rw [tch, Tests.length_filter_eq_card]
  refine (card_le_card (t := ((range (objs D).length).filter fun o => ∃ l ∈ clOf D o, l.1 / qv g n = a) ∪
    ((range (objs D).length).filter fun o => (obAt D o).1 = 1 ∧ home g (obAt D o).2.2 = a)) ?_).trans
    ((card_union_le _ _).trans (Nat.add_le_add (card_var_at_le hg hW hΔ hc a) (card_home_at_le hW a)))
  intro o ho
  obtain ⟨ho1, ho2⟩ := mem_filter.1 ho
  rcases Basic.tchB_iff.1 ho2 with h | h
  · exact mem_union_left _ (mem_filter.2 ⟨ho1, h⟩)
  · exact mem_union_right _ (mem_filter.2 ⟨ho1, h⟩)

/-- r ≤ ⌈r/g⌉·g for 0 < g. -/
theorem le_qv_mul (hg : 0 < g) (r : ℕ) : r ≤ qv g r * g := by
  have h1 := Nat.div_add_mod (r + g - 1) g
  have h2 := Nat.mod_lt (r + g - 1) hg
  unfold qv
  rw [Nat.mul_comm]
  omega

/-- At most ⌈r/g⌉ of the checks j < r have the home a (0 < g). -/
theorem card_home_le (hg : 0 < g) (r a : ℕ) : #((range r).filter fun j => home g j = a) ≤ qv g r := by
  rw [← card_range (qv g r)]
  refine card_le_card_of_injOn (fun j => j / g) ?_ ?_
  · intro j hj
    have h1 := mem_range.1 (mem_filter.1 (mem_coe.1 hj)).1
    exact mem_coe.2 (mem_range.2 ((Nat.div_lt_iff_lt_mul hg).2 (h1.trans_le (le_qv_mul hg r))))
  · intro j hj j' hj' heq
    have h1 : j % g = a := (mem_filter.1 (mem_coe.1 hj)).2
    have h2 : j' % g = a := (mem_filter.1 (mem_coe.1 hj')).2
    have h3 : j / g = j' / g := heq
    rw [← Nat.div_add_mod j g, ← Nat.div_add_mod j' g, h1, h2, h3]

/-- ⌈r/g⌉ grows with r. -/
theorem qv_mono {r r' : ℕ} (h : r ≤ r') : qv g r ≤ qv g r' := Nat.div_le_div_right (by omega)

/-! ### The size of the network of a profile -/

/-- Step 3, «The parameters»: ⌈log C(t, μ)⌉ ≤ t. -/
theorem cw_le (t μ : ℕ) : cw t μ ≤ t := Nat.clog_le_of_le_pow (Nat.choose_le_two_pow t μ)

/-- The capacities at a node a < g sum to at most twice the number of objects that touch a: «an
object has at most two tests at a, and ⌈log C(t, μ)⌉ ≤ t». -/
theorem sum_capD_le (y : ℕ) {a : ℕ} (ha : a < g) : ∑ b ∈ (range g).erase a, capD g n D y a b ≤ 2 * (tch g n D a).length := by
  refine le_trans (sum_le_sum fun b _ => ?_) (Tests.sum_length_tst_node_le ha)
  rw [Tests.capD_eq]
  exact sum_le_sum fun κ _ => cw_le _ _

/-- A number that is 0 or 1 is at most 1 in absolute value. -/
theorem abs_boole_le (p : Prop) [Decidable p] : |if p then (1 : ℤ) else 0| ≤ 1 := by
  split_ifs <;> simp

/-- 1 ≤ 2^B in the integers. -/
theorem one_le_two_pow (B : ℕ) : (1 : ℤ) ≤ 2 ^ B := one_le_pow₀ (by norm_num)

/-- The network of the profile y has size P with values bounded by 2^B, if at every node a < g the
number ⌈n/g⌉ + (number of objects that touch a) of bits of a setting is at most P, twice the number
of
objects that touch a is at most P, and |W_a| ≤ 2^B. -/
theorem sized_netDN {P B y : ℕ} {fl : Bool} (h1 : ∀ a < g, qv g n + (tch g n D a).length ≤ P) (h2 : ∀ a < g, 2 * (tch g n D a).length ≤ P)
    (h3 : ∀ a < g, ∀ z, |WD g n D y fl a z| ≤ 2 ^ B) : (netDN g (ctx g n D y fl)).Sized P B where
  card_S a := by
    simp only [netDN, netD, ctx, Tests.length_rep, card_words]
    exact Nat.pow_le_pow_right (by norm_num) (h1 a a.2)
  c_symm a b := by
    simp only [netDN, netD, ctx, Tests.length_rep]
    exact Tests.capD_comm _ _ _
  sum_c a := by
    simp only [netDN, netD, ctx, Tests.length_rep]
    rw [Tests.sum_erase_fin a fun b => capD g n D y a.val b]
    exact (sum_capD_le y a.2).trans (h2 a a.2)
  card_lab a b _ := by
    simp only [Network.lab, netDN, netD, ctx, Tests.length_rep, card_words]
    refine Nat.pow_le_pow_right (by norm_num) (le_of_eq ?_)
    rcases le_total a b with hab | hab
    · rw [min_eq_left hab, max_eq_right hab]
    · rw [min_eq_right hab, max_eq_left hab, Tests.capD_comm]
  abs_W a z := by
    simp only [netDN, netD, ctx, Tests.length_rep]
    exact h3 a a.2 z
  abs_f a b z θ := by
    simp only [netDN, netD]
    exact (abs_boole_le _).trans (one_le_two_pow B)
  abs_Ψ a b z z' _ := by
    simp only [Network.Ψ, netDN, netD]
    refine le_trans ?_ (one_le_two_pow B)
    have e : ∀ (L L' θ : List Bool), ((if (L == θ) = true then (1 : ℤ) else 0) * if (L' == θ) = true then 1 else 0) =
        if θ = L ∧ θ = L' then 1 else 0 := by
      intro L L' θ
      by_cases h1 : θ = L
      · by_cases h2 : θ = L'
        · subst h1; simp [← h2]
        · have h2' : ¬ L' = θ := fun h => h2 h.symm
          simp [h2, h2']
      · have h1' : ¬ L = θ := fun h => h1 h.symm
        simp [h1, h1']
    simp only [e]
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one, abs_of_nonneg (Nat.cast_nonneg _)]
    refine Nat.cast_le_one.2 (card_le_one.2 fun θ hθ θ' hθ' => ?_)
    exact ((mem_filter.1 hθ).2.1).trans ((mem_filter.1 hθ').2.1).symm

/-! ### P₀ and P -/

/-- Step 3, «The parameters»: «the checks with home a give at most ⌈r̄/g⌉·s̄ more», if 0 < g, 0 ≤
s̄, r ≤ r̄ and |Λ_j| ≤ s̄ for all j. -/
theorem sum_home_le (hg : 0 < g) {rb : ℕ} {sb : ℚ} (hsb : 0 ≤ sb) (hr : D.2.length ≤ rb) (hs : ∀ L ∈ D.2, (L.length : ℚ) ≤ sb) (a : ℕ) :
    ((∑ j ∈ (range D.2.length).filter (fun j => home g j = a), (D.2.getD j []).length : ℕ) : ℚ) ≤ (qv g rb : ℚ) * sb := by
  push_cast
  calc ∑ j ∈ (range D.2.length).filter (fun j => home g j = a), ((D.2.getD j []).length : ℚ)
      ≤ ∑ _j ∈ (range D.2.length).filter (fun j => home g j = a), sb :=
        sum_le_sum fun j hj => hs _ (Basic.getD_mem (mem_range.1 (mem_filter.1 hj).1))
    _ = (#((range D.2.length).filter fun j => home g j = a) : ℚ) * sb := by rw [sum_const, nsmul_eq_mul]
    _ ≤ (qv g rb : ℚ) * sb := by
        refine mul_le_mul_of_nonneg_right ?_ hsb
        exact_mod_cast (card_home_le hg _ a).trans (qv_mono hr)

/-- Step 3, «The parameters»: «so z_a has at most P₀ bits», if 0 < g, 0 ≤ s̄, the data are
well-formed (`WfD`), every variable occurs in at most Δ clauses, r ≤ r̄, |Λ_j| ≤ s̄ for all j and
load(E) ≤ t̄ + 2 for
every clause. -/
theorem bits_le_P0 (hg : 0 < g) {tb rb : ℕ} {sb : ℚ} (hsb : 0 ≤ sb) (hW : WfD k n D) (hΔ : ∀ v, (occ D.1 v).length ≤ Δ) (hr : D.2.length ≤ rb)
    (hs : ∀ L ∈ D.2, (L.length : ℚ) ≤ sb) (hc : ∀ e < D.1.length, colD D e ≤ tb + 2) (a : ℕ) :
    ((qv g n + (tch g n D a).length : ℕ) : ℚ) ≤ P0 g n Δ tb rb sb := by
  have h1 : ((tch g n D a).length : ℚ) ≤
      ((qv g n * Δ * (1 + (tb + 2)) + ∑ j ∈ (range D.2.length).filter (fun j => home g j = a), (D.2.getD j []).length : ℕ) : ℚ) := by
    exact_mod_cast length_tch_le hg hW hΔ hc a
  have h2 := sum_home_le hg hsb hr hs a
  rw [Nat.cast_add] at h1
  unfold P0
  push_cast at h1 h2 ⊢
  nlinarith [h1, h2]

/-- A natural number that is at most 2P₀ is at most P = ⌈2P₀⌉. -/
theorem le_PD {tb rb x : ℕ} {sb : ℚ} (h : (x : ℚ) ≤ 2 * P0 g n Δ tb rb sb) : x ≤ PD g n Δ tb rb sb := by
  have h1 : (x : ℚ) ≤ (PD g n Δ tb rb sb : ℚ) := h.trans (Nat.le_ceil _)
  exact_mod_cast h1

/-- Step 3, «The parameters»: the network of a profile has size P = ⌈2P₀⌉ with values bounded by
2^B, if |W_a| ≤ 2^B at every node a < g, and 0 < g, 0 ≤ s̄, the data are well-formed (`WfD`), every
variable
occurs in at most Δ clauses, r ≤ r̄, |Λ_j| ≤ s̄ for all j and load(E) ≤ t̄ + 2 for every clause. -/
theorem sized_PD (hg : 0 < g) {tb rb B y : ℕ} {sb : ℚ} {fl : Bool} (hsb : 0 ≤ sb) (hW : WfD k n D) (hΔ : ∀ v, (occ D.1 v).length ≤ Δ) (hr : D.2.length ≤ rb)
    (hs : ∀ L ∈ D.2, (L.length : ℚ) ≤ sb) (hc : ∀ e < D.1.length, colD D e ≤ tb + 2) (h3 : ∀ a < g, ∀ z, |WD g n D y fl a z| ≤ 2 ^ B) :
    (netDN g (ctx g n D y fl)).Sized (PD g n Δ tb rb sb) B := by
  refine sized_netDN (fun a _ => le_PD ?_) (fun a _ => le_PD ?_) h3
  · have h := bits_le_P0 hg hsb hW hΔ hr hs hc a
    have h0 : (0 : ℚ) ≤ ((qv g n + (tch g n D a).length : ℕ) : ℚ) := Nat.cast_nonneg _
    linarith
  · have h := bits_le_P0 hg hsb hW hΔ hr hs hc a
    push_cast at h ⊢
    have h0 : (0 : ℚ) ≤ (qv g n : ℚ) := Nat.cast_nonneg _
    linarith

/-- Step 3, «The parameters»: for a list with display (67), the network of an admissible profile
satisfies conditions (i) and (ii) of the definition of a network with P = ⌈2P₀⌉ and B = (k + 1)M + 1.
Hypotheses: 0 < g, 0 ≤ s̄, the data are well-formed (`WfD`), every variable occurs in at most Δ
clauses, r ≤ r̄, |Λ_j| ≤ s̄ for all j, load(E) ≤ t̄ + 2 for every clause, and the profile is
admissible. -/
theorem stSized : StSized := fun _ _ _ _ _ _ _ _ _ _ _ _ hg hsb hW hΔ hr hs hc hadm =>
  sized_PD hg hsb hW hΔ hr hs hc fun _ ha z => SizeB.abs_WD_le hg hW hadm ha z

end VariableBound.Net.SizeP
