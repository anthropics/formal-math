/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec4.Theorem30.Preprocessing
public import ThreeSumApsp.Programs.Sec4.Theorem30.ThinLayout
public import ThreeSumApsp.Programs.Sec4.Theorem30.WordSize

/-!
# Theorem 30 on the word RAM: the two main procedures for the trusted layout

The trusted layout of the input, the one in the statement of the theorem (`ThinPair.input`), is N,
D, m, L, t, X, Y (`Layout`, `layout_input`). The main procedure of the preprocessing reads the sizes
and calls preCore with the block of the data structure right behind the input (`preMain_meets`); the
main procedure of a query reads N and D, computes the address of the block and calls queryAt
(`queryMain_meets`); between them the memory satisfies `DS`. `Meets.main` and
`AnswersQueries.of_meets` pass from the procedures to the outermost statement.

Time, space and the nesting of calls are within a constant times the expressions of the theorem
(`exists_bounds30`, from `exists_tPreCore_le`, `exists_tQueryAt_le`, `exists_top_sub_le`), the
limits `lim30` suffice and are polynomial in N (`lim30_ok`, `small_lim30`), and the numbers of the
input fit in a word (`abs_input_le`). This makes the light program a data structure (`top30`). The
compiler (`isDataStructure_of_program_scaled`) then gives Items.Theorem_30 for every program that
holds the two main procedures at their numbers and meets the specifications of preCore and queryAt
(`theorem_30_of`).
-/

@[expose] public section

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.Spec ThreeSumApsp.WordRam

abbrev Proc.preMain : ℕ := 81
abbrev Proc.queryMain : ℕ := 80

namespace Thm30

/-- The locals of the two main procedures: the answer, which in a query is at first the row I, and
the column J; then N, D, the product N D, and in preMain the address of Y.  The last local is the
address of the block. -/
abbrev Ans : ℕ := 0
@[inherit_doc Ans] abbrev Col : ℕ := 1
@[inherit_doc Ans] abbrev Size : ℕ := 2
@[inherit_doc Ans] abbrev Dim : ℕ := 3
@[inherit_doc Ans] abbrev Area : ℕ := 4
@[inherit_doc Ans] abbrev MatY : ℕ := 5
@[inherit_doc Ans] abbrev Block : ℕ := 6
@[inherit_doc Ans] abbrev QBlock : ℕ := 5

end Thm30

open Thm30 in
/-- preMain (its two arguments are not used): read the sizes, compute the two addresses, call
preCore. -/
def preMainBody : Stmt :=
  .set Size (M (k 0)) ;; .set Dim (M (k 1)) ;; .set Area (v Size *' v Dim) ;;
  .set MatY (k 5 +' v Area) ;; .set Block (v MatY +' v Area) ;;
  .call Proc.preCore [M (k 3), M (k 2), M (k 4), v Size, v Dim, k 5, v MatY, v Block] Ans

open Thm30 in
/-- queryMain(I, J): read the sizes, compute the address of the block, call queryAt. -/
def queryMainBody : Stmt :=
  .set Size (M (k 0)) ;; .set Dim (M (k 1)) ;; .set Area (v Size *' v Dim) ;;
  .set QBlock (k 5 +' v Area +' v Area) ;;
  .call Proc.queryAt [v Ans, v Col, v QBlock] Ans

namespace Thm30

/-- The base address of the block of the data structure: the length of the input. -/
def blockBase (N m : ℕ) : ℕ := 5 + N * D m + N * D m

/-- The memory holds the input of the preprocessing, with D = 4^m, from cell 0 on. -/
structure Layout {N : ℕ} (m L t : ℕ) (X : Matrix (Fin N) (Fin (D m)) ℤ)
    (Y : Matrix (Fin (D m)) (Fin N) ℤ) (μ : ℕ → ℤ) : Prop where
  cellN : μ 0 = N
  cellD : μ 1 = D m
  cellm : μ 2 = m
  cellL : μ 3 = L
  cellt : μ 4 = t
  matX : MatAt μ 5 X
  matY : MatAt μ (5 + N * D m) Y

/-- **The memory holds the data structure for X and Y**: the two sizes that a query reads, and the
block behind the input. -/
structure DS {N : ℕ} (m L t : ℕ) (hmL : m ≤ L) (X : Matrix (Fin N) (Fin (D m)) ℤ)
    (Y : Matrix (Fin (D m)) (Fin N) ℤ) (μ : ℕ → ℤ) : Prop where
  cellN : μ 0 = N
  cellD : μ 1 = D m
  ready : DSReady ⟨L, m, N⟩ t hmL 5 (5 + N * D m) (blockBase N m) X Y μ

end Thm30

open Thm30

section
variable {lim : Limits} {P : Program} {N m L t : ℕ} {hmL : m ≤ L}
  {X : Matrix (Fin N) (Fin (D m)) ℤ} {Y : Matrix (Fin (D m)) (Fin N) ℤ} {U : ℤ} {μ : ℕ → ℤ}

/-- **The main procedure of the preprocessing** builds the data structure behind the input. -/
theorem preMain_meets {c : ℕ} (hP : P[Proc.preMain]? = some preMainBody)
    (hcore : PreCoreSpec lim P c) (ht : t ≤ m) (hX : ∀ i j, |X i j| ≤ U) (hY : ∀ i j, |Y i j| ≤ U)
    (hlim : Lim30 lim ⟨L, m, N⟩ t (blockBase N m) U) (hd : L + 8 ≤ lim.depth)
    (hμ : Layout m L t X Y μ) :
    Meets lim P Proc.preMain 1 [0, 0] μ (tPreCore c ⟨L, m, N⟩ t + 46) fun _ μ' =>
      DS m L t hmL X Y μ' := by
  refine Meets.of_body hP ?_
  light_facts hlim hlim.std
  have htop := base_add_lt_top ⟨L, m, N⟩ t (blockBase N m)
  -- a name for the product N D
  obtain ⟨area, harea⟩ : ∃ area, area = N * D m := ⟨_, rfl⟩
  have hmul : (N : ℤ) * (D m : ℤ) = area := by rw [harea]; push_cast; rfl
  have hb0 : blockBase N m = 5 + area + area := by rw [harea]; rfl
  -- Size := mem[0] ; Dim := mem[1] ; Area := Size * Dim
  light_set N using hμ.cellN
  light_set (D m) using hμ.cellD
  light_set area using hmul
  -- MatY := 5 + Area ; Block := MatY + Area
  light_set (5 + area : ℕ)
  light_set (blockBase N m : ℕ) using hb0
  -- Ans := preCore(mem[3], mem[2], mem[4], Size, Dim, 5, MatY, Block)
  refine Ends.callTo (hcore ⟨L, m, N⟩ t hmL 5 (5 + area) (blockBase N m) X Y U μ ht hlim hX hY
    hμ.matX (harea ▸ hμ.matY) (by change 5 + N * D m ≤ _; omega)
    (by change 5 + area + D m * N ≤ _; rw [Nat.mul_comm (D m) N]; omega) _
      (by change 2 + (L + 6) ≤ lim.depth; omega)) ?_
    (ha := by light_side [hμ.cellm, hμ.cellL, hμ.cellt, Sec2.Par.D])
  rintro r μ' ⟨hready, hsame⟩
  subst harea
  exact ⟨(hsame 0 (Or.inl (by omega))).trans hμ.cellN, (hsame 1 (Or.inl (by omega))).trans hμ.cellD,
    hready⟩

/-- **The main procedure of a query** returns the entry and keeps the data structure. -/
theorem queryMain_meets (hP : P[Proc.queryMain]? = some queryMainBody) (hq : QueryAtSpec lim P)
    (ht : t ≤ m) (hX : ∀ i j, |X i j| ≤ U) (hY : ∀ i j, |Y i j| ≤ U)
    (hlim : Lim30 lim ⟨L, m, N⟩ t (blockBase N m) U) (hd : 4 ≤ lim.depth) (hμ : DS m L t hmL X Y μ)
    (I J : Fin N) :
    Meets lim P Proc.queryMain 1 [((I : ℕ) : ℤ), ((J : ℕ) : ℤ)] μ (tQueryAt L m t + 26) fun r μ' =>
      r = (X * Y) I J ∧ DS m L t hmL X Y μ' := by
  refine Meets.of_body hP ?_
  light_facts hlim hlim.std
  have htop := base_add_lt_top ⟨L, m, N⟩ t (blockBase N m)
  have hscratch := wd_ge ⟨L, m, N⟩ (blockBase N m)
  obtain ⟨area, harea⟩ : ∃ area, area = N * D m := ⟨_, rfl⟩
  have hmul : (N : ℤ) * (D m : ℤ) = area := by rw [harea]; push_cast; rfl
  have hb0 : blockBase N m = 5 + area + area := by rw [harea]; rfl
  -- Size := mem[0] ; Dim := mem[1] ; Area := Size * Dim
  light_set N using hμ.cellN
  light_set (D m) using hμ.cellD
  light_set area using hmul
  -- QBlock := 5 + Area + Area
  light_set (blockBase N m : ℕ) using hb0
  -- Ans := queryAt(I, J, QBlock)
  light_call (hq ⟨L, m, N⟩ t hmL 5 (5 + N * D m) (blockBase N m) X Y U μ I J ht hlim hX hY
    hμ.ready _ (by omega)) with r μ' ⟨hr, hready, hsame⟩
  exact ⟨by simpa using hr, (hsame 0 (Or.inl (by omega))).trans hμ.cellN,
    (hsame 1 (Or.inl (by omega))).trans hμ.cellD, hready⟩

end

/-- The trusted input of the preprocessing, with D = 4^m, is laid out as preMain expects. -/
theorem layout_input {N U : ℕ} (m L t : ℕ) (X : Matrix (Fin N) (Fin (D m)) ℤ)
    (Y : Matrix (Fin (D m)) (Fin N) ℤ) (bX : ∀ i j, |X i j| ≤ (U : ℤ))
    (bY : ∀ i j, |Y i j| ≤ (U : ℤ)) :
    Layout m L t X Y
      (memOf ((⟨N, D m, U, X, Y, bX, bY⟩ : ThinPair).input [(m : ℤ), (L : ℤ), (t : ℤ)])) :=
  ⟨rfl, rfl, rfl, rfl, rfl, thinPair_matAt_X _ _, thinPair_matAt_Y _ _⟩

/-- **The numbers of the input fit in a word** of the limits of Theorem 30, if the block starts
behind them. -/
theorem abs_input_le (x : ThinPair) {m L t c b : ℕ} (hmL : m ≤ L) (ht : t ≤ m) (hU : x.U = x.N ^ c)
    (hN : x.N ≤ b) (hD : x.D ≤ b) :
    (x.N : ℤ) ≤ (lim30 ⟨L, m, x.N⟩ t b c).word ∧
      ∀ v ∈ x.input [(m : ℤ), (L : ℤ), (t : ℤ)], |v| ≤ (lim30 ⟨L, m, x.N⟩ t b c).word := by
  exact ⟨cast_le_word30 _ t b c (Or.inl hN), abs_thinPair_input_le
    (cast_le_word30 _ t b c (Or.inl hN))
    (cast_le_word30 _ t b c (Or.inl hD)) (hU ▸ pow_le_word30 ⟨L, m, x.N⟩ t b c)
    (abs_params_le_word30 x.N b c hmL ht)⟩

/-- **The block** starts at an address that is polynomial in N. -/
theorem b0_le {N m : ℕ} (hD : D m ≤ N) : blockBase N m ≤ 10 * (N + 1) ^ 3 := by
  have harea : N * D m ≤ N * N := Nat.mul_le_mul_left _ hD
  have hcube : (N + 1) ^ 3 = N * N * N + 3 * (N * N) + 3 * N + 1 := by ring
  simp only [blockBase]
  omega

/-- The time of the two main procedures, the length of the block and the nesting of calls are at
most C times the expressions of Theorem 30. -/
structure Bounds30 (c0 : ℕ) (C : ℝ) (p : Sec2.Par) (t : ℕ) : Prop where
  pre : ((tPreCore c0 p t + 50 : ℕ) : ℝ) ≤ C * cost8 p.L p.m t p.N
  query : ((tQueryAt p.L p.m t + 30 : ℕ) : ℝ) ≤ C * costQuery p.L p.m t
  block : ∀ b, ((top p t b - b : ℕ) : ℝ) ≤ C * cost8 p.L p.m t p.N
  depth : ((p.L + 10 : ℕ) : ℝ) ≤ C * cost8 p.L p.m t p.N

/-- **Time and space** are within a constant times the expressions of Theorem 30. -/
theorem exists_bounds30 (c0 : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (p : Sec2.Par) (t : ℕ), Hyp30 p t → Bounds30 c0 C p t := by
  obtain ⟨A, hA, hpre⟩ := exists_tPreCore_le c0
  obtain ⟨B, hB, hquery⟩ := exists_tQueryAt_le
  obtain ⟨S, hS, hblock⟩ := exists_top_sub_le
  refine ⟨A + B + S + 50, by positivity, fun p t h => ?_⟩
  have hpre := hpre p t h
  have hquery := hquery p t h
  have hone8 := one_le_cost8 p.L p.m t p.N h.L_ge h.N_ge
  have honeQ := one_le_costQuery (t := t) h.m_pos h.L_ge
  have hA8 := mul_nonneg hA (zero_le_one.trans hone8)
  have hB8 := mul_nonneg hB (zero_le_one.trans hone8)
  have hS8 := mul_nonneg hS (zero_le_one.trans hone8)
  have hAQ := mul_nonneg hA (zero_le_one.trans honeQ)
  have hSQ := mul_nonneg hS (zero_le_one.trans honeQ)
  -- L + 10 ≤ 11 · 10^L, and 10^L is within (8)
  have hpow : p.L + 10 ≤ 11 * 10 ^ p.L := by
    have : (p.L + 1) ^ 2 = p.L * p.L + 2 * p.L + 1 := by ring
    have := succ_sq_le_ten_pow p.L
    omega
  have hpow' : ((p.L + 10 : ℕ) : ℝ) ≤ 11 * (10 : ℝ) ^ p.L := by exact_mod_cast hpow
  have hten := ten_pow_le_cost8 h
  refine ⟨?_, ?_, fun b => ?_, ?_⟩
  · push_cast
    linarith
  · push_cast
    linarith
  · linarith [hblock p t b h]
  · linarith

/-- **Theorem 30 as a light program.** c0 is the constant of the shared stage, c the exponent of the
bound N^c on the entries. -/
theorem top30 {P : Program} {c0 : ℕ} (h81 : P[Proc.preMain]? = some preMainBody)
    (h80 : P[Proc.queryMain]? = some queryMainBody) (hpre : ∀ lim, PreCoreSpec lim P c0)
    (hq : ∀ lim, QueryAtSpec lim P) : ∃ C : ℝ, 0 ≤ C ∧ ∀ c m L t : ℕ,
    ProgramIsDataStructure P Proc.preMain Proc.queryMain 9 (20 + 2 * c) [(m : ℤ), (L : ℤ), (t : ℤ)]
      (Items.theorem30Dom c m L t) (fun x => C * cost8 L m t x.N) (fun x => C * cost8 L m t x.N)
      (fun _ => C * costQuery L m t) := by
  obtain ⟨C, hC, hbounds⟩ := exists_bounds30 c0
  refine ⟨C, hC, fun c m L t => ?_⟩
  rintro ⟨N, D', U, X, Y, bX, bY⟩ ⟨hm, hD, hL, ht, hN, hU⟩
  simp only at hD hN hU bX bY
  subst hD hU
  have hmL : m ≤ L := by omega
  have hyp : Hyp30 ⟨L, m, N⟩ t := ⟨hm, hL, ht, hN⟩
  have hbound := hbounds _ t hyp
  have hDN : D m ≤ N := hyp.D_le_N
  have hNb : N ≤ N * D m := Nat.le_mul_of_pos_right _ (by unfold D; positivity)
  have hb0 := b0_le hDN
  have hlim := lim30_ok ⟨L, m, N⟩ t (blockBase N m) c
  have bX' : ∀ i j, |X i j| ≤ (N : ℤ) ^ c := fun i j => by exact_mod_cast bX i j
  have bY' : ∀ i j, |Y i j| ≤ (N : ℤ) ^ c := fun i j => by exact_mod_cast bY i j
  obtain ⟨hNw, hinput⟩ := abs_input_le ⟨N, D m, N ^ c, X, Y, bX, bY⟩ (b := blockBase N m) hmL ht rfl
    (by change N ≤ blockBase N m; simp only [blockBase]; omega)
    (by change D m ≤ blockBase N m; simp only [blockBase]; omega)
  refine ⟨lim30 ⟨L, m, N⟩ t (blockBase N m) c, DS m L t hmL X Y, small_lim30 hyp _ c hb0, hNw,
    hinput, mul_nonneg hC (zero_le_one.trans (one_le_costQuery hm hL)), ?space, hbound.depth, ?pre,
    ?query⟩
  case space =>
    -- the space is the input, of length blockBase N m, and the block
    change ((top ⟨L, m, N⟩ t (blockBase N m) : ℕ) : ℝ) ≤ _
    rw [length_thinPair_input, ← Nat.add_sub_cancel' (base_le_top ⟨L, m, N⟩ t (blockBase N m)),
      Nat.cast_add]
    exact add_le_add (le_of_eq rfl) (hbound.block _)
  case pre =>
    exact (preMain_meets (hmL := hmL) h81 (hpre _) ht bX' bY' hlim (by change L + 8 ≤ L + 10; omega)
      (layout_input m L t X Y bX bY)).main (by change 0 < L + 10; omega) hbound.pre
  case query =>
    exact AnswersQueries.of_meets (by change 0 < L + 10; omega) hbound.query fun μ hμ I J =>
      queryMain_meets h80 (hq _) ht bX' bY' hlim (by change 4 ≤ L + 10; omega) hμ I J

/-- **Theorem 30 on the word RAM**, for any program that holds the routines. -/
theorem theorem_30_of {P : Program} {c0 : ℕ} (h81 : P[Proc.preMain]? = some preMainBody)
    (h80 : P[Proc.queryMain]? = some queryMainBody) (hpre : ∀ lim, PreCoreSpec lim P c0)
    (hq : ∀ lim, QueryAtSpec lim P) : Items.Theorem_30 := by
  obtain ⟨C, -, htop⟩ := top30 h81 h80 hpre hq
  intro c
  refine ⟨compileProgram P Proc.preMain false, compileProgram P Proc.queryMain false, -1, -2, -3,
    slopeOf P false 9 (20 + 2 * c) 2, (timeConst P false : ℝ) * (C + 1), fun m L t => ?_⟩
  refine isDataStructure_of_program_scaled (htop c m L t) ?_
  rintro x ⟨hm, -, hL, -, hN, -⟩
  exact ⟨one_le_cost8 L m t x.N hL hN, one_le_cost8 L m t x.N hL hN, one_le_costQuery hm hL⟩

end Light.Sec4
