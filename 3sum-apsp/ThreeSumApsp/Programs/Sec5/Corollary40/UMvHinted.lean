/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec5.Corollary40.UMvRoutines

/-!
# uMv-hinted uMv over a kit: the four phases

Proof of Corollary 40.  A kit is a data structure for the entries of a thin matrix
product that can be placed anywhere in the memory.  Phases 1 and 2 return at once.  Phase 3 computes
the addresses (`uMvAddr_spec`), writes Y := N_{I,J}, and builds the structures of the blocks and the
table of first rows (`uMvPhase3_meets`).  Phase 4 reads i and j, looks up the first row s of the
block of row i, asks the structure of that block, and writes the result (`uMvPhase4_meets`).
`uMv_lightPhases` puts the phases together.
-/

@[expose] public section

namespace Light.Sec5

open ThreeSumApsp ThreeSumApsp.WordRam ThreeSumApsp.HintedMv ThreeSumApsp.Spec.Sec5 Light.Sec4
open ThreeSumApsp.Corollary40 (abs_toInt_le)

/-! ## The scratch space -/

/-- The address of Y = N_{I,J}, t₁ t₂ cells. -/
def uMvY (n t₁ t₂ : ℕ) : ℕ := uMvFree n t₁ t₂
/-- The table of the first rows of the blocks, n cells. -/
def uMvS (n t₁ t₂ : ℕ) : ℕ := uMvY n t₁ t₂ + t₁ * t₂
/-- The address of the structure of a block with the first row 0. -/
def uMvBase (n t₁ t₂ : ℕ) : ℕ := uMvS n t₁ t₂ + n
/-- The distance of the structures of two blocks whose first rows differ by 1; A is a numeral in the
program text. -/
def uMvSz (A t₂ : ℕ) : ℕ := A * (t₂ * t₂)
/-- The address of the structure of the block with the first row s. -/
def uMvFr (A n t₁ t₂ s : ℕ) : ℕ := uMvBase n t₁ t₂ + s * uMvSz A t₂
/-- An address above all cells that are used. -/
def uMvTop (A n t₁ t₂ : ℕ) : ℕ := uMvBase n t₁ t₂ + n * uMvSz A t₂ + 1

/-- The limits that the four phases need. -/
structure UMvLim {P : Program} (K : DsKit P) (lim : Limits) (A n t₁ t₂ : ℕ) : Prop where
  lims : ∀ s, s + t₂ ≤ n → K.Lim lim t₂ t₁ (uMvFr A n t₁ t₂ s) 1
  space : uMvTop A n t₁ t₂ ≤ lim.space
  depth : K.depPre t₁ + 8 ≤ lim.depth
  numeral : (A : ℤ) ≤ lim.word

/-- How the addresses follow one another. -/
theorem uMvAddresses (A n t₁ t₂ : ℕ) :
    uMvN n t₁ = 3 + n * t₁ ∧ uMvV n t₁ = uMvN n t₁ + n * n ∧ uMvI n t₁ t₂ = uMvV n t₁ + t₂ * n ∧
      uMvJ n t₁ t₂ = uMvI n t₁ t₂ + t₁ ∧ uMvQ n t₁ t₂ = uMvJ n t₁ t₂ + t₂ ∧
      uMvOut n t₁ t₂ = uMvJ n t₁ t₂ + t₂ + 2 ∧ uMvY n t₁ t₂ = uMvJ n t₁ t₂ + t₂ + 3 ∧
      uMvS n t₁ t₂ = uMvY n t₁ t₂ + t₁ * t₂ ∧ uMvBase n t₁ t₂ = uMvS n t₁ t₂ + n ∧
      uMvTop A n t₁ t₂ = uMvBase n t₁ t₂ + n * uMvSz A t₂ + 1 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## The procedures -/

namespace UMv

/-- The locals of Phases 3 and 4.  Locals 0 and 1 are the arguments of the main procedure, which are
not used.  Then the sizes n, t₁, t₂; the addresses of N, V, I, J, of Y, of the table and of the
structures; the distance of the structures.  In Phase 3 two results that are not used follow.  In
Phase 4: i, j, the first row of the block of row i, and the result. -/
abbrev Size : ℕ := 2
@[inherit_doc Size] abbrev Inner : ℕ := 3
@[inherit_doc Size] abbrev Height : ℕ := 4
@[inherit_doc Size] abbrev AddrN : ℕ := 5
@[inherit_doc Size] abbrev AddrV : ℕ := 6
@[inherit_doc Size] abbrev AddrI : ℕ := 7
@[inherit_doc Size] abbrev AddrJ : ℕ := 8
@[inherit_doc Size] abbrev AddrY : ℕ := 9
@[inherit_doc Size] abbrev Table : ℕ := 10
@[inherit_doc Size] abbrev Base : ℕ := 11
@[inherit_doc Size] abbrev Dist : ℕ := 12
@[inherit_doc Size] abbrev RowI : ℕ := 13
@[inherit_doc Size] abbrev ColJ : ℕ := 14
@[inherit_doc Size] abbrev First : ℕ := 15
@[inherit_doc Size] abbrev Result : ℕ := 16

end UMv

open UMv

/-- The start of Phases 3 and 4: n, t₁ and t₂ are read from cells 0, 1 and 2, and the addresses are
computed from them. -/
def uMvAddr (A : ℕ) : Stmt :=
  .set Size (M (k 0)) ;;
  .set Inner (M (k 1)) ;;
  .set Height (M (k 2)) ;;
  .set AddrN (k 3 +' v Size *' v Inner) ;;
  .set AddrV (v AddrN +' v Size *' v Size) ;;
  .set AddrI (v AddrV +' v Height *' v Size) ;;
  .set AddrJ (v AddrI +' v Inner) ;;
  .set AddrY (v AddrJ +' v Height +' k 3) ;;
  .set Table (v AddrY +' v Inner *' v Height) ;;
  .set Base (v Table +' v Size) ;;
  .set Dist (k A *' (v Height *' v Height))

/-- Phase 3: gather(n, t₁, t₂, aN, aI, aJ, aY), then blocks(n, t₁, t₂, aY, aS, base, Sz). -/
def uMvPhase3Body (A pGather pBlocks : ℕ) : Stmt :=
  uMvAddr A ;;
  .call pGather [v Size, v Inner, v Height, v AddrN, v AddrI, v AddrJ, v AddrY] RowI ;;
  .call pBlocks [v Size, v Inner, v Height, v AddrY, v Table, v Base, v Dist] ColJ

/-- Phase 4: i and j are read from their cells and the first row s of the block of row i from the
table; the result of scan(i - s, j, t₂, t₁, 3 + s t₁, aY, base + s Sz, aV, n) goes to the output
cell. -/
def uMvPhase4Body (A pScan : ℕ) : Stmt :=
  uMvAddr A ;;
  .set RowI (M (v AddrJ +' v Height)) ;;
  .set ColJ (M (v AddrJ +' v Height +' k 1)) ;;
  .set First (M (v Table +' v RowI)) ;;
  .call pScan [v RowI -' v First, v ColJ, v Height, v Inner, k 3 +' v First *' v Inner, v AddrY,
    v Base +' v First *' v Dist, v AddrV, v Size] Result ;;
  .store (v AddrJ +' v Height +' k 2) (v Result)

/-- The procedures of the four phases and their three routines are in the program. -/
structure UMvProcs (P : Program) (A pNop p3 p4 pGather pBlocks pScan : ℕ) : Prop where
  nop : P[pNop]? = some .skip
  phase3 : P[p3]? = some (uMvPhase3Body A pGather pBlocks)
  phase4 : P[p4]? = some (uMvPhase4Body A pScan)
  gather : P[pGather]? = some gatherBody
  blocks : P[pBlocks]? = some blocksBody
  scan : P[pScan]? = some scanBody

/-- The local variables after the addresses have been computed. -/
def uMvLoc (A n t₁ t₂ : ℕ) : List ℤ :=
  [0, 0, n, t₁, t₂, (uMvN n t₁ : ℕ), (uMvV n t₁ : ℕ), (uMvI n t₁ t₂ : ℕ), (uMvJ n t₁ t₂ : ℕ),
    (uMvY n t₁ t₂ : ℕ), (uMvS n t₁ t₂ : ℕ), (uMvBase n t₁ t₂ : ℕ), (uMvSz A t₂ : ℕ)]

/-- **Sizes and addresses.**  `uMvAddr` leaves the list `uMvLoc A n t₁ t₂` in the locals and changes
no cell. -/
theorem uMvAddr_spec {P : Program} {lim : Limits} {d A n t₁ t₂ : ℕ} {μ : ℕ → ℤ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hn : 1 ≤ n) (h2n : t₂ ≤ n)
    (hsp : uMvTop A n t₁ t₂ ≤ lim.space) (hA : (A : ℤ) ≤ lim.word) (h0 : μ 0 = n) (h1 : μ 1 = t₁)
    (h2 : μ 2 = t₂) :
    Ends lim P d (uMvAddr A) ⟨frame [0, 0], μ⟩ 53 fun σ' => σ' = ⟨frame (uMvLoc A n t₁ t₂), μ⟩ := by
  have hplaces := uMvAddresses A n t₁ t₂
  have eSz : ((uMvSz A t₂ : ℕ) : ℤ) = A * ((t₂ : ℤ) * t₂) := by simp [uMvSz]
  have hSz : uMvSz A t₂ ≤ n * uMvSz A t₂ := Nat.le_mul_of_pos_left _ hn
  have hsq : t₂ * t₂ ≤ n * n := Nat.mul_le_mul h2n h2n
  unfold uMvAddr
  light_set n using h0
  light_set t₁ using h1
  light_set t₂ using h2
  light_set (uMvN n t₁ : ℕ)
  light_set (uMvV n t₁ : ℕ)
  light_set (uMvI n t₁ t₂ : ℕ)
  light_set (uMvJ n t₁ t₂ : ℕ)
  light_set (uMvY n t₁ t₂ : ℕ)
  light_set (uMvS n t₁ t₂ : ℕ)
  light_set (uMvBase n t₁ t₂ : ℕ)
  light_set (uMvSz A t₂ : ℕ)
  rfl

/-- What Phase 3 leaves: for every row the table has the first row of its block, and the structure
of this block is ready. -/
structure UMvPhase3Post {P : Program} (K : DsKit P) (A : ℕ) {n t₁ t₂ : ℕ}
    (U : Matrix (Fin n) (Fin t₁) Bool) (N : Matrix (Fin n) (Fin n) Bool) (I : Fin t₁ → Fin n)
    (J : Fin t₂ → Fin n) (μ : ℕ → ℤ) : Prop where
  table : ∀ i < n, ∃ s : ℕ, μ (uMvS n t₁ t₂ + i) = s ∧ s ≤ i ∧ i < s + t₂ ∧
    BlockReady K (toInt U) ((toInt N).submatrix I J) (uMvY n t₁ t₂) (uMvBase n t₁ t₂) (uMvSz A t₂) s
      μ

section phases

variable {P : Program} (K : DsKit P) {lim : Limits} {A pNop p3 p4 pGather pBlocks pScan : ℕ}
  (hP : UMvProcs P A pNop p3 p4 pGather pBlocks pScan) {n t₁ t₂ : ℕ}
  {U : Matrix (Fin n) (Fin t₁) Bool} {N : Matrix (Fin n) (Fin n) Bool}
  {V : Matrix (Fin t₂) (Fin n) Bool} {I : Fin t₁ → Fin n} {J : Fin t₂ → Fin n} {μ : ℕ → ℤ}

include hP

/-- **Phase 3** writes Y and builds the structures of the blocks and the table of their first rows.
It changes no cell below Y. -/
theorem uMvPhase3_meets (h1 : 1 ≤ t₁) (h2 : 1 ≤ t₂) (h2n : t₂ ≤ n)
    (hsize : K.size t₂ t₁ ≤ A * (t₂ * t₂)) (hlim : UMvLim K lim A n t₁ t₂)
    (hM : UMvMem3 μ U N V I J) :
    Meets lim P p3 1 [0, 0] μ (tGather t₁ t₂ + tBlocks K n t₁ t₂ + 71) fun _ μ' =>
      UMvPhase3Post K A U N I J μ' ∧ Kept μ μ' (uMvY n t₁ t₂) := by
  obtain ⟨hw, -, -, -⟩ := K.basics (hlim.lims 0 (by omega))
  have hsp := hlim.space
  have hdep := hlim.depth
  have hplaces := uMvAddresses A n t₁ t₂
  refine .of_body hP.phase3 ?_
  unfold uMvPhase3Body
  light_piece (uMvAddr_spec hw (by omega) h2n hsp hlim.numeral hM.n_eq hM.t₁_eq
    hM.t₂_eq) with _ rfl
  unfold uMvLoc
  -- gather(n, t₁, t₂, aN, aI, aJ, aY)
  light_call (gather_meets hP.gather (aY := uMvY n t₁ t₂) hw hM.matN hM.vecI hM.vecJ
    (by omega) (by omega) (by omega) (by omega)) with _ μ₁ ⟨hY, hsame⟩
  -- blocks(n, t₁, t₂, aY, aS, base, Sz)
  light_call (blocks_meets (K := K) hP.blocks (aS := uMvS n t₁ t₂) (base := uMvBase n t₁ t₂)
    (Sz := uMvSz A t₂) {
      inner_pos := h1, height_pos := h2, height_le := h2n, size_le := hsize
      matU := hM.matU.keep, matY := hY
      absU := abs_toInt_le U, absY := fun a b => abs_toInt_le N (I a) (J b)
      belowY := by omega, belowTable := by omega, belowBase := by omega
      lims := hlim.lims, space := by omega } (by omega)) with _ μ₂ ⟨htable, hkept⟩
  exact ⟨⟨htable⟩, by light_keep⟩

/-- **Phase 4** writes the entry (i, j) of U N_{I,J} V, as 0 or 1, into the output cell. -/
theorem uMvPhase4_meets (h1 : 1 ≤ t₁) (h2 : 1 ≤ t₂) (h2n : t₂ ≤ n) (hlim : UMvLim K lim A n t₁ t₂)
    {i j : Fin n} (hM : UMvMem4 μ U N V I J i j) (h3 : UMvPhase3Post K A U N I J μ) :
    Meets lim P p4 1 [0, 0] μ (tScan K t₁ t₂ + 98) fun _ μ' =>
      μ' (uMvOut n t₁ t₂) = bit (uMvHintedOutput U N V I J i j) := by
  obtain ⟨hw, h100, -, -⟩ := K.basics (hlim.lims 0 (by omega))
  have hsp := hlim.space
  have hdep := hlim.depth
  have hi := i.isLt
  obtain ⟨s, htab, hle, hlt, hs, hready⟩ := h3.table i hi
  have hplaces := uMvAddresses A n t₁ t₂
  have hst : s * t₁ + t₂ * t₁ ≤ n * t₁ := (Nat.add_mul _ _ _).symm.trans_le
    (Nat.mul_le_mul_right _ hs)
  have hsSz : s * uMvSz A t₂ ≤ n * uMvSz A t₂ := Nat.mul_le_mul_right _ (by omega)
  have hμi : μ (uMvJ n t₁ t₂ + t₂) = (i : ℕ) := hM.i_eq
  have hμj : μ (uMvJ n t₁ t₂ + t₂ + 1) = (j : ℕ) := hM.j_eq
  have haddr₁ : ((uMvJ n t₁ t₂ : ℤ) + t₂ + 1).toNat = uMvJ n t₁ t₂ + t₂ + 1 := by omega
  have hsub : ((i : ℕ) : ℤ) - s = ((i - s : ℕ) : ℤ) := by omega
  have hin : K.Input lim (rowsFrom (toInt U) s t₂ hs) ((toInt N).submatrix I J) (3 + s * t₁)
      (uMvY n t₁ t₂) (uMvBase n t₁ t₂ + s * uMvSz A t₂) 1 :=
    { one_le_D := h1, one_le_N := h2, lim := hlim.lims s hs
      absX := abs_rowsFrom_le (abs_toInt_le U) s t₂ hs
      absY := fun a b => abs_toInt_le N (I a) (J b), belowX := by omega, belowY := by omega }
  refine .of_body hP.phase4 ?_
  unfold uMvPhase4Body
  light_piece (uMvAddr_spec hw (by omega) h2n hsp hlim.numeral hM.n_eq hM.t₁_eq
    hM.t₂_eq) with _ rfl
  unfold uMvLoc
  -- i, j, and the first row s of the block of row i
  light_set (i : ℕ) using hμi
  light_set (j : ℕ) using haddr₁, hμj
  light_set s using htab
  -- scan(i - s, j, t₂, t₁, 3 + s t₁, aY, base + s Sz, aV, n)
  light_call (scan_meets K hP.scan (⟨i - s, by omega⟩ : Fin t₂) j hin hM.matV (by omega)
    hready (by omega)) using hsub with r μ₁ ⟨hr, -⟩
  -- the output cell
  light_store (uMvOut n t₁ t₂) r
  change Function.update μ₁ (uMvOut n t₁ t₂) r (uMvOut n t₁ t₂) = _
  rw [Function.update_self, hr, uMvHintedOutput_eq]
  refine congrArg bit (decide_eq_decide.2 (exists_congr fun l => and_congr_right fun _ => ?_))
  rw [rowsFrom_mul]
  simp only [Nat.add_sub_cancel' hle]

end phases

/-- What Phase 3 leaves stays if neither U nor a cell from Y on changes. -/
theorem UMvPhase3Post.keep {P : Program} {K : DsKit P} {A n t₁ t₂ : ℕ}
    {U : Matrix (Fin n) (Fin t₁) Bool} {N : Matrix (Fin n) (Fin n) Bool} {I : Fin t₁ → Fin n}
    {J : Fin t₂ → Fin n} {μ μ' : ℕ → ℤ} (h : UMvPhase3Post K A U N I J μ)
    (hs : SameOn (fun b => b < uMvN n t₁ ∨ uMvY n t₁ t₂ ≤ b) μ μ' := by light_keep) :
    UMvPhase3Post K A U N I J μ' := by
  have hplaces := uMvAddresses A n t₁ t₂
  refine ⟨fun r hr => ?_⟩
  obtain ⟨s, htab, hle, hlt, hblock⟩ := h.table r hr
  exact ⟨s, Eq.trans (by light_keep) htab, hle, hlt, hblock.keep⟩

/-- **The four phases of uMv-hinted uMv over a kit.** -/
theorem uMv_lightPhases {P : Program} (K : DsKit P) {lim : Limits}
    {A pNop p3 p4 pGather pBlocks pScan : ℕ} (hP : UMvProcs P A pNop p3 p4 pGather pBlocks pScan)
    {n t₁ t₂ : ℕ} (h1 : 1 ≤ t₁) (h2 : 1 ≤ t₂) (h2n : t₂ ≤ n)
    (hsize : K.size t₂ t₁ ≤ A * (t₂ * t₂)) (hlim : UMvLim K lim A n t₁ t₂)
    (U : Matrix (Fin n) (Fin t₁) Bool) (N : Matrix (Fin n) (Fin n) Bool)
    (V : Matrix (Fin t₂) (Fin n) Bool) (I : Fin t₁ → Fin n) (J : Fin t₂ → Fin n) (i j : Fin n) :
    ∃ c₁ c₂ c₃ c₄ : ℕ, c₁ ≤ 4 ∧ c₂ ≤ 4 ∧ c₃ ≤ tGather t₁ t₂ + tBlocks K n t₁ t₂ + 75 ∧
      c₄ ≤ tScan K t₁ t₂ + 102 ∧
      LightPhases lim P (fun μ off => μ (off + 0) = bit (uMvHintedOutput U N V I J i j))
        (fun _ => 0) 0
        [(pNop, [(n : ℤ), (t₁ : ℤ), (t₂ : ℤ)] ++ rowMajor (toInt U) ++ rowMajor (toInt N) ++
            rowMajor (toInt V), c₁),
          (pNop, List.ofFn fun k => ((I k).val : ℤ), c₂),
          (p3, List.ofFn fun k => ((J k).val : ℤ), c₃), (p4, [(i.val : ℤ), (j.val : ℤ)], c₄)] := by
  have hd0 : 0 < lim.depth := by have := hlim.depth; omega
  have hplaces := uMvAddresses A n t₁ t₂
  -- Phases 1 and 2 leave the memory as it is
  have in₁ := InputsAt.first (fun _ => 0) ([(n : ℤ), (t₁ : ℤ), (t₂ : ℤ)] ++ rowMajor (toInt U) ++
    rowMajor (toInt N) ++ rowMajor (toInt V))
  obtain ⟨σ₁, c₁, run₁, hc₁, in₁⟩ := phase_of_ends (T := 0) (Q := fun μ' => InputsAt μ' _ _)
    hP.nop hd0 (Ends.skip in₁)
  obtain ⟨σ₂, c₂, run₂, hc₂, in₂⟩ := phase_of_ends (T := 0) (Q := fun μ' => InputsAt μ' _ _)
    hP.nop hd0 (Ends.skip (in₁.next (List.ofFn fun k => ((I k).val : ℤ))))
  -- Phase 3
  have in₃ := in₂.next (List.ofFn fun k => ((J k).val : ℤ))
  obtain ⟨hμ₃, e₃⟩ := uMvMem3_of_inputs in₃
  obtain ⟨σ₃, c₃, run₃, hc₃, -, hpost, hsame⟩ :=
    phase_of_meets hd0 (uMvPhase3_meets K hP h1 h2 h2n hsize hlim hμ₃)
  -- Phase 4: the inputs lie below Y, and the indices i and j are written between U and Y
  have in₃' := in₃.keep (μ' := σ₃.mem) (by light_keep [hsame])
  obtain ⟨hμ₄, e₄⟩ := uMvMem4_of_inputs (in₃'.next [(i.val : ℤ), (j.val : ℤ)])
  have hwrite := in₃'.sameOutside [(i.val : ℤ), (j.val : ℤ)]
  obtain ⟨σ₄, c₄, run₄, hc₄, -, hout⟩ :=
    phase_of_meets hd0
      (uMvPhase4_meets K hP h1 h2 h2n hlim hμ₄ (hpost.keep (by light_keep [hwrite])))
  refine ⟨c₁, c₂, c₃, c₄, by omega, by omega, by omega, by omega, σ₁, run₁, σ₂, run₂, σ₃, run₃, σ₄,
    run₄, ?_⟩
  rw [e₄]
  exact hout

end Light.Sec5
