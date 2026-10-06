/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec5.Corollary40.Column
public import ThreeSumApsp.Programs.Sec5.Corollary40.Gather
public import ThreeSumApsp.Programs.Sec5.Corollary40.PhaseLayout

/-!
# Corollary 40: Mv-hinted Mv as a light program that runs in phases

Proof of Corollary 40, paragraph "Conjecture 5.7 of [vdBNS19]": "The proof is the same, with
X := N_{[n],I} and Y := V, which are both known in Phase 2".

The inputs of the phases lie one after the other: n in cell 0, t in cell 1, N from cell 2, V from
cell 2 + n², the t column indices I from 2 + n² + tn, the index j in the cell after them, then the n
cells of the output (`MvMem2`, `MvMem3`).  After the output come the nt cells of X.  The data
structure, an arbitrary kit, is built from the cell 3 + 2nt + 3n² on.  Phase 1 returns at once.
Phase 2 writes X, whose column k is column I_k of N (`mvGather_spec`), and preprocesses X and V
(`mvPhase2_meets`).  Phase 3 asks the n queries (`mvPhase3_meets`).  `mv_lightPhases` puts the
phases together.
-/

@[expose] public section

namespace Light.Sec5

open ThreeSumApsp ThreeSumApsp.WordRam ThreeSumApsp.HintedMv ThreeSumApsp.Spec.Sec5 Light.Sec4
open ThreeSumApsp.Corollary40 (abs_toInt_le)

namespace MvHinted

/-- The locals of Phases 2 and 3.  Sizes: n, t, n², nt.  Addresses: of V, of I, of j, of the output,
of X, and the first cell of the data structure.  For the loops that write X: the row r (this local
also takes the results of the calls, which are not used), the addresses of row r of N and of X, and
the column. -/
abbrev Size : ℕ := 0
@[inherit_doc Size] abbrev Thin : ℕ := 1
@[inherit_doc Size] abbrev Square : ℕ := 2
@[inherit_doc Size] abbrev Cells : ℕ := 3
@[inherit_doc Size] abbrev AddrV : ℕ := 4
@[inherit_doc Size] abbrev AddrI : ℕ := 5
@[inherit_doc Size] abbrev AddrJ : ℕ := 6
@[inherit_doc Size] abbrev Out : ℕ := 7
@[inherit_doc Size] abbrev AddrX : ℕ := 8
@[inherit_doc Size] abbrev Free : ℕ := 9
@[inherit_doc Size] abbrev Row : ℕ := 10
@[inherit_doc Size] abbrev RowN : ℕ := 11
@[inherit_doc Size] abbrev RowX : ℕ := 12
@[inherit_doc Size] abbrev Col : ℕ := 13

end MvHinted

open MvHinted

/-! ## Addresses -/

/-- The address of X. -/
def mvX (n t : ℕ) : ℕ := mvOut n t + n
/-- The first cell of the data structure. -/
def mvFr (n t : ℕ) : ℕ := 3 + 2 * (n * t) + 3 * (n * n)

/-- The addresses, written out. -/
theorem mvAddresses (n t : ℕ) :
    mvV n = 2 + n * n ∧ mvI n t = 2 + n * n + n * t ∧ mvJ n t = mvI n t + t ∧
      mvOut n t = mvI n t + t + 1 ∧ mvX n t = mvI n t + t + 1 + n ∧
      mvFr n t = 3 + 2 * (n * t) + 3 * (n * n) :=
  ⟨rfl, congrArg (2 + n * n + ·) (Nat.mul_comm t n), rfl, rfl, rfl, rfl⟩

/-- The start of Phases 2 and 3: n and t are read from cells 0 and 1, and the addresses are computed
from them. -/
def mvAddr : Stmt :=
  .set Size (M (k 0)) ;;
  .set Thin (M (k 1)) ;;
  .set Square (v Size *' v Size) ;;
  .set Cells (v Size *' v Thin) ;;
  .set AddrV (k 2 +' v Square) ;;
  .set AddrI (v AddrV +' v Cells) ;;
  .set AddrJ (v AddrI +' v Thin) ;;
  .set Out (v AddrJ +' k 1) ;;
  .set AddrX (v Out +' v Size) ;;
  .set Free (k 3 +' k 2 *' v Cells +' k 3 *' v Square)

/-- The local variables after the addresses have been computed. -/
def mvLoc (n t : ℕ) : List ℤ :=
  [n, t, (n * n : ℕ), (n * t : ℕ), mvV n, mvI n t, mvJ n t, mvOut n t, mvX n t, mvFr n t]

/-- **Sizes and addresses.**  `mvAddr` leaves the list `mvLoc n t` in the locals and changes no
cell. -/
theorem mvAddr_spec {lim : Limits} {P : Program} {d n t : ℕ} {μ : ℕ → ℤ}
    (hw : (lim.space : ℤ) ≤ lim.word) (htn : t ≤ n) (hn : 1 ≤ n) (hsp : mvFr n t < lim.space)
    (hμn : μ 0 = n) (hμt : μ 1 = t) :
    Ends lim P d mvAddr ⟨frame [0, 0], μ⟩ 44 fun σ' => σ' = ⟨frame (mvLoc n t), μ⟩ := by
  have hplaces := mvAddresses n t
  have hnn : n ≤ n * n := Nat.le_mul_of_pos_left n hn
  unfold mvAddr
  light_set n using hμn
  light_set t using hμt
  light_set (n * n : ℕ)
  light_set (n * t : ℕ)
  light_set (mvV n)
  light_set (mvI n t)
  light_set (mvJ n t)
  light_set (mvOut n t)
  light_set (mvX n t)
  light_set (mvFr n t)
  rfl

/-! ## The matrix of the selected columns -/

/-- for r < n, c < t: X[r, c] := N[r, I_c].  N lies at 2. -/
def mvGather : Stmt :=
  .for Row (v Size) (
    .set RowN (k 2 +' v Row *' v Size) ;;
    .set RowX (v AddrX +' v Row *' v Thin) ;;
    pick Col Thin RowX RowN AddrI)

/-- The time of `mvGather`: n rows of t entries. -/
def tMvGather (n t : ℕ) : ℕ := n * (19 * t + 26) + 6

/-- **The matrix of the selected columns** is written, and only its cells change. -/
theorem mvGather_spec {lim : Limits} {P : Program} {d n t : ℕ} {μ : ℕ → ℤ}
    {N : Matrix (Fin n) (Fin n) Bool} {V : Matrix (Fin t) (Fin n) Bool} {I : Fin t → Fin n}
    (hw : (lim.space : ℤ) ≤ lim.word) (htn : t ≤ n) (hsp : mvFr n t < lim.space)
    (hμ : MvMem2 μ N V I) :
    Ends lim P d mvGather ⟨frame (mvLoc n t), μ⟩ (tMvGather n t) fun σ' =>
      RowsWritten μ (mvX n t) (toInt (N.submatrix id I)) n σ'.mem := by
  have hplaces := mvAddresses n t
  have hnn : n ≤ n * n := Nat.le_mul_self n
  unfold mvGather mvLoc tMvGather
  -- for r < n: the rows below r are written
  refine Ends.forScratch [RowN, RowX, Col] (RowsWritten μ (mvX n t) (toInt (N.submatrix id I))) n
    (19 * t + 18) .zero (fun r _ μ' hr hrows => ?_) fun _ _ h => h
  have hsame := hrows.same
  have hrn : r * n + n ≤ n * n := Nat.mul_add_le_mul hr le_rfl
  have hrt : r * t + t ≤ n * t := Nat.mul_add_le_mul hr le_rfl
  -- the addresses of row r of N and of X
  light_set (2 + r * n : ℕ)
  light_set (mvX n t + r * t : ℕ)
  -- for c < t: X[r, c] := N[r, I_c]
  refine Ends.pick (aRow := 2 + r * n) (rowFn (toInt (N.submatrix id I)) r) hμ.vecI.keep
    (fun c => ?_) (by omega) (by omega) (by omega) hw (hrows.succ hr)
  have := (I c).isLt
  rw [hsame _ (.inl (by omega)), rowFn_eq _ hr]
  exact hμ.matN ⟨r, hr⟩ (I c)

/-! ## The three phases -/

/-- Phase 1 does nothing. -/
def mvPhase1Body : Stmt := .skip

/-- Phase 2: X is written; then pre(n, t, aX, aV, fr). -/
def mvPhase2Body : Stmt :=
  mvAddr ;;
  mvGather ;;
  .call Proc.pre31 [v Size, v Thin, v AddrX, v AddrV, v Free] Row

/-- Phase 3: col(n, t, aX, aV, fr, j, out), where j is read from its cell. -/
def mvPhase3Body (pCol : ℕ) : Stmt :=
  mvAddr ;;
  .call pCol [v Size, v Thin, v AddrX, v AddrV, v Free, M (v AddrJ), v Out] Row

section phases

variable {P : Program} (K : DsKit P) {lim : Limits} {n t : ℕ} {μ : ℕ → ℤ}
  {N : Matrix (Fin n) (Fin n) Bool} {V : Matrix (Fin t) (Fin n) Bool} {I : Fin t → Fin n}

/-- **Phase 2** writes X and preprocesses X and V: the data structure is ready, and no cell below X
has changed. -/
theorem mvPhase2_meets {p₂ : ℕ} (h2 : P[p₂]? = some mvPhase2Body) (hn : 1 ≤ n) (ht : 1 ≤ t)
    (htn : t ≤ n) (hlim : K.Lim lim n t (mvFr n t) 1) (hdep : K.depPre t + 2 ≤ lim.depth)
    (hμ : MvMem2 μ N V I) :
    Meets lim P p₂ 1 [0, 0] μ (K.tPre n t + tMvGather n t + 51) fun _ μ' =>
      K.Ready (toInt (N.submatrix id I)) (toInt V) (mvX n t) (mvV n) (mvFr n t) μ' ∧
        Kept μ μ' (mvX n t) := by
  obtain ⟨hw, -, hsp, hsz⟩ := K.basics hlim
  have hplaces := mvAddresses n t
  have hcomm : t * n = n * t := Nat.mul_comm _ _
  have hnn : n ≤ n * n := Nat.le_mul_of_pos_left n hn
  refine .of_body h2 ?_
  unfold mvPhase2Body
  light_piece (mvAddr_spec hw htn hn (by omega) hμ.n_eq hμ.t_eq) with _ rfl
  refine Ends.pieceToThen [Row, RowN, RowX, Col] (mvGather_spec hw htn (by omega) hμ)
    (fun _ μ₁ (hrows : RowsWritten μ (mvX n t) _ n μ₁) => ?_) (by simp [mvGather])
  have hsame := hrows.same
  unfold mvLoc
  -- pre(n, t, aX, aV, fr)
  light_call (K.pre
    { one_le_D := ht, one_le_N := hn, lim := hlim, absX := abs_toInt_le _, absY := abs_toInt_le _
      belowX := by omega, belowY := by omega }
    hrows.matAt hμ.matV.keep _ (by omega)) with _ μ₂ ⟨hready, hsame₂⟩
  exact ⟨hready, by light_keep⟩

/-- **Phase 3** asks the n queries for column j: output cell r tells whether the entry (r, j) of the
product of X and V over the integers is positive. -/
theorem mvPhase3_meets {p₃ pCol : ℕ} (h3 : P[p₃]? = some (mvPhase3Body pCol))
    (hc : P[pCol]? = some colBody) (hn : 1 ≤ n) (ht : 1 ≤ t) (htn : t ≤ n)
    (hlim : K.Lim lim n t (mvFr n t) 1) (hdep : 6 ≤ lim.depth) {j : Fin n} (hμ : MvMem3 μ N V I j)
    (hR : K.Ready (toInt (N.submatrix id I)) (toInt V) (mvX n t) (mvV n) (mvFr n t) μ) :
    Meets lim P p₃ 1 [0, 0] μ (n * (K.tQ t + 30) + 60) fun _ μ' =>
      ∀ r : Fin n, μ' (mvOut n t + r) =
        if 0 < (toInt (N.submatrix id I) * toInt V) r j then 1 else 0 := by
  obtain ⟨hw, -, hsp, hsz⟩ := K.basics hlim
  have hplaces := mvAddresses n t
  have hcomm : t * n = n * t := Nat.mul_comm _ _
  have hnn : n ≤ n * n := Nat.le_mul_of_pos_left n hn
  refine .of_body h3 ?_
  unfold mvPhase3Body
  light_piece (mvAddr_spec hw htn hn (by omega) hμ.n_eq hμ.t_eq) with _ rfl
  unfold mvLoc
  -- col(n, t, aX, aV, fr, j, out)
  light_call (col_meets K hc (out := mvOut n t) j
    { one_le_D := ht, one_le_N := hn, lim := hlim, absX := abs_toInt_le _, absY := abs_toInt_le _
      belowX := by omega, belowY := by omega }
    (by omega) (by omega) (by omega) hR (by omega)) using hμ.j_eq, tCol with _ _ h
  exact h

end phases

/-- **Mv-hinted Mv runs in phases**, with explicit numbers of steps. -/
theorem mv_lightPhases {P : Program} (K : DsKit P) {p₁ p₂ p₃ pCol : ℕ}
    (h1 : P[p₁]? = some mvPhase1Body) (h2 : P[p₂]? = some mvPhase2Body)
    (h3 : P[p₃]? = some (mvPhase3Body pCol)) (hc : P[pCol]? = some colBody) {lim : Limits}
    {n t : ℕ} (hn : 1 ≤ n) (ht : 1 ≤ t) (htn : t ≤ n) (hlim : K.Lim lim n t (mvFr n t) 1)
    (hdep : K.depPre t + 2 ≤ lim.depth) (hdep' : 6 ≤ lim.depth)
    (N : Matrix (Fin n) (Fin n) Bool) (V : Matrix (Fin t) (Fin n) Bool) (I : Fin t → Fin n)
    (j : Fin n) :
    ∃ c₁ c₂ c₃ : ℕ, c₁ ≤ 4 ∧ c₂ ≤ K.tPre n t + tMvGather n t + 55 ∧
      c₃ ≤ n * (K.tQ t + 30) + 64 ∧
      LightPhases lim P
        (fun μ off => ∀ r : Fin n, μ (off + r.val) = bit (MvHintedOutput N V I j r)) (fun _ => 0) 0
        [(p₁, [(n : ℤ), (t : ℤ)] ++ rowMajor (toInt N) ++ rowMajor (toInt V), c₁),
          (p₂, List.ofFn fun k => ((I k).val : ℤ), c₂), (p₃, [(j.val : ℤ)], c₃)] := by
  have hplaces := mvAddresses n t
  have hcomm : t * n = n * t := Nat.mul_comm _ _
  have hnn : n ≤ n * n := Nat.le_mul_of_pos_left n hn
  -- Phase 1 leaves the memory as it is
  have in₁ := InputsAt.first (fun _ => 0)
    ([(n : ℤ), (t : ℤ)] ++ rowMajor (toInt N) ++ rowMajor (toInt V))
  obtain ⟨σ₁, c₁, run₁, hc₁, in₁⟩ := phase_of_ends (lim := lim) (T := 0)
    (Q := fun μ' => InputsAt μ' _ _) h1 (by omega) (Ends.skip in₁)
  -- Phase 2
  have in₂ := in₁.next (List.ofFn fun k => ((I k).val : ℤ))
  obtain ⟨hμ₂, e₂⟩ := mvMem2_of_inputs in₂
  obtain ⟨σ₂, c₂, run₂, hc₂, -, hready, hsame⟩ :=
    phase_of_meets (by omega) (mvPhase2_meets K h2 hn ht htn hlim hdep hμ₂)
  -- Phase 3: the inputs lie below X, and the index j is written below X
  have in₂' := in₂.keep (μ' := σ₂.mem) (by light_keep [hsame])
  obtain ⟨hμ₃, e₃⟩ := mvMem3_of_inputs (in₂'.next [(j.val : ℤ)])
  have hwrite := in₂'.sameOutside [(j.val : ℤ)]
  obtain ⟨σ₃, c₃, run₃, hc₃, -, hout⟩ :=
    phase_of_meets (by omega)
      (mvPhase3_meets K h3 hc hn ht htn hlim hdep' hμ₃ (hready.keep (by light_keep [hwrite])))
  refine ⟨c₁, c₂, c₃, by omega, by omega, by omega, σ₁, run₁, σ₂, run₂, σ₃, run₃, fun r => ?_⟩
  rw [e₃]
  exact (hout r).trans (ite_pos_eq_bit (Corollary40.MvHintedOutput_eq_true_iff N V I j r))

end Light.Sec5
