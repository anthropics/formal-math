/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec5.Corollary40.Column
public import ThreeSumApsp.Programs.Sec5.Corollary40.PhaseLayout

/-!
# Corollary 40: v-hinted Mv as a light program that runs in phases

Proof of Corollary 40, paragraph "Conjecture 5.2 of [vdBNS19]": "we preprocess X := M and Y := V
[...]  In Phase 3, the n entries of column i of MV are n queries".

The inputs of the phases lie one after the other: n in cell 0, t in cell 1, M from cell 2, V from
cell 2 + nt, the index i in cell 2 + 2nt, and the n cells of the output from 3 + 2nt on (`VMem2`,
`VMem3`).  The data structure, an arbitrary kit, is built from the cell 3 + 2nt + 3n on.  Phase 1
returns at once.  Phase 2 preprocesses M and V where they lie (`vPhase2_meets`).  Phase 3 asks the n
queries (`vPhase3_meets`).  `v_lightPhases` puts the phases together.
-/

@[expose] public section

namespace Light.Sec5

open ThreeSumApsp ThreeSumApsp.WordRam ThreeSumApsp.HintedMv ThreeSumApsp.Spec.Sec5 Light.Sec4
open ThreeSumApsp.Corollary40 (abs_toInt_le)

/-- The first cell of the data structure. -/
def vFr (n t : ℕ) : ℕ := 3 + 2 * (n * t) + 3 * n

/-- The addresses, written out. -/
theorem vAddresses (n t : ℕ) :
    vV n t = 2 + n * t ∧ vI n t = 2 + 2 * (n * t) ∧ vOut n t = 3 + 2 * (n * t) ∧
      vFr n t = 3 + 2 * (n * t) + 3 * n := by
  have hcomm : t * n = n * t := Nat.mul_comm _ _
  unfold vFr vOut vI vV
  omega

namespace VHinted

/-- The locals of Phases 2 and 3: n, t, the number nt of cells of a matrix, the address of V, the
first cell of the data structure, and the result of the call, which is not used. -/
abbrev Size : ℕ := 0
@[inherit_doc Size] abbrev Thin : ℕ := 1
@[inherit_doc Size] abbrev Cells : ℕ := 2
@[inherit_doc Size] abbrev AddrV : ℕ := 3
@[inherit_doc Size] abbrev Free : ℕ := 4
@[inherit_doc Size] abbrev Result : ℕ := 5

end VHinted

open VHinted

/-- Phase 1 does nothing. -/
def vPhase1Body : Stmt := .skip

/-- The start of Phases 2 and 3: n and t are read from cells 0 and 1, and the addresses are computed
from them. -/
def vAddr : Stmt :=
  .set Size (M (k 0)) ;;
  .set Thin (M (k 1)) ;;
  .set Cells (v Size *' v Thin) ;;
  .set AddrV (k 2 +' v Cells) ;;
  .set Free (k 3 +' k 2 *' v Cells +' k 3 *' v Size)

/-- Phase 2: pre(n, t, 2, aV, fr). -/
def vPhase2Body : Stmt :=
  vAddr ;;
  .call Proc.pre31 [v Size, v Thin, k 2, v AddrV, v Free] Result

/-- Phase 3: col(n, t, 2, aV, fr, i, out), where i is read from the cell after V. -/
def vPhase3Body (pCol : ℕ) : Stmt :=
  vAddr ;;
  .call pCol [v Size, v Thin, k 2, v AddrV, v Free, M (v AddrV +' v Cells),
    k 3 +' k 2 *' v Cells] Result

/-- **Sizes and addresses.**  `vAddr` leaves n, t, nt, the address of V and the first cell of the
data structure in the locals, and changes no cell. -/
theorem vAddr_spec {lim : Limits} {P : Program} {d n t : ℕ} {μ : ℕ → ℤ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hsp : vFr n t < lim.space) (hn : μ 0 = n) (ht : μ 1 = t) :
    Ends lim P d vAddr ⟨frame [0, 0], μ⟩ 24 fun σ' =>
      σ' = ⟨frame [(n : ℤ), t, (n * t : ℕ), vV n t, vFr n t], μ⟩ := by
  have hplaces := vAddresses n t
  unfold vAddr
  light_set n using hn
  light_set t using ht
  light_set (n * t : ℕ)
  light_set (vV n t)
  light_set (vFr n t)
  rfl

section phases

variable {P : Program} (K : DsKit P) {lim : Limits} {n t : ℕ} {μ : ℕ → ℤ}
  {A : Matrix (Fin n) (Fin t) Bool} {V : Matrix (Fin t) (Fin n) Bool}

/-- **Phase 2** preprocesses M and V where they lie: the data structure is ready, and only its cells
have changed. -/
theorem vPhase2_meets {p₂ : ℕ} (h2 : P[p₂]? = some vPhase2Body) (hn : 1 ≤ n) (ht : 1 ≤ t)
    (hlim : K.Lim lim n t (vFr n t) 1) (hdep : K.depPre t + 2 ≤ lim.depth) (hμ : VMem2 μ A V) :
    Meets lim P p₂ 1 [0, 0] μ (K.tPre n t + 36) fun _ μ' =>
      K.Ready (toInt A) (toInt V) 2 (vV n t) (vFr n t) μ' ∧
        SameOutside μ μ' (vFr n t) (K.size n t) := by
  obtain ⟨hw, h100, hsp, hsz⟩ := K.basics hlim
  have hplaces := vAddresses n t
  have hcomm : t * n = n * t := Nat.mul_comm _ _
  refine .of_body h2 ?_
  unfold vPhase2Body
  light_piece (vAddr_spec hw (by omega) hμ.n_eq hμ.t_eq) with _ rfl
  -- pre(n, t, 2, aV, fr)
  light_call (K.pre
    { one_le_D := ht, one_le_N := hn, lim := hlim, absX := abs_toInt_le _, absY := abs_toInt_le _
      belowX := by omega, belowY := by omega }
    hμ.matM hμ.matV _ (by omega)) with _ _ h
  exact h

/-- **Phase 3** asks the n queries for column i: output cell r tells whether the entry (r, i) of the
product of M and V over the integers is positive. -/
theorem vPhase3_meets {p₃ pCol : ℕ} (h3 : P[p₃]? = some (vPhase3Body pCol))
    (hc : P[pCol]? = some colBody) (ht : 1 ≤ t) (hlim : K.Lim lim n t (vFr n t) 1)
    (hdep : 6 ≤ lim.depth) {i : Fin n} (hμ : VMem3 μ A V i)
    (hR : K.Ready (toInt A) (toInt V) 2 (vV n t) (vFr n t) μ) :
    Meets lim P p₃ 1 [0, 0] μ (n * (K.tQ t + 30) + 56) fun _ μ' =>
      ∀ r : Fin n, μ' (vOut n t + r) = if 0 < (toInt A * toInt V) r i then 1 else 0 := by
  obtain ⟨hw, h100, hsp, hsz⟩ := K.basics hlim
  have hplaces := vAddresses n t
  have hcomm : t * n = n * t := Nat.mul_comm _ _
  have haddr : ((vV n t : ℤ) + n * t).toNat = vI n t := by omega
  refine .of_body h3 ?_
  unfold vPhase3Body
  light_piece (vAddr_spec hw (by omega) hμ.n_eq hμ.t_eq) with _ rfl
  -- col(n, t, 2, aV, fr, i, out)
  light_call (col_meets K hc (out := vOut n t) i
    { one_le_D := ht, one_le_N := i.pos, lim := hlim, absX := abs_toInt_le _, absY := abs_toInt_le _
      belowX := by omega, belowY := by omega }
    (by omega) (by omega) (by omega) hR (by omega)) using haddr, hμ.i_eq, tCol with _ _ h
  exact h

end phases

/-- **v-hinted Mv runs in phases**, with explicit numbers of steps. -/
theorem v_lightPhases {P : Program} (K : DsKit P) {p₁ p₂ p₃ pCol : ℕ}
    (h1 : P[p₁]? = some vPhase1Body) (h2 : P[p₂]? = some vPhase2Body)
    (h3 : P[p₃]? = some (vPhase3Body pCol)) (hc : P[pCol]? = some colBody) {lim : Limits}
    {n t : ℕ} (hn : 1 ≤ n) (ht : 1 ≤ t) (hlim : K.Lim lim n t (vFr n t) 1)
    (hdep : K.depPre t + 2 ≤ lim.depth) (hdep' : 6 ≤ lim.depth)
    (A : Matrix (Fin n) (Fin t) Bool) (V : Matrix (Fin t) (Fin n) Bool) (i : Fin n) :
    ∃ c₁ c₂ c₃ : ℕ, c₁ ≤ 4 ∧ c₂ ≤ K.tPre n t + 40 ∧ c₃ ≤ n * (K.tQ t + 30) + 60 ∧
      LightPhases lim P
        (fun μ off => ∀ r : Fin n, μ (off + r.val) = bit (vHintedOutput A V i r)) (fun _ => 0) 0
        [(p₁, [(n : ℤ), (t : ℤ)] ++ rowMajor (toInt A), c₁), (p₂, rowMajor (toInt V), c₂),
          (p₃, [(i.val : ℤ)], c₃)] := by
  have hplaces := vAddresses n t
  have hcomm : t * n = n * t := Nat.mul_comm _ _
  -- Phase 1 leaves the memory as it is
  have in₁ := InputsAt.first (fun _ => 0) ([(n : ℤ), (t : ℤ)] ++ rowMajor (toInt A))
  obtain ⟨σ₁, c₁, run₁, hc₁, in₁⟩ := phase_of_ends (lim := lim) (T := 0)
    (Q := fun μ' => InputsAt μ' _ _) h1 (by omega) (Ends.skip in₁)
  -- Phase 2
  have in₂ := in₁.next (rowMajor (toInt V))
  obtain ⟨hμ₂, e₂⟩ := vMem2_of_inputs in₂
  obtain ⟨σ₂, c₂, run₂, hc₂, -, hready, hsame⟩ :=
    phase_of_meets (by omega) (vPhase2_meets K h2 hn ht hlim hdep hμ₂)
  -- Phase 3: the inputs lie below the data structure, and the index i is written below it
  have in₂' := in₂.keep (μ' := σ₂.mem) (by light_keep [hsame])
  obtain ⟨hμ₃, e₃⟩ := vMem3_of_inputs (in₂'.next [(i.val : ℤ)])
  have hwrite := in₂'.sameOutside [(i.val : ℤ)]
  obtain ⟨σ₃, c₃, run₃, hc₃, -, hout⟩ :=
    phase_of_meets (by omega)
      (vPhase3_meets K h3 hc ht hlim hdep' hμ₃ (hready.keep (by light_keep [hwrite])))
  refine ⟨c₁, c₂, c₃, by omega, by omega, by omega, σ₁, run₁, σ₂, run₂, σ₃, run₃, fun r => ?_⟩
  rw [e₃, hout r]
  exact ite_pos_eq_bit (Corollary40.vHintedOutput_eq_true_iff A V i r)

end Light.Sec5
