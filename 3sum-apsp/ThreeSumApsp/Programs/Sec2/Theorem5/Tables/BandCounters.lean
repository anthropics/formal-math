/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec2.Theorem5.Contracts
public import ThreeSumApsp.Spec.Sec2.Theorem5.Counters

/-!
# Band and block of every row, by counting (Section 2.3.4)

Section 2.3.4 cuts the N rows of X into bands of K₀ blocks of N₀ rows.  counters(N, K0, N0, dst)
writes, for every row I < N, its band I / (K0 N0) to the cell dst + I and its block I / N0 % K0 to
the cell dst + N + I.  There is no division: three counters (band, block, offset) are stepped from
each row to the next, as `Spec.stepCtr` says, and `Spec.ctrAt_succ` says that they are the
quotients and remainders.

A round writes two cells (`Counted.step`) and steps the counters (`countersRound_spec`);
`counters_spec` runs through the rows, and `counters_entry` is the specification that the callers of
the procedure assume.
-/

@[expose] public section

namespace Light.Sec2

open ThreeSumApsp

variable {lim : Limits} {P : Program} {d : ℕ}

namespace Counters

/-- The local variables of counters: Total = N, Blocks = K0, Width = N0, Dest = dst (the arguments);
Row is the current row, and Band, Block, Offset are its band, its block and its offset. -/
abbrev Total : ℕ := 0
@[inherit_doc Total] abbrev Blocks : ℕ := 1
@[inherit_doc Total] abbrev Width : ℕ := 2
@[inherit_doc Total] abbrev Dest : ℕ := 3
@[inherit_doc Total] abbrev Row : ℕ := 4
@[inherit_doc Total] abbrev Band : ℕ := 5
@[inherit_doc Total] abbrev Block : ℕ := 6
@[inherit_doc Total] abbrev Offset : ℕ := 7

end Counters

open Counters in
/-- One round: the band and the block of the current row are written, and the counters move on to
the next row. -/
def countersRound : Stmt :=
  .store (v Dest +' v Row) (v Band) ;;
  .store (v Dest +' v Total +' v Row) (v Block) ;;
  .set Row (v Row +' k 1) ;;
  .set Offset (v Offset +' k 1) ;;
  .ite (v Offset <' v Width) .skip (
    .set Offset (k 0) ;;
    .set Block (v Block +' k 1) ;;
    .ite (v Block <' v Blocks) .skip (
      .set Block (k 0) ;;
      .set Band (v Band +' k 1)))

open Counters in
/-- counters(N, K0, N0, dst).  The row and the three counters are not set at the beginning: local
variables that are not arguments start at 0. -/
def countersBody : Stmt := .while (v Row <' v Total) countersRound

namespace Counters

variable {μ μ' : ℕ → ℤ} {N K0 N0 dst i : ℕ}

/-- The memory before round i: band and block of the rows below i are written, and no cell outside
the 2 N cells from dst has changed. -/
def Counted (μ : ℕ → ℤ) (N K0 N0 dst i : ℕ) (μ' : ℕ → ℤ) : Prop :=
  (∀ I < i, μ' (dst + I) = (I / (K0 * N0) : ℕ) ∧ μ' (dst + N + I) = (I / N0 % K0 : ℕ)) ∧
    SameOutside μ μ' dst (2 * N)

/-- The two cells that round i writes. -/
theorem Counted.step (h : Counted μ N K0 N0 dst i μ') (hi : i < N) :
    Counted μ N K0 N0 dst (i + 1) (Function.update (Function.update μ' (dst + i)
      ((Spec.ctrAt K0 N0 i).band : ℕ)) (dst + N + i) ((Spec.ctrAt K0 N0 i).block : ℕ)) := by
  refine ⟨fun I hI => ?_, (h.2.update ⟨by omega, by omega⟩ _).update ⟨by omega, by omega⟩ _⟩
  rcases Nat.lt_succ_iff_lt_or_eq.1 hI with hI | rfl
  · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
    exact h.1 I hI
  · rw [Function.update_of_ne (by omega), Function.update_self, Function.update_self]
    exact ⟨rfl, rfl⟩

/-- The state before round i: the counters are those of row i. -/
def Inv (μ : ℕ → ℤ) (N K0 N0 dst i : ℕ) (σ : State) : Prop :=
  ∃ μ' : ℕ → ℤ, σ = ⟨frame [N, K0, N0, dst, i, (Spec.ctrAt K0 N0 i).band,
    (Spec.ctrAt K0 N0 i).block, (Spec.ctrAt K0 N0 i).off], μ'⟩ ∧ Counted μ N K0 N0 dst i μ'

end Counters

open Counters

variable {μ : ℕ → ℤ} {N K0 N0 dst : ℕ}

/-- **One round** writes the band and the block of row `i` and steps the counters to those of row
`i + 1`. -/
theorem countersRound_spec (std : Std lim) (hsp : dst + 2 * N ≤ lim.space) (hK : 0 < K0)
    (hN0 : 0 < N0) (hw : ((K0 + N0 : ℕ) : ℤ) ≤ lim.word) {i : ℕ} (hi : i < N) {σ : State}
    (h : Inv μ N K0 N0 dst i σ) :
    Ends lim P d countersRound σ countersRound.blockCost (Inv μ N K0 N0 dst (i + 1)) := by
  obtain ⟨μ', rfl, hI⟩ := h
  light_facts std
  push_cast at hw
  have hnext := Spec.ctrAt_succ hK hN0 i
  have hstep := hI.step hi
  have hband : (Spec.ctrAt K0 N0 i).band ≤ i := Nat.div_le_self _ _
  have hblock : (Spec.ctrAt K0 N0 i).block < K0 := Nat.mod_lt _ hK
  have hoff : (Spec.ctrAt K0 N0 i).off < N0 := Nat.mod_lt _ hN0
  generalize Spec.ctrAt K0 N0 i = c at *
  unfold countersRound
  rw [Spec.stepCtr] at hnext
  -- mem[dst + Row] := Band; mem[dst + N + Row] := Block; Row := Row + 1; Offset := Offset + 1
  light_store (dst + i) c.band
  light_store (dst + N + i) c.block
  light_set (i + 1 : ℕ)
  light_set (c.off + 1 : ℕ)
  -- if Offset < N0
  refine Ends.iteLast (fun hc => Ends.skip ⟨_, ?_, hstep⟩) fun hc => ?_
  · -- The next row of the same block.
    rw [hnext, if_pos (by simp at hc; omega)]
    rfl
  -- Offset := 0; Block := Block + 1; if Block < K0
  light_set 0
  light_set (c.block + 1 : ℕ)
  refine Ends.iteLast (fun hc' => Ends.skip ⟨_, ?_, hstep⟩) fun hc' => ?_
  · -- The first row of the next block of the same band.
    rw [hnext, if_neg (by simp at hc; omega), if_pos (by simp at hc'; omega)]
    rfl
  · -- The first row of the first block of the next band: Block := 0; Band := Band + 1
    refine Ends.setToThen 0 (Ends.setTo ((c.band + 1 : ℕ) : ℤ) ⟨_, ?_, hstep⟩)
    rw [hnext, if_neg (by simp at hc; omega), if_neg (by simp at hc'; omega)]
    rfl

/-- **counters** writes the band and the block of every row and changes nothing else. -/
theorem counters_spec (std : Std lim) (hsp : dst + 2 * N ≤ lim.space) (hK : 0 < K0) (hN0 : 0 < N0)
    (hw : ((K0 + N0 : ℕ) : ℤ) ≤ lim.word) :
    Ends lim P d countersBody ⟨frame [N, K0, N0, dst], μ⟩ (44 * (N + 1)) fun σ' =>
      (∀ I < N, σ'.mem (dst + I) = (I / (K0 * N0) : ℕ) ∧
        σ'.mem (dst + N + I) = (I / N0 % K0 : ℕ)) ∧ SameOutside μ σ'.mem dst (2 * N) := by
  have hspace := std.space_le
  -- while Row < N; a round takes at most 40 steps
  refine Ends.whileConst (Inv μ N K0 N0 dst) N countersRound.blockCost ?start ?round ?done
    (by simp [countersRound]; omega)
  case start =>
    refine ⟨μ, ?_, fun I hI => absurd hI (by omega), .refl⟩
    -- The row and the three counters start at 0.
    rw [← frame_append_zeros _ 4]
    simp [Spec.ctrAt]
  case round =>
    intro i σ hi h
    have hround := countersRound_spec (P := P) (d := d) std hsp hK hN0 hw hi h
    obtain ⟨μ', rfl, -⟩ := h
    exact ⟨by light_side, by light_side, hround⟩
  case done =>
    rintro _ ⟨μ', rfl, hcells, same⟩
    exact ⟨by light_side, by light_side, hcells, same⟩

/-- **The specification that the callers of counters assume.** -/
theorem counters_entry (std : Std lim) (hP : P[pCounters]? = some countersBody) {c : ℕ}
    (hc : 44 ≤ c) : CountersSpec lim P c :=
  fun _ _ _ _ _ hsp hK hN0 hw _ _ => .mono_const (.of_body hP (counters_spec std hsp hK hN0 hw)) hc

end Light.Sec2
