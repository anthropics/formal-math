/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Lang.Compiler.Conditions

/-!
# Pieces of a call: the arguments and the new frame

A call first evaluates its arguments into T₀, T₁, … (`effects_argsCode`).  Then it sets up the frame
of the procedure, F + 1 stack cells further on (`effects_newFrame`): NFP receives the new frame
pointer, the local variables of the new frame receive the arguments and zeros
(`effects_frameInit`), the stack cell before the new frame receives the position to return to, and
FP moves to the new frame.  After that the memory represents the state in which the procedure
starts.
-/

public section

open ThreeSumApsp.WordRam

namespace Light.Compiler

variable {W : ℕ} {Z : Sizes W} {σ : State} {q : ℕ} {m : ℤ → BitVec W}

/-! ## The arguments -/

/-- The code of the arguments only changes the memory. -/
theorem straight_argsCode : ∀ (es : List Expr) (k : ℕ), ∀ i ∈ argsCode es k, Straight i
  | [], _ => by simp [argsCode]
  | e :: es, k => List.forall_mem_append.2 ⟨straight_compileExpr e k, straight_argsCode es (k + 1)⟩

/-- The code of the arguments leaves their values in T_k, T_{k+1}, … and changes nothing but ADDR
and the temporaries from T_k on. -/
theorem effects_argsCode (I : Framed Z σ q m) (es : List Expr) (k : ℕ)
    (hw : ∀ e ∈ es, e.width ≤ Z.F) (hs : ∀ e ∈ es, e.Safe Z.lim σ)
    (hk : k + es.length ≤ Z.F + 1) :
    (∀ i < es.length,
        effects (argsCode es k) m (cT (k + i)) = wd W (frame (es.map (·.val σ)) i)) ∧
      AgreeOutside (Temps k Z.F) m (effects (argsCode es k) m) := by
  induction es generalizing k m with
  | nil => exact ⟨fun i h => absurd h (by simp), AgreeOutside.refl _ m⟩
  | cons e es ih =>
    obtain ⟨hwe, hwes⟩ := List.forall_mem_cons.1 hw
    obtain ⟨hse, hses⟩ := List.forall_mem_cons.1 hs
    rw [List.length_cons] at hk
    obtain ⟨ve, Ae⟩ := effects_compileExpr_of_width I e k hwe hse (by omega)
    obtain ⟨ves, Aes⟩ := ih (I.same (Ae.mono temps_subset_scratch)) (k + 1) hwes hses (by omega)
    rw [argsCode, effects_append]
    refine ⟨fun i hi => ?_, Ae.trans (Aes.mono (by cells))⟩
    cases i with
    | zero => exact Aes.read (by cells) ve
    | succ i =>
      rw [show k + (i + 1) = k + 1 + i by omega]
      exact ves i (by simpa using hi)

/-! ## The new frame -/

/-- The code for one more local variable. -/
private theorem frameInit_succ (F' n : ℕ) : frameInit (F' + 1) n = frameInit F' n ++
    [.sub cADDR cNFP (cPool (2 * F')), .store cADDR (if F' < n then cT F' else cZERO)] := by
  simp [frameInit, List.range_succ, List.flatMap_append]

private theorem straight_frameInit (n : ℕ) : ∀ F' : ℕ, ∀ i ∈ frameInit F' n, Straight i
  | 0 => by simp [frameInit]
  | F' + 1 => by
    rw [frameInit_succ]
    exact List.forall_mem_append.2 ⟨straight_frameInit n F', by simp [Straight]⟩

/-- The code that fills the first F' local variables of the new frame at q': the first n from the
temporaries, the others with 0.  It changes nothing but ADDR and stack cells from q' on. -/
private theorem effects_frameInit (Z : Sizes W) (n q' F' : ℕ) (m : ℤ → BitVec W)
    (hNFP : m cNFP = wd W (cStack q'))
    (hpool : ∀ i < F', m (cPool (2 * i)) = wd W ((2 * i : ℕ) : ℤ)) (hQ : q' + F' ≤ Z.Q) :
    (∀ i < F',
        effects (frameInit F' n) m (cStack (q' + i)) = if i < n then m (cT i) else m cZERO) ∧
      AgreeOutside (insert cADDR (Stack q' Z.Q)) m (effects (frameInit F' n) m) := by
  induction F' with
  | zero => exact ⟨fun i h => absurd h (by omega), AgreeOutside.refl _ m⟩
  | succ F' ih =>
    obtain ⟨val, A⟩ := ih (fun i hi => hpool i (by omega)) (by omega)
    -- ADDR := NFP - 2 F'; the cell at ADDR := T_{F'} or 0
    rw [frameInit_succ, effects_append, effects_cons, effects_cons, effects_nil,
      effect_sub cADDR (A.read (by cells) hNFP) (A.read (by cells) (hpool F' (by omega))),
      cStack_sub, effect_store _ (Function.update_self _ _ _) (Z.inRange_stack (by omega))]
    refine ⟨fun i hi => ?_, (A.update (by cells) _).update (by cells) _⟩
    obtain rfl | hne := eq_or_ne i F'
    · rw [Function.update_self]
      split_ifs <;> rw [Function.update_of_ne (by cells), A.cell (by cells)]
    · cell_read using val i (by omega)

/-- The code of the new frame only changes the memory. -/
theorem straight_newFrame (F n ret : ℕ) : ∀ i ∈ newFrame F n ret, Straight i :=
  List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨by simp [Straight], straight_frameInit n F⟩,
    by simp [Straight]⟩

/-- The new frame.  If T₀, T₁, … hold the values of the arguments, then afterwards the memory
represents the state in which the procedure starts, in the frame q + F + 1, and the stack cell
before that frame holds the position to return to.  Of the stack, only cells from q + F on have
changed. -/
theorem effects_newFrame (I : Framed Z σ q m) (hQ : q + Z.F + 1 + Z.F ≤ Z.Q) (args : List Expr)
    (hargs : ∀ i < args.length, m (cT i) = wd W (frame (args.map (·.val σ)) i)) {ret : ℕ}
    (hret : ret ≤ Z.disp) :
    Rel Z ⟨frame (args.map (·.val σ)), σ.mem⟩ (q + Z.F + 1)
        (effects (newFrame Z.F args.length ret) m) ∧
      effects (newFrame Z.F args.length ret) m (cStack (q + Z.F)) = wd W ret ∧
      AgreeOutside (Writable Z (q + Z.F)) m (effects (newFrame Z.F args.length ret) m) := by
  have R := I.rel
  have hq := I.low
  have hN := Z.offsets_le
  simp only [newFrame, effects_append, effects_cons, effects_nil]
  -- NFP := FP - 2 (F + 1).  Up to the last instruction, only scratch cells and the stack beyond the
  -- frame q change, so the memory goes on representing σ in the frame q.
  rw [effect_sub cNFP R.fp (R.pool _ hN), cStack_sub, ← Nat.add_assoc]
  have A₁ := (AgreeOutside.refl (Scratch Z.F ∪ Stack (q + Z.F) Z.Q) m).update (a := cNFP) (by cells)
    (wd W (cStack (q + Z.F + 1)))
  -- the local variables of the new frame
  obtain ⟨val, A⟩ := effects_frameInit Z args.length (q + Z.F + 1) Z.F _
    (Function.update_self cNFP _ m) (fun i hi => (R.beyond hq A₁).pool _ (by omega)) hQ
  generalize effects (frameInit Z.F args.length) _ = m₂ at val A ⊢
  have hNFP : m₂ cNFP = wd W (cStack (q + Z.F + 1)) :=
    A.read (by cells) (Function.update_self _ _ _)
  have A₂ := A₁.trans (A.mono (by cells))
  -- ADDR := NFP + 2
  rw [effect_add cADDR hNFP ((R.beyond hq A₂).pool 2 (by omega)), cStack_succ_add]
  have A₃ := A₂.update (a := cADDR) (by cells) (wd W (cStack (q + Z.F)))
  -- the cell at ADDR := ret
  rw [effect_store _ (Function.update_self _ _ _) (Z.inRange_stack (by omega)),
    (R.beyond hq A₃).pool ret hret]
  have A₄ := A₃.update (a := cStack (q + Z.F)) (by cells) (wd W ret)
  have R₄ := R.beyond hq A₄
  -- FP := NFP + 0
  rw [effect_add cFP (by cell_read using hNFP) R₄.zero, add_zero]
  refine ⟨?_, by cell_read,
    (A₄.mono (Set.union_subset scratch_subset_writable stack_subset_writable)).update (by cells) _⟩
  refine R₄.of_agreeOutside ((AgreeOutside.refl {cFP} _).update rfl _) (by cells)
    (Function.update_self _ _ _) (fun i hi => ?_)
    fun a ha => (Function.update_of_ne (by cells) _ _).trans (R₄.mem a ha)
  -- local variable i of the new frame: argument i, or 0
  cell_read
  rw [val i hi]
  split_ifs with h
  · cell_read using hargs i h
  · cell_read
    rw [R.zero]
    simp [frame, List.getElem?_eq_none (not_lt.1 h)]

end Light.Compiler
