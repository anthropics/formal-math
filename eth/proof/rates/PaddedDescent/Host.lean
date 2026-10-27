/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ToTuring.PolyT
public import Mathlib.Computability.TuringMachine.Computable
import ToTuring.Machine.Host

/-! The host machine for stepped computations whose states may be large. `exists_tm'`: a stepped
computation on bit strings
whose init, step and out are polynomial-time runs on ONE of Mathlib's multi-stack machines, with ONE
constant q, such that a run
of T steps on the input x with all states of size at most S costs the machine at most
q·(T+1)·(|x|+S+1)^q steps. The machine and q
are chosen before x, T and S. The proof is that of `exists_tm`, which asks S ≤ (|x|+2)^d and lets
the constant depend on d. -/

namespace PaddedDescent

open Groundwork Groundwork.TM Groundwork.Host Turing

/-- A stepped computation `M` on bit strings with polynomial-time init, step and out runs on one of
Mathlib's multi-stack
machines `N` with finite alphabets. There is one number `q` such that, whenever `M` ends on `x` with
the bit `b` within `T`
steps and with all states of size at most `S`, the machine `N` started on `x` halts with output `b`
within
q · (T + 1) · (|x| + S + 1)^q steps. `N` and `q` depend on `M` only: not on `x`, `T`, `S`. -/
public theorem exists_tm' (M : Stepped (List Bool) Bool) [IsPolyT M] :
    ∃ (N : TM2ComputableAux Bool Bool) (q : ℕ), (∀ k, Finite (N.tm.Γ k)) ∧
      ∀ (x : List Bool) (T S : ℕ) (b : Bool), M.Runs x T S b →
        Nonempty (TM2OutputsInTime N.tm (x.map N.inputAlphabet.invFun) (some ([b].map N.outputAlphabet.invFun))
          (q * (T + 1) * (x.length + S + 1) ^ q)) := by
  obtain ⟨Pi, tI, pI, mI, hI, -⟩ := (IsPolyT.init (M := M)).elim
  obtain ⟨Ps, tS, pS, mS, hS, -⟩ := (IsPolyT.step (M := M)).elim
  obtain ⟨Po, tO, pO, mO, hO, -⟩ := (IsPolyT.out (M := M)).elim
  have pL : PB fun m => 7 * m := (PB.const 7).mul PB.id'
  have pK : PB fun m => 3 * (7 * m) + 3 + tO (7 * m) :=
    (((PB.const 3).mul pL).add (PB.const 3)).add (pO.comp pL)
  have pG : PB fun m => 1 + (tS (7 * m) + (3 * (7 * m) + 3 + tO (7 * m))) :=
    (PB.const 1).add ((pS.comp pL).add pK)
  have pQ : PB fun m => (4 * m + 3 + (tI (3 * m + 2) + (3 * (7 * m) + 3 + tO (7 * m))) + 1 +
      (7 * m + 1)) + (1 + (tS (7 * m) + (3 * (7 * m) + 3 + tO (7 * m)))) :=
    ((((((PB.const 4).mul PB.id').add (PB.const 3)).add
      ((pI.comp (((PB.const 3).mul PB.id').add (PB.const 2))).add pK)).add (PB.const 1)).add
      (pL.add (PB.const 1))).add pG
  obtain ⟨q, hq⟩ := pQ
  refine ⟨⟨tmOf (prog Pi Ps Po), Equiv.refl _, Equiv.refl _⟩, q, fun k => ?_, fun x T S b hr => ?_⟩
  · rcases k with _ | k
    · exact inferInstanceAs (Finite Bool)
    · exact inferInstanceAs (Finite Sym)
  · obtain ⟨m, hm⟩ : ∃ m, m = x.length + S := ⟨_, rfl⟩
    obtain ⟨L, hLdef⟩ : ∃ L, L = 7 * m := ⟨_, rfl⟩
    have hL : ∀ s : M.σ, size s ≤ S → len s ≤ L := fun s hs => by
      have h1 := Carried.le s
      omega
    obtain ⟨s', hs', h3⟩ := mainLoop_within hS hO mS mO hL hr
    have h1 := prologue_within x
    have h2 := within_io ((hI x [] [] [] []).seq (look_within hO (M.init x) [] [] [] [])) []
    have h4 := within_io (dropF_within (Enc.toV s') [] [] [] []) [b]
    rw [List.append_nil] at h2
    have h := ((h1.seq h2).seq h3).seq h4
    have hq' := hq m
    dsimp only at hq'
    rw [← hLdef] at hq'
    refine outputs_of_within (h.mono ?_) (List.map_id x) (List.map_id [b])
    have g1 := hL _ (size_le_of_reaches hr)
    have g2 := mO g1
    have g3 : (code (Enc.toV s')).length ≤ L := hL s' hs'
    have g4 : len x = 3 * x.length + 2 := len_bools x
    have g6 : tI (3 * x.length + 2) ≤ tI (3 * m + 2) := mI (by omega)
    rw [g4]
    obtain ⟨G, hG⟩ : ∃ G, G = 1 + (tS L + (3 * L + 3 + tO L)) := ⟨_, rfl⟩
    rw [← hG] at hq' ⊢
    rw [← hm]
    obtain ⟨Y, hY⟩ : ∃ Y, Y = q * (m + 1) ^ q := ⟨_, rfl⟩
    have e : q * (T + 1) * (m + 1) ^ q = T * Y + Y := by rw [hY]; ring
    rw [e]
    rw [← hY] at hq'
    have g5 : T * G ≤ T * Y := Nat.mul_le_mul_left _ (by omega)
    omega

end PaddedDescent
