/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec2.Theorem5.Contracts

/-!
# Theorem 5 in the light language: gathering the codes in sorted order

Section 2.4.4: "sort the sets W_T", the wanted positions of each tile T.  Sorting produces a
permutation of the wanted positions.  The procedure gather(w, perm, src, dst) then copies their
codes into sorted order: dst[i] := src[perm[i]] for i < w.

gather_entry shows that a call ends within 20 (w + 1) steps, with dst[i] = src[π[i]] for the list π
at perm, and that no cell outside the w cells of dst has changed.  The proof is one loop with the
invariant GatherInv; each round reads two cells that are still as at the start and writes dst[i].
-/

@[expose] public section

namespace Light.Sec2

open ThreeSumApsp

variable {lim : Limits} {P : Program}

namespace GatherLocal

/-- The number w of cells. -/
abbrev Len : ℕ := 0
/-- The permutation. -/
abbrev Perm : ℕ := 1
/-- The array that is read. -/
abbrev Src : ℕ := 2
/-- The array that is written. -/
abbrev Dest : ℕ := 3
/-- The counter i of the loop. -/
abbrev Pos : ℕ := 4

end GatherLocal

open GatherLocal

/-- gather(w, perm, src, dst): dst[i] := src[perm[i]] for i < w. -/
def gatherBody : Stmt :=
  .for Pos (v Len) (.store (v Dest +' v Pos) (M (v Src +' M (v Perm +' v Pos))))

/-- The memory before round i: the first i cells of dst are filled, and no cell outside the w cells
of dst has changed. -/
def GatherInv (μ : ℕ → ℤ) (w src dst : ℕ) (π : List ℕ) (i : ℕ) (μ' : ℕ → ℤ) : Prop :=
  (∀ j (h : j < π.length), j < i → μ' (dst + j) = μ (src + π[j])) ∧ SameOutside μ μ' dst w

/-- **gather**: a call ends within 20 (w + 1) steps with dst[i] = src[π[i]] for i < w, and no cell
outside the w cells of dst has changed. -/
theorem gather_entry (std : Std lim) (hP : P[pGather]? = some gatherBody) {c : ℕ} (hc : 20 ≤ c) :
    GatherSpec lim P c := by
  intro w perm src dst μ π hspace hlen hperm hlt hpermDst hsrcDst d _
  have hword := std.space_le
  have hconst := std.const_le
  refine .mono_const (.of_body hP ?_) hc
  -- for i < w
  refine Ends.forFrame (GatherInv μ w src dst π) w
    ⟨fun j _ hj => absurd hj (by omega), .refl⟩ ?round ?done
  case round =>
    rintro i μ' hi ⟨filled, rest⟩
    -- The two cells that the round reads are still as at the start: perm[i] = π[i], and src[π[i]].
    have hiπ : i < π.length := by omega
    have hentry : π[i] < w := hlt _ (List.getElem_mem _)
    have hp : μ' (perm + i) = (π[i] : ℕ) := (rest _ (by omega)).trans (hperm.getElem hiπ)
    have hs : μ' (src + π[i]) = μ (src + π[i]) := rest _ (by omega)
    -- dst[i] := src[perm[i]]
    light_store (dst + i) (μ (src + π[i])) using hp, hs
    refine ⟨rfl, fun j hj hji => ?_, rest.update ⟨by omega, by omega⟩ _⟩
    -- The cells below dst + i are as before, and the cell dst + i has just been written.
    rcases Nat.lt_succ_iff_lt_or_eq.1 hji with hji | rfl
    · exact (Function.update_of_ne (by omega) _ _).trans (filled j hj hji)
    · exact Function.update_self ..
  case done => exact fun μ' ⟨filled, rest⟩ => ⟨fun j hj => filled j hj (by omega), rest⟩

end Light.Sec2
