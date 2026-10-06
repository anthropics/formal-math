/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Lang.Calls
public import ThreeSumApsp.Lang.Lib.Pass

/-!
# Copying and filling a segment

copy(src, dst, n) copies n cells from src to dst (the two segments do not overlap), within
`copyTime n` steps.  fill(dst, n, x) writes x into n cells from dst, within `fillTime n` steps.
Both change no other cell (`copy_meets`, `fill_meets`).  Each of the two is one pass over the cells
from dst, so `Ends.pass` says what it does, and the proof only says what round i reads.
-/

@[expose] public section

namespace Light

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## copy -/

namespace Copy

/-- The local variables of copy: the arguments src, dst and n, and the counter. -/
abbrev Src : ℕ := 0
@[inherit_doc Src] abbrev Dst : ℕ := 1
@[inherit_doc Src] abbrev Len : ℕ := 2
@[inherit_doc Src] abbrev Idx : ℕ := 3

end Copy

open Copy in
/-- copy(src, dst, n): for i < n, dst[i] := src[i]. -/
def copyBody : Stmt := pass Idx (v Len) (v Dst) (M (v Src +' v Idx))

/-- The time of copy. -/
@[simp] def copyTime (n : ℕ) : ℕ := 16 * n + 6

/-- **copy(src, dst, n)** copies the n cells from src to dst and changes nothing else. -/
theorem copy_meets {p : ℕ} (hp : P[p]? = some copyBody) {μ : ℕ → ℤ} {src dst n : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hsrc : src + n ≤ lim.space) (hdst : dst + n ≤ lim.space)
    (hsep : Apart src n dst n) :
    Meets lim P p d [(src : ℤ), dst, n] μ (copyTime n) fun _ μ' =>
      (∀ i < n, μ' (dst + i) = μ (src + i)) ∧ SameOutside μ μ' dst n := by
  refine .of_body hp (Ends.pass (fun i => μ (src + i)) (fun i hi => ?_)
    ⟨fun i hi => wrote_done (f := fun i => μ (src + i)) hi, by light_keep⟩ hw hdst rfl rfl
    (hT := by light_time [copyTime]))
  -- Round i reads src[i], which no earlier round has written.
  have hread : wrote μ dst (fun i => μ (src + i)) i (src + i) = μ (src + i) :=
    wrote_rest (by omega)
  light_side [hread]

/-! ## fill -/

namespace Fill

/-- The local variables of fill: the arguments dst, n and x, and the counter. -/
abbrev Dst : ℕ := 0
@[inherit_doc Dst] abbrev Len : ℕ := 1
@[inherit_doc Dst] abbrev Val : ℕ := 2
@[inherit_doc Dst] abbrev Idx : ℕ := 3

end Fill

open Fill in
/-- fill(dst, n, x): for i < n, dst[i] := x. -/
def fillBody : Stmt := pass Idx (v Len) (v Dst) (v Val)

/-- The time of fill. -/
@[simp] def fillTime (n : ℕ) : ℕ := 13 * n + 6

/-- **fill(dst, n, x)** writes x into the n cells from dst and changes nothing else. -/
theorem fill_meets {p : ℕ} (hp : P[p]? = some fillBody) {μ : ℕ → ℤ} {dst n : ℕ} {x : ℤ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hdst : dst + n ≤ lim.space) :
    Meets lim P p d [(dst : ℤ), n, x] μ (fillTime n) fun _ μ' =>
      Seg μ' dst (List.replicate n x) ∧ SameOutside μ μ' dst n :=
  .of_body hp (Ends.pass (fun _ => x) (fun i hi => by light_side)
    ⟨seg_wrote List.length_replicate fun i hi => List.getElem_replicate .., by light_keep⟩
    hw hdst rfl rfl (hT := by light_time [fillTime]))

end Light
