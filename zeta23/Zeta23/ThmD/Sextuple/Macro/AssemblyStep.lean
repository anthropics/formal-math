import Zeta23.ThmD.Sextuple.AffineTree

/-!
# One generic split step of the affine-tree replay

Every internal node of the concrete certificate tree is assembled from its two children by
this single lemma, proved once symbolically.  Concrete node lemmas are then plain
applications, so the kernel never re-evaluates any subtree replay.
-/

noncomputable section

namespace Zeta23.ThmD.Sextuple

/-- A split node replays to the result of its right child, given the token, the left child's
replay (starting at `t + 1`), and the right child's replay (starting at the left result). -/
theorem replayAffineTree_split_step {α : Type*} {leafCheck : GapBox → α → Bool}
    {topology : CursorStream AffineTreeToken} {payloads : CursorStream α}
    {fuel t p : ℕ} {box : GapBox} {axis : Fin 5} {tm pm t' p' : ℕ}
    (htok : topology.get? t = some (.split axis))
    (hl : replayAffineTree leafCheck topology payloads fuel (t + 1) p (box.lowerHalf axis) =
      some (tm, pm))
    (hr : replayAffineTree leafCheck topology payloads fuel tm pm (box.upperHalf axis) =
      some (t', p')) :
    replayAffineTree leafCheck topology payloads (fuel + 1) t p box = some (t', p') := by
  rw [replayAffineTree, htok]
  simp only [hl, hr]

end Zeta23.ThmD.Sextuple

end
