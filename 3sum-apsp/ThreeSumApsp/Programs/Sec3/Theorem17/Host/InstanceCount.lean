/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec3.Theorem17.Host.InstanceData
public import ThreeSumApsp.Sec3.Theorem17.Instances
public import ThreeSumApsp.Spec.Sec3.Theorem17.Classes

/-!
# The number of instances of the host of Theorem 17

Proof of Theorem 17: "There are at most 2√D h ≤ 2√D(ng/s + 1) ≤ 4ng instances", where `s = ⌊√D⌋` and
`h` is the number of pieces.  The host's table of chunks has as many entries as the paper's count of
the chunks (`length_chunkTab_eq_totalChunks`), and its number of pieces is the paper's
(`numPiecesNat_eq`), so the bound of `TriangleInstance.card_instanceIndices_le` applies.
-/

public section

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec

/-- Proof of Theorem 17: "There are at most 2√D h ≤ 2√D(ng/s + 1) ≤ 4ng instances".  Here `m` is the
number of instances of the host. -/
theorem HostData.m_le {n D g p : ℕ} {AB BC AC : List ℤ} (h : BigCase n D g)
    (hp : p ∈ primesInRange D) :
    (⟨n, D, p, pieceSizeNat D g, queryCapNat n D, AB, BC, AC⟩ : HostData).m ≤ 4 * n * g := by
  obtain ⟨hD, hDn, hg, -⟩ := h
  have hD1 : 1 ≤ D := by omega
  have hcap : 1 ≤ queryCapNat n D := by rw [queryCapNat_eq n hD1]; exact one_le_queryCap hD1 hDn
  -- The host's numbers of pieces and of chunks are the paper's.
  have hpieces :
      (⟨n, D, p, pieceSizeNat D g, queryCapNat n D, AB, BC, AC⟩ : HostData).h = numPieces n D g :=
    numPiecesNat_eq n D hg (pieceSize_pos hD hg)
  have hchunks : (⟨n, D, p, pieceSizeNat D g, queryCapNat n D, AB, BC, AC⟩ : HostData).chunkCount
      = (triOf n AB BC AC).totalChunks D p :=
    length_chunkTab_eq_totalChunks n AB BC AC (mem_primesInRange.mp hp).1.ne_zero hD1 hcap
  have hcard : (((triOf n AB BC AC).instanceIndices D g p).card : ℝ) ≤ ((4 * n * g : ℕ) : ℝ) := by
    push_cast
    exact (triOf n AB BC AC).card_instanceIndices_le hD hDn hg hp
  rw [HostData.m, hpieces, hchunks, Nat.mul_comm, ← TriangleInstance.card_instanceIndices]
  exact_mod_cast hcard

end Light.Sec3
