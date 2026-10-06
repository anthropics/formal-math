import Zeta23.ThmD.Sextuple.A1285.Layout

/-! The two-level readers of the `A = 257 / 20000` certificate agree with the audited flat readers. -/

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace Zeta23.ThmD.Sextuple.MacroPrototype.A1285

open Zeta23.ThmD.Sextuple

def blockedListRead (blockSize : ℕ) (blocks : List (List ℕ)) (k : ℕ) : Option ℕ :=
  match blocks[k / blockSize]? with
  | none => none
  | some blk => blk[k % blockSize]?

def UniformBlocks (blockSize : ℕ) : List (List ℕ) → Prop
  | [] => True
  | [blk] => blk.length ≤ blockSize
  | blk :: rest => blk.length = blockSize ∧ UniformBlocks blockSize rest

def uniformBlocksBool (blockSize : ℕ) : List (List ℕ) → Bool
  | [] => true
  | [blk] => decide (blk.length ≤ blockSize)
  | blk :: rest => decide (blk.length = blockSize) && uniformBlocksBool blockSize rest

theorem uniformBlocksBool_sound {blockSize : ℕ} :
    ∀ {blocks : List (List ℕ)}, uniformBlocksBool blockSize blocks = true →
      UniformBlocks blockSize blocks
  | [], _ => trivial
  | [blk], h => by simpa [uniformBlocksBool, UniformBlocks] using h
  | blk :: b :: rest, h => by
      simp only [uniformBlocksBool, Bool.and_eq_true, decide_eq_true_eq] at h
      exact ⟨h.1, uniformBlocksBool_sound h.2⟩

theorem blockedListRead_eq_flatten {blockSize : ℕ} (hB : 0 < blockSize) :
    ∀ (blocks : List (List ℕ)), UniformBlocks blockSize blocks →
      ∀ k, blockedListRead blockSize blocks k = blocks.flatten[k]?
  | [], _, k => by simp [blockedListRead]
  | [blk], hlen, k => by
      simp only [UniformBlocks] at hlen
      by_cases hk : k < blockSize
      · simp [blockedListRead, Nat.div_eq_of_lt hk, Nat.mod_eq_of_lt hk]
      · have hk' : blockSize ≤ k := Nat.le_of_not_lt hk
        have hdiv : 1 ≤ k / blockSize := (Nat.le_div_iff_mul_le hB).2 (by simpa using hk')
        have hnone : ([blk] : List (List ℕ))[k / blockSize]? = none := by
          rw [List.getElem?_eq_none_iff]; simpa using hdiv
        have hflat : blk[k]? = none := by
          rw [List.getElem?_eq_none_iff]; exact hlen.trans hk'
        simp [blockedListRead, hnone, hflat]
  | blk :: b :: rest, hlen, k => by
      obtain ⟨hblk, hrest⟩ := hlen
      have ih := blockedListRead_eq_flatten hB (b :: rest) hrest
      by_cases hk : k < blockSize
      · have hkl : k < blk.length := hblk ▸ hk
        simp [blockedListRead, Nat.div_eq_of_lt hk, Nat.mod_eq_of_lt hk,
          List.getElem?_append_left hkl]
      · have hk' : blockSize ≤ k := Nat.le_of_not_lt hk
        obtain ⟨j, rfl⟩ : ∃ j, k = j + blockSize := ⟨k - blockSize, by omega⟩
        have hdiv : (j + blockSize) / blockSize = j / blockSize + 1 := Nat.add_div_right j hB
        have hmod : (j + blockSize) % blockSize = j % blockSize := Nat.add_mod_right j blockSize
        have hlenle : blk.length ≤ j + blockSize := by omega
        simp only [blockedListRead, hdiv, hmod, List.getElem?_cons_succ, List.flatten_cons,
          List.getElem?_append_right hlenle, hblk, Nat.add_sub_cancel]
        exact ih j

theorem blockedWordRead_eq_list (blockSize : ℕ) (blocks : Array (Array ℕ)) (k : ℕ) :
    blockedWordRead blockSize blocks k =
      blockedListRead blockSize (blocks.toList.map Array.toList) k := by
  unfold blockedWordRead blockedListRead
  rw [← Array.getElem?_toList, List.getElem?_map]
  cases blocks.toList[k / blockSize]? with
  | none => rfl
  | some blk => simp [Array.getElem?_toList]

theorem improvedTopologyBlocks_uniform :
    UniformBlocks improvedTopologyBlockSize (improvedTopologyBlocks.toList.map Array.toList) :=
  uniformBlocksBool_sound (by decide +kernel)

theorem improvedLeafBlockGroups_uniform :
    UniformBlocks improvedLeafGroupSize (improvedLeafBlockGroups.toList.map Array.toList) :=
  uniformBlocksBool_sound (by decide +kernel)

theorem improvedTopologyWordRead_eq (k : ℕ) :
    blockedWordRead improvedTopologyBlockSize improvedTopologyBlocks k =
      improvedTopologyWords[k]? := by
  rw [blockedWordRead_eq_list,
    blockedListRead_eq_flatten (by decide) _ improvedTopologyBlocks_uniform k,
    ← Array.getElem?_toList]
  rfl

theorem improvedLeafBlockRead_eq (k : ℕ) :
    blockedWordRead improvedLeafGroupSize improvedLeafBlockGroups k =
      improvedLeafBlocks[k]? := by
  rw [blockedWordRead_eq_list,
    blockedListRead_eq_flatten (by decide) _ improvedLeafBlockGroups_uniform k,
    ← Array.getElem?_toList]
  rfl

theorem improvedTopologyStream_eq_packed :
    improvedTopologyStream = packedTopologyStream improvedTokenCount improvedTopologyWords := by
  unfold improvedTopologyStream blockedTopologyStream packedTopologyStream
  congr 1
  funext cursor
  unfold blockedTopologyRead packedTopologyRead
  rw [improvedTopologyWordRead_eq]
  rfl

theorem improvedPayloadStream_eq_packed :
    improvedPayloadStream = improvedPackedLeafStream improvedLeafCount improvedLeafBlocks := by
  unfold improvedPayloadStream groupedLeafStream improvedPackedLeafStream
  congr 1
  funext p
  unfold groupedLeafWordRead improvedLeafWordRead
  rw [improvedLeafBlockRead_eq]

#print axioms improvedTopologyStream_eq_packed
#print axioms improvedPayloadStream_eq_packed

end Zeta23.ThmD.Sextuple.MacroPrototype.A1285
