import Zeta23.ThmD.Sextuple.Macro.TreeWords

/-!
# Linear-time physical layout checks

The audited `packedTopologyLayoutCheck` is stated through a bounded `Fin`-quantifier and an
existential on `Option`; its `Decidable` instance evaluates very slowly in the kernel.  This
module provides explicit Boolean loops over the underlying lists and proves that they imply
the audited `PackedTopologyLayoutValid` (and the analogous leaf-block layout predicate).
-/

set_option maxHeartbeats 0

noncomputable section

namespace Zeta23.ThmD.Sextuple.MacroPrototype

open Zeta23.ThmD.Sextuple

/-- Every element of the list is below `bound`. -/
def allBelow (bound : ℕ) : List ℕ → Bool
  | [] => true
  | w :: ws => decide (w < bound) && allBelow bound ws

theorem allBelow_sound {bound : ℕ} : ∀ {l : List ℕ}, allBelow bound l = true →
    ∀ w ∈ l, w < bound
  | [], _, _, h => by simp at h
  | w :: ws, h, x, hx => by
      simp only [allBelow, Bool.and_eq_true, decide_eq_true_eq] at h
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact h.1
      · exact allBelow_sound h.2 x hx'

/-- Zero padding of the final partial word: the word at index `i` (if any) is below `bound`. -/
def finalWordBelow (words : Array ℕ) (i bound : ℕ) : Bool :=
  match words[i]? with
  | none => false
  | some w => decide (w < bound)

/-- Linear topology layout check. -/
def topologyLayoutBool (tokenCount : ℕ) (words : Array ℕ) : Bool :=
  decide (words.size = (tokenCount + 19) / 20) &&
  allBelow (2 ^ 60) words.toList &&
  (decide (tokenCount % 20 = 0) ||
    finalWordBelow words (tokenCount / 20) (2 ^ (3 * (tokenCount % 20))))

theorem topologyLayoutBool_sound {tokenCount : ℕ} {words : Array ℕ}
    (h : topologyLayoutBool tokenCount words = true) :
    PackedTopologyLayoutValid tokenCount words := by
  simp only [topologyLayoutBool, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hsize, hall⟩, hfinal⟩ := h
  refine ⟨hsize, ?_, ?_⟩
  · intro i
    exact allBelow_sound hall _ (Array.getElem_mem_toList i.isLt)
  · rcases hfinal with h0 | hf
    · exact Or.inl h0
    · right
      unfold finalWordBelow at hf
      split at hf
      · simp at hf
      · rename_i w hw
        exact ⟨w, hw, by simpa using hf⟩

/-- Canonical physical layout of the packed leaf blocks. -/
def PackedLeafLayoutValid (leafCount : ℕ) (blocks : Array ℕ) : Prop :=
  blocks.size = (leafCount + leafBlockSize - 1) / leafBlockSize ∧
    (∀ i : Fin blocks.size, blocks[i] < 2 ^ (leafWordBits * leafBlockSize)) ∧
    (leafCount % leafBlockSize = 0 ∨
      ∃ blk, blocks[leafCount / leafBlockSize]? = some blk ∧
        blk < 2 ^ (leafWordBits * (leafCount % leafBlockSize)))

/-- Linear leaf-block layout check. -/
def leafLayoutBool (leafCount : ℕ) (blocks : Array ℕ) : Bool :=
  decide (blocks.size = (leafCount + leafBlockSize - 1) / leafBlockSize) &&
  allBelow (2 ^ (leafWordBits * leafBlockSize)) blocks.toList &&
  (decide (leafCount % leafBlockSize = 0) ||
    finalWordBelow blocks (leafCount / leafBlockSize)
      (2 ^ (leafWordBits * (leafCount % leafBlockSize))))

theorem leafLayoutBool_sound {leafCount : ℕ} {blocks : Array ℕ}
    (h : leafLayoutBool leafCount blocks = true) :
    PackedLeafLayoutValid leafCount blocks := by
  simp only [leafLayoutBool, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hsize, hall⟩, hfinal⟩ := h
  refine ⟨hsize, ?_, ?_⟩
  · intro i
    exact allBelow_sound hall _ (Array.getElem_mem_toList i.isLt)
  · rcases hfinal with h0 | hf
    · exact Or.inl h0
    · right
      unfold finalWordBelow at hf
      split at hf
      · simp at hf
      · rename_i w hw
        exact ⟨w, hw, by simpa using hf⟩

end Zeta23.ThmD.Sextuple.MacroPrototype
