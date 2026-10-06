import Zeta23.ThmD.Sextuple.A1290.ScalarData
import Zeta23.ThmD.Sextuple.Macro.ParametricAdapter

/-!
# Readers and the concrete leaf checker for the `A = 129 / 10000` certificate

Decoders for the 321-bit leaf words (kind bit, five 16-bit dyadic-16384 relative anchor codes,
fifteen 16-bit term codes: `0..271` catalog model, `32768+n` scalar certificate `n`, `65535` zero),
the two-level word readers, and `improvedConcreteLeafCheck` with its soundness theorem.
-/

noncomputable section

namespace Zeta23.ThmD.Sextuple.MacroPrototype.A1290

open Zeta23.ThmD.Sextuple

abbrev improvedA : ℚ := 129 / 10000
abbrev improvedB : ℚ := 1094977 / 5000000000
abbrev improvedCutoff : ℚ := 64500000 / 1094977

def improvedLeafWordBits : ℕ := 321

def improvedLeafBlockSize : ℕ := 256

def improvedLeafField (w k : ℕ) : ℕ := (w >>> (1 + 16 * k)) &&& 65535

def improvedDecodeTermRef (code : ℕ) : Option (MacroTermRef 666 4299) :=
  if h : code < 666 then some (.piece ⟨code, h⟩)
  else if code = 65535 then some .zero
  else if h : 32768 ≤ code ∧ code - 32768 < 4299 then
    some (.scalar ⟨code - 32768, h.2⟩)
  else none

def improvedLeafTerm (w : ℕ) (p : Fin 15) : MacroTermRef 666 4299 :=
  (improvedDecodeTermRef (improvedLeafField w (5 + p.val))).getD .zero

def improvedLeafTermsValid (w : ℕ) : Bool :=
  decide (∀ p : Fin 15,
    (improvedDecodeTermRef (improvedLeafField w (5 + p.val))).isSome = true)

def improvedLeafAnchor (w : ℕ) : RelativeAnchor :=
  ⟨fun i => improvedLeafField w i.val⟩

def improvedDecodeLeafWord (w : ℕ) :
    Option (AffineLeafPayload (MacroScalarLeaf 666 4299)) :=
  if w = 0 then some .tail
  else if w % 2 = 1 ∧ w < 2 ^ improvedLeafWordBits ∧
      improvedLeafTermsValid w = true then
    some (.quadratic ⟨improvedLeafAnchor w, improvedLeafTerm w⟩)
  else none

/-- Flat leaf-word read (the audited single-level form). -/
def improvedLeafWordRead (blocks : Array ℕ) (p : ℕ) : Option ℕ :=
  match blocks[p / improvedLeafBlockSize]? with
  | none => none
  | some blk => some ((blk >>> (improvedLeafWordBits * (p % improvedLeafBlockSize))) &&&
      (2 ^ improvedLeafWordBits - 1))

/-- Flat payload stream (the audited single-level form). -/
def improvedPackedLeafStream (leafCount : ℕ) (blocks : Array ℕ) :
    CursorStream (AffineLeafPayload (MacroScalarLeaf 666 4299)) where
  length := leafCount
  read := fun p =>
    match improvedLeafWordRead blocks p with
    | none => none
    | some w => improvedDecodeLeafWord w

/-! ### Two-level word arrays (kernel lookups stay short). -/

def improvedTopologyBlockSize : ℕ := 140

def improvedLeafGroupSize : ℕ := 25

def blockedWordRead (blockSize : ℕ) (blocks : Array (Array ℕ)) (k : ℕ) : Option ℕ :=
  match blocks[k / blockSize]? with
  | none => none
  | some blk => blk[k % blockSize]?

def blockedTopologyRead (blockSize : ℕ) (blocks : Array (Array ℕ)) (cursor : ℕ) :
    Option AffineTreeToken :=
  match blockedWordRead blockSize blocks (cursor / 20) with
  | none => none
  | some word =>
      decodeAffineTreeToken ((word / 2 ^ (3 * (cursor % 20))) % 8)

def blockedTopologyStream (tokenCount blockSize : ℕ) (blocks : Array (Array ℕ)) :
    CursorStream AffineTreeToken where
  length := tokenCount
  read := blockedTopologyRead blockSize blocks

def groupedLeafWordRead (groups : Array (Array ℕ)) (p : ℕ) : Option ℕ :=
  match blockedWordRead improvedLeafGroupSize groups (p / improvedLeafBlockSize) with
  | none => none
  | some blk => some ((blk >>> (improvedLeafWordBits * (p % improvedLeafBlockSize))) &&&
      (2 ^ improvedLeafWordBits - 1))

def groupedLeafStream (leafCount : ℕ) (groups : Array (Array ℕ)) :
    CursorStream (AffineLeafPayload (MacroScalarLeaf 666 4299)) where
  length := leafCount
  read := fun p =>
    match groupedLeafWordRead groups p with
    | none => none
    | some w => improvedDecodeLeafWord w

def improvedConcreteLeafCheck :
    GapBox → AffineLeafPayload (MacroScalarLeaf 666 4299) → Bool :=
  affineLeafCheck improvedA improvedB
    (fastLeafCheckAt 16384 improvedCutoff improvedA improvedB
      improvedCatalog2 improvedScalarTable)

theorem improvedConcreteLeafCheck_sound :
    ∀ box payload, improvedConcreteLeafCheck box payload = true →
      BoxPredicate (affineEnergyGoal improvedA improvedB) box :=
  affineLeafCheck_sound
    (fastLeafCheckAt_sound (by norm_num [improvedB])
      (by norm_num [improvedA, improvedB, improvedCutoff])
      improvedCatalog2_check improvedScalarTable_check)

/-- A chain of midpoint halvings from a root box (head = deepest halving). -/
def improvedPathBox (root : GapBox) : List (Bool × Fin 5) → GapBox
  | [] => root
  | (false, a) :: rest => (improvedPathBox root rest).lowerHalf a
  | (true, a) :: rest => (improvedPathBox root rest).upperHalf a

#print axioms improvedConcreteLeafCheck_sound

end Zeta23.ThmD.Sextuple.MacroPrototype.A1290
