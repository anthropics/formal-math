import Zeta23.ThmD.Sextuple.A1275.ScalarData
import Zeta23.ThmD.Sextuple.Macro.ParametricAdapter

noncomputable section

namespace Zeta23.ThmD.Sextuple.MacroPrototype

open Zeta23.ThmD.Sextuple

abbrev improvedA : ℚ := 51 / 4000
abbrev improvedB : ℚ := 1094977 / 5000000000
abbrev improvedCutoff : ℚ := 63750000 / 1094977

def improvedLeafWordBits : ℕ := 321

def improvedLeafBlockSize : ℕ := 256

def improvedLeafField (w k : ℕ) : ℕ := (w >>> (1 + 16 * k)) &&& 65535


def improvedDecodeTermRef (code : ℕ) : Option (MacroTermRef 272 1383) :=
  if h : code < 272 then some (.piece ⟨code, h⟩)
  else if code = 65535 then some .zero
  else if h : 32768 ≤ code ∧ code - 32768 < 1383 then
    some (.scalar ⟨code - 32768, h.2⟩)
  else none


def improvedLeafTerm (w : ℕ) (p : Fin 15) : MacroTermRef 272 1383 :=
  (improvedDecodeTermRef (improvedLeafField w (5 + p.val))).getD .zero


def improvedLeafTermsValid (w : ℕ) : Bool :=
  decide (∀ p : Fin 15,
    (improvedDecodeTermRef (improvedLeafField w (5 + p.val))).isSome = true)


def improvedLeafAnchor (w : ℕ) : RelativeAnchor :=
  ⟨fun i => improvedLeafField w i.val⟩


def improvedDecodeLeafWord (w : ℕ) :
    Option (AffineLeafPayload (MacroScalarLeaf 272 1383)) :=
  if w = 0 then some .tail
  else if w % 2 = 1 ∧ w < 2 ^ improvedLeafWordBits ∧
      improvedLeafTermsValid w = true then
    some (.quadratic ⟨improvedLeafAnchor w, improvedLeafTerm w⟩)
  else none


def improvedLeafWordRead (blocks : Array ℕ) (p : ℕ) : Option ℕ :=
  match blocks[p / improvedLeafBlockSize]? with
  | none => none
  | some blk => some ((blk >>> (improvedLeafWordBits * (p % improvedLeafBlockSize))) &&&
      (2 ^ improvedLeafWordBits - 1))


def improvedPackedLeafStream (leafCount : ℕ) (blocks : Array ℕ) :
    CursorStream (AffineLeafPayload (MacroScalarLeaf 272 1383)) where
  length := leafCount
  read := fun p =>
    match improvedLeafWordRead blocks p with
    | none => none
    | some w => improvedDecodeLeafWord w

/-! ### Two-level word arrays

Kernel lookups in an `Array` literal cost one step per index, so the certificate words are
stored two levels deep: `improvedTopologyBlockSize` words per topology block and
`improvedLeafGroupSize` leaf-block words per `WordData` group.  The readers below decode
exactly as the audited flat readers (`packedTopologyRead`, `improvedLeafWordRead`) on the
concatenated arrays; `Layout.lean` states the flat layout predicates for those
concatenations. -/

/-- Words per topology block. -/
def improvedTopologyBlockSize : ℕ := 140

/-- Leaf-block words per `WordData` group. -/
def improvedLeafGroupSize : ℕ := 25

/-- Read word `k` of a two-level array holding `blockSize` words per block. -/
def blockedWordRead (blockSize : ℕ) (blocks : Array (Array ℕ)) (k : ℕ) : Option ℕ :=
  match blocks[k / blockSize]? with
  | none => none
  | some blk => blk[k % blockSize]?

/-- `packedTopologyRead` on a two-level word array: twenty three-bit tokens per word. -/
def blockedTopologyRead (blockSize : ℕ) (blocks : Array (Array ℕ)) (cursor : ℕ) :
    Option AffineTreeToken :=
  match blockedWordRead blockSize blocks (cursor / 20) with
  | none => none
  | some word =>
      decodeAffineTreeToken ((word / 2 ^ (3 * (cursor % 20))) % 8)

/-- Topology stream backed by two-level 60-bit word blocks. -/
def blockedTopologyStream (tokenCount blockSize : ℕ) (blocks : Array (Array ℕ)) :
    CursorStream AffineTreeToken where
  length := tokenCount
  read := blockedTopologyRead blockSize blocks

/-- Read leaf word `p` from the grouped leaf-block arrays. -/
def groupedLeafWordRead (groups : Array (Array ℕ)) (p : ℕ) : Option ℕ :=
  match blockedWordRead improvedLeafGroupSize groups (p / improvedLeafBlockSize) with
  | none => none
  | some blk => some ((blk >>> (improvedLeafWordBits * (p % improvedLeafBlockSize))) &&&
      (2 ^ improvedLeafWordBits - 1))

/-- The payload stream backed by grouped leaf blocks. -/
def groupedLeafStream (leafCount : ℕ) (groups : Array (Array ℕ)) :
    CursorStream (AffineLeafPayload (MacroScalarLeaf 272 1383)) where
  length := leafCount
  read := fun p =>
    match groupedLeafWordRead groups p with
    | none => none
    | some w => improvedDecodeLeafWord w


def improvedConcreteLeafCheck :
    GapBox → AffineLeafPayload (MacroScalarLeaf 272 1383) → Bool :=
  affineLeafCheck improvedA improvedB
    (fastLeafCheckAt 16384 improvedCutoff improvedA improvedB
      improvedCatalog improvedScalarTable)


theorem improvedConcreteLeafCheck_sound :
    ∀ box payload, improvedConcreteLeafCheck box payload = true →
      BoxPredicate (affineEnergyGoal improvedA improvedB) box :=
  affineLeafCheck_sound
    (fastLeafCheckAt_sound (by norm_num [improvedB])
      (by norm_num [improvedA, improvedB, improvedCutoff])
      improvedCatalog_check improvedScalarTable_check)

/-- A chain of midpoint halvings from a root box. -/
def improvedPathBox (root : GapBox) : List (Bool × Fin 5) → GapBox
  | [] => root
  | (false, a) :: rest => (improvedPathBox root rest).lowerHalf a
  | (true, a) :: rest => (improvedPathBox root rest).upperHalf a

#print axioms improvedConcreteLeafCheck_sound

end Zeta23.ThmD.Sextuple.MacroPrototype
