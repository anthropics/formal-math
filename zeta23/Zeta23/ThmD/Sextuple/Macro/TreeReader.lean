import Zeta23.ThmD.Sextuple.Macro.TreeFormat
import Zeta23.ThmD.Sextuple.Macro.ScalarData
import Zeta23.ThmD.Sextuple.Macro.LeafCheck

/-!
# Packed stream readers for the concrete macro-scalar certificate tree

Physical layout (all values are natural-number literals):

* topology: `20` three-bit tokens per `60`-bit word, exactly as the audited
  `packedTopologyStream`; `0` = terminal, `1..5` = split on axis `0..4`.
* leaves: one `321`-bit word per terminal in DFS order:
  - bit `0`: kind (`0` = affine tail, `1` = quadratic);
  - bits `1..80`: five `16`-bit dyadic-`16384` relative anchor codes;
  - bits `81..320`: fifteen `16`-bit term codes
    (`0..55` stable envelope piece, `32768+n` scalar certificate `n`, `65535` zero model);
  - tail words are exactly `0`.
  Leaf words are packed `leafBlockSize` per block word, least significant first.

Soundness of the replay never depends on how the streams are read; physical canonicality
(exact sizes, ranges, zero padding) is checked separately in `Macro/Layout.lean`.
-/

noncomputable section

namespace Zeta23.ThmD.Sextuple.MacroPrototype

open Zeta23.ThmD.Sextuple

/-- Extract the `k`-th `16`-bit field starting at bit `1 + 16 k`. -/
def leafField (w k : ℕ) : ℕ := (w >>> (1 + 16 * k)) &&& 65535

/-- Decode one term code; out-of-range codes are rejected. -/
def decodeTermRef (code : ℕ) : Option (MacroTermRef 56 871) :=
  if h : code < 56 then some (.piece ⟨code, h⟩)
  else if code = 65535 then some .zero
  else if h2 : 32768 ≤ code ∧ code - 32768 < 871 then some (.scalar ⟨code - 32768, h2.2⟩)
  else none

/-- Decoded term, with a placeholder that is never used unless every code decodes. -/
def leafTerm (w : ℕ) (p : Fin 15) : MacroTermRef 56 871 :=
  (decodeTermRef (leafField w (5 + p.val))).getD .zero

/-- Every one of the fifteen term codes decodes. -/
def leafTermsValid (w : ℕ) : Bool :=
  decide (∀ p : Fin 15, (decodeTermRef (leafField w (5 + p.val))).isSome = true)

/-- Decoded relative anchor. -/
def leafAnchor (w : ℕ) : RelativeAnchor := ⟨fun i => leafField w i.val⟩

/-- Decode one leaf word into a terminal payload. -/
def decodeLeafWord (w : ℕ) : Option (AffineLeafPayload (MacroScalarLeaf 56 871)) :=
  if w = 0 then some .tail
  else if w % 2 = 1 ∧ w < 2 ^ leafWordBits ∧ leafTermsValid w = true then
    some (.quadratic ⟨leafAnchor w, leafTerm w⟩)
  else none

/-- Read leaf word `p` from the block array. -/
def leafWordRead (blocks : Array ℕ) (p : ℕ) : Option ℕ :=
  match blocks[p / leafBlockSize]? with
  | none => none
  | some blk => some ((blk >>> (leafWordBits * (p % leafBlockSize))) &&& (2 ^ leafWordBits - 1))

/-- The payload stream backed by packed leaf blocks. -/
def packedLeafStream (leafCount : ℕ) (blocks : Array ℕ) :
    CursorStream (AffineLeafPayload (MacroScalarLeaf 56 871)) where
  length := leafCount
  read := fun p =>
    match leafWordRead blocks p with
    | none => none
    | some w => decodeLeafWord w

/-- The concrete terminal checker: exact affine tail or the kernel-reducible quadratic leaf. -/
def concreteLeafCheck : GapBox → AffineLeafPayload (MacroScalarLeaf 56 871) → Bool :=
  affineLeafCheck (1 / 80) (1094977 / 5000000000)
    (fastLeafCheck stableMacroTable scalarCertTable)

/-- Soundness of the concrete terminal checker. -/
theorem concreteLeafCheck_sound :
    ∀ box payload, concreteLeafCheck box payload = true →
      BoxPredicate (affineEnergyGoal (1 / 80) (1094977 / 5000000000)) box :=
  affineLeafCheck_sound (fastLeafCheck_sound stableMacroTable_check scalarCertTable_check)

/-- A chain of midpoint halvings from a root box. `true` selects the upper half. -/
def pathBox (root : GapBox) : List (Bool × Fin 5) → GapBox
  | [] => root
  | (false, a) :: rest => (pathBox root rest).lowerHalf a
  | (true, a) :: rest => (pathBox root rest).upperHalf a

end Zeta23.ThmD.Sextuple.MacroPrototype
