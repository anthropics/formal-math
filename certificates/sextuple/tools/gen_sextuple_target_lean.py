#!/usr/bin/env python3
"""Generate the complete Lean module set for a sextuple certificate target `A = a/b`, `B = B₆`.

Inputs: an exact serialized tree directory (`manifest.json`, `topology-u64le.bin`,
`terminal-kinds-u8.bin`, `anchors-u16le.bin`, `term-codes-u16le.bin`, `scalar-certificates.json`)
produced by the exact-rational branch-and-bound generators of `certificates/sextuple/a1275/generators/`
over the 272-model catalog (56 stable pieces + 216 refinement cells, `Zeta23.ThmD.Sextuple.A1275.Catalog`).

Outputs (under `--repo`, namespace tag `--ns`, e.g. `A1290`):
  Zeta23/ThmD/Sextuple/<NS>/{ScalarData,TreeReader,TreeWords,Layout,FlatEquivalence,TreeAssembly,
    Certificate,Assembly,Unconditional,LineDecimal,AxiomAudit}.lean, WordData/LeafBlocksNNN.lean,
    Chunks/ChunkNNNN.lean, Assembly/PartNNN.lean
  comparator/{Challenge,Solution,PrintAxioms}/Sextuple<NS>.lean, comparator/config-sextuple-<ns>.json
All definitions live in `Zeta23.ThmD.Sextuple.MacroPrototype.<NS>` (data/replay) and
`Zeta23.ThmD.Sextuple.<NS>` / `Zeta23.ThmD.Sextuple.ImprovedAssembly.<NS>` (theorems), so several targets
coexist in one library.  Words are stored two levels deep; node lemmas never pass an explicit box.

`--validate-a1275` regenerates the committed `A1275` target into a scratch root and diffs the chunk
partition, assembly DAG, word literals and scalar certificates against the committed artifacts.
Standard library only; no `assert`.
"""
from __future__ import annotations
import argparse, hashlib, json, re, struct, sys
from fractions import Fraction
from pathlib import Path

sys.set_int_max_str_digits(0)

MAX_TOKENS = 100
TOPO_BLOCK = 140
LEAF_BITS, LEAF_PER_BLOCK, LEAF_GROUP = 321, 256, 25
NODES_PER_PART = 100
B6 = Fraction(1094977, 5000000000)
HD1_LOWER = Fraction(672500703679, 10**12)
PI_UPPER = Fraction(314159265358979323847, 10**20)
LIMIT = 59


def require(cond: bool, msg: str) -> None:
    if not cond:
        raise SystemExit(f"gen_sextuple_target_lean: {msg}")


def sha256(b: bytes) -> str:
    return hashlib.sha256(b).hexdigest()


def q(s: str) -> Fraction:
    return Fraction(s)


def lean_rat(x: Fraction) -> str:
    return str(x.numerator) if x.denominator == 1 else f"({x.numerator}/{x.denominator})"


# ----------------------------------------------------------------------------- inputs
class Tree:
    def __init__(self, tree_dir: Path):
        self.dir = tree_dir
        m = json.loads((tree_dir / "manifest.json").read_text())
        self.manifest = m
        raw = {k: (tree_dir / f).read_bytes() for k, f in
               (("topology", "topology-u64le.bin"), ("kinds", "terminal-kinds-u8.bin"),
                ("anchors", "anchors-u16le.bin"), ("terms", "term-codes-u16le.bin"))}
        for k, b in raw.items():
            require(sha256(b) == m["stream_sha256"][k], f"{k} stream SHA-256 mismatch against manifest")
        self.words = [int.from_bytes(raw["topology"][i:i + 8], "little") for i in range(0, len(raw["topology"]), 8)]
        self.leaves = int(m["leaves"])
        self.token_count = 2 * self.leaves - 1
        require(len(self.words) == (self.token_count + 19) // 20, "topology word count")
        toks = []
        for t in range(self.token_count):
            toks.append((self.words[t // 20] >> (3 * (t % 20))) & 7)
        require(all(x <= 5 for x in toks), "bad topology token")
        rem = self.token_count % 20
        require(rem == 0 or self.words[-1] < 2 ** (3 * rem), "nonzero topology padding")
        self.tokens = toks
        self.kinds = list(raw["kinds"])
        require(len(self.kinds) == self.leaves and all(k in (0, 1) for k in self.kinds), "kinds stream")
        self.quadratic = sum(self.kinds)
        require(self.quadratic == int(m["quadratic_leaves"]), "quadratic leaf count")
        self.anchors = list(struct.unpack("<" + "H" * (len(raw["anchors"]) // 2), raw["anchors"]))
        self.terms = list(struct.unpack("<" + "H" * (len(raw["terms"]) // 2), raw["terms"]))
        require(len(self.anchors) == 5 * self.quadratic and len(self.terms) == 15 * self.quadratic, "anchor/term lengths")
        sc = json.loads((tree_dir / "scalar-certificates.json").read_text())
        self.scalars = sc["certificates"]
        self.scalar_count = len(self.scalars)
        require(self.scalar_count == int(m["scalar_certificate_count"]), "scalar certificate count")
        self.A = q(m["A"]); self.B = q(m["B"])
        require(self.B == B6, "B must be B6")
        require(q(sc["A"]) == self.A and q(sc["B"]) == self.B, "scalar certificates A/B")
        self.cutoff = self.A / self.B
        require(self.cutoff == q(m["cutoff"]), "cutoff")
        require(self.A <= self.B * LIMIT, "A must satisfy A <= B * 59 (root box limit)")
        for x in self.anchors:
            require(0 <= x <= 16384, "anchor code range")
        for x in self.terms:
            require(x < 272 or 32768 <= x < 32768 + self.scalar_count or x == 65535, "term code range")
        self.max_depth = int(m["maximum_depth"])
        self.fuel = int(m["fuel"])
        require(self.fuel == self.max_depth + 1, "fuel must be maximum depth + 1")


# ----------------------------------------------------------------------------- tree structure
class Node:
    __slots__ = ("t0", "p0", "t1", "p1", "depth", "axis", "left", "right", "size", "parent", "path", "chunk", "nid")

    def __init__(self, t0, p0, depth, parent):
        self.t0, self.p0, self.depth, self.parent = t0, p0, depth, parent
        self.t1 = self.p1 = None
        self.axis = None; self.left = self.right = None
        self.size = 0; self.path = None; self.chunk = None; self.nid = None


def build_tree(tree: Tree):
    """Explicit-stack DFS reproducing `replayAffineTree`'s cursor discipline."""
    toks, kinds = tree.tokens, tree.kinds
    root = Node(0, 0, 0, None)
    root.path = []
    stack = [root]
    order = []           # post-order
    while stack:
        n = stack[-1]
        if n.left is None and n.right is None and n.t1 is None:
            require(n.t0 < len(toks), "topology underflow")
            tok = toks[n.t0]
            require(n.depth <= tree.max_depth, "depth exceeds manifest maximum")
            if tok == 0:
                require(n.p0 < len(kinds), "payload underflow")
                n.t1, n.p1, n.size = n.t0 + 1, n.p0 + 1, 1
                stack.pop(); order.append(n)
                continue
            n.axis = tok - 1
            n.left = Node(n.t0 + 1, n.p0, n.depth + 1, n)
            n.left.path = [(0, n.axis)] + n.path
            stack.append(n.left)
            continue
        if n.right is None:
            n.right = Node(n.left.t1, n.left.p1, n.depth + 1, n)
            n.right.path = [(1, n.axis)] + n.path
            stack.append(n.right)
            continue
        n.t1, n.p1 = n.right.t1, n.right.p1
        n.size = 1 + n.left.size + n.right.size
        stack.pop(); order.append(n)
    require(root.t1 == tree.token_count and root.p1 == tree.leaves, "root does not exhaust both streams")
    return root, order


def partition(root: Node, order: list[Node]):
    chunks, nodes = [], []
    for n in order:            # post-order
        if n.size <= MAX_TOKENS and (n.parent is None or n.parent.size > MAX_TOKENS):
            chunks.append(n)
        elif n.size > MAX_TOKENS:
            nodes.append(n)
    chunks.sort(key=lambda n: n.t0)
    for i, c in enumerate(chunks):
        c.chunk = i
    for i, n in enumerate(nodes):
        n.nid = i
    require(nodes[-1] is root, "root must be the last assembly node")
    for n in nodes:
        for ch in (n.left, n.right):
            require(ch.chunk is not None or ch.nid is not None, "assembly child is neither chunk nor node")
    return chunks, nodes


def render_path(path) -> str:
    return "[" + ", ".join(f"({'true' if s else 'false'}, ⟨{a}, by decide⟩)" for s, a in path) + "]"


# ----------------------------------------------------------------------------- leaf words
def encode_leaf_words(tree: Tree) -> list[int]:
    words, qi = [], 0
    for kind in tree.kinds:
        if kind == 0:
            words.append(0); continue
        w = 1
        for i in range(5):
            w |= tree.anchors[5 * qi + i] << (1 + 16 * i)
        for i in range(15):
            w |= tree.terms[15 * qi + i] << (1 + 16 * (5 + i))
        require(w < 2 ** LEAF_BITS, "leaf word overflow")
        words.append(w); qi += 1
    blocks = []
    for j in range(0, len(words), LEAF_PER_BLOCK):
        blk = 0
        for k, w in enumerate(words[j:j + LEAF_PER_BLOCK]):
            blk |= w << (LEAF_BITS * k)
        blocks.append(blk)
    return blocks


# ----------------------------------------------------------------------------- Lean emitters
class Emitter:
    def __init__(self, tree: Tree, ns: str, chunk_width: int):
        self.tree, self.ns = tree, ns
        self.mp = f"Zeta23.ThmD.Sextuple.MacroPrototype.{ns}"
        self.mod = f"Zeta23.ThmD.Sextuple.{ns}"
        self.cw = chunk_width
        A = tree.A
        self.A_str = f"{A.numerator} / {A.denominator}"
        self.lower = (6 * HD1_LOWER - 10 * PI_UPPER * B6) / (6 - A)
        dec = self.lower * 10**10
        num = dec.numerator // dec.denominator
        if Fraction(num, 10**10) >= self.lower:
            num -= 1
        self.dec_num = num
        self.dec = f"{num} / 10 ^ 10"
        require(Fraction(num, 10**10) < self.lower, "public decimal not strictly below the bound")
        self.margin = self.lower - Fraction(num, 10**10)
        self.denom_cleared = (6 - A)  # for docs

    def chunk_name(self, i: int) -> str:
        return f"improvedChunk{i:0{self.cw}d}"

    def chunk_module(self, i: int) -> str:
        return f"{self.mod}.Chunks.Chunk{i:0{self.cw}d}"

    # ---- data modules
    def word_data(self, blocks: list[int]) -> dict[str, str]:
        out = {}
        groups = [blocks[i:i + LEAF_GROUP] for i in range(0, len(blocks), LEAF_GROUP)]
        for g, arr in enumerate(groups):
            body = "\n".join(f"  {w}" + ("," if k < len(arr) - 1 else "") for k, w in enumerate(arr))
            out[f"WordData/LeafBlocks{g:03d}.lean"] = (
                f"namespace {self.mp}\n\nset_option maxHeartbeats 0\n\nset_option maxRecDepth 100000 in\n"
                f"def improvedLeafBlocksChunk{g:03d} : Array Nat := #[\n{body}\n]\n\nend {self.mp}\n")
        self.group_count = len(groups)
        return out

    def tree_words(self) -> str:
        t = self.tree
        blocks = [t.words[i:i + TOPO_BLOCK] for i in range(0, len(t.words), TOPO_BLOCK)]
        L = [f"import {self.mod}.TreeReader", "import Zeta23.ThmD.Sextuple.AffineTree"]
        L += [f"import {self.mod}.WordData.LeafBlocks{g:03d}" for g in range(self.group_count)]
        L += ["", "/-!", f"# Packed words of the `A = {self.A_str}` certificate tree (two-level layout)", "",
              "Generated by `certificates/sextuple/tools/gen_sextuple_target_lean.py` from the canonical",
              f"`certificates/sextuple/{self.ns.lower()}/macro-scalar-tree/` streams.", "",
              f"* topology: `{t.token_count}` three-bit tokens, `20` per `60`-bit word, `{len(t.words)}` words",
              f"  stored in `{len(blocks)}` blocks of `{TOPO_BLOCK}` words (the last has `{len(blocks[-1])}`);",
              f"* leaves: `{t.leaves}` `321`-bit leaf words, `256` per block word, `{(t.leaves + 255) // 256}` block words",
              f"  stored in the `{self.group_count}` `WordData` groups of `{LEAF_GROUP}` block words.",
              "-/", "", "set_option maxHeartbeats 0", "", "noncomputable section", f"namespace {self.mp}",
              "open Zeta23.ThmD.Sextuple", "",
              f"def improvedTokenCount : ℕ := {t.token_count}", f"def improvedLeafCount : ℕ := {t.leaves}", "",
              "set_option maxRecDepth 100000 in", "def improvedTopologyBlocks : Array (Array Nat) := #["]
        for bi, b in enumerate(blocks):
            L.append("  #[" + ", ".join(str(w) for w in b) + "]" + ("," if bi < len(blocks) - 1 else ""))
        L += ["]", "", "def improvedLeafBlockGroups : Array (Array Nat) := #["]
        L += [f"  improvedLeafBlocksChunk{g:03d}" + ("," if g < self.group_count - 1 else "") for g in range(self.group_count)]
        L += ["]", "", "def improvedTopologyStream : CursorStream AffineTreeToken :=",
              "  blockedTopologyStream improvedTokenCount improvedTopologyBlockSize improvedTopologyBlocks", "",
              f"def improvedPayloadStream : CursorStream (AffineLeafPayload (MacroScalarLeaf 272 {t.scalar_count})) :=",
              "  groupedLeafStream improvedLeafCount improvedLeafBlockGroups", "",
              f"def improvedRootBox : GapBox := initialGapBox {LIMIT}", "", f"end {self.mp}", "end", ""]
        return "\n".join(L)

    def scalar_data(self) -> str:
        t = self.tree
        L = ["import Zeta23.ThmD.Sextuple.A1275.Catalog", "", f"namespace {self.mp}", "",
             "open Zeta23.ThmD.Sextuple", "open RatInterval", "", "set_option maxRecDepth 1000000",
             "set_option maxHeartbeats 0", ""]
        piece_lists = []
        for i, c in enumerate(t.scalars):
            segs = c["segments"]
            require(segs and all(0 <= s["piece_index"] < 272 for s in segs), f"scalar {i}: segments")
            lo, hi, a = q(c["lo"]), q(c["hi"]), q(c["a"])
            require(lo <= hi and a >= 0, f"scalar {i}: box/a")
            L.append(f"def improvedScalarCert{i} : MacroScalarCert 272 := {{")
            L.append(f"  box := ⟨{lean_rat(lo)}, {lean_rat(hi)}⟩")
            L.append(f"  a := {lean_rat(a)}")
            L.append("  segments := [")
            for k, s in enumerate(segs):
                L.append(f"    {{ box := ⟨{lean_rat(q(s['lo']))}, {lean_rat(q(s['hi']))}⟩, pieceIndex := ⟨{s['piece_index']}, by decide⟩ }}"
                         + ("," if k < len(segs) - 1 else ""))
            L.append("  ]"); L.append("}")
            names = []
            for s in segs:
                p = s["piece_index"]
                names.append(f"macroPiece{p}" if p < 56 else f"refinementPiece{p - 56}")
            tables = []
            if any(s["piece_index"] < 56 for s in segs): tables.append("stableMacroTable")
            if any(s["piece_index"] >= 56 for s in segs): tables.append("refinementTable")
            seen, uniq = set(), []
            for n in names:
                if n not in seen: seen.add(n); uniq.append(n)
            piece_lists.append(", ".join(tables + uniq))
        L.append("")
        # Kernel evaluation of the Boolean check (the `norm_num` route used for the A1275 stable-piece
        # certificates overflows the recursion depth on refinement-piece segments).
        for i in range(t.scalar_count):
            L.append(f"lemma improvedScalarCert{i}_check : improvedScalarCert{i}.check improvedCatalog = true := by")
            L.append("  decide +kernel")
        # Two-level table: a Nat-literal `match` compiles to a linear `casesOn` chain, so a flat
        # N-arm table costs O(index) kernel steps per lookup (measured: ~54 ms at index 3300);
        # nesting on (i / 64, i % 64) bounds every lookup by ~117 steps.
        G = 64
        L += ["", f"def improvedScalarTable (i : Fin {t.scalar_count}) : MacroScalarCert 272 :=",
              f"  match i.val / {G}, i.val % {G} with"]
        L += [f"  | {i // G}, {i % G} => improvedScalarCert{i}" for i in range(t.scalar_count)]
        L += [f"  | _, _ => improvedScalarCert0", "",
              f"theorem improvedScalarTable_check (i : Fin {t.scalar_count}) :",
              "    (improvedScalarTable i).check improvedCatalog = true := by", "  fin_cases i"]
        L += [f"  · exact improvedScalarCert{i}_check" for i in range(t.scalar_count)]
        L += ["", "#print axioms improvedScalarTable_check", "", f"end {self.mp}", ""]
        return "\n".join(L)

    def tree_reader(self) -> str:
        t = self.tree
        A, B, C = t.A, t.B, t.cutoff
        n = t.scalar_count
        return f'''import {self.mod}.ScalarData
import Zeta23.ThmD.Sextuple.Macro.ParametricAdapter

/-!
# Readers and the concrete leaf checker for the `A = {self.A_str}` certificate

Decoders for the 321-bit leaf words (kind bit, five 16-bit dyadic-16384 relative anchor codes,
fifteen 16-bit term codes: `0..271` catalog model, `32768+n` scalar certificate `n`, `65535` zero),
the two-level word readers, and `improvedConcreteLeafCheck` with its soundness theorem.
-/

noncomputable section

namespace {self.mp}

open Zeta23.ThmD.Sextuple

abbrev improvedA : ℚ := {A.numerator} / {A.denominator}
abbrev improvedB : ℚ := {B.numerator} / {B.denominator}
abbrev improvedCutoff : ℚ := {C.numerator} / {C.denominator}

def improvedLeafWordBits : ℕ := {LEAF_BITS}

def improvedLeafBlockSize : ℕ := {LEAF_PER_BLOCK}

def improvedLeafField (w k : ℕ) : ℕ := (w >>> (1 + 16 * k)) &&& 65535

def improvedDecodeTermRef (code : ℕ) : Option (MacroTermRef 272 {n}) :=
  if h : code < 272 then some (.piece ⟨code, h⟩)
  else if code = 65535 then some .zero
  else if h : 32768 ≤ code ∧ code - 32768 < {n} then
    some (.scalar ⟨code - 32768, h.2⟩)
  else none

def improvedLeafTerm (w : ℕ) (p : Fin 15) : MacroTermRef 272 {n} :=
  (improvedDecodeTermRef (improvedLeafField w (5 + p.val))).getD .zero

def improvedLeafTermsValid (w : ℕ) : Bool :=
  decide (∀ p : Fin 15,
    (improvedDecodeTermRef (improvedLeafField w (5 + p.val))).isSome = true)

def improvedLeafAnchor (w : ℕ) : RelativeAnchor :=
  ⟨fun i => improvedLeafField w i.val⟩

def improvedDecodeLeafWord (w : ℕ) :
    Option (AffineLeafPayload (MacroScalarLeaf 272 {n})) :=
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
    CursorStream (AffineLeafPayload (MacroScalarLeaf 272 {n})) where
  length := leafCount
  read := fun p =>
    match improvedLeafWordRead blocks p with
    | none => none
    | some w => improvedDecodeLeafWord w

/-! ### Two-level word arrays (kernel lookups stay short). -/

def improvedTopologyBlockSize : ℕ := {TOPO_BLOCK}

def improvedLeafGroupSize : ℕ := {LEAF_GROUP}

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
    CursorStream (AffineLeafPayload (MacroScalarLeaf 272 {n})) where
  length := leafCount
  read := fun p =>
    match groupedLeafWordRead groups p with
    | none => none
    | some w => improvedDecodeLeafWord w

def improvedConcreteLeafCheck :
    GapBox → AffineLeafPayload (MacroScalarLeaf 272 {n}) → Bool :=
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

/-- A chain of midpoint halvings from a root box (head = deepest halving). -/
def improvedPathBox (root : GapBox) : List (Bool × Fin 5) → GapBox
  | [] => root
  | (false, a) :: rest => (improvedPathBox root rest).lowerHalf a
  | (true, a) :: rest => (improvedPathBox root rest).upperHalf a

#print axioms improvedConcreteLeafCheck_sound

end {self.mp}
'''

    def layout(self) -> str:
        return f'''import {self.mod}.TreeWords
import Zeta23.ThmD.Sextuple.Macro.Layout

/-! Physical layout of the `A = {self.A_str}` certificate words: the audited flat predicates for the
concatenations of the two-level arrays. -/

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

noncomputable section

namespace {self.mp}

def improvedTopologyWords : Array ℕ :=
  ⟨(improvedTopologyBlocks.toList.map Array.toList).flatten⟩

def improvedLeafBlocks : Array ℕ :=
  ⟨(improvedLeafBlockGroups.toList.map Array.toList).flatten⟩

lemma improvedTopologyLayoutBool_check :
    topologyLayoutBool improvedTokenCount improvedTopologyWords = true := by
  decide +kernel

lemma improvedLeafLayoutBool_check :
    leafLayoutBool improvedLeafCount improvedLeafBlocks = true := by
  decide +kernel

theorem improvedTopologyLayoutValid :
    PackedTopologyLayoutValid improvedTokenCount improvedTopologyWords :=
  topologyLayoutBool_sound improvedTopologyLayoutBool_check

theorem improvedLeafLayoutValid :
    PackedLeafLayoutValid improvedLeafCount improvedLeafBlocks :=
  leafLayoutBool_sound improvedLeafLayoutBool_check

#print axioms improvedTopologyLayoutValid
#print axioms improvedLeafLayoutValid

end {self.mp}

end
'''

    def flat_equivalence(self) -> str:
        return f'''import {self.mod}.Layout

/-! The two-level readers of the `A = {self.A_str}` certificate agree with the audited flat readers. -/

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace {self.mp}

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

theorem uniformBlocksBool_sound {{blockSize : ℕ}} :
    ∀ {{blocks : List (List ℕ)}}, uniformBlocksBool blockSize blocks = true →
      UniformBlocks blockSize blocks
  | [], _ => trivial
  | [blk], h => by simpa [uniformBlocksBool, UniformBlocks] using h
  | blk :: b :: rest, h => by
      simp only [uniformBlocksBool, Bool.and_eq_true, decide_eq_true_eq] at h
      exact ⟨h.1, uniformBlocksBool_sound h.2⟩

theorem blockedListRead_eq_flatten {{blockSize : ℕ}} (hB : 0 < blockSize) :
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

end {self.mp}
'''

    # ---- replay modules
    def chunk(self, c: Node) -> str:
        fuel = self.tree.fuel - c.depth
        return (f"import {self.mod}.TreeWords\n\nset_option maxHeartbeats 0\nset_option maxRecDepth 100000\n\n"
                f"namespace {self.mp}\nopen Zeta23.ThmD.Sextuple\n\n"
                f"/-- Subtree at topology cursor {c.t0}, payload cursor {c.p0}, depth {c.depth}, {c.size} tokens. -/\n"
                f"theorem {self.chunk_name(c.chunk)} :\n"
                f"    replayAffineTree improvedConcreteLeafCheck improvedTopologyStream improvedPayloadStream\n"
                f"      {fuel} {c.t0} {c.p0} (improvedPathBox improvedRootBox {render_path(c.path)}) =\n"
                f"      some ({c.t1}, {c.p1}) := by\n  decide +kernel\n\nend {self.mp}\n")

    def ref(self, n: Node) -> str:
        return self.chunk_name(n.chunk) if n.chunk is not None else f"improvedNode{n.nid:04d}"

    def parts(self, nodes: list[Node]) -> dict[str, str]:
        out, groups = {}, [nodes[i:i + NODES_PER_PART] for i in range(0, len(nodes), NODES_PER_PART)]
        self.part_count = len(groups)
        for k, grp in enumerate(groups):
            chunk_ids = sorted({ch.chunk for n in grp for ch in (n.left, n.right) if ch.chunk is not None})
            L = [f"import {self.mod}.TreeWords"] + [f"import {self.chunk_module(i)}" for i in chunk_ids]
            if k > 0:
                L.append(f"import {self.mod}.Assembly.Part{k - 1:03d}")
            L += ["import Zeta23.ThmD.Sextuple.Macro.AssemblyStep", "", "set_option maxHeartbeats 0",
                  "set_option maxRecDepth 100000", "", f"namespace {self.mp}", "open Zeta23.ThmD.Sextuple", ""]
            for n in grp:
                fuel = self.tree.fuel - n.depth - 1
                L += [f"theorem improvedNode{n.nid:04d} :",
                      f"    replayAffineTree improvedConcreteLeafCheck improvedTopologyStream improvedPayloadStream "
                      f"{fuel + 1} {n.t0} {n.p0} (improvedPathBox improvedRootBox {render_path(n.path)}) =",
                      f"      some ({n.t1}, {n.p1}) :=",
                      f"  replayAffineTree_split_step (fuel := {fuel}) (t := {n.t0}) (p := {n.p0})",
                      f"    (axis := ⟨{n.axis}, by decide⟩) (tm := {n.left.t1}) (pm := {n.left.p1})",
                      f"    (t' := {n.t1}) (p' := {n.p1})",
                      f"    (by decide +kernel) {self.ref(n.left)} {self.ref(n.right)}", ""]
            L.append(f"end {self.mp}")
            out[f"Assembly/Part{k:03d}.lean"] = "\n".join(L) + "\n"
        return out

    def tree_assembly(self, root: Node) -> str:
        t = self.tree
        return (f"import {self.mod}.Layout\nimport {self.mod}.Assembly.Part{self.part_count - 1:03d}\n\n"
                f"set_option maxHeartbeats 0\nset_option maxRecDepth 100000\n\nnamespace {self.mp}\nopen Zeta23.ThmD.Sextuple\n\n"
                f"/-- The complete replay consumes both logical streams exactly. -/\n"
                f"theorem improvedRootReplay :\n"
                f"    replayAffineTree improvedConcreteLeafCheck improvedTopologyStream improvedPayloadStream\n"
                f"      {t.fuel} 0 0 improvedRootBox = some ({t.token_count}, {t.leaves}) := by\n"
                f"  have h := improvedNode{root.nid:04d}\n  simpa only [improvedPathBox] using h\n\n"
                f"#print axioms improvedRootReplay\n\nend {self.mp}\n")

    # ---- theorem modules
    def certificate(self) -> str:
        t = self.tree; ns = self.ns
        return f'''import {self.mod}.TreeAssembly

/-!
# The concrete five-dimensional affine certificate at `A = {self.A_str}`

`improvedRootReplay` plus the exact stream lengths and the audited generic soundness layer give
`{ns}.Certificate.sextuple_affine : {self.A_str} ≤ sextupleEnergy g + B6 * sextupleSpan g`.
-/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

noncomputable section

namespace {self.mp}

open Zeta23.ThmD.Sextuple

theorem improvedTreeCheck :
    checkAffineTree improvedConcreteLeafCheck improvedTopologyStream
      improvedPayloadStream {t.fuel} improvedRootBox = true := by
  unfold checkAffineTree
  rw [improvedRootReplay]
  rfl

theorem improvedRootBox_predicate :
    BoxPredicate (affineEnergyGoal improvedA improvedB) improvedRootBox :=
  checkAffineTree_sound improvedConcreteLeafCheck_sound improvedTreeCheck

end {self.mp}

namespace Zeta23.ThmD.Sextuple.{ns}.Certificate

open Zeta23.ThmD.Sextuple
open Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple.MacroPrototype.{ns}

/-- **The concrete sextuple affine certificate at `A = {self.A_str}`, `B = B₆`.** -/
theorem sextuple_affine (g : Fin 5 → ℝ) (hg : ∀ i, 0 ≤ g i) :
    ({self.A_str} : ℝ) ≤ sextupleEnergy g + B6 * sextupleSpan g := by
  have hroot := improvedRootBox_predicate
  have hglobal := affineTree_global_at
    (A := ({self.A_str} : ℚ)) (B := ({B6.numerator} / {B6.denominator} : ℚ))
    (limit := ({LIMIT} : ℚ)) (by norm_num) (by norm_num) hroot g hg
  simpa [affineEnergyGoal, B6] using hglobal

end Zeta23.ThmD.Sextuple.{ns}.Certificate

end
'''

    def assembly(self) -> str:
        A = self.tree.A; ns = self.ns; d = self.dec_num
        den = 6 - A
        # denominator-cleared exact form: (3000000000*HD1 - 1094977*pi) / (5000000000 * (6 - A) / ... ) keep generic:
        # sextupleLowerConstant = (6*HD1 - 10*pi*B6)/(6-A) = (3000000000*HD1 - 1094977*pi) / (500000000 * (6-A))
        cleared_den = Fraction(500000000) * den
        require(cleared_den.denominator == 1, "denominator-cleared form")
        return f'''import Zeta23.ThmD.Sextuple.Ledger
import Zeta23.ThmD.Sextuple.Final

/-!
# Conditional sextuple assembly at `A = {self.A_str}`, `B = B₆`

Specializes the existing general ledger and final-assembly theorems to the exact constants.
The affine certificate is an explicit theorem hypothesis throughout; the concrete certificate
is supplied by `{self.mod}.Certificate`.
-/

noncomputable section

open Filter Asymptotics Topology Real

namespace Zeta23
namespace ThmD
namespace Sextuple
namespace ImprovedAssembly
namespace {ns}

/-- The affine-energy coefficient. -/
def A : ℝ := {self.A_str}

/-- The span coefficient retained from the baseline certificate. -/
def B : ℝ := B6

/-- The transferred zeta-ledger error. -/
def zetaSextupleLedgerError : ℝ → ℝ :=
  zetaLedgerError ({self.A_str}) (fun T => 10 * gramTransferError T)

theorem zetaSextupleLedgerInterface_of_certificate
    (hcertificate : ∀ g : Fin 5 → ℝ, (∀ i, 0 ≤ g i) →
      ({self.A_str} : ℝ) ≤ sextupleEnergy g + B6 * sextupleSpan g) :
    ZetaSextupleLedgerInterface
      ({self.A_str}) B6 zetaSextuplePenalty zetaSextupleLedgerError := by
  change ZetaSextupleLedgerInterface
    ({self.A_str}) B6 zetaSextuplePenalty
    (zetaLedgerError ({self.A_str}) (fun T => 10 * gramTransferError T))
  exact zetaSextupleLedgerInterface_of_ordered_entry_close
    (A := ({self.A_str} : ℝ)) (B := B6) (entryError := gramTransferError)
    (by norm_num) (by norm_num) (by norm_num [B6])
    gramTransferError_eventually_nonneg gramTransferError_tendsto_zero
    hcertificate eventually_zeta_simpleZeroGram_interior_sub_mtKernel_le

theorem zetaSextupleLedgerError_isLittleO :
    zetaSextupleLedgerError =o[atTop]
      (fun T => (Ncount T (2 * T) : ℝ)) := by
  change zetaLedgerError ({self.A_str}) (fun T => 10 * gramTransferError T)
    =o[atTop] (fun T => (Ncount T (2 * T) : ℝ))
  apply Zeta23.ThmD.Sextuple.zetaLedgerError_isLittleO
  simpa using gramTransferError_tendsto_zero.const_mul 10

/-- The exact feedback constant at `A = {self.A_str}` and `B = B₆`. -/
def sextupleLowerConstant : ℝ :=
  feedbackConstant (HD 1) ({self.A_str}) B6

theorem sextupleLowerConstant_exact :
    sextupleLowerConstant =
      (3000000000 * HD 1 - 1094977 * Real.pi) / {cleared_den.numerator} := by
  rw [sextupleLowerConstant, feedbackConstant, B6]
  ring

/-- Strict fixed-rational comparison from the two directed analytic bounds. -/
theorem sextupleLowerConstant_gt_{d} :
    ({d} / 10 ^ 10 : ℝ) < sextupleLowerConstant := by
  rw [sextupleLowerConstant, feedbackConstant, B6]
  have hBMT := HD_one_decimal.1
  have hpi := Real.pi_lt_d20
  have hden : (0 : ℝ) < 6 - {self.A_str} := by norm_num
  rw [lt_div_iff₀ hden]
  norm_num at hBMT hpi ⊢
  linarith

theorem sextupleDyadic_of_interfaces
    {{penalty baseError ledgerError : ℝ → ℝ}}
    (hbase : ZetaBasePenaltyInterface penalty baseError)
    (hledger : ZetaSextupleLedgerInterface
      ({self.A_str}) B6 penalty ledgerError) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (sextupleLowerConstant - ε) * (Ncount T (2 * T) : ℝ)
        ≤ N0simple T (2 * T) := by
  simpa only [sextupleLowerConstant] using
    (sextuple_zeta_dyadic_of_interfaces (A := ({self.A_str} : ℝ))
      (B := B6) (by norm_num) hbase hledger)

theorem sextupleCumulative_of_interfaces
    {{penalty baseError ledgerError : ℝ → ℝ}}
    (hbase : ZetaBasePenaltyInterface penalty baseError)
    (hledger : ZetaSextupleLedgerInterface
      ({self.A_str}) B6 penalty ledgerError) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (sextupleLowerConstant - ε) * (Ncount 0 T : ℝ)
        ≤ N0simple 0 T := by
  simpa only [sextupleLowerConstant] using
    (sextuple_zeta_cumulative_of_interfaces (A := ({self.A_str} : ℝ))
      (B := B6) (by norm_num) hbase hledger)

private theorem fixedLowerOfEpsForm {{c q : ℝ}} {{N lower : ℝ → ℝ}}
    (hq : q < c)
    (h : ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (c - ε) * N T ≤ lower T) :
    ∃ T₀ : ℝ, ∀ T ≥ T₀, q * N T ≤ lower T := by
  obtain ⟨T₀, hT₀⟩ := h (c - q) (sub_pos.mpr hq)
  refine ⟨T₀, fun T hT => ?_⟩
  convert hT₀ T hT using 1
  ring

theorem sextupleDyadic_{d}_of_interfaces
    {{penalty baseError ledgerError : ℝ → ℝ}}
    (hbase : ZetaBasePenaltyInterface penalty baseError)
    (hledger : ZetaSextupleLedgerInterface
      ({self.A_str}) B6 penalty ledgerError) :
    ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ({d} / 10 ^ 10 : ℝ) * (Ncount T (2 * T) : ℝ)
        ≤ N0simple T (2 * T) :=
  fixedLowerOfEpsForm sextupleLowerConstant_gt_{d}
    (sextupleDyadic_of_interfaces hbase hledger)

theorem sextupleCumulative_{d}_of_interfaces
    {{penalty baseError ledgerError : ℝ → ℝ}}
    (hbase : ZetaBasePenaltyInterface penalty baseError)
    (hledger : ZetaSextupleLedgerInterface
      ({self.A_str}) B6 penalty ledgerError) :
    ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ({d} / 10 ^ 10 : ℝ) * (Ncount 0 T : ℝ) ≤ N0simple 0 T :=
  fixedLowerOfEpsForm sextupleLowerConstant_gt_{d}
    (sextupleCumulative_of_interfaces hbase hledger)

end {ns}
end ImprovedAssembly
end Sextuple
end ThmD
end Zeta23

end
'''

    def unconditional(self) -> str:
        ns = self.ns
        return f'''import Zeta23.ThmD.Sextuple.Base
import {self.mod}.Certificate
import {self.mod}.Assembly

/-! # Unconditional sextuple improvement at `A = {self.A_str}` -/

noncomputable section

open Filter Asymptotics Topology Real

namespace Zeta23
namespace ThmD
namespace Sextuple
namespace {ns}

theorem zetaSextupleLedgerInterface :
    ZetaSextupleLedgerInterface ({self.A_str}) B6 zetaSextuplePenalty
      ImprovedAssembly.{ns}.zetaSextupleLedgerError :=
  ImprovedAssembly.{ns}.zetaSextupleLedgerInterface_of_certificate
    Certificate.sextuple_affine

theorem zetaSextupleLedgerInterface_exactConstants :
    ZetaSextupleLedgerInterface ({self.A_str}) ({B6.numerator} / {B6.denominator})
      zetaSextuplePenalty ImprovedAssembly.{ns}.zetaSextupleLedgerError := by
  simpa only [B6] using zetaSextupleLedgerInterface

/-- Unconditional exact-constant dyadic sextuple improvement at `A = {self.A_str}`. -/
theorem thmD₀_sextuple :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (ImprovedAssembly.{ns}.sextupleLowerConstant - ε) *
          (Ncount T (2 * T) : ℝ) ≤ N0simple T (2 * T) :=
  ImprovedAssembly.{ns}.sextupleDyadic_of_interfaces
    zetaBasePenaltyInterface zetaSextupleLedgerInterface_exactConstants

/-- Unconditional exact-constant cumulative sextuple improvement at `A = {self.A_str}`. -/
theorem thmD₀_sextuple_cumulative :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (ImprovedAssembly.{ns}.sextupleLowerConstant - ε) *
          (Ncount 0 T : ℝ) ≤ N0simple 0 T :=
  ImprovedAssembly.{ns}.sextupleCumulative_of_interfaces
    zetaBasePenaltyInterface zetaSextupleLedgerInterface_exactConstants

end {ns}
end Sextuple
end ThmD
end Zeta23

end
'''

    def line_decimal(self) -> str:
        ns, d = self.ns, self.dec_num
        return f'''import {self.mod}.Unconditional

/-! # Fixed decimal headline `{d}/10^10` for the `A = {self.A_str}` sextuple improvement -/

noncomputable section

open Filter Asymptotics Topology Real

namespace Zeta23
namespace ThmD
namespace Sextuple
namespace {ns}

/-- Unconditional fixed `0.{d}` dyadic headline. -/
theorem thmD₀_sextuple_{d} :
    ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ({d} / 10 ^ 10 : ℝ) * (Ncount T (2 * T) : ℝ)
        ≤ N0simple T (2 * T) :=
  ImprovedAssembly.{ns}.sextupleDyadic_{d}_of_interfaces
    zetaBasePenaltyInterface zetaSextupleLedgerInterface_exactConstants

/-- Unconditional fixed `0.{d}` cumulative headline. -/
theorem thmD₀_sextuple_cumulative_{d} :
    ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ({d} / 10 ^ 10 : ℝ) * (Ncount 0 T : ℝ) ≤ N0simple 0 T :=
  ImprovedAssembly.{ns}.sextupleCumulative_{d}_of_interfaces
    zetaBasePenaltyInterface zetaSextupleLedgerInterface_exactConstants

end {ns}
end Sextuple
end ThmD
end Zeta23

end
'''

    def axiom_audit(self, chunk_count: int, node_count: int) -> str:
        ns, d, mp = self.ns, self.dec_num, self.mp
        mid = chunk_count // 2
        names = [f"{mp}.improvedScalarTable_check", f"{mp}.improvedConcreteLeafCheck_sound",
                 f"{mp}.improvedTopologyLayoutValid", f"{mp}.improvedLeafLayoutValid",
                 f"{mp}.improvedTopologyStream_eq_packed", f"{mp}.improvedPayloadStream_eq_packed",
                 f"{mp}.{self.chunk_name(0)}", f"{mp}.{self.chunk_name(mid)}", f"{mp}.{self.chunk_name(chunk_count - 1)}",
                 f"{mp}.improvedNode0000", f"{mp}.improvedNode{node_count - 1:04d}", f"{mp}.improvedRootReplay",
                 f"{mp}.improvedTreeCheck", f"{mp}.improvedRootBox_predicate",
                 f"Zeta23.ThmD.Sextuple.{ns}.Certificate.sextuple_affine",
                 f"Zeta23.ThmD.Sextuple.ImprovedAssembly.{ns}.zetaSextupleLedgerInterface_of_certificate",
                 f"Zeta23.ThmD.Sextuple.ImprovedAssembly.{ns}.sextupleLowerConstant_exact",
                 f"Zeta23.ThmD.Sextuple.ImprovedAssembly.{ns}.sextupleLowerConstant_gt_{d}",
                 f"Zeta23.ThmD.Sextuple.{ns}.zetaSextupleLedgerInterface",
                 f"Zeta23.ThmD.Sextuple.{ns}.zetaSextupleLedgerInterface_exactConstants",
                 f"Zeta23.ThmD.Sextuple.{ns}.thmD₀_sextuple", f"Zeta23.ThmD.Sextuple.{ns}.thmD₀_sextuple_cumulative",
                 f"Zeta23.ThmD.Sextuple.{ns}.thmD₀_sextuple_{d}", f"Zeta23.ThmD.Sextuple.{ns}.thmD₀_sextuple_cumulative_{d}"]
        return (f"import {self.mod}.LineDecimal\nimport {self.mod}.FlatEquivalence\n\n"
                f"/-! Axiom audit for the unconditional `A = {self.A_str}` sextuple chain. Not imported by the root. -/\n\n"
                + "".join(f"#print axioms {n}\n" for n in names))

    # ---- comparator
    def comparator(self, challenge_template: str) -> dict[str, str]:
        ns, d = self.ns, self.dec_num
        topic = f"Sextuple{ns}"
        tag = ns.lower()
        head_end = challenge_template.index("import Mathlib")
        stmts_start = challenge_template.index("noncomputable section\n\n/-- Sextuple simple-and-on-line endpoint in dyadic windows, ε-form. -/")
        inlined = challenge_template[head_end:stmts_start]
        head = f'''/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Challenge/{topic}.lean — TRUSTED comparator challenge module for the
refined sextuple (six-translate) improvement of the simple critical-line
proportion at `A = {self.A_str}`.

The coefficient `0.{d}` is strictly below the exact endpoint
`(6·B_MT − 10π·B₆)/(6 − {self.A_str})` with `B₆ = 1094977/5000000000`.
`N0simple` counts simple on-line zeros; the denominator `Ncount` counts all
zeros with multiplicity.
Proof: Solution.{topic}.  Config: comparator/config-sextuple-{tag}.json.

The four `sorry`s are deliberate (challenge side).
-/
'''
        names = [f"sextuple_{tag}_simple_on_critical_line_decimal", f"sextuple_{tag}_simple_on_critical_line_cumulative_decimal",
                 f"sextuple_{tag}_simple_on_critical_line_{d}", f"sextuple_{tag}_simple_on_critical_line_cumulative_{d}"]
        stmts = f'''noncomputable section

/-- Refined sextuple simple-and-on-line endpoint in dyadic windows, ε-form. -/
theorem {names[0]} :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (({d} / 10 ^ 10 : ℝ) - ε) *
          (Ncount T (2 * T) : ℝ) ≤
        N0simple T (2 * T) := by
  sorry

/-- Refined sextuple simple-and-on-line endpoint in cumulative windows, ε-form. -/
theorem {names[1]} :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (({d} / 10 ^ 10 : ℝ) - ε) * (Ncount 0 T : ℝ) ≤
        N0simple 0 T := by
  sorry

/-- Fixed coefficient `0.{d}` in dyadic windows. -/
theorem {names[2]} :
    ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ({d} / 10 ^ 10 : ℝ) * (Ncount T (2 * T) : ℝ) ≤
        N0simple T (2 * T) := by
  sorry

/-- Fixed coefficient `0.{d}` in cumulative windows. -/
theorem {names[3]} :
    ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ({d} / 10 ^ 10 : ℝ) * (Ncount 0 T : ℝ) ≤
        N0simple 0 T := by
  sorry
'''
        sol = f'''/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Solution/{topic}.lean — UNTRUSTED solution module for the refined
(`A = {self.A_str}`) sextuple simple-critical-line statements.
-/
import ChallengeDeps
import {self.mod}.LineDecimal

noncomputable section

/-- A fixed-coefficient bound implies the ε-form with the same coefficient. -/
private theorem eps_form_of_fixed {{q : ℝ}} {{N X : ℝ → ℝ}}
    (hN : ∀ T, 0 ≤ N T)
    (h : ∃ T₀ : ℝ, ∀ T ≥ T₀, q * N T ≤ X T) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (q - ε) * N T ≤ X T := by
  intro ε hε
  obtain ⟨T₀, hT₀⟩ := h
  refine ⟨T₀, fun T hT => ?_⟩
  have h1 : (q - ε) * N T ≤ q * N T := by
    have := mul_le_mul_of_nonneg_right (show q - ε ≤ q by linarith) (hN T)
    exact this
  exact h1.trans (hT₀ T hT)

theorem {names[0]} :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (({d} / 10 ^ 10 : ℝ) - ε) *
          (Ncount T (2 * T) : ℝ) ≤
        N0simple T (2 * T) :=
  eps_form_of_fixed (N := fun T => (Ncount T (2 * T) : ℝ))
    (X := fun T => (N0simple T (2 * T) : ℝ)) (fun _ => Nat.cast_nonneg _)
    Zeta23.ThmD.Sextuple.{ns}.thmD₀_sextuple_{d}

theorem {names[1]} :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (({d} / 10 ^ 10 : ℝ) - ε) * (Ncount 0 T : ℝ) ≤
        N0simple 0 T :=
  eps_form_of_fixed (N := fun T => (Ncount 0 T : ℝ))
    (X := fun T => (N0simple 0 T : ℝ)) (fun _ => Nat.cast_nonneg _)
    Zeta23.ThmD.Sextuple.{ns}.thmD₀_sextuple_cumulative_{d}

theorem {names[2]} :
    ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ({d} / 10 ^ 10 : ℝ) * (Ncount T (2 * T) : ℝ) ≤
        N0simple T (2 * T) :=
  Zeta23.ThmD.Sextuple.{ns}.thmD₀_sextuple_{d}

theorem {names[3]} :
    ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ({d} / 10 ^ 10 : ℝ) * (Ncount 0 T : ℝ) ≤
        N0simple 0 T :=
  Zeta23.ThmD.Sextuple.{ns}.thmD₀_sextuple_cumulative_{d}
'''
        cfg = json.dumps({"challenge_module": f"Challenge.{topic}", "solution_module": f"Solution.{topic}",
                          "theorem_names": names, "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"],
                          "enable_nanoda": True}, indent=2) + "\n"
        pa = (f"import Solution.{topic}\nimport {self.mod}.LineDecimal\n\n"
              f"#print axioms Zeta23.ThmD.Sextuple.{ns}.Certificate.sextuple_affine\n"
              f"#print axioms Zeta23.ThmD.Sextuple.{ns}.zetaSextupleLedgerInterface\n"
              f"#print axioms Zeta23.ThmD.Sextuple.ImprovedAssembly.{ns}.sextupleLowerConstant_gt_{d}\n"
              f"#print axioms Zeta23.ThmD.Sextuple.{ns}.thmD₀_sextuple\n"
              f"#print axioms Zeta23.ThmD.Sextuple.{ns}.thmD₀_sextuple_cumulative\n"
              f"#print axioms Zeta23.ThmD.Sextuple.{ns}.thmD₀_sextuple_{d}\n"
              f"#print axioms Zeta23.ThmD.Sextuple.{ns}.thmD₀_sextuple_cumulative_{d}\n"
              + "".join(f"#print axioms {n}\n" for n in names))
        return {f"comparator/Challenge/{topic}.lean": head + inlined + stmts,
                f"comparator/Solution/{topic}.lean": sol,
                f"comparator/config-sextuple-{tag}.json": cfg,
                f"comparator/PrintAxioms/{topic}.lean": pa}


# ----------------------------------------------------------------------------- main
def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--tree-dir", type=Path, required=True)
    ap.add_argument("--ns", required=True, help="namespace tag, e.g. A1290")
    ap.add_argument("--repo", type=Path, required=True, help="output root (repository or scratch)")
    ap.add_argument("--chunk-width", type=int, default=4)
    ap.add_argument("--report", type=Path, default=None)
    ap.add_argument("--validate-a1275", type=Path, default=None,
                    help="repository root holding the committed A1275 target and its bounded plan; diff against it")
    a = ap.parse_args()
    tree = Tree(a.tree_dir)
    root, order = build_tree(tree)
    chunks, nodes = partition(root, order)
    require(len(chunks) == len(nodes) + 1, "chunk/node count relation")
    width = max(a.chunk_width, len(str(len(chunks) - 1)))
    em = Emitter(tree, a.ns, width)
    blocks = encode_leaf_words(tree)
    files: dict[str, str] = {}
    base = f"Zeta23/ThmD/Sextuple/{a.ns}/"
    for rel, text in em.word_data(blocks).items():
        files[base + rel] = text
    files[base + "TreeWords.lean"] = em.tree_words()
    files[base + "ScalarData.lean"] = em.scalar_data()
    files[base + "TreeReader.lean"] = em.tree_reader()
    files[base + "Layout.lean"] = em.layout()
    files[base + "FlatEquivalence.lean"] = em.flat_equivalence()
    for c in chunks:
        files[base + f"Chunks/Chunk{c.chunk:0{width}d}.lean"] = em.chunk(c)
    for rel, text in em.parts(nodes).items():
        files[base + rel] = text
    files[base + "TreeAssembly.lean"] = em.tree_assembly(root)
    files[base + "Certificate.lean"] = em.certificate()
    files[base + "Assembly.lean"] = em.assembly()
    files[base + "Unconditional.lean"] = em.unconditional()
    files[base + "LineDecimal.lean"] = em.line_decimal()
    files[base + "AxiomAudit.lean"] = em.axiom_audit(len(chunks), len(nodes))
    challenge_template = (a.repo / "comparator/Challenge/Sextuple.lean")
    if not challenge_template.exists() and a.validate_a1275 is not None:
        challenge_template = a.validate_a1275 / "comparator/Challenge/Sextuple.lean"
    if challenge_template.exists():
        for rel, text in em.comparator(challenge_template.read_text()).items():
            files[rel] = text

    if a.validate_a1275 is not None:
        R = a.validate_a1275
        plan = json.loads((R / "certificates/sextuple/a1275/tree-artifacts/bounded-replay-plan.json").read_text())
        pc, pn = plan["chunks"], plan["assembly"]
        require(len(pc) == len(chunks) and len(pn) == len(nodes), "plan chunk/node counts differ")
        for c, p in zip(chunks, pc):
            require((c.t0, c.p0, c.t1, c.p1, c.depth, c.size) == (p["t0"], p["p0"], p["t1"], p["p1"], p["depth"], p["tokens"]),
                    f"chunk {c.chunk} cursors differ from the plan")
            require([list(x) for x in c.path] == [list(x) for x in reversed(p["path"])], f"chunk {c.chunk} path differs")
        for n, p in zip(nodes, pn):
            require((n.t0, n.p0, n.t1, n.p1, n.depth, n.axis) == (p["t0"], p["p0"], p["t1"], p["p1"], p["depth"], p["axis"]),
                    f"node {n.nid} differs from the plan")
            require(tree.fuel - n.depth - 1 == p["fuel_after_split"], f"node {n.nid} fuel")
            for ch, ref in ((n.left, p["left"]), (n.right, p["right"])):
                require((ref[0] == "chunk" and ch.chunk == ref[1]) or (ref[0] == "node" and ch.nid == ref[1]),
                        f"node {n.nid} children differ from the plan")
        # committed sources (modulo namespace): chunks, parts, word data, tree words numbers, scalar certs
        def ns_fold(s: str) -> str:
            return s.replace("Zeta23.ThmD.Sextuple.MacroPrototype.A1275", "Zeta23.ThmD.Sextuple.MacroPrototype")
        mismatches = []
        for c in chunks:
            rel = f"Zeta23/ThmD/Sextuple/A1275/Chunks/Chunk{c.chunk:04d}.lean"
            if ns_fold(files[rel]) != (R / rel).read_text():
                mismatches.append(rel)
        for k in range(em.part_count):
            rel = f"Zeta23/ThmD/Sextuple/A1275/Assembly/Part{k:03d}.lean"
            mine = ns_fold(files[rel]); theirs = (R / rel).read_text()
            if sorted(mine.splitlines()) != sorted(theirs.splitlines()):
                mismatches.append(rel)
        for g in range(em.group_count):
            rel = f"Zeta23/ThmD/Sextuple/A1275/WordData/LeafBlocks{g:03d}.lean"
            if re.findall(r"\d+", files[rel].split("#[")[1].split("]")[0]) != re.findall(r"\d+", (R / rel).read_text().split("#[")[1].split("]")[0]):
                mismatches.append(rel)
        rel = "Zeta23/ThmD/Sextuple/A1275/TreeWords.lean"
        mine_words = re.findall(r"\d+", files[rel].split("improvedTopologyBlocks : Array (Array Nat) := #[")[1].split("]\n\ndef")[0])
        theirs_words = re.findall(r"\d+", (R / rel).read_text().split("improvedTopologyBlocks : Array (Array Nat) := #[")[1].split("]\n\ndef")[0])
        if mine_words != theirs_words:
            mismatches.append(rel)
        rel = "Zeta23/ThmD/Sextuple/A1275/ScalarData.lean"
        theirs = (R / rel).read_text()
        mine = files[rel]
        def certs(s):
            return re.findall(r"def improvedScalarCert\d+ : MacroScalarCert 272 := \{.*?\n\}", s, re.S)
        def checks(s):
            return re.findall(r"lemma improvedScalarCert\d+_check.*?\]\n", s, re.S)
        if certs(mine) != certs(theirs):
            mismatches.append(rel + " (certificate definitions)")
        # check lemmas: the committed A1275 module uses `norm_num`, the generator `decide +kernel`; only
        # the certificate definitions are compared.
        if mismatches:
            for rel, text in files.items():
                p = a.repo / rel; p.parent.mkdir(parents=True, exist_ok=True); p.write_text(text)
        require(not mismatches, "validation mismatches: " + ", ".join(mismatches[:10]))
        print(f"validate-a1275: PASS ({len(chunks)} chunks, {len(nodes)} nodes, {em.part_count} parts, "
              f"{em.group_count} word groups, {tree.scalar_count} scalar certificates all reproduced)")

    for rel, text in files.items():
        p = a.repo / rel
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(text)
    report = {"ns": a.ns, "A": str(tree.A), "B": str(tree.B), "cutoff": str(tree.cutoff),
              "public_decimal": f"{em.dec_num}/10^10", "exact_lower_bound": str(em.lower), "margin": str(em.margin),
              "token_count": tree.token_count, "leaves": tree.leaves, "quadratic_leaves": tree.quadratic,
              "max_depth": tree.max_depth, "fuel": tree.fuel, "chunks": len(chunks), "assembly_nodes": len(nodes),
              "parts": em.part_count, "word_groups": em.group_count, "scalar_certificates": tree.scalar_count,
              "files": len(files), "manifest_sha256": sha256((a.tree_dir / "manifest.json").read_bytes()),
              "generator_sha256": sha256(Path(__file__).read_bytes())}
    if a.report is not None:
        a.report.write_text(json.dumps(report, indent=1, sort_keys=True) + "\n")
    print(json.dumps(report, sort_keys=True))
    return 0


if __name__ == "__main__":
    sys.exit(main())
