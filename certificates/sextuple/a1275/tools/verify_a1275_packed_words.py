#!/usr/bin/env python3
"""Decode the Lean word literals of the A1275 certificate back to the canonical byte streams.

Reads `Zeta23/ThmD/Sextuple/A1275/TreeWords.lean` (topology blocks) and the 31
`WordData/LeafBlocksNNN.lean` modules (leaf block words), reconstructs the four
serialized streams of `certificates/sextuple/a1275/macro-scalar-tree/` — topology
(u64le), terminal kinds (u8), anchors (5 × u16le per quadratic leaf), term codes
(15 × u16le per quadratic leaf) — and compares their SHA-256 with `manifest.json`.
Independent of the generators; standard library only; no `assert`.
"""
from __future__ import annotations
import argparse, hashlib, json, re, sys
sys.set_int_max_str_digits(0)
from pathlib import Path

LEAF_BITS, LEAF_PER_BLOCK, GROUPS = 321, 256, 31


def fail(msg: str) -> None:
    raise SystemExit(f"verify_a1275_packed_words: FAIL: {msg}")


def parse_nested(src: str, name: str) -> list[list[int]]:
    key = f"def {name} : Array (Array Nat) := #["
    i = src.index(key) + len(key)
    depth, j = 1, i
    while depth:
        c = src[j]
        depth += (c == "[") - (c == "]")
        j += 1
    body = src[i:j - 1]
    return [[int(x) for x in re.findall(r"\d+", blk)] for blk in re.findall(r"#\[([^\]]*)\]", body)]


def parse_flat(src: str, name: str) -> list[int]:
    key = f"def {name} : Array Nat := #["
    i = src.index(key) + len(key)
    j = src.index("]", i)
    return [int(x) for x in re.findall(r"\d+", src[i:j])]


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--repo", type=Path, default=Path(__file__).resolve().parents[4])
    a = ap.parse_args()
    a1275 = a.repo / "Zeta23/ThmD/Sextuple/A1275"
    tree = a.repo / "certificates/sextuple/a1275/macro-scalar-tree"
    manifest = json.loads((tree / "manifest.json").read_text())
    tw = (a1275 / "TreeWords.lean").read_text()
    blocks = parse_nested(tw, "improvedTopologyBlocks")
    token_count = int(re.search(r"def improvedTokenCount : ℕ := (\d+)", tw)[1])
    leaf_count = int(re.search(r"def improvedLeafCount : ℕ := (\d+)", tw)[1])
    if token_count != 2 * int(manifest["leaves"]) - 1 or leaf_count != int(manifest["leaves"]):
        fail("token/leaf counts disagree with manifest")
    block_size = int(re.search(r"def improvedTopologyBlockSize : ℕ := (\d+)", (a1275 / "TreeReader.lean").read_text())[1])
    if any(len(b) != block_size for b in blocks[:-1]) or not (0 < len(blocks[-1]) <= block_size):
        fail("topology block sizes are not uniform")
    words = [w for b in blocks for w in b]
    if len(words) != (token_count + 19) // 20 or any(w >= 2 ** 60 for w in words):
        fail("topology word count or width")
    topo = b"".join(w.to_bytes(8, "little") for w in words)
    # leaf words
    group_names = re.findall(r"improvedLeafBlocksChunk(\d{3})", tw[tw.index("def improvedLeafBlockGroups"):])
    if [int(g) for g in group_names] != list(range(GROUPS)):
        fail("leaf group list is not LeafBlocks000..030 in order")
    block_words: list[int] = []
    for g in range(GROUPS):
        src = (a1275 / f"WordData/LeafBlocks{g:03d}.lean").read_text()
        arr = parse_flat(src, f"improvedLeafBlocksChunk{g:03d}")
        if g < GROUPS - 1 and len(arr) != 25:
            fail(f"group {g} has {len(arr)} block words, expected 25")
        block_words.extend(arr)
    if len(block_words) != (leaf_count + LEAF_PER_BLOCK - 1) // LEAF_PER_BLOCK:
        fail("leaf block word count")
    mask = (1 << LEAF_BITS) - 1
    kinds, anchors, terms = bytearray(), bytearray(), bytearray()
    quadratic = 0
    for p in range(leaf_count):
        blk = block_words[p // LEAF_PER_BLOCK]
        w = (blk >> (LEAF_BITS * (p % LEAF_PER_BLOCK))) & mask
        if w == 0:
            kinds.append(0)
            continue
        if w % 2 != 1:
            fail(f"leaf {p}: nonzero even word")
        kinds.append(1)
        quadratic += 1
        for k in range(5):
            anchors += ((w >> (1 + 16 * k)) & 65535).to_bytes(2, "little")
        for k in range(15):
            terms += ((w >> (1 + 16 * (5 + k))) & 65535).to_bytes(2, "little")
    last = block_words[-1]
    if leaf_count % LEAF_PER_BLOCK and last >= 1 << (LEAF_BITS * (leaf_count % LEAF_PER_BLOCK)):
        fail("nonzero leaf padding")
    if quadratic != int(manifest["quadratic_leaves"]):
        fail(f"quadratic leaf count {quadratic}")
    got = {"topology": hashlib.sha256(topo).hexdigest(), "kinds": hashlib.sha256(kinds).hexdigest(),
           "anchors": hashlib.sha256(anchors).hexdigest(), "terms": hashlib.sha256(terms).hexdigest()}
    for k, v in got.items():
        if v != manifest["stream_sha256"][k]:
            fail(f"{k} stream SHA-256 {v} != manifest {manifest['stream_sha256'][k]}")
        raw = tree / {"topology": "topology-u64le.bin", "kinds": "terminal-kinds-u8.bin",
                      "anchors": "anchors-u16le.bin", "terms": "term-codes-u16le.bin"}[k]
        if raw.exists() and hashlib.sha256(raw.read_bytes()).hexdigest() != v:
            fail(f"{k}: on-disk stream differs from decoded Lean literal")
    print(json.dumps({"status": "PASS", "token_count": token_count, "leaf_count": leaf_count,
                      "quadratic_leaves": quadratic, "topology_words": len(words),
                      "topology_blocks": len(blocks), "leaf_block_words": len(block_words),
                      "stream_sha256": got}, indent=1, sort_keys=True))
    return 0


if __name__ == "__main__":
    sys.exit(main())
