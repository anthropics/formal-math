#!/usr/bin/env python3
"""Fail-closed generator for the bounded A1275 replay source modules."""
from __future__ import annotations
import argparse
import hashlib
import json
import os
import platform
import shutil
import struct
import sys
from collections import Counter
from pathlib import Path

sys.setrecursionlimit(1000000)
sys.set_int_max_str_digits(0)

PREFIX = "Zeta23.ThmD.Sextuple.A1275"
TREEWORDS = PREFIX + ".TreeWords"
LAYOUT = PREFIX + ".Layout"
ASSEMBLY_STEP = "Zeta23.ThmD.Sextuple.Macro.AssemblyStep"
EXPECTED_PLAN_SHA256 = "e33c363129cc0d2b00480a04e914a1977680265994f1bd7cd7e6fae068aeccf5"
EXPECTED_RAW_MANIFEST_SHA256 = "732a99cf5c4755ee18686f4a14669c61162bf6bdf87d7ca2d2564098e3346c30"
EXPECTED_RAW = {
    "topology-u64le.bin": "cc1dc05c152a218d4a44466d102db703a60e819cd83eccaf4196fed19ba8352b",
    "terminal-kinds-u8.bin": "a2df050738a1bc4052da743ea26a8e8aa56373b7bcd23ac9b6aed3bfa5fd0aab",
    "anchors-u16le.bin": "e6dbe9ca333f8757b5ba39ab62fd902e02662b5e412ad688d0890e7664677394",
    "term-codes-u16le.bin": "0f8c90f474e75f9dd41d29b4e2a2df77883250c8a1882258e62b6c7f28d6748f",
}
EXPECTED_FREEZE_SHA256 = "dca59eeef948a61d20121d6799c721ca50933d02313ac7b027ec05431a6febf7"
EXPECTED_TREEWORDS_SHA256 = "1407a17502b086957d5af7d2c1f24fde0897b93c18adb0903dbbbac85c33da27"
EXPECTED_ASSEMBLY_STEP_SHA256 = "b714f09932210bb1374e550f3ce747316e477afc19a7fcc476580cefe239aa35"
TOKEN_COUNT = 385967
LEAF_COUNT = 192984
QUADRATIC_COUNT = 191474
TAIL_COUNT = 1510
CHUNK_COUNT = 8953
NODE_COUNT = 8952
PART_COUNT = 90
FUEL = 90
MAX_DEPTH = 89
MAX_TOKENS = 100
GROUP_SIZE = 100
PATH_FIN_COUNT = 397456
ASSEMBLY_FIN_COUNT = 8952
TOTAL_FIN_COUNT = 406408


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sha256_file(path: Path) -> str:
    return sha256_bytes(path.read_bytes())


def canonical_json(obj: object) -> bytes:
    return (json.dumps(obj, sort_keys=True, separators=(",", ":")) + "\n").encode("utf-8")


def load_json_no_duplicates(path: Path) -> object:
    def pairs_hook(pairs: list[tuple[str, object]]) -> dict:
        out = {}
        for key, value in pairs:
            require(key not in out, f"duplicate JSON key: {key}")
            out[key] = value
        return out
    return json.loads(path.read_text(), object_pairs_hook=pairs_hook)


def object_sha256(obj: object) -> str:
    return sha256_bytes(canonical_json(obj))


def exact_keys(obj: object, keys: set[str], label: str) -> dict:
    require(type(obj) is dict, f"{label}: expected object")
    require(set(obj) == keys, f"{label}: schema keys mismatch")
    return obj


def natural(value: object, label: str) -> int:
    require(type(value) is int and value >= 0, f"{label}: expected natural")
    return value


def bounded_axis(value: object, label: str) -> int:
    axis = natural(value, label)
    require(axis < 5, f"{label}: axis outside Fin 5")
    return axis


def bool_bit(value: object, label: str) -> int:
    require(type(value) is int and value in (0, 1), f"{label}: expected 0/1")
    return value


class Node:
    __slots__ = ("id", "t0", "p0", "t1", "p1", "depth", "axis", "path", "children", "tokens")


def validate_raw_manifest(manifest: object) -> dict:
    require(type(manifest) is dict, "raw manifest: expected object")
    required = {
        "A": "51/4000", "B": "1094977/5000000000",
        "cutoff": "63750000/1094977", "catalog_piece_count": 272,
        "scalar_certificate_count": 1383, "fuel": FUEL,
        "maximum_depth": MAX_DEPTH, "token_count": TOKEN_COUNT,
        "leaves": LEAF_COUNT, "quadratic_leaves": QUADRATIC_COUNT,
        "tail_leaves": TAIL_COUNT,
    }
    for key, value in required.items():
        require(manifest.get(key) == value, f"raw manifest: wrong {key}")
    require(manifest.get("full_stack_exhaustion") is True, "raw manifest: stack not exhausted")
    require(natural(manifest.get("topology_word_count"), "raw topology_word_count") == (TOKEN_COUNT + 19) // 20,
            "raw manifest: topology word count")
    return manifest


def read_raw(raw_dir: Path, verify_hashes: bool = True) -> tuple[dict, dict[str, bytes]]:
    manifest_path = raw_dir / "manifest.json"
    require(manifest_path.is_file(), "raw manifest missing")
    if verify_hashes:
        require(sha256_file(manifest_path) == EXPECTED_RAW_MANIFEST_SHA256, "raw manifest hash mismatch")
    manifest = validate_raw_manifest(load_json_no_duplicates(manifest_path))
    blobs: dict[str, bytes] = {}
    for name, expected in EXPECTED_RAW.items():
        path = raw_dir / name
        require(path.is_file(), f"raw stream missing: {name}")
        data = path.read_bytes()
        if verify_hashes:
            require(sha256_bytes(data) == expected, f"raw stream hash mismatch: {name}")
        blobs[name] = data
    return manifest, blobs


def validate_raw_blobs(manifest: dict, blobs: dict[str, bytes]) -> tuple[list[int], bytes]:
    top = blobs["topology-u64le.bin"]
    kinds = blobs["terminal-kinds-u8.bin"]
    anchors_data = blobs["anchors-u16le.bin"]
    terms_data = blobs["term-codes-u16le.bin"]
    word_count = manifest["topology_word_count"]
    require(len(top) == 8 * word_count, "raw topology truncation/extension")
    require(len(kinds) == LEAF_COUNT, "raw kind truncation/extension")
    require(len(anchors_data) % 2 == 0 and len(terms_data) % 2 == 0, "raw u16 alignment")
    words = list(struct.unpack("<" + "Q" * word_count, top))
    require(all(word < 2 ** 60 for word in words), "raw topology physical range")
    valid_last = TOKEN_COUNT % 20
    require(valid_last != 0 and words[-1] < 2 ** (3 * valid_last), "raw topology padding")
    tokens = [(words[i // 20] >> (3 * (i % 20))) & 7 for i in range(TOKEN_COUNT)]
    require(all(token <= 5 for token in tokens), "raw topology token range")
    require(all(kind in (0, 1) for kind in kinds), "raw terminal kind range")
    require(kinds.count(1) == QUADRATIC_COUNT and kinds.count(0) == TAIL_COUNT, "raw terminal kind counts")
    anchors = struct.unpack("<" + "H" * (len(anchors_data) // 2), anchors_data)
    terms = struct.unpack("<" + "H" * (len(terms_data) // 2), terms_data)
    require(len(anchors) == 5 * QUADRATIC_COUNT, "raw anchor count")
    require(len(terms) == 15 * QUADRATIC_COUNT, "raw term count")
    require(all(anchor <= 16384 for anchor in anchors), "raw anchor range")
    require(all(term < 272 or 32768 <= term < 32768 + 1383 or term == 65535 for term in terms),
            "raw term range")
    require(sum(56 <= term < 272 for term in terms) == manifest["refinement_term_count"],
            "raw refinement term count")
    require(sum(32768 <= term < 32768 + 1383 for term in terms) == manifest["scalar_term_count"],
            "raw scalar term count")
    require(sum(term == 65535 for term in terms) == manifest["zero_term_count"], "raw zero term count")
    return tokens, kinds


def build_tree(tokens: list[int], kinds: bytes) -> tuple[Node, int, int]:
    topology_cursor = 0
    payload_cursor = 0
    next_id = 0
    maximum_depth = 0

    def rec(depth: int, path: list[list[int]]) -> Node:
        nonlocal topology_cursor, payload_cursor, next_id, maximum_depth
        require(topology_cursor < len(tokens), "raw topology cursor underflow")
        node = Node()
        node.id = next_id
        next_id += 1
        node.t0 = topology_cursor
        node.p0 = payload_cursor
        node.depth = depth
        node.path = path
        node.children = []
        maximum_depth = max(maximum_depth, depth)
        token = tokens[topology_cursor]
        topology_cursor += 1
        if token == 0:
            node.axis = None
            require(payload_cursor < len(kinds), "raw payload cursor underflow")
            require(kinds[payload_cursor] in (0, 1), "raw payload kind")
            payload_cursor += 1
        else:
            axis = bounded_axis(token - 1, "raw split")
            node.axis = axis
            node.children = [rec(depth + 1, path + [[0, axis]]), rec(depth + 1, path + [[1, axis]])]
        node.t1 = topology_cursor
        node.p1 = payload_cursor
        node.tokens = node.t1 - node.t0
        return node

    root = rec(0, [])
    require(topology_cursor == len(tokens), "raw topology cursor not exhausted")
    require(payload_cursor == len(kinds), "raw payload cursor not exhausted")
    require(maximum_depth == MAX_DEPTH, "raw maximum depth")
    return root, maximum_depth, next_id


def partition(root: Node) -> tuple[list[Node], list[Node]]:
    chunks: list[Node] = []
    internals: list[Node] = []

    def rec(node: Node) -> None:
        if node.tokens <= MAX_TOKENS or not node.children:
            chunks.append(node)
        else:
            internals.append(node)
            rec(node.children[0])
            rec(node.children[1])

    rec(root)
    require(len(chunks) == CHUNK_COUNT and len(internals) == NODE_COUNT, "canonical partition counts")
    return chunks, internals


def canonical_plan(manifest: dict, root: Node, chunks: list[Node]) -> dict:
    chunk_index = {node.id: index for index, node in enumerate(chunks)}
    order: list[Node] = []

    def post(node: Node) -> None:
        if node.id in chunk_index:
            return
        post(node.children[0])
        post(node.children[1])
        order.append(node)

    post(root)
    node_index = {node.id: index for index, node in enumerate(order)}

    def ref(node: Node) -> list[object]:
        if node.id in chunk_index:
            return ["chunk", chunk_index[node.id]]
        return ["node", node_index[node.id]]

    chunk_data = []
    for node in chunks:
        chunk_data.append({
            "id": node.id, "t0": node.t0, "p0": node.p0, "t1": node.t1, "p1": node.p1,
            "depth": node.depth, "tokens": node.tokens, "payloads": node.p1 - node.p0,
            "fuel": FUEL - node.depth, "path": node.path,
        })
    assembly_data = []
    for node in order:
        assembly_data.append({
            "id": node.id, "t0": node.t0, "p0": node.p0, "t1": node.t1, "p1": node.p1,
            "depth": node.depth, "axis": node.axis, "fuel_after_split": FUEL - node.depth - 1,
            "left": ref(node.children[0]), "right": ref(node.children[1]),
        })
    return {
        "schema": 1,
        "source_manifest_sha256": EXPECTED_RAW_MANIFEST_SHA256,
        "constants": {
            "A": "51/4000", "B": "1094977/5000000000", "cutoff": "63750000/1094977",
            "table_count": 272, "scalar_count": 1383, "fuel": FUEL,
            "max_tokens_per_kernel_reduction": MAX_TOKENS,
        },
        "tree": {
            "token_count": TOKEN_COUNT, "leaf_count": LEAF_COUNT,
            "quadratic_leaves": QUADRATIC_COUNT, "tail_leaves": TAIL_COUNT,
            "maximum_depth": MAX_DEPTH, "node_count": TOKEN_COUNT,
        },
        "module_grouping": {"chunks_per_module": 100, "assembly_per_module": GROUP_SIZE},
        "chunks": chunk_data,
        "assembly": assembly_data,
        "root": ref(root),
    }


def reference_metadata(ref: list[object], chunks: list[dict], nodes: list[dict]) -> dict:
    require(type(ref) is list and len(ref) == 2, "DAG reference schema")
    kind = ref[0]
    index = natural(ref[1], "DAG reference index")
    require(kind in ("chunk", "node"), "DAG reference kind")
    table = chunks if kind == "chunk" else nodes
    require(index < len(table), "DAG reference out of range")
    return table[index]


def validate_plan_semantics(plan: object, expected: dict | None = None) -> dict:
    plan = exact_keys(plan, {"schema", "source_manifest_sha256", "constants", "tree", "module_grouping", "chunks", "assembly", "root"}, "plan")
    require(plan["schema"] == 1 and plan["source_manifest_sha256"] == EXPECTED_RAW_MANIFEST_SHA256, "plan header")
    require(plan["constants"] == {
        "A": "51/4000", "B": "1094977/5000000000", "cutoff": "63750000/1094977",
        "table_count": 272, "scalar_count": 1383, "fuel": FUEL,
        "max_tokens_per_kernel_reduction": MAX_TOKENS,
    }, "plan constants")
    require(plan["tree"] == {
        "token_count": TOKEN_COUNT, "leaf_count": LEAF_COUNT, "quadratic_leaves": QUADRATIC_COUNT,
        "tail_leaves": TAIL_COUNT, "maximum_depth": MAX_DEPTH, "node_count": TOKEN_COUNT,
    }, "plan tree summary")
    require(plan["module_grouping"] == {"chunks_per_module": 100, "assembly_per_module": GROUP_SIZE}, "plan grouping")
    chunks = plan["chunks"]
    nodes = plan["assembly"]
    require(type(chunks) is list and len(chunks) == CHUNK_COUNT, "plan chunk omission/duplication/count")
    require(type(nodes) is list and len(nodes) == NODE_COUNT, "plan assembly omission/duplication/count")
    chunk_paths: list[tuple[tuple[int, int], ...]] = []
    ids: list[int] = []
    payload_cursor = 0
    covered_tokens: list[int] = []
    for index, item in enumerate(chunks):
        chunk = exact_keys(item, {"id", "t0", "p0", "t1", "p1", "depth", "tokens", "payloads", "fuel", "path"}, f"chunk {index}")
        values = {key: natural(chunk[key], f"chunk {index} {key}") for key in ("id", "t0", "p0", "t1", "p1", "depth", "tokens", "payloads", "fuel")}
        require(values["t0"] < values["t1"] <= TOKEN_COUNT, f"chunk {index}: topology cursor")
        require(values["p0"] < values["p1"] <= LEAF_COUNT, f"chunk {index}: payload cursor")
        require(values["tokens"] == values["t1"] - values["t0"] and 1 <= values["tokens"] <= MAX_TOKENS, f"chunk {index}: token bound")
        require(values["payloads"] == values["p1"] - values["p0"], f"chunk {index}: payload count")
        require(values["tokens"] == 2 * values["payloads"] - 1, f"chunk {index}: subtree cardinality")
        require(values["depth"] <= MAX_DEPTH and values["fuel"] == FUEL - values["depth"] and values["fuel"] > 0, f"chunk {index}: fuel/depth")
        path = chunk["path"]
        require(type(path) is list and len(path) == values["depth"], f"chunk {index}: path/depth")
        normalized = []
        for step_index, step in enumerate(path):
            require(type(step) is list and len(step) == 2, f"chunk {index}: path step schema")
            up = bool_bit(step[0], f"chunk {index}: path direction {step_index}")
            axis = bounded_axis(step[1], f"chunk {index}: path axis {step_index}")
            normalized.append((up, axis))
        chunk_paths.append(tuple(normalized))
        require(values["p0"] == payload_cursor, f"chunk {index}: payload cursor gap/overlap")
        payload_cursor = values["p1"]
        ids.append(values["id"])
        covered_tokens.extend(range(values["t0"], values["t1"]))
    require(payload_cursor == LEAF_COUNT, "chunk payload cursor exhaustion")
    require(len(set(chunk_paths)) == CHUNK_COUNT, "duplicate chunk path")
    sorted_paths = sorted(chunk_paths)
    for left, right in zip(sorted_paths, sorted_paths[1:]):
        require(not (len(left) <= len(right) and right[:len(left)] == left), "chunk path prefix overlap")
    node_paths: list[tuple[tuple[int, int], ...]] = []
    all_meta: list[dict] = list(chunks)
    edge_records = []
    for index, item in enumerate(nodes):
        node = exact_keys(item, {"id", "t0", "p0", "t1", "p1", "depth", "axis", "fuel_after_split", "left", "right"}, f"node {index}")
        values = {key: natural(node[key], f"node {index} {key}") for key in ("id", "t0", "p0", "t1", "p1", "depth", "fuel_after_split")}
        axis = bounded_axis(node["axis"], f"node {index}: assembly axis")
        require(values["t0"] < values["t1"] <= TOKEN_COUNT and values["p0"] < values["p1"] <= LEAF_COUNT, f"node {index}: cursor range")
        require(values["t1"] - values["t0"] == 2 * (values["p1"] - values["p0"]) - 1, f"node {index}: subtree cardinality")
        require(values["depth"] < MAX_DEPTH and values["fuel_after_split"] == FUEL - values["depth"] - 1, f"node {index}: fuel/depth")
        for label, ref in (("left", node["left"]), ("right", node["right"])):
            require(type(ref) is list and len(ref) == 2 and ref[0] in ("chunk", "node"), f"node {index}: {label} reference schema")
            ref_index = natural(ref[1], f"node {index}: {label} index")
            require(ref_index < (CHUNK_COUNT if ref[0] == "chunk" else index), f"node {index}: {label} forward/out-of-range DAG reference")
        require(node["left"] != node["right"], f"node {index}: duplicate DAG children")
        left_meta = reference_metadata(node["left"], chunks, nodes[:index])
        right_meta = reference_metadata(node["right"], chunks, nodes[:index])
        require(left_meta["depth"] == values["depth"] + 1 and right_meta["depth"] == values["depth"] + 1, f"node {index}: child depth")
        require(left_meta["t0"] == values["t0"] + 1 and left_meta["p0"] == values["p0"], f"node {index}: left cursor start")
        require(right_meta["t0"] == left_meta["t1"] and right_meta["p0"] == left_meta["p1"], f"node {index}: child cursor continuity")
        require(right_meta["t1"] == values["t1"] and right_meta["p1"] == values["p1"], f"node {index}: right cursor end")
        def ref_path(ref: list[object]) -> tuple[tuple[int, int], ...]:
            if ref[0] == "chunk":
                return chunk_paths[ref[1]]
            return node_paths[ref[1]]
        left_path = ref_path(node["left"])
        right_path = ref_path(node["right"])
        require(len(left_path) == values["depth"] + 1 and len(right_path) == values["depth"] + 1, f"node {index}: child path length")
        require(left_path[:-1] == right_path[:-1], f"node {index}: child path parent mismatch")
        require(left_path[-1] == (0, axis) and right_path[-1] == (1, axis), f"node {index}: child path split mismatch")
        node_paths.append(left_path[:-1])
        ids.append(values["id"])
        covered_tokens.append(values["t0"])
        edge_records.append([index, node["left"], node["right"], axis])
        all_meta.append(node)
    require(len(ids) == CHUNK_COUNT + NODE_COUNT and len(set(ids)) == len(ids), "plan partition-root ID duplication")
    require(all(node_id < TOKEN_COUNT for node_id in ids), "plan partition-root ID range")
    require(sorted(covered_tokens) == list(range(TOKEN_COUNT)), "plan topology token coverage/duplication/omission")
    require(plan["root"] == ["node", NODE_COUNT - 1], "plan root reference")
    root = nodes[-1]
    require((root["t0"], root["p0"], root["t1"], root["p1"], root["depth"], root["fuel_after_split"]) ==
            (0, 0, TOKEN_COUNT, LEAF_COUNT, 0, FUEL - 1), "plan root cursor/fuel")
    require(node_paths[-1] == (), "plan root path")
    require(sum(len(path) for path in chunk_paths) == PATH_FIN_COUNT, "plan chunk path Fin count")
    require(len(nodes) == ASSEMBLY_FIN_COUNT, "plan assembly Fin count")
    if expected is not None:
        require(plan == expected, "plan differs from raw-derived canonical plan")
    return {
        "chunk_paths": chunk_paths, "node_paths": node_paths,
        "edge_records": edge_records, "path_sha256": object_sha256(plan["chunks"]),
        "dag_sha256": object_sha256(plan["assembly"]),
    }


def load_and_validate_inputs(plan_path: Path, raw_dir: Path) -> tuple[dict, dict]:
    require(plan_path.is_file(), "bounded plan missing")
    require(sha256_file(plan_path) == EXPECTED_PLAN_SHA256, "bounded plan hash mismatch")
    manifest, blobs = read_raw(raw_dir, True)
    tokens, kinds = validate_raw_blobs(manifest, blobs)
    root, maximum_depth, raw_nodes = build_tree(tokens, kinds)
    require(maximum_depth == MAX_DEPTH and raw_nodes == TOKEN_COUNT, "raw tree counts")
    chunks, internals = partition(root)
    require(len(internals) == NODE_COUNT, "raw partition internal count")
    derived = canonical_plan(manifest, root, chunks)
    plan = load_json_no_duplicates(plan_path)
    semantics = validate_plan_semantics(plan, derived)
    return plan, semantics


def verify_foundations(foundation_root: Path, freeze_manifest_path: Path, repo_root: Path) -> tuple[dict, dict[str, Path]]:
    require(sha256_file(freeze_manifest_path) == EXPECTED_FREEZE_SHA256, "foundation freeze manifest hash")
    freeze = load_json_no_duplicates(freeze_manifest_path)
    require(freeze.get("status") == "PASS" and freeze.get("source_count") == 44, "foundation freeze status/count")
    require(type(freeze.get("files")) is dict and len(freeze["files"]) == 44, "foundation freeze inventory")
    current = {}
    for rel, expected in sorted(freeze["files"].items()):
        path = foundation_root / rel
        require(path.is_file(), f"foundation source missing: {rel}")
        now = {"sha256": sha256_file(path), "bytes": path.stat().st_size}
        require(now == expected, f"foundation source changed: {rel}")
        current[rel] = now
    treewords_path = foundation_root / "Zeta23/ThmD/Sextuple/A1275/TreeWords.lean"
    require(sha256_file(treewords_path) == EXPECTED_TREEWORDS_SHA256, "TreeWords source hash")
    assembly_step_path = repo_root / "Zeta23/ThmD/Sextuple/Macro/AssemblyStep.lean"
    require(assembly_step_path.is_file() and sha256_file(assembly_step_path) == EXPECTED_ASSEMBLY_STEP_SHA256,
            "AssemblyStep source hash")
    layout_path = foundation_root / "Zeta23/ThmD/Sextuple/A1275/Layout.lean"
    module_sources = {TREEWORDS: treewords_path, LAYOUT: layout_path, ASSEMBLY_STEP: assembly_step_path}
    return current, module_sources


def fin_axis(axis: object, label: str) -> str:
    value = bounded_axis(axis, label)
    return f"⟨{value}, by decide⟩"


def render_path(path: object, label: str) -> str:
    require(type(path) is list, f"{label}: path list")
    items = []
    for index, step in enumerate(reversed(path)):
        require(type(step) is list and len(step) == 2, f"{label}: path step")
        up = bool_bit(step[0], f"{label}: path direction {index}")
        axis = fin_axis(step[1], f"{label}: path axis {index}")
        items.append(f"({'true' if up else 'false'}, {axis})")
    return "[" + ", ".join(items) + "]"


def chunk_module(index: int) -> str:
    return f"{PREFIX}.Chunks.Chunk{index:04d}"


def node_name(index: int) -> str:
    return f"improvedNode{index:04d}"


def ref_name(ref: list[object]) -> str:
    if ref[0] == "chunk":
        return f"improvedChunk{ref[1]:04d}"
    return node_name(ref[1])


def render_chunk(index: int, chunk: dict) -> tuple[str, list[str], list[str]]:
    imports = [TREEWORDS]
    path = render_path(chunk["path"], f"chunk {index}")
    theorem = f"improvedChunk{index:04d}"
    text = f'''import {TREEWORDS}

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor {chunk["t0"]}, payload cursor {chunk["p0"]}, depth {chunk["depth"]}, {chunk["tokens"]} tokens. -/
theorem {theorem} :
    replayAffineTree improvedConcreteLeafCheck improvedTopologyStream improvedPayloadStream
      {chunk["fuel"]} {chunk["t0"]} {chunk["p0"]} (improvedPathBox improvedRootBox {path}) =
      some ({chunk["t1"]}, {chunk["p1"]}) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
'''
    return text, imports, [theorem]


def render_part(part_index: int, nodes: list[dict], chunks: list[dict]) -> tuple[str, list[str], list[str]]:
    start = part_index * GROUP_SIZE
    end = min(start + GROUP_SIZE, len(nodes))
    group = nodes[start:end]
    imports = [TREEWORDS]
    if part_index > 0:
        imports.append(f"{PREFIX}.Assembly.Part{part_index - 1:03d}")
    needed_chunks = sorted({ref[1] for node in group for ref in (node["left"], node["right"]) if ref[0] == "chunk"})
    imports.extend(chunk_module(index) for index in needed_chunks)
    imports.append(ASSEMBLY_STEP)
    lines = [*(f"import {module}" for module in imports), "", "set_option maxHeartbeats 0", "set_option maxRecDepth 100000", "", "namespace Zeta23.ThmD.Sextuple.MacroPrototype", "open Zeta23.ThmD.Sextuple", ""]
    theorem_names = []
    for index in range(start, end):
        node = nodes[index]
        left = reference_metadata(node["left"], chunks, nodes[:index])
        axis = fin_axis(node["axis"], f"node {index}: assembly axis")
        theorem = node_name(index)
        theorem_names.append(theorem)
        lines.extend([
            f"theorem {theorem} :=",
            f"  replayAffineTree_split_step (fuel := {node['fuel_after_split']}) (t := {node['t0']}) (p := {node['p0']})",
            f"    (axis := {axis}) (tm := {left['t1']}) (pm := {left['p1']})",
            f"    (t' := {node['t1']}) (p' := {node['p1']})",
            f"    (by decide +kernel) {ref_name(node['left'])} {ref_name(node['right'])}",
            "",
        ])
    lines.append("end Zeta23.ThmD.Sextuple.MacroPrototype")
    return "\n".join(lines) + "\n", imports, theorem_names


def render_tree_assembly(plan: dict) -> tuple[str, list[str], list[str]]:
    require(plan["root"] == ["node", NODE_COUNT - 1], "render root reference")
    imports = [LAYOUT, f"{PREFIX}.Assembly.Part{PART_COUNT - 1:03d}"]
    text = f'''import {imports[0]}
import {imports[1]}

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- The complete improved replay consumes both logical streams exactly. -/
theorem improvedRootReplay :
    replayAffineTree improvedConcreteLeafCheck improvedTopologyStream improvedPayloadStream
      {FUEL} 0 0 improvedRootBox = some ({TOKEN_COUNT}, {LEAF_COUNT}) := by
  have h := {node_name(NODE_COUNT - 1)}
  simpa only [improvedPathBox] using h

#print axioms improvedRootReplay

end Zeta23.ThmD.Sextuple.MacroPrototype
'''
    return text, imports, ["improvedRootReplay"]


def validate_import_record(imports: list[str], hashes: dict[str, str], module_sources: dict[str, Path]) -> None:
    require(len(imports) == len(set(imports)), "duplicate source import")
    require(set(imports) == set(hashes), "import hash key mismatch")
    for module in imports:
        require(module in module_sources, f"unresolved source import: {module}")
        require(hashes[module] == sha256_file(module_sources[module]), f"source import hash mismatch: {module}")


def write_source(stage: Path, rel: str, text: str) -> Path:
    require(not rel.startswith("/") and ".." not in Path(rel).parts, "unsafe output path")
    require(text.endswith("\n"), "source lacks final newline")
    path = stage / rel
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(text.encode("utf-8"))
    return path


def source_record(path: Path, rel: str, module: str, imports: list[str], theorem_names: list[str], module_sources: dict[str, Path], metadata: dict) -> dict:
    import_hashes = {name: sha256_file(module_sources[name]) for name in imports}
    validate_import_record(imports, import_hashes, module_sources)
    text = path.read_text()
    require(text.count("theorem ") == len(theorem_names), f"theorem declaration count: {rel}")
    require(all(text.count("theorem " + name) == 1 for name in theorem_names), f"theorem name missing/duplicate: {rel}")
    return {
        "module": module, "sha256": sha256_file(path), "bytes": path.stat().st_size,
        "imports": imports, "import_source_sha256": import_hashes,
        "theorems": theorem_names, **metadata,
    }


def generate_sources(plan: dict, semantics: dict, stage: Path, module_sources: dict[str, Path]) -> dict:
    files: dict[str, dict] = {}
    chunks = plan["chunks"]
    nodes = plan["assembly"]
    for index, chunk in enumerate(chunks):
        rel = f"Zeta23/ThmD/Sextuple/A1275/Chunks/Chunk{index:04d}.lean"
        module = chunk_module(index)
        text, imports, theorems = render_chunk(index, chunk)
        path = write_source(stage, rel, text)
        module_sources[module] = path
        files[rel] = source_record(path, rel, module, imports, theorems, module_sources, {
            "kind": "chunk", "index": index, "raw_node_id": chunk["id"],
            "cursors": [chunk["t0"], chunk["p0"], chunk["t1"], chunk["p1"]],
            "depth": chunk["depth"], "fuel": chunk["fuel"], "tokens": chunk["tokens"],
            "payloads": chunk["payloads"], "path_length": len(chunk["path"]),
            "path_sha256": object_sha256(chunk["path"]),
        })
    imported_chunks: list[int] = []
    for part_index in range(PART_COUNT):
        rel = f"Zeta23/ThmD/Sextuple/A1275/Assembly/Part{part_index:03d}.lean"
        module = f"{PREFIX}.Assembly.Part{part_index:03d}"
        text, imports, theorems = render_part(part_index, nodes, chunks)
        path = write_source(stage, rel, text)
        module_sources[module] = path
        chunk_indices = sorted(int(name.rsplit("Chunk", 1)[1]) for name in imports if ".Chunks.Chunk" in name)
        imported_chunks.extend(chunk_indices)
        start = part_index * GROUP_SIZE
        end = min(start + GROUP_SIZE, NODE_COUNT)
        files[rel] = source_record(path, rel, module, imports, theorems, module_sources, {
            "kind": "assembly_part", "index": part_index, "node_range": [start, end],
            "node_count": end - start, "nodes_sha256": object_sha256(nodes[start:end]),
            "direct_chunk_indices": chunk_indices,
        })
    require(sorted(imported_chunks) == list(range(CHUNK_COUNT)), "assembly chunk import coverage/duplication")
    rel = "Zeta23/ThmD/Sextuple/A1275/TreeAssembly.lean"
    module = PREFIX + ".TreeAssembly"
    text, imports, theorems = render_tree_assembly(plan)
    path = write_source(stage, rel, text)
    module_sources[module] = path
    files[rel] = source_record(path, rel, module, imports, theorems, module_sources, {
        "kind": "root", "root_reference": plan["root"], "cursors": [0, 0, TOKEN_COUNT, LEAF_COUNT], "fuel": FUEL,
    })
    require(len(files) == CHUNK_COUNT + PART_COUNT + 1, "generated source count")
    all_text = "".join((stage / rel).read_text() for rel in sorted(files))
    explicit = all_text.count("⟨")
    require(explicit == TOTAL_FIN_COUNT, "explicit Fin 5 constructor count")
    require(all_text.count("by decide⟩") == TOTAL_FIN_COUNT, "proof-bearing Fin 5 constructor count")
    require("(axis := 0)" not in all_text and "(axis := 1)" not in all_text and "(axis := 2)" not in all_text and "(axis := 3)" not in all_text and "(axis := 4)" not in all_text, "bare assembly axis")
    for up in ("false", "true"):
        for axis in range(5):
            require(f"({up}, {axis})" not in all_text, "bare chunk path axis")
    require(all_text.count("theorem improvedChunk") == CHUNK_COUNT, "chunk theorem count")
    require(all_text.count("theorem improvedNode") == NODE_COUNT, "assembly theorem count")
    require(all_text.count("theorem improvedRootReplay") == 1, "root theorem count")
    file_core = {rel: {"sha256": record["sha256"], "bytes": record["bytes"]} for rel, record in sorted(files.items())}
    import_edges = [[record["module"], imported, record["import_source_sha256"][imported]] for record in files.values() for imported in record["imports"]]
    return {
        "files": files,
        "file_inventory_sha256": object_sha256(file_core),
        "source_bytes": sum(record["bytes"] for record in files.values()),
        "import_edge_count": len(import_edges),
        "import_edges_sha256": object_sha256(sorted(import_edges)),
        "explicit_fin": {
            "chunk_path": PATH_FIN_COUNT, "assembly_axis": ASSEMBLY_FIN_COUNT,
            "total": TOTAL_FIN_COUNT, "rendered_total": explicit,
        },
        "path_sha256": semantics["path_sha256"], "dag_sha256": semantics["dag_sha256"],
    }


def atomic_report(report_path: Path, report: dict) -> None:
    stage = report_path.with_name(report_path.name + ".new")
    stage.unlink(missing_ok=True)
    data = canonical_json(report)
    with stage.open("wb") as handle:
        handle.write(data)
        handle.flush()
        os.fsync(handle.fileno())
    os.replace(stage, report_path)


def run(args: argparse.Namespace) -> int:
    output_root = args.output_root.resolve()
    report_path = args.report.resolve()
    local_root = Path(__file__).resolve().parent
    require(output_root.is_relative_to(local_root), "output root must be project-local under generator directory")
    require(report_path.is_relative_to(local_root), "report must be project-local under generator directory")
    require(not report_path.is_relative_to(output_root), "report must be outside generated source root")
    require((args.mode == "optimized") == (sys.flags.optimize > 0), "declared mode does not match Python optimization mode")
    stage = output_root.with_name(output_root.name + ".new")
    report_path.unlink(missing_ok=True)
    report_path.with_name(report_path.name + ".new").unlink(missing_ok=True)
    require(not output_root.exists(), "output root already exists; prior canonical output left untouched")
    if stage.exists():
        shutil.rmtree(stage)
    try:
        plan, semantics = load_and_validate_inputs(args.plan.resolve(), args.raw_dir.resolve())
        foundations, module_sources = verify_foundations(args.foundation_root.resolve(), args.freeze_manifest.resolve(), args.repo_root.resolve())
        stage.mkdir(parents=True)
        generated = generate_sources(plan, semantics, stage, module_sources)
        foundations_after, _ = verify_foundations(args.foundation_root.resolve(), args.freeze_manifest.resolve(), args.repo_root.resolve())
        require(foundations_after == foundations, "44 foundation sources changed during generation")
        os.replace(stage, output_root)
        report = {
            "schema": 1, "status": "PASS", "mode": args.mode,
            "generator_sha256": sha256_file(Path(__file__)),
            "python": {"implementation": platform.python_implementation(), "version": platform.python_version(), "optimize": sys.flags.optimize},
            "inputs": {
                "bounded_plan": {"path": "tree-artifacts/bounded-replay-plan.json", "sha256": EXPECTED_PLAN_SHA256},
                "raw_manifest": {"path": "refined-A-0p01275/manifest.json", "sha256": EXPECTED_RAW_MANIFEST_SHA256},
                "raw_stream_sha256": EXPECTED_RAW,
                "foundation_freeze": {"path": "qualified-v2-repo-shadow/FREEZE-MANIFEST.json", "sha256": EXPECTED_FREEZE_SHA256},
                "assembly_step_sha256": EXPECTED_ASSEMBLY_STEP_SHA256,
            },
            "foundations": {"count": len(foundations), "inventory_sha256": object_sha256(foundations), "unchanged": True},
            "plan": {
                "token_count": TOKEN_COUNT, "leaf_count": LEAF_COUNT, "chunk_count": CHUNK_COUNT,
                "assembly_node_count": NODE_COUNT, "assembly_part_count": PART_COUNT,
                "maximum_depth": MAX_DEPTH, "fuel": FUEL, "max_chunk_tokens": MAX_TOKENS,
                "root": plan["root"], "final_cursor": [TOKEN_COUNT, LEAF_COUNT],
                "chunks_sha256": semantics["path_sha256"], "assembly_dag_sha256": semantics["dag_sha256"],
                "chunk_metadata_sha256": object_sha256(plan["chunks"]), "assembly_metadata_sha256": object_sha256(plan["assembly"]),
                "fuel_histogram": dict(sorted(Counter(chunk["fuel"] for chunk in plan["chunks"]).items())),
                "token_histogram": dict(sorted(Counter(chunk["tokens"] for chunk in plan["chunks"]).items())),
            },
            "sources": generated,
        }
        atomic_report(report_path, report)
        require(report_path.is_file() and json.loads(report_path.read_text()).get("status") == "PASS", "PASS report publication")
        print(json.dumps(report, sort_keys=True, indent=2))
        return 0
    except Exception:
        if stage.exists():
            shutil.rmtree(stage)
        report_path.unlink(missing_ok=True)
        report_path.with_name(report_path.name + ".new").unlink(missing_ok=True)
        raise


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--plan", required=True, type=Path)
    parser.add_argument("--raw-dir", required=True, type=Path)
    parser.add_argument("--foundation-root", required=True, type=Path)
    parser.add_argument("--freeze-manifest", required=True, type=Path)
    parser.add_argument("--repo-root", required=True, type=Path)
    parser.add_argument("--output-root", required=True, type=Path)
    parser.add_argument("--report", required=True, type=Path)
    parser.add_argument("--mode", required=True, choices=("normal", "optimized"))
    return parser.parse_args()


if __name__ == "__main__":
    try:
        sys.exit(run(parse_args()))
    except Exception as error:
        print(f"FAIL: {error}", file=sys.stderr)
        sys.exit(1)
