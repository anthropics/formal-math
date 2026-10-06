#!/usr/bin/env python3
"""Rewrite the 90 A1275 assembly part modules with explicit node statements.

The frozen generator emitted `theorem improvedNodeNNNN :=` (no statement), which Lean 4
rejects.  This tool keeps every part module's imports, options, namespace and node order,
and rewrites each node lemma in the audited baseline form

    theorem improvedNodeNNNN :
        replayAffineTree improvedConcreteLeafCheck improvedTopologyStream improvedPayloadStream
          FUEL T0 P0 (improvedPathBox improvedRootBox [PATH]) = some (T1, P1) :=
      replayAffineTree_split_step (fuel := FUEL-1) (t := T0) (p := P0)
        (axis := ⟨A, by decide⟩) (tm := TM) (pm := PM) (t' := T1) (p' := P1)
        (by decide +kernel) LEFT RIGHT

(the box is inferred from the statement: passing it explicitly as `(box := …)` makes the
elaborator's unification blow up exponentially in the path depth) with every number taken from `tree-artifacts/bounded-replay-plan.json` and the node paths
derived by walking the assembly DAG from the root (`[]`); the derived chunk paths are checked
against the plan's chunk paths.  No `assert`: every admission check raises.
"""
from __future__ import annotations
import argparse, json, re, sys
from pathlib import Path

REPO = Path(__file__).resolve().parents[4]
PLAN = REPO / "certificates/sextuple/a1275/tree-artifacts/bounded-replay-plan.json"
PARTS = REPO / "Zeta23/ThmD/Sextuple/A1275/Assembly"
NODE_RE = re.compile(
    r"theorem improvedNode(\d{4})(?: :\n    replayAffineTree [^\n]*\n      some \(\d+, \d+\) :=| :=)\n"
    r"  replayAffineTree_split_step \(fuel := (\d+)\) \(t := (\d+)\) \(p := (\d+)\)\n"
    r"(?:    \(box := [^\n]*\)\n)?"
    r"    \(axis := ⟨(\d), by decide⟩\) \(tm := (\d+)\) \(pm := (\d+)\)\n"
    r"    \(t' := (\d+)\) \(p' := (\d+)\)\n"
    r"    \(by decide \+kernel\) (improved(?:Chunk|Node)\d{4}) (improved(?:Chunk|Node)\d{4})\n")


def require(cond: bool, msg: str) -> None:
    if not cond:
        raise SystemExit(f"fix_a1275_assembly_statements: {msg}")


def render_path(path: list[tuple[int, int]]) -> str:
    return "[" + ", ".join(f"({'true' if s else 'false'}, ⟨{a}, by decide⟩)" for s, a in path) + "]"


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--check-only", action="store_true")
    a = ap.parse_args()
    plan = json.loads(PLAN.read_text())
    chunks, nodes = plan["chunks"], plan["assembly"]
    require(len(chunks) == 8953 and len(nodes) == 8952, "plan sizes")
    require(plan["root"] == ["node", 8951], "plan root")
    # derive paths from the root downwards
    node_path: dict[int, list] = {8951: []}
    chunk_path: dict[int, list] = {}
    stack = [8951]
    while stack:
        i = stack.pop()
        n = nodes[i]
        p = node_path[i]
        for side, ref in ((0, n["left"]), (1, n["right"])):
            child = [(side, n["axis"])] + p
            kind, j = ref
            if kind == "node":
                require(j not in node_path, f"node {j} reached twice")
                node_path[j] = child
                stack.append(j)
            else:
                require(kind == "chunk" and j not in chunk_path, f"bad child {ref}")
                chunk_path[j] = child
    require(len(node_path) == 8952 and len(chunk_path) == 8953, "DAG does not cover the plan")
    # plan paths are listed root-first; `improvedPathBox` consumes them deepest-first, which is
    # the order used in the chunk sources and derived above.
    chunk_re = re.compile(r"improvedPathBox improvedRootBox \[(.*?)\]\)")
    for j, c in enumerate(chunks):
        require([list(x) for x in chunk_path[j]] == [list(x) for x in reversed(c["path"])],
                f"chunk {j} path mismatch against the plan")
        require(c["depth"] == len(c["path"]), f"chunk {j} depth")
        lean = (REPO / f"Zeta23/ThmD/Sextuple/A1275/Chunks/Chunk{j:04d}.lean").read_text()
        m = chunk_re.search(lean)
        require(m is not None and "[" + m[1] + "]" == render_path(chunk_path[j]),
                f"chunk {j} path mismatch against Chunk{j:04d}.lean")
    for i, n in enumerate(nodes):
        require(n["depth"] == len(node_path[i]), f"node {i} depth")
    # rewrite parts
    seen = set()
    changed = 0
    for part in sorted(PARTS.glob("Part*.lean")):
        src = part.read_text()
        def repl(m: re.Match) -> str:
            i = int(m[1]); fuel = int(m[2]); t0 = int(m[3]); p0 = int(m[4]); axis = int(m[5])
            tm = int(m[6]); pm = int(m[7]); t1 = int(m[8]); p1 = int(m[9]); left = m[10]; right = m[11]
            n = nodes[i]
            require(fuel == n["fuel_after_split"] and t0 == n["t0"] and p0 == n["p0"] and axis == n["axis"]
                    and t1 == n["t1"] and p1 == n["p1"], f"node {i}: numbers differ from plan")
            lk, lj = n["left"]; rk, rj = n["right"]
            require(left == f"improved{'Chunk' if lk == 'chunk' else 'Node'}{lj:04d}", f"node {i}: left child")
            require(right == f"improved{'Chunk' if rk == 'chunk' else 'Node'}{rj:04d}", f"node {i}: right child")
            lt1 = chunks[lj]["t1"] if lk == "chunk" else nodes[lj]["t1"]
            lp1 = chunks[lj]["p1"] if lk == "chunk" else nodes[lj]["p1"]
            require((tm, pm) == (lt1, lp1), f"node {i}: middle cursors")
            require(i not in seen, f"node {i} duplicated"); seen.add(i)
            box = f"improvedPathBox improvedRootBox {render_path(node_path[i])}"
            return (f"theorem improvedNode{i:04d} :\n"
                    f"    replayAffineTree improvedConcreteLeafCheck improvedTopologyStream improvedPayloadStream "
                    f"{fuel + 1} {t0} {p0} ({box}) =\n"
                    f"      some ({t1}, {p1}) :=\n"
                    f"  replayAffineTree_split_step (fuel := {fuel}) (t := {t0}) (p := {p0})\n"
                    f"    (axis := ⟨{axis}, by decide⟩) (tm := {tm}) (pm := {pm})\n"
                    f"    (t' := {t1}) (p' := {p1})\n"
                    f"    (by decide +kernel) {left} {right}\n")
        new, k = NODE_RE.subn(repl, src)
        require("theorem improvedNode" not in re.sub(r"theorem improvedNode\d{4} :\n", "", new), f"{part.name}: unrewritten node")
        if k and not a.check_only:
            part.write_text(new); changed += 1
    require(len(seen) == 8952, f"rewrote {len(seen)} nodes, expected 8952")
    print(f"nodes={len(seen)} parts_changed={changed} root_path=[] check_only={a.check_only}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
