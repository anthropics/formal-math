#!/usr/bin/env python3
"""Hostile admission matrix for the A1275 full source generator."""
from __future__ import annotations
import argparse
import copy
import hashlib
import json
import os
import shutil
import subprocess
import sys
from pathlib import Path

import generate_a1275_full_sources as gen


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def canonical(obj: object) -> bytes:
    return (json.dumps(obj, sort_keys=True, separators=(",", ":")) + "\n").encode()


def atomic(path: Path, obj: object) -> None:
    stage = path.with_name(path.name + ".new")
    stage.unlink(missing_ok=True)
    with stage.open("wb") as handle:
        handle.write(canonical(obj))
        handle.flush()
        os.fsync(handle.fileno())
    os.replace(stage, path)


def expect_reject(results: dict, label: str, plan: dict, mutate, marker: str) -> None:
    candidate = copy.deepcopy(plan)
    mutate(candidate)
    try:
        gen.validate_plan_semantics(candidate)
    except Exception as error:
        message = str(error)
        require(marker in message, f"{label}: wrong rejection: {message}")
        results[label] = {"status": "REJECTED", "marker": marker, "error": message}
        return
    raise RuntimeError(f"{label}: hostile plan admitted")


def expect_call_reject(results: dict, label: str, call, marker: str) -> None:
    try:
        call()
    except Exception as error:
        message = str(error)
        require(marker in message, f"{label}: wrong rejection: {message}")
        results[label] = {"status": "REJECTED", "marker": marker, "error": message}
        return
    raise RuntimeError(f"{label}: hostile call admitted")


def run(args: argparse.Namespace) -> int:
    report = args.report.resolve()
    local_root = Path(__file__).resolve().parent
    require(report.is_relative_to(local_root), "hostile report must be project-local")
    require((args.mode == "optimized") == (sys.flags.optimize > 0), "mode/optimization mismatch")
    report.unlink(missing_ok=True)
    report.with_name(report.name + ".new").unlink(missing_ok=True)
    plan, _ = gen.load_and_validate_inputs(args.plan.resolve(), args.raw_dir.resolve())
    results: dict[str, dict] = {}
    expect_reject(results, "path_axis_one_past", plan,
                  lambda p: p["chunks"][0]["path"][0].__setitem__(1, 5), "axis outside Fin 5")
    expect_reject(results, "path_axis_negative", plan,
                  lambda p: p["chunks"][0]["path"][0].__setitem__(1, -1), "expected natural")
    expect_reject(results, "assembly_axis_one_past", plan,
                  lambda p: p["assembly"][0].__setitem__("axis", 5), "axis outside Fin 5")
    expect_reject(results, "assembly_axis_negative", plan,
                  lambda p: p["assembly"][0].__setitem__("axis", -1), "expected natural")
    expect_reject(results, "chunk_duplicate", plan,
                  lambda p: p["chunks"].__setitem__(-1, copy.deepcopy(p["chunks"][0])), "payload cursor")
    expect_reject(results, "chunk_omission", plan,
                  lambda p: p["chunks"].pop(), "chunk omission/duplication/count")
    expect_reject(results, "assembly_omission", plan,
                  lambda p: p["assembly"].pop(), "assembly omission/duplication/count")
    expect_reject(results, "root_reference", plan,
                  lambda p: p.__setitem__("root", ["node", gen.NODE_COUNT - 2]), "plan root reference")
    expect_reject(results, "chunk_cursor", plan,
                  lambda p: p["chunks"][0].__setitem__("t1", p["chunks"][0]["t1"] + 1), "token bound")
    expect_reject(results, "assembly_cursor", plan,
                  lambda p: p["assembly"][0].__setitem__("t1", p["assembly"][0]["t1"] + 1), "subtree cardinality")
    expect_reject(results, "chunk_fuel", plan,
                  lambda p: p["chunks"][0].__setitem__("fuel", p["chunks"][0]["fuel"] - 1), "fuel/depth")
    expect_reject(results, "assembly_fuel", plan,
                  lambda p: p["assembly"][0].__setitem__("fuel_after_split", p["assembly"][0]["fuel_after_split"] - 1), "fuel/depth")
    expect_reject(results, "dag_forward_reference", plan,
                  lambda p: p["assembly"][0].__setitem__("left", ["node", 0]), "forward/out-of-range DAG reference")
    expect_reject(results, "dag_duplicate_children", plan,
                  lambda p: p["assembly"][0].__setitem__("right", copy.deepcopy(p["assembly"][0]["left"])), "duplicate DAG children")
    manifest, blobs = gen.read_raw(args.raw_dir.resolve(), True)
    short_blobs = dict(blobs)
    short_blobs["topology-u64le.bin"] = short_blobs["topology-u64le.bin"][:-1]
    expect_call_reject(results, "raw_topology_truncation", lambda: gen.validate_raw_blobs(manifest, short_blobs), "truncation/extension")
    expect_call_reject(results, "plan_json_truncation", lambda: json.loads(args.plan.read_bytes()[:-2]), "Expecting")
    duplicate_json = local_root / f"hostile-duplicate-key-{args.mode}.json"
    duplicate_json.write_text('{"schema":1,"schema":1}\n')
    try:
        expect_call_reject(results, "duplicate_json_key", lambda: gen.load_json_no_duplicates(duplicate_json), "duplicate JSON key")
    finally:
        duplicate_json.unlink(missing_ok=True)
    _, module_sources = gen.verify_foundations(args.foundation_root.resolve(), args.freeze_manifest.resolve(), args.repo_root.resolve())
    valid_hashes = {gen.TREEWORDS: sha(module_sources[gen.TREEWORDS])}
    invalid_hashes = dict(valid_hashes)
    invalid_hashes[gen.TREEWORDS] = "0" * 64
    expect_call_reject(results, "import_source_hash", lambda: gen.validate_import_record([gen.TREEWORDS], invalid_hashes, module_sources), "source import hash mismatch")
    stale_dir = local_root / f"hostile-stale-pass-{args.mode}"
    require(not stale_dir.exists(), "stale case directory already exists")
    stale_dir.mkdir()
    hostile_plan = stale_dir / "bad-plan.json"
    bad = copy.deepcopy(plan)
    bad["root"] = ["node", gen.NODE_COUNT - 2]
    hostile_plan.write_bytes(canonical(bad))
    stale_report = stale_dir / "generation-report.json"
    stale_report.write_bytes(canonical({"status": "PASS", "stale": True}))
    stale_output = stale_dir / "output"
    command = [sys.executable]
    if sys.flags.optimize > 0:
        command.append("-O")
    command.extend([
        str(Path(gen.__file__).resolve()), "--plan", str(hostile_plan), "--raw-dir", str(args.raw_dir.resolve()),
        "--foundation-root", str(args.foundation_root.resolve()), "--freeze-manifest", str(args.freeze_manifest.resolve()),
        "--repo-root", str(args.repo_root.resolve()), "--output-root", str(stale_output),
        "--report", str(stale_report), "--mode", args.mode,
    ])
    proc = subprocess.run(command, text=True, capture_output=True)
    require(proc.returncode != 0, "stale PASS hostile run returned zero")
    require(not stale_report.exists(), "stale PASS report survived failure")
    require(not stale_output.exists() and not stale_output.with_name(stale_output.name + ".new").exists(), "hostile Lean output survived failure")
    results["stale_pass_invalidation"] = {"status": "REJECTED", "exit_code": proc.returncode, "report_absent": True, "lean_output_absent": True, "stderr_sha256": hashlib.sha256(proc.stderr.encode()).hexdigest()}
    require(len(results) == 19 and all(item["status"] == "REJECTED" for item in results.values()), "hostile case count/status")
    output = {
        "schema": 1, "status": "PASS", "mode": args.mode, "optimize": sys.flags.optimize,
        "driver_sha256": sha(Path(__file__)), "generator_sha256": sha(Path(gen.__file__)),
        "plan_sha256": sha(args.plan), "case_count": len(results), "cases": results,
        "no_lean_compilation": True, "no_full_chunks_built": True,
    }
    atomic(report, output)
    print(json.dumps(output, sort_keys=True, indent=2))
    return 0


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--plan", required=True, type=Path)
    parser.add_argument("--raw-dir", required=True, type=Path)
    parser.add_argument("--foundation-root", required=True, type=Path)
    parser.add_argument("--freeze-manifest", required=True, type=Path)
    parser.add_argument("--repo-root", required=True, type=Path)
    parser.add_argument("--report", required=True, type=Path)
    parser.add_argument("--mode", required=True, choices=("normal", "optimized"))
    return parser.parse_args()


if __name__ == "__main__":
    try:
        sys.exit(run(parse_args()))
    except Exception as error:
        print(f"FAIL: {error}", file=sys.stderr)
        sys.exit(1)
