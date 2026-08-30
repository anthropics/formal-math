#!/usr/bin/env python3
"""Compare normal/optimized source runs and atomically publish the verified A1275 modules."""
from __future__ import annotations
import argparse
import hashlib
import json
import os
import shutil
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


def object_sha(obj: object) -> str:
    return hashlib.sha256(canonical(obj)).hexdigest()


def atomic(path: Path, obj: object) -> None:
    stage = path.with_name(path.name + ".new")
    stage.unlink(missing_ok=True)
    with stage.open("wb") as handle:
        handle.write(canonical(obj))
        handle.flush()
        os.fsync(handle.fileno())
    os.replace(stage, path)


def read_pass(path: Path, label: str) -> dict:
    require(path.is_file(), f"{label} report missing")
    obj = gen.load_json_no_duplicates(path)
    require(type(obj) is dict and obj.get("status") == "PASS", f"{label} report not PASS")
    return obj


def inventory(root: Path, expected: dict[str, dict]) -> dict[str, dict]:
    require(root.is_dir() and not root.is_symlink(), "source run root missing/symlink")
    paths = sorted(path for path in root.rglob("*") if path.is_file())
    require(all(not path.is_symlink() and path.suffix == ".lean" for path in paths), "non-Lean or symlink generated output")
    actual = {str(path.relative_to(root)): {"sha256": sha(path), "bytes": path.stat().st_size} for path in paths}
    expected_core = {rel: {"sha256": record["sha256"], "bytes": record["bytes"]} for rel, record in expected.items()}
    require(actual == expected_core, "generated source inventory/report mismatch")
    return actual


def run(args: argparse.Namespace) -> int:
    local_root = Path(__file__).resolve().parent
    publish_report = args.publish_report.resolve()
    require(publish_report.is_relative_to(local_root), "publish report must be project-local")
    publish_report.unlink(missing_ok=True)
    publish_report.with_name(publish_report.name + ".new").unlink(missing_ok=True)
    normal_root = args.normal_root.resolve()
    optimized_root = args.optimized_root.resolve()
    require(normal_root.is_relative_to(local_root) and optimized_root.is_relative_to(local_root), "run roots must be project-local")
    normal_report_path = args.normal_report.resolve()
    optimized_report_path = args.optimized_report.resolve()
    normal = read_pass(normal_report_path, "normal")
    optimized = read_pass(optimized_report_path, "optimized")
    require(normal.get("mode") == "normal" and normal.get("python", {}).get("optimize") == 0, "normal mode binding")
    require(optimized.get("mode") == "optimized" and optimized.get("python", {}).get("optimize", 0) > 0, "optimized mode binding")
    generator_hash = sha(Path(gen.__file__))
    require(normal.get("generator_sha256") == generator_hash == optimized.get("generator_sha256"), "generator/report hash binding")
    require(normal["inputs"] == optimized["inputs"] and normal["foundations"] == optimized["foundations"] and normal["plan"] == optimized["plan"], "normal/optimized admission metadata mismatch")
    require(normal["sources"] == optimized["sources"], "normal/optimized source manifest mismatch")
    expected = normal["sources"]["files"]
    require(type(expected) is dict and len(expected) == gen.CHUNK_COUNT + gen.PART_COUNT + 1, "source report count")
    normal_inventory = inventory(normal_root, expected)
    optimized_inventory = inventory(optimized_root, expected)
    require(normal_inventory == optimized_inventory, "normal/optimized byte identity")
    hostile_normal_path = args.hostile_normal.resolve()
    hostile_optimized_path = args.hostile_optimized.resolve()
    hostile_normal = read_pass(hostile_normal_path, "hostile normal")
    hostile_optimized = read_pass(hostile_optimized_path, "hostile optimized")
    require(hostile_normal.get("mode") == "normal" and hostile_optimized.get("mode") == "optimized", "hostile mode binding")
    require(hostile_normal.get("generator_sha256") == generator_hash == hostile_optimized.get("generator_sha256"), "hostile generator binding")
    require(hostile_normal.get("driver_sha256") == sha(args.hostile_driver.resolve()) == hostile_optimized.get("driver_sha256"), "hostile driver binding")
    require(hostile_normal.get("case_count") == 19 == hostile_optimized.get("case_count") and hostile_normal["cases"] == hostile_optimized["cases"], "hostile normal/optimized mismatch")
    foundation_before, _ = gen.verify_foundations(args.foundation_root.resolve(), args.freeze_manifest.resolve(), args.repo_root.resolve())
    base = args.foundation_root.resolve() / "Zeta23/ThmD/Sextuple/A1275"
    destinations = {
        "Chunks": base / "Chunks",
        "Assembly": base / "Assembly",
        "TreeAssembly.lean": base / "TreeAssembly.lean",
    }
    require(all(not path.exists() for path in destinations.values()), "canonical full source target already exists")
    stages = {name: path.with_name(path.name + ".new") for name, path in destinations.items()}
    require(all(not path.exists() for path in stages.values()), "canonical publication stage already exists")
    published: list[str] = []
    try:
        shutil.copytree(normal_root / "Zeta23/ThmD/Sextuple/A1275/Chunks", stages["Chunks"])
        shutil.copytree(normal_root / "Zeta23/ThmD/Sextuple/A1275/Assembly", stages["Assembly"])
        shutil.copy2(normal_root / "Zeta23/ThmD/Sextuple/A1275/TreeAssembly.lean", stages["TreeAssembly.lean"])
        staged_inventory = {}
        for rel in expected:
            source = normal_root / rel
            suffix = Path(rel).relative_to("Zeta23/ThmD/Sextuple/A1275")
            if suffix.parts[0] == "Chunks":
                staged = stages["Chunks"] / Path(*suffix.parts[1:])
            elif suffix.parts[0] == "Assembly":
                staged = stages["Assembly"] / Path(*suffix.parts[1:])
            else:
                require(str(suffix) == "TreeAssembly.lean", "unexpected generated target path")
                staged = stages["TreeAssembly.lean"]
            require(staged.is_file() and not staged.is_symlink() and staged.read_bytes() == source.read_bytes(), f"staged byte mismatch: {rel}")
            staged_inventory[rel] = {"sha256": sha(staged), "bytes": staged.stat().st_size}
        require(staged_inventory == normal_inventory, "staged inventory mismatch")
        for name in ("Chunks", "Assembly", "TreeAssembly.lean"):
            os.replace(stages[name], destinations[name])
            published.append(name)
        canonical_inventory = {}
        for rel in expected:
            path = args.foundation_root.resolve() / rel
            require(path.is_file() and not path.is_symlink(), f"published source missing/symlink: {rel}")
            canonical_inventory[rel] = {"sha256": sha(path), "bytes": path.stat().st_size}
        require(canonical_inventory == normal_inventory, "published canonical inventory mismatch")
        foundation_after, _ = gen.verify_foundations(args.foundation_root.resolve(), args.freeze_manifest.resolve(), args.repo_root.resolve())
        require(foundation_after == foundation_before, "44 foundation sources changed during publication")
        report = {
            "schema": 1, "status": "PASS", "publisher_sha256": sha(Path(__file__)),
            "generator_sha256": generator_hash, "hostile_driver_sha256": sha(args.hostile_driver.resolve()),
            "normal_report_sha256": sha(normal_report_path), "optimized_report_sha256": sha(optimized_report_path),
            "hostile_normal_sha256": sha(hostile_normal_path), "hostile_optimized_sha256": sha(hostile_optimized_path),
            "source_count": len(canonical_inventory), "source_bytes": sum(item["bytes"] for item in canonical_inventory.values()),
            "source_inventory_sha256": object_sha(canonical_inventory), "normal_optimized_byte_identical": True,
            "canonical_inventory": canonical_inventory,
            "foundations": {"count": len(foundation_before), "inventory_sha256": object_sha(foundation_before), "unchanged": True},
            "plan": normal["plan"], "explicit_fin": normal["sources"]["explicit_fin"],
            "import_edge_count": normal["sources"]["import_edge_count"], "import_edges_sha256": normal["sources"]["import_edges_sha256"],
            "no_lean_compilation": True, "no_full_chunks_built": True,
        }
        atomic(publish_report, report)
        print(json.dumps(report, sort_keys=True, indent=2))
        return 0
    except Exception:
        for path in stages.values():
            if path.is_dir():
                shutil.rmtree(path)
            else:
                path.unlink(missing_ok=True)
        publish_report.unlink(missing_ok=True)
        raise


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--normal-root", required=True, type=Path)
    parser.add_argument("--optimized-root", required=True, type=Path)
    parser.add_argument("--normal-report", required=True, type=Path)
    parser.add_argument("--optimized-report", required=True, type=Path)
    parser.add_argument("--hostile-normal", required=True, type=Path)
    parser.add_argument("--hostile-optimized", required=True, type=Path)
    parser.add_argument("--hostile-driver", required=True, type=Path)
    parser.add_argument("--foundation-root", required=True, type=Path)
    parser.add_argument("--freeze-manifest", required=True, type=Path)
    parser.add_argument("--repo-root", required=True, type=Path)
    parser.add_argument("--publish-report", required=True, type=Path)
    return parser.parse_args()


if __name__ == "__main__":
    try:
        sys.exit(run(parse_args()))
    except Exception as error:
        print(f"FAIL: {error}", file=sys.stderr)
        sys.exit(1)
