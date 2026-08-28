#!/usr/bin/env python3
"""Batched, memory-shaped Lake build of the A1275 chunk modules.

Every chunk module `Zeta23.ThmD.Sextuple.A1275.Chunks.ChunkNNNN` is one `decide +kernel`
subtree replay.  Lake 5 has no `-j`; the number of concurrent `lean` builders is capped by
`LEAN_NUM_THREADS`.  Kernel memory per chunk depends on the chunk size (topology tokens),
so this driver groups chunks into batches of similar predicted footprint and picks the
builder count per batch from a memory budget.  Lake itself decides what is up to date, so
the driver is restart-safe: re-running it only builds what is missing.

Usage (from the repository root):
  python3 certificates/sextuple/a1275/tools/build_a1275_chunks.py --budget-gib 100 --max-workers 8
"""
from __future__ import annotations
import argparse, json, os, re, subprocess, sys, time
from pathlib import Path

REPO = Path(__file__).resolve().parents[4]
CHUNK_DIR = REPO / "Zeta23/ThmD/Sextuple/A1275/Chunks"
OLEAN_DIR = REPO / ".lake/build/lib/lean/Zeta23/ThmD/Sextuple/A1275/Chunks"
LAKE = Path.home() / ".elan/bin/lake"
HEADER = re.compile(r"topology cursor (\d+), payload cursor (\d+), depth (\d+), (\d+) tokens")


def chunk_table() -> list[dict]:
    rows = []
    for path in sorted(CHUNK_DIR.glob("Chunk*.lean")):
        m = HEADER.search(path.read_text())
        if not m:
            raise SystemExit(f"no header in {path}")
        idx = int(path.stem[5:])
        rows.append({"idx": idx, "tcur": int(m[1]), "pcur": int(m[2]),
                     "depth": int(m[3]), "tokens": int(m[4])})
    return rows


def predicted_gib(row: dict, base: float, per_token: float, per_token_cursor: float) -> float:
    return base + per_token * row["tokens"] + per_token_cursor * row["tokens"] * row["tcur"]


def built(idx: int) -> bool:
    return (OLEAN_DIR / f"Chunk{idx:04d}.olean").exists() and \
        (OLEAN_DIR / f"Chunk{idx:04d}.trace").exists()


def free_gib() -> float:
    out = subprocess.run(["/usr/bin/vm_stat"], capture_output=True, text=True).stdout
    vals = {}
    for line in out.splitlines():
        m = re.match(r"Pages (free|inactive|speculative):\s+(\d+)", line)
        if m:
            vals[m[1]] = int(m[2])
    return sum(vals.values()) * 16384 / 2**30


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--budget-gib", type=float, default=100.0)
    ap.add_argument("--max-workers", type=int, default=8)
    ap.add_argument("--min-workers", type=int, default=2)
    ap.add_argument("--batch-size", type=int, default=64)
    ap.add_argument("--mem-base", type=float, default=11.0, help="GiB per chunk, fixed part")
    ap.add_argument("--mem-per-token", type=float, default=0.0)
    ap.add_argument("--mem-per-token-cursor", type=float, default=0.0)
    ap.add_argument("--order", choices=("index", "heavy-first"), default="index")
    ap.add_argument("--log", type=Path, default=REPO / "certificates/sextuple/logs/a1275-chunks-driver.log")
    ap.add_argument("--state", type=Path, default=REPO / "certificates/sextuple/logs/a1275-chunks-state.json")
    ap.add_argument("--dry-run", action="store_true")
    a = ap.parse_args()

    rows = chunk_table()
    for r in rows:
        r["gib"] = predicted_gib(r, a.mem_base, a.mem_per_token, a.mem_per_token_cursor)
    todo = [r for r in rows if not built(r["idx"])]
    if a.order == "heavy-first":
        todo.sort(key=lambda r: -r["gib"])
    log = open(a.log, "a")
    def say(msg: str) -> None:
        line = f"{time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime())} {msg}"
        print(line, flush=True); log.write(line + "\n"); log.flush()
    say(f"chunks total={len(rows)} todo={len(todo)} budget={a.budget_gib}GiB max_workers={a.max_workers}")
    state = {"started": time.time(), "batches": []}
    i = 0
    while i < len(todo):
        batch = todo[i:i + a.batch_size]
        i += a.batch_size
        peak = max(r["gib"] for r in batch)
        workers = max(a.min_workers, min(a.max_workers, int(a.budget_gib // peak)))
        targets = [f"+Zeta23.ThmD.Sextuple.A1275.Chunks.Chunk{r['idx']:04d}" for r in batch]
        say(f"batch {len(state['batches'])}: {len(batch)} chunks idx {batch[0]['idx']}..{batch[-1]['idx']} "
            f"peak_pred={peak:.1f}GiB workers={workers} free={free_gib():.1f}GiB")
        if a.dry_run:
            continue
        env = dict(os.environ, LEAN_NUM_THREADS=str(workers), LC_ALL="C", TZ="UTC")
        t0 = time.time()
        proc = subprocess.run([str(LAKE), "build", *targets], cwd=REPO, env=env,
                              capture_output=True, text=True)
        dt = time.time() - t0
        built_lines = [l for l in proc.stdout.splitlines() if "Built Zeta23.ThmD.Sextuple.A1275.Chunks" in l]
        secs = [float(m[1]) for l in built_lines for m in [re.search(r"\((\d+\.?\d*)s\)", l)] if m]
        rec = {"first": batch[0]["idx"], "last": batch[-1]["idx"], "n": len(batch), "workers": workers,
               "exit": proc.returncode, "wall": round(dt, 1), "built": len(built_lines),
               "sum_secs": round(sum(secs), 1), "max_secs": round(max(secs), 1) if secs else None}
        state["batches"].append(rec)
        a.state.write_text(json.dumps(state, indent=1))
        say(f"  -> exit={proc.returncode} wall={dt:.0f}s built={len(built_lines)} "
            f"sum={sum(secs):.0f}s max={max(secs) if secs else 0:.0f}s")
        if proc.returncode != 0:
            fail = a.log.with_suffix(f".batch{len(state['batches'])-1}.fail.log")
            fail.write_text(proc.stdout + "\n--- stderr ---\n" + proc.stderr)
            say(f"  FAILED; output saved to {fail}")
            return 1
    missing = [r["idx"] for r in rows if not built(r["idx"])]
    say(f"done; missing={len(missing)}")
    return 0 if not missing else 2


if __name__ == "__main__":
    sys.exit(main())
