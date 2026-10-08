#!/usr/bin/env python3
# Copyright (c) 2026 Anthropic, PBC. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# SPDX-License-Identifier: Apache-2.0
"""The order of the folders of the library.

    python3 scripts/layers.py [--check]

A file in a folder of ThreeSumApsp/ imports Mathlib, EndStatement.lean, PaperStatements.lean, files of its own folder, and
files of the folders that the table MAY_IMPORT lists for its folder.  Sec1/ to Sec5/ count as one folder, Sec.  A file
ThreeSumApsp/X.lean stands beside a folder X/ and imports all files of that folder and nothing else, and ThreeSumApsp.lean
reaches every file.  The import lines are read at the head of a file: after the license and the word module.

The script prints the table, with the number of import lines from each folder to each folder below it, and then every
breach of these rules.  --check prints the breaches only.  The script fails if there is a breach.
It is a help for keeping the layout; it checks nothing about the mathematics.
"""
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
MAY_IMPORT = {                                   # from the bottom up
    "Util": "",
    "Sec": "Util",
    "ConditionalTimes": "Util Sec",
    "TimeClaims": "Util Sec",
    "Spec": "Util Sec",
    "Machine": "Util",
    "Lang": "Util Machine",
    "Programs": "Util Sec TimeClaims Spec Machine Lang",
    "RunningTimes": "Util Sec TimeClaims Spec Machine Lang Programs",
    "Statements": "Util Sec ConditionalTimes TimeClaims Spec Machine Lang Programs RunningTimes",
    "ModelChecks": "Util Sec Machine Statements",
}
HEAD = re.compile(r"/-.*?-/\nmodule\n((?:\n|(?:\w+ )*import (?:all )?[\w.]+\n)*)", re.S)
files = sorted(ROOT.glob("ThreeSumApsp/**/*.lean")) + [ROOT / "ThreeSumApsp.lean"]
texts = {".".join(f.relative_to(ROOT).with_suffix("").parts): f.read_text(encoding="utf-8") for f in files}
heads = {m: HEAD.match(text) for m, text in texts.items()}
imports = {m: [line.split()[-1] for line in h.group(1).split("\n") if line] if h else [] for m, h in heads.items()}
folder = lambda m: re.sub(r"^Sec\d$", "Sec", m.split(".")[1])
allowed = lambda m: [folder(m)] + MAY_IMPORT.get(folder(m), "").split()
count, breaches = {}, [f"{m} does not begin with the license and the word module" for m, h in heads.items() if not h]
breaches += [f"{m} has an import line after its head" for m, h in heads.items()
             if h and re.search(r"^(?:\w+ )*import (?:all )?[A-Z]", texts[m][h.end():], re.M)]
for m, used in imports.items():
    if m.count(".") == 1 and (not used or sorted(used) != sorted(n for n in imports if n.startswith(m + "."))):
        breaches.append(f"{m} does not import exactly the files of its folder")
    if m.count(".") > 1 and folder(m) not in MAY_IMPORT:
        breaches.append(f"{m} lies in a folder that the table does not know")
    for n in used:
        if m.count(".") > 1 and n.split(".")[0] in ("Mathlib", "EndStatement", "PaperStatements"):
            continue
        if n not in imports or n == "ThreeSumApsp" or m.count(".") > 1 and folder(n) not in allowed(m):
            breaches.append(f"{m} imports {n}")
        elif m.count(".") > 1:
            count[folder(m), folder(n)] = count.get((folder(m), folder(n)), 0) + 1
reached, todo = set(), ["ThreeSumApsp"]
while todo:
    m = todo.pop()
    todo += [] if m in reached else imports.get(m, [])
    reached.add(m)
breaches += [f"ThreeSumApsp.lean does not reach {m}" for m in sorted(set(imports) - reached)]
if "--check" not in sys.argv[1:]:
    for a, below in MAY_IMPORT.items():
        print(f"{a:17}" + ", ".join(f"{b} ({count.get((a, b), 0)})" for b in below.split()))
sys.exit("\n".join(breaches) or 0)
