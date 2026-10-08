#!/usr/bin/env python3
# Copyright (c) 2026 Anthropic, PBC. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# SPDX-License-Identifier: Apache-2.0
"""Write the files that are derived from the files Challenge/T.lean.

    scripts/generate.py [--check]

For each topic T it writes comparator-t.json (t is T in lower case), which tells Comparator to compare the theorems of
Challenge/T.lean with the theorems of the same names that Solution/T.lean imports.  It also writes
scripts/PrintAxioms.lean, which prints the axioms behind each of these theorems.
--check writes nothing and fails if a file on disk differs from what would be written.

A statement that is missing from a list would silently not be compared.  To guard against such accidents the script
accepts only Challenge files of a simple form, described at the function theorem_names.  It also fails if a trusted file
imports more than this: EndStatement.lean nothing, PaperStatements.lean Mathlib and EndStatement, Challenge/T.lean the
trusted file T; see the function trusted_code, which says what form of text it accepts.

The script reads Lean text without Lean's parser.  So it guards against accidents, and does not prove that a file has the
form described.  It is not a defence against a trusted file written to deceive: these files are meant to be read.  It does
not look at lakefile.toml, lake-manifest.json and lean-toolchain, which have to be trusted as well.
"""
import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
AXIOMS = ["propext", "Quot.sound", "Classical.choice"]
HEADER = "".join(Path(__file__).read_text(encoding="utf-8").splitlines(keepends=True)[1:4]).replace("# ", "")
IMPORT = re.compile(r"(?:public )?import (\w+(?:\.\w+)*)")
PLAIN_LINE = re.compile(rf"module|{IMPORT.pattern}|public section|open( [A-Z][\w.]*)+( in)?|(namespace|section|end)( \w+)?")
THEOREM = re.compile(r"theorem ([\w']+)[\s:({\[⦃].*:=\s*(by\s+)?sorry", re.S)
DECLARES = re.compile(r"(?<![\w.'])(theorem|lemma|def|abbrev|instance|structure|inductive|class|axiom|opaque|example|sorry)(?![\w'])")
COMMAND = re.compile(r"(?<![\w.'])(variable|include|omit|universe|attribute|set_option|open|export|local|scoped|namespace|section|end|mutual|"
                     r"private|protected|noncomputable|unsafe|partial|irreducible_def|alias|deriving|infix[lr]?|prefix|postfix|"
                     r"macro\w*|syntax\w*|elab\w*|notation\w*|initialize\w*|simproc\w*|run_\w+|declare_\w+|register_\w+|add_\w+|"
                     r"unif_hint|proof_wanted|binder_predicate|recall|seal|unseal|where)(?![\w'])|@\[|#[a-z_]")


def stop(message):
    sys.exit("error: " + message)


def without_comments(text, starts=None):
    """The text with every character of a comment, other than the end of a line, replaced by a blank.  Comments may be nested.
    If starts is a list, the positions at which outermost comments begin are appended to it."""
    out, i, depth = [], 0, 0
    while i < len(text):
        if starts is not None and not depth and text.startswith(("/-", "--"), i):
            starts.append(i)
        if text.startswith("/-", i) or (depth and text.startswith("-/", i)):
            n = 2 if depth else 3
            depth += 1 if text[i] == "/" else -1
            out.append("".join(c if c == "\n" else " " for c in text[i:i + n]))
            i += n
        elif depth or text.startswith("--", i):
            end = i + 1 if depth else (text.find("\n", i) + 1 or len(text) + 1) - 1
            out.append("".join(c if c == "\n" else " " for c in text[i:end]))
            i = end
        else:
            out.append(text[i])
            i += 1
    return "".join(out)


def trusted_code(path, may_import, mathlib=True):
    """The text of a trusted file without its comments.  Stops with an error unless all of this holds:

    * Neither the file nor a folder that it lies in is a symbolic link.
    * The only white space is the blank and the line feed.  There is no byte order mark.
    * Each "/-", "/--" or "/-!" in the file, also inside a comment, is followed by one blank or the end of the line, and directly
      after that by a letter, a digit or one of # * ` " ( [
    * A comment that is not inside another begins at the start of a line or after a blank.
    * Outside comments there is no string literal and no «quoted» name.
    * Outside comments, a line that contains the letters "import" is "import M" or "public import M" and nothing else, where M is
      one of the modules may_import or, if mathlib is true, Mathlib or one of its modules."""
    where = path.relative_to(ROOT)
    if any(p.is_symlink() for p in (path, *path.parents) if p != ROOT and ROOT in p.parents):
        stop(f"{where}: a trusted file must not be, or lie behind, a symbolic link")
    try:
        text = path.read_bytes().decode("utf-8")
    except (OSError, UnicodeDecodeError) as e:
        stop(f"{where}: this trusted file cannot be read as UTF-8 text ({type(e).__name__})")
    line = lambda i: f"{where}:{text.count(chr(10), 0, i) + 1}"
    if m := re.search(r"[^\S \n]|\ufeff", text):
        stop(f"{line(m.start())}: in a trusted file the only white space is the blank and the line feed; here is the character "
             f"U+{ord(m[0]):04X}" + (" (check the files out with line feeds: git config core.autocrlf false)" if m[0] == "\r" else ""))
    if m := re.search(r"/-(?![-!]?[ \n](?:[^\W_]|[#*`\"(\[]))", text):
        stop(f"{line(m.start())}: in a trusted file, '/-', '/--' or '/-!' must be followed by one blank or the end of the line, and "
             "directly after that by a letter, a digit or one of # * ` \" ( [")
    starts = []
    code = without_comments(text, starts)
    if glued := [i for i in starts if i and text[i - 1] not in " \n"]:
        stop(f"{line(glued[0])}: in a trusted file a comment must begin at the start of a line or after a blank")
    if m := re.search('["«»]', code):
        stop(f"{line(m.start())}: string literals and «quoted» names are not supported in a trusted file")
    for m in re.finditer(r"^.*import.*$", code, re.M):
        i = IMPORT.fullmatch(m[0].rstrip(" "))
        if not i:
            stop(f"{line(m.start())}: in a trusted file, a line with the letters 'import' must be 'import M' or 'public import M'")
        if not may_import and not mathlib:
            stop(f"{line(m.start())}: this file must import nothing, and it imports {i[1]}")
        if i[1] not in may_import and not (mathlib and i[1].split(".")[0] == "Mathlib"):
            stop(f"{line(m.start())}: a trusted file imports {i[1]}, which is neither Mathlib nor a trusted file that it may import")
    return code


def theorem_names(path, may_import):
    """The full names of the theorems of a Challenge file, in order.

    The file is cut into blocks: a line that begins in column 0, with the indented lines below it.  Comments apart, a block must
    be either "theorem NAME ... := by sorry", with no second declaration, no second ":=" and none of the words and signs of the
    list COMMAND inside it, or one line of these kinds: module, an import, public section, open, namespace, section, end.
    NAME consists of letters, digits, _ and '.  The first line of code begins in column 0.  The conditions of trusted_code hold."""
    where, code = path.relative_to(ROOT), trusted_code(path, may_import)
    if next((line for line in code.splitlines() if line.strip()), "")[:1].isspace():
        stop(f"{where}: the first line of code does not begin in column 0")
    scopes, names = [], []          # scopes: the namespaces and sections that are open, as pairs (kind, name)
    for m in re.finditer(r"^\S.*(\n([ \t].*)?$)*", code, re.M):
        block, here = m[0].strip(), f"{where}:{code.count(chr(10), 0, m.start()) + 1}"
        kind, name = (block.split() + [""])[:2]
        if t := THEOREM.fullmatch(block):
            if len(DECLARES.findall(block)) != 2:
                stop(f"{here}: between its first word and the sorry at its end, this theorem contains another declaration or sorry")
            if block.count(":=") != 1:
                stop(f"{here}: this theorem contains ':=' more than once; a statement has one, before the sorry at its end")
            if c := COMMAND.search(block):
                stop(f"{here}: this theorem contains '{c[0]}', which the list COMMAND matches; if it is a name, write it with its "
                     "namespace or choose another")
            names.append(".".join([n for k, n in scopes if k == "namespace"] + [t[1]]))
        elif not PLAIN_LINE.fullmatch(block) or (kind == "namespace" and not name):
            stop(f"{here}: the block that begins here (it runs up to the next line that begins in column 0) is neither 'theorem NAME ... := "
                 "by sorry' nor one line of these kinds: module, import, public section, open, "
                 "namespace, section, end")
        elif kind in ("namespace", "section") or block == "public section":
            scopes.append((kind, name) if kind != "public" else (block, None))          # no end closes "public section"
        elif kind == "end" and (not scopes or scopes.pop()[1] != name):
            stop(f"{here}: '{block}' does not close the namespace or section that was opened last")
    if [k for k, _ in scopes] not in ([], ["public section"]):
        stop(f"{where}: at the end of the file all of these are open: {', '.join(f'{k} {n or str()}'.strip() for k, n in scopes)}")
    if not names:
        stop(f"{where}: there is no theorem in this file")
    return names


def main():
    check = sys.argv[1:] == ["--check"]
    if sys.argv[1:] and not check:
        sys.exit(__doc__)
    found = sorted((ROOT / "Challenge").glob("*"))
    problems = [f"Challenge/{p.name}: Challenge/ may hold only files T.lean, where T consists of letters, digits and _"
                for p in found if p.suffix != ".lean" or p.is_dir() or not re.fullmatch(r"\w+", p.stem)]
    problems += [f"{n}: the folder that holds lakefile.toml must not hold a file or folder of this name"
                 for n in ("Mathlib", "Mathlib.lean", "EndStatement", "PaperStatements", "Challenge.lean") if (ROOT / n).exists()]
    may_import = {"EndStatement", "PaperStatements"}
    trusted_code(ROOT / "EndStatement.lean", set(), mathlib=False)          # it imports nothing
    trusted_code(ROOT / "PaperStatements.lean", {"EndStatement"})
    for p in found:          # Challenge/T.lean imports nothing but T
        if p.suffix == ".lean" and p.is_file():
            trusted_code(p, {p.stem}, mathlib=False)
    topics = {p.stem: theorem_names(p, may_import) for p in found if p.suffix == ".lean" and p.is_file()}
    if not topics:
        stop("there is no file Challenge/T.lean")
    files = {f"comparator-{t.lower()}.json": json.dumps({
        "challenge_module": f"Challenge.{t}", "solution_module": f"Solution.{t}", "theorem_names": names,
        "definition_names": [], "permitted_axioms": AXIOMS, "enable_nanoda": True}, indent=2) + "\n" for t, names in topics.items()}
    if len(files) != len(topics):
        stop("the names of two topics differ only in upper and lower case")
    files["scripts/PrintAxioms.lean"] = (
        f"/-\n{HEADER}-/\n/-\nWritten by scripts/generate.py.  Prints the axioms behind every theorem that Comparator compares:\n"
        "    lake build Solution && lake env lean scripts/PrintAxioms.lean\n"
        "No line of the output names an axiom other than propext, Classical.choice and Quot.sound.\n"
        "This is a convenience for a reader, and not a check of files that one does not trust, because the command runs\n"
        "inside Lean with the library imported.  Comparator does not depend on that.\n-/\n"
        + "".join(f"import Solution.{t}\n" for t in topics)
        + "".join(f"\n-- {t}\n" + "".join(f"#print axioms {n}\n" for n in names) for t, names in topics.items()))
    problems += [f"Solution/{t}.lean is missing" for t in topics if not (ROOT / "Solution" / f"{t}.lean").exists()]
    problems += [f"{p.name} belongs to no file of Challenge/; remove it" for p in ROOT.glob("comparator*.json") if p.name not in files]
    everything = [n for names in topics.values() for n in names]
    problems += [f"{n} is stated twice" for n in sorted(set(everything)) if everything.count(n) > 1]
    for rel, text in files.items():
        if not check:
            (ROOT / rel).write_text(text, encoding="utf-8")
        elif not (ROOT / rel).exists() or (ROOT / rel).read_text(encoding="utf-8") != text:
            problems.append(f"{rel} is not what scripts/generate.py would write; run scripts/generate.py")
    for p in problems:
        print("error: " + p, file=sys.stderr)
    print(f"{len(topics)} topics, {len(everything)} statements")
    return 1 if problems else 0


if __name__ == "__main__":
    sys.exit(main())
