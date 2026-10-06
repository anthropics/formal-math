# scripts/

Five files besides this one. The Python scripts use the standard library only. Run everything from the folder that holds `lakefile.toml`.

| file | what it does |
|---|---|
| `generate.py` | Reads the names of the theorems in the files of `Challenge/` and writes, for each of these files, the configuration `comparator-*.json` that tells Comparator which theorems to compare, and `PrintAxioms.lean`. Run it after every change to a file of `Challenge/`. |
| `PrintAxioms.lean` | Written by `generate.py`. Prints the axioms behind every compared theorem. It is not a check of files that one does not trust: the command runs inside Lean with the library imported. |
| `index.py` | Writes `docs/INDEX.md` (which statements render which item of the paper, and in which files they are stated and proved) from `docs/paper-items.json`, `docs/FILES.md` (the trusted files and every file of the library, each with the title of its header), `docs/PROGRAMS.md` (the programs item by item, from `docs/programs.json`), and the list of all NOTE paragraphs at the end of `docs/REMARKS.md`. Run it after a file has moved, a statement has changed its name, or a NOTE has changed. |
| `layers.py` | Tests the order of the folders of the library: a file imports only the folders that the script's table `MAY_IMPORT` allows for its folder; a file `ThreeSumApsp/X.lean` beside a folder `X/` imports all files of that folder and nothing else; `ThreeSumApsp.lean` reaches every file. Without `--check` it also prints the table, with the number of import lines from folder to folder. It is a help for keeping the layout; it checks nothing about the mathematics. |
| `check.sh` | Runs `generate.py --check`, `index.py --check --names` and `layers.py --check`, then `lake exe cache get` and the build, and stops at the first failure. It fails on an error and on a warning outside `Challenge/`. It does not run Comparator. |

    python3 scripts/generate.py            # write the lists
    python3 scripts/generate.py --check    # write nothing; fail if a list on disk is out of date
    lake build Solution && lake env lean scripts/PrintAxioms.lean
    python3 scripts/index.py               # write INDEX.md, FILES.md, PROGRAMS.md and the list of NOTE paragraphs
    python3 scripts/index.py --check --names
    python3 scripts/layers.py --check
    scripts/check.sh                       # the three checks with --check, then the build

## What `generate.py` checks

A theorem that is missing from its list would not be compared, and nothing would say so. So the script reads only Challenge files of a simple form and stops at anything else:

* Every command begins in column 0, and what belongs to it is indented.
* A theorem has the form `theorem NAME ... := by sorry` (or `:= sorry`). Inside it there is no second declaration, no second `sorry`, no second `:=`, and none of the words and signs of the script's list `COMMAND`, such as `variable`, `open`, `@[` or `#eval`. The list also matches the notation `#s`, and some names, for instance unqualified names that begin with `run_`, `add_` or `register_`; write such a name with its namespace, or choose another.
* The only other lines are `module`, imports, `public section`, `open`, `namespace`, `section` and `end`, and every `end` closes what was opened last.

Of every trusted file (`EndStatement.lean`, `PaperStatements.lean` and the files of `Challenge/`) it asks the following.

* The file imports only Mathlib, `EndStatement` and `PaperStatements`, each with a line `import M` or `public import M` and nothing else on it; `EndStatement.lean` imports nothing, `PaperStatements.lean` imports only Mathlib and `EndStatement`, and a file `Challenge/T.lean` imports only `T`.
* Neither the file nor a folder in which it lies is a symbolic link. The names of the files of `Challenge/` consist of letters, digits and `_`.
* The only white space is the blank and the line feed.
* `/-`, `/--` and `/-!` are followed by one blank or the end of the line, and directly after that by a letter, a digit or one of ``# * ` " ( [``. A comment that is not inside another begins at the start of a line or after a blank.
* Outside comments there are no string literals and no «quoted» names.

It also fails if

* `Challenge/` holds anything but Lean files, or a file of `Challenge/` has no file of the same name in `Solution/`;
* the folder that holds `lakefile.toml` also holds a file or folder named `Mathlib`, `Mathlib.lean`, `EndStatement`, `PaperStatements` or `Challenge.lean`;
* a name is stated twice, or a `comparator-*.json` belongs to no file of `Challenge/`.

These checks guard against accidents. The script reads Lean text without Lean's parser, and the checks do not prove that a file has the form described. So it is no defence against a trusted file written to deceive: these files are meant to be read. It does not look at `lakefile.toml`, `lake-manifest.json` and `lean-toolchain`.

## What `index.py` checks

The script fails if `docs/paper-items.json` names a theorem that is not in `Challenge/`, if a theorem of `Challenge/` occurs in no row of the index, if a theorem of `Challenge/` has no theorem of the same name in the library, or if `docs/programs.json` names a declaration that does not exist. With `--check` it writes nothing and fails if `docs/INDEX.md`, `docs/FILES.md`, `docs/PROGRAMS.md` or the list in `docs/REMARKS.md` is out of date. With `--names` it also fails if `README.md` or a file of `docs/` names, between backticks, a declaration or a file that does not exist. It is a help for keeping the guides true; it checks nothing about the mathematics.
