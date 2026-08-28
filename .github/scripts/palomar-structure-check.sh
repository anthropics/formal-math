#!/usr/bin/env bash
# Palomar structure check for one project directory of this repository.
#
# Usage: .github/scripts/palomar-structure-check.sh <project-dir>
#
# Checks -- without network access and without a Lean toolchain -- that <project-dir> has the layout the
# Palomar registry requires of "the selected project directory" (https://palomar-registry.org/how-to-submit,
# starter layout github.com/PalomarRegistry/PalomarTemplate):
#   1. exactly one of lakefile.toml / lakefile.lean, and a committed lake-manifest.json (required for
#      lakefile.lean projects, strongly recommended for lakefile.toml projects) whose git packages are
#      public https://github.com URLs pinned to full commit SHAs;
#   2. lean-toolchain -- the project-local file, else the repository-root file -- pinned to a Lean release
#      or release candidate: leanprover/lean4:vX.Y.Z or leanprover/lean4:vX.Y.Z-rcN (no nightly, no custom);
#   3. a small, readable Challenge module (conventionally Challenge.lean): at most 1000 lines / 100 KiB
#      (hard limit; more than 300 lines / 32 KiB is a warning), importing only Lean core, Mathlib and its
#      dependency closure, or TauCeti -- never a module of the project itself --, declaring at least one
#      theorem/def, with `sorry` placeholders expected (a Challenge without sorry is a warning);
#   4. a proved Solution module (conventionally Solution.lean): no `sorry`, no `native_decide`
#      (Lean.ofReduceBool), no `axiom` declarations;
#   5. a comparator configuration -- conventionally comparator.json next to the lakefile; like
#      comparator-check.sh this script also accepts comparator*.json and comparator/config*.json, and any
#      path named by formalization.yaml -- in leanprover/comparator's schema, the only shape accepted here:
#          { "challenge_module": "Challenge", "solution_module": "Solution",
#            "theorem_names": ["Namespace.result", ...],
#            "definition_names": [],                                            <- optional
#            "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"],
#            "enable_nanoda": true }
#      (no other keys) naming at least one declaration; permitted_axioms within the standard three; every named
#      declaration must occur (by its final name component) in the Challenge module's source (violation)
#      and in the Solution module's source (warning; violation if none of them does);
#   6. formalization.yaml at the project root (standard github.com/mathlib-initiative/formalization.yaml
#      v0.4, key set of PalomarRegistry/PalomarTemplate's formalization.yaml):
#        required (submission policy CONTRIBUTING.md 3.1-3.2) -> violation if missing or empty:
#            project.name, project.description (the public registry abstract, <= 10000 chars),
#            project.authors[], project.license, project.responsible_maintainers[],
#            classification.arxiv (arXiv categories; 1-2 recommended), automation.methods[].method
#            (manual|copilot|agent|autonomous|other), review.status; for a thin wrapper
#            repository.substantive_formalization.{id,revision}
#        expected -> warning if missing/odd:
#            version: "v0.4"; sources[] (each with title + relationship in formalizes|adapts|
#            independently-proves|background|other; type: original-proof marks a result first presented by
#            the formalization); classification.msc2020 (1-8 MSC2020 codes);
#            status.scope, status.sorry_count, status.axioms; fidelity.divergences;
#            status.main_results[] or alignment.statements[] (plain-language account of the theorems);
#        leftover "TEMPLATE:" placeholder values -> violation (the registry's validator rejects them);
#      optional path keys honoured by this script: top-level `challenge:`, `solution:`,
#      `comparator_config:` and status.main_results[].comparator_config (project-relative paths);
#   7. exactly one conventional licence file (LICENSE, LICENCE, COPYING, ... [.md|.txt]) at the repository
#      root -- it stays at the root even for a nested project.
# In addition the whole project (outside .lake, the Challenge and the Solution modules) is grepped for
# `axiom` declarations and `native_decide`; hits are warnings only -- the comparator run
# (.github/scripts/comparator-check.sh) is the real gate for axioms.
#
# Challenge/Solution modules named by a configuration are resolved to files through the source
# directories of the lakefile ("." plus every srcDir), e.g. Challenge.XiPrime -> Challenge/XiPrime.lean; compiled artefacts (.olean, ...) outside .lake are a violation.
# The repository root is the directory two levels above this script; override with PALOMAR_REPO_ROOT.
#
# Exit status: 1 and the list of violations if any check fails, 0 (possibly with warnings) otherwise.
# Needs bash >= 4 and python3 (PyYAML if available; without it formalization.yaml keys are checked textually).
set -euo pipefail

usage() { echo "usage: $0 <project-dir>" >&2; exit 2; }
[ "$#" -eq 1 ] || usage
[ -d "$1" ] || { echo "error: $1 is not a directory" >&2; exit 2; }
command -v python3 >/dev/null 2>&1 || { echo "error: python3 is required" >&2; exit 2; }

P="$(cd "$1" && pwd)"
R="${PALOMAR_REPO_ROOT:-$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)}"

fails=(); warns=(); infos=()
fail() { fails+=("$*"); }
warn() { warns+=("$*"); }
info() { infos+=("$*"); }
rel() { if [[ "$1" == "$R"/* ]]; then printf '%s\n' "${1#"$R"/}"; elif [[ "$1" == "$R" ]]; then echo .; else printf '%s\n' "$1"; fi; }

# ---- helpers (python3) -------------------------------------------------------------------------------

# Lean source with block comments (nested /- -/) and line comments (--) removed; line breaks are kept.
strip_comments() {
  python3 - "$1" <<'PY'
import sys
s = open(sys.argv[1], encoding="utf-8", errors="replace").read()
out, i, n, depth = [], 0, len(s), 0
while i < n:
    if s.startswith("/-", i):
        depth += 1; i += 2; continue
    if depth:
        if s.startswith("-/", i):
            depth -= 1; i += 2
        else:
            if s[i] == "\n": out.append("\n")
            i += 1
        continue
    if s.startswith("--", i):
        j = s.find("\n", i); i = n if j < 0 else j; continue
    out.append(s[i]); i += 1
sys.stdout.write("".join(out))
PY
}

# comparator configuration -> lines "CHALLENGE <module>", "SOLUTION <module>", "NAME <decl>", "ERR <message>".
read_config() {
  python3 - "$1" <<'PY'
import json, sys
try:
    cfg = json.load(open(sys.argv[1], encoding="utf-8"))
except Exception as e:
    print("ERR not valid JSON: %s" % str(e).splitlines()[0]); sys.exit(0)
if not isinstance(cfg, dict):
    print("ERR top level must be a JSON object (comparator schema)"); sys.exit(0)
for key in ("challenge_module", "solution_module"):
    v = cfg.get(key)
    if isinstance(v, str) and v.strip():
        print("%s %s" % (key.split("_")[0].upper(), v.strip()))
    else:
        print("ERR missing string key %s" % key)
names = []
tn = cfg.get("theorem_names")
if not isinstance(tn, list) or not all(isinstance(x, str) for x in tn):
    print("ERR theorem_names must be a list of declaration names")
else:
    names += tn
dn = cfg.get("definition_names", [])
if not isinstance(dn, list) or not all(isinstance(x, str) for x in dn):
    print("ERR definition_names, when present, must be a list of declaration names")
else:
    names += dn
for x in names:
    if x.strip(): print("NAME %s" % x.strip())
ax = cfg.get("permitted_axioms")
std = {"propext", "Quot.sound", "Classical.choice"}
if not isinstance(ax, list):
    print("ERR permitted_axioms must be a list (subset of propext, Quot.sound, Classical.choice)")
elif set(ax) - std:
    print("ERR permitted_axioms outside the standard three: %s" % ", ".join(sorted(set(ax) - std)))
extra = sorted(set(cfg) - {"challenge_module", "solution_module", "theorem_names", "definition_names", "permitted_axioms", "enable_nanoda"})
if extra:
    print("ERR keys not accepted by the registry: %s (allowed: challenge_module, solution_module, theorem_names, definition_names, permitted_axioms, enable_nanoda)" % ", ".join(extra))
import re
for key in ("challenge_module", "solution_module"):
    v = cfg.get(key)
    if isinstance(v, str) and v.strip() and not re.match(r"^[A-Za-z_][A-Za-z0-9_']*(\.[A-Za-z_][A-Za-z0-9_']*)*$", v.strip()):
        print("ERR %s %r is not a dotted Lean module name" % (key, v))
if isinstance(cfg.get("challenge_module"), str) and cfg.get("challenge_module") == cfg.get("solution_module"):
    print("ERR challenge_module and solution_module must be distinct modules")
if cfg.get("enable_nanoda") is not True:
    print("WARN enable_nanoda is not true (the registry and this repository's CI run nanoda regardless)")
PY
}

# formalization.yaml -> lines "FAIL <msg>", "WARN <msg>", "INFO <msg>", "PATH <key> <value>".
read_yaml() {
  python3 - "$1" <<'PY'
import re, sys
path = sys.argv[1]
text = open(path, encoding="utf-8", errors="replace").read()
def emit(kind, msg): print(kind, msg)
try:
    import yaml
except ImportError:
    yaml = None
structured = yaml is not None
if structured:
    try:
        doc = yaml.safe_load(text)
    except Exception as e:
        emit("FAIL", "formalization.yaml: not valid YAML (%s)" % str(e).splitlines()[0]); sys.exit(0)
    if not isinstance(doc, dict):
        emit("FAIL", "formalization.yaml: the top level must be a mapping"); sys.exit(0)
else:
    emit("WARN", "formalization.yaml: PyYAML not available to python3; keys checked textually, formats not checked")
    # Two-level textual scan: "key:" at column 0 and its children at the first deeper indentation.
    def scalar(v):
        v = re.sub(r"\s+#.*$", "", v.strip())
        return v[1:-1] if len(v) >= 2 and v[0] == v[-1] and v[0] in "\"'" else v
    doc, cur, ind = {}, None, None
    for line in text.splitlines():
        if not line.strip() or line.lstrip().startswith("#"): continue
        m = re.match(r"^([A-Za-z_][\w-]*):\s*(.*)$", line)
        if m:
            cur, val, ind = m.group(1), scalar(m.group(2)), None
            doc[cur] = val if val else {}
            continue
        m = re.match(r"^(\s+)-?\s*([A-Za-z_][\w-]*):\s*(.*)$", line)
        if m and cur is not None and isinstance(doc.get(cur), dict):
            depth = len(m.group(1))
            if ind is None: ind = depth
            if depth == ind: doc[cur][m.group(2)] = scalar(m.group(3)) or "present"
        elif re.match(r"^\s*- ", line) and cur is not None and doc.get(cur) == {}:
            doc[cur] = ["present"]
def get(*ks):
    d = doc
    for k in ks:
        if not isinstance(d, dict) or k not in d: return None
        d = d[k]
    return d
def nonempty(v): return v not in (None, "", [], {})
def as_list(v): return v if isinstance(v, list) else ([] if v in (None, "", {}) else [v])

# hard mechanical requirements of the registry (submission policy, CONTRIBUTING.md 3.1-3.2)
for key, label in (("name", "project.name"), ("authors", "project.authors"), ("license", "project.license")):
    if not nonempty(get("project", key)): emit("FAIL", "formalization.yaml: %s is missing or empty" % label)
maint = get("project", "responsible_maintainers")
if not nonempty(maint): maint = get("project", "responsible_maintainer")
if not nonempty(maint): emit("FAIL", "formalization.yaml: project.responsible_maintainers (nonempty list of names) is missing or empty")
desc = get("project", "description")
if not nonempty(desc):
    emit("FAIL", "formalization.yaml: project.description (the public registry abstract, <= 10000 characters) is missing")
elif structured and isinstance(desc, str) and len(desc.strip()) > 10000:
    emit("FAIL", "formalization.yaml: project.description exceeds 10000 characters")
meth = get("automation", "methods")
if not nonempty(meth):
    emit("FAIL", "formalization.yaml: automation.methods[] (each with method: manual|copilot|agent|autonomous|other, models, the role of AI) is missing")
elif structured:
    for i, m in enumerate(as_list(meth)):
        if not isinstance(m, dict) or not nonempty(m.get("method")):
            emit("FAIL", "formalization.yaml: automation.methods[%d].method is missing" % i)
if not nonempty(get("review", "status")): emit("FAIL", "formalization.yaml: review.status is missing (e.g. unchecked, self-assessed, agent-reviewed, author-verified, peer-reviewed)")
arx = get("classification", "arxiv")
if not nonempty(arx):
    emit("FAIL", "formalization.yaml: classification.arxiv (1-2 arXiv categories, e.g. math.NT) is missing")
elif structured:
    arx = as_list(arx)
    bad = [a for a in arx if not (isinstance(a, str) and re.match(r"^[a-z][a-z-]*(\.[A-Za-z-]+)?$", a))]
    if bad or len(arx) > 8:
        emit("FAIL", "formalization.yaml: classification.arxiv must hold arXiv category identifiers such as math.NT (found %s)" % arx)
    elif len(arx) > 2:
        emit("WARN", "formalization.yaml: classification.arxiv has %d entries; 1-2 are recommended" % len(arx))

# expected by the registry / the formalization.yaml standard (warnings)
if get("version") != "v0.4": emit("WARN", "formalization.yaml: version is %r, the current standard is 'v0.4'" % get("version"))
lic = get("project", "license")
if nonempty(lic) and lic != "Apache-2.0":
    emit("WARN", "formalization.yaml: project.license is %r; it must be the SPDX identifier of the repository-root LICENSE (Apache-2.0 in this repository)" % lic)
src = get("sources")
if not nonempty(src):
    emit("WARN", "formalization.yaml: sources[] is missing or empty (a result first presented here uses one source with type: original-proof, relationship: other)")
elif structured:
    rels = {"formalizes", "adapts", "independently-proves", "background", "other"}
    for i, s in enumerate(as_list(src)):
        if not isinstance(s, dict) or not nonempty(s.get("title")) or s.get("relationship") not in rels:
            emit("WARN", "formalization.yaml: sources[%d] needs a title and a relationship in formalizes|adapts|independently-proves|background|other" % i)
msc = get("classification", "msc2020")
if not nonempty(msc):
    emit("WARN", "formalization.yaml: classification.msc2020 (1-8 five-character MSC2020 codes, e.g. 11M26) is missing (accepted, but expected)")
elif structured:
    msc = as_list(msc)
    bad = [c for c in msc if not (isinstance(c, str) and re.match(r"^[0-9]{2}[A-Z-][0-9Xx]{2}$", c))]
    if not 1 <= len(msc) <= 8 or bad:
        emit("WARN", "formalization.yaml: classification.msc2020 should hold 1-8 five-character MSC2020 codes (found %s)" % msc)
repo = get("repository")
if structured and isinstance(repo, dict) and (repo.get("role") == "thin-wrapper" or "substantive_formalization" in repo):
    sf = repo.get("substantive_formalization")
    if not (isinstance(sf, dict) and nonempty(sf.get("id")) and isinstance(sf.get("revision"), str) and re.match(r"^[0-9a-f]{40}$", sf["revision"])):
        emit("FAIL", "formalization.yaml: a thin wrapper must give repository.substantive_formalization.id (owner/repository) and .revision (full 40-character commit SHA)")
for key in ("scope", "sorry_count", "axioms"):
    if get("status", key) is None: emit("WARN", "formalization.yaml: status.%s is missing" % key)
if structured and get("status", "sorry_count") not in (None, 0):
    emit("WARN", "formalization.yaml: status.sorry_count is %r (a registered proof development has 0; Challenge placeholders are not counted)" % get("status", "sorry_count"))
if get("fidelity", "divergences") is None: emit("WARN", "formalization.yaml: fidelity.divergences is missing (write 'none known' if so)")
if not nonempty(get("status", "main_results")) and not nonempty(get("alignment", "statements")):
    emit("WARN", "formalization.yaml: neither status.main_results[] nor alignment.statements[] gives an account of the compared theorems")
sentinels = re.findall(r"^[^#\n]*\bTEMPLATE:", text, flags=re.M)
if sentinels: emit("FAIL", "formalization.yaml: %d TEMPLATE placeholder value(s) left from the starter template" % len(sentinels))

# optional path overrides used by the structure check
for key in ("challenge", "solution", "comparator_config"):
    v = get(key)
    if isinstance(v, str) and v.strip(): emit("PATH", "%s %s" % (key, v.strip()))
if structured:
    for r in as_list(get("status", "main_results")):
        if isinstance(r, dict) and isinstance(r.get("comparator_config"), str):
            emit("PATH", "comparator_config %s" % r["comparator_config"].strip())
name = get("project", "name")
if isinstance(name, str) and name.strip(): emit("INFO", "formalization.yaml: project %r" % (name.strip()[:80] + ("..." if len(name.strip()) > 80 else "")))
PY
}

# lake-manifest.json -> one line per violation (git packages must be public github URLs at full commit SHAs).
check_manifest() {
  python3 - "$1" <<'PY'
import json, re, sys
try:
    m = json.load(open(sys.argv[1], encoding="utf-8"))
except Exception as e:
    print("not valid JSON: %s" % str(e).splitlines()[0]); sys.exit(0)
pk = m.get("packages", []) if isinstance(m, dict) else None
if not isinstance(pk, list):
    print("unexpected shape (no packages list)"); sys.exit(0)
for p in pk:
    if not isinstance(p, dict) or p.get("type") != "git": continue
    url, rev = str(p.get("url", "")), str(p.get("rev", ""))
    if not re.match(r"^https://github\.com/[^/?#@]+/[^/?#@]+?(\.git)?/?$", url):
        print("package %s: url %s is not a credential-free public https://github.com/owner/repository URL" % (p.get("name"), url))
    if not re.match(r"^[0-9a-f]{40}$", rev):
        print("package %s: rev %r is not a full 40-character commit SHA" % (p.get("name"), rev))
PY
}

# ---- 1. lakefile and manifest ------------------------------------------------------------------------
lakefile=""
count=0
for f in lakefile.toml lakefile.lean; do
  if [ -f "$P/$f" ]; then lakefile="$f"; count=$((count + 1)); fi
done
if [ "$count" -eq 0 ]; then
  fail "no lakefile: exactly one of lakefile.toml or lakefile.lean is required"
elif [ "$count" -gt 1 ]; then
  fail "both lakefile.toml and lakefile.lean exist: exactly one is allowed"
else
  info "lakefile: $lakefile"
  if [ ! -f "$P/lake-manifest.json" ]; then
    if [ "$lakefile" = lakefile.lean ]; then
      fail "lake-manifest.json is missing: a committed manifest is required for lakefile.lean projects"
    else
      warn "lake-manifest.json is missing: a committed manifest is strongly recommended (run lake update and commit it)"
    fi
  else
    while IFS= read -r msg; do
      [ -n "$msg" ] && fail "lake-manifest.json: $msg"
    done < <(check_manifest "$P/lake-manifest.json")
  fi
fi

# Source directories of the Lake package: "." plus every srcDir of the lakefile.
srcdirs=(.)
if [ -n "$lakefile" ]; then
  while IFS= read -r d; do
    [ -n "$d" ] && [ "$d" != . ] && srcdirs+=("$d")
  done < <(sed -n -E 's/^[[:space:]]*srcDir[[:space:]]*:?=[[:space:]]*"([^"]*)".*/\1/p' "$P/$lakefile" | sort -u)
fi

# <dotted module> -> absolute path of its source file, if it exists under one of the source directories.
resolve_module() {
  local relpath="${1//.//}.lean" d
  for d in "${srcdirs[@]}"; do
    if [ -f "$P/$d/$relpath" ]; then (cd "$P/$d" && printf '%s/%s\n' "$(pwd)" "$relpath"); return 0; fi
  done
  return 1
}

# ---- 2. toolchain ------------------------------------------------------------------------------------
tc_file=""
if [ -f "$P/lean-toolchain" ]; then tc_file="$P/lean-toolchain"
elif [ -f "$R/lean-toolchain" ]; then tc_file="$R/lean-toolchain"
fi
if [ -z "$tc_file" ]; then
  fail "lean-toolchain is missing (neither $(rel "$P")/lean-toolchain nor a repository-root lean-toolchain)"
else
  tc="$(tr -d '[:space:]' < "$tc_file")"
  if [[ "$tc" =~ ^leanprover/lean4:v[0-9]+\.[0-9]+\.[0-9]+(-rc[0-9]+)?$ ]]; then
    info "lean-toolchain: $tc (from $(rel "$tc_file"))"
  else
    fail "lean-toolchain (from $(rel "$tc_file")): '$tc' is not a Lean release or release candidate (expected leanprover/lean4:vX.Y.Z or vX.Y.Z-rcN; nightlies and custom toolchains are not accepted)"
  fi
fi

# ---- 6. formalization.yaml (read early: it may name the Challenge/Solution/config paths) --------------
yaml_challenge=""; yaml_solution=""; yaml_configs=()
if [ ! -f "$P/formalization.yaml" ]; then
  fail "formalization.yaml is missing at the project root (required registry metadata; start from PalomarRegistry/PalomarTemplate's formalization.yaml)"
else
  while IFS= read -r line; do
    kind="${line%% *}"; msg="${line#* }"
    case "$kind" in
      FAIL) fail "$msg" ;;
      WARN) warn "$msg" ;;
      INFO) info "$msg" ;;
      PATH)
        key="${msg%% *}"; val="${msg#* }"
        case "$key" in
          challenge) yaml_challenge="$val" ;;
          solution) yaml_solution="$val" ;;
          comparator_config) yaml_configs+=("$val") ;;
        esac ;;
    esac
  done < <(read_yaml "$P/formalization.yaml")
fi

# ---- 5. comparator configuration(s) ------------------------------------------------------------------
declare -A seen_cfg=()
configs=()
add_config() {  # <path relative to P>
  local c="$1" key
  if [ ! -f "$P/$c" ]; then
    if [ -z "${seen_cfg[missing:$c]:-}" ]; then seen_cfg[missing:$c]=1; fail "comparator configuration $c (named in formalization.yaml) does not exist"; fi
    return 0
  fi
  key="$(cd "$(dirname "$P/$c")" && pwd)/$(basename "$c")"
  if [ -z "${seen_cfg[$key]:-}" ]; then seen_cfg[$key]=1; configs+=("$c"); fi
}
for c in "${yaml_configs[@]}"; do add_config "$c"; done
shopt -s nullglob
for c in "$P"/comparator*.json "$P"/comparator/config*.json; do add_config "${c#"$P"/}"; done
shopt -u nullglob
if [ "${#configs[@]}" -eq 0 ]; then
  fail "no comparator configuration: comparator.json (or comparator*.json / comparator/config*.json) naming every theorem and definition to compare is required"
fi

# ---- 3./4. Challenge and Solution modules, per configuration -----------------------------------------
declare -A checked_challenge=() checked_solution=()
challenge_files=()   # absolute paths, excluded from the project-wide grep
solution_files=()
allowed_import_roots="Init Std Lean Mathlib Batteries Aesop Qq ProofWidgets Plausible LeanSearchClient ImportGraph TauCeti"
decl_re='^[[:space:]]*(@\[[^]]*\][[:space:]]*)*((private|protected|noncomputable|unsafe|partial|nonrec|scoped|local)[[:space:]]+)*(theorem|lemma|def|abbrev|instance|structure|inductive|class|opaque)[[:space:]]'
axiom_re='^[[:space:]]*(@\[[^]]*\][[:space:]]*)*((private|protected)[[:space:]]+)*axiom[[:space:]]'

check_challenge() {  # <abs file>
  local f="$1" lines bytes text imports bad tok root ok
  lines="$(wc -l < "$f" | tr -d ' ')"; bytes="$(wc -c < "$f" | tr -d ' ')"
  if [ "$lines" -gt 1000 ] || [ "$bytes" -gt 102400 ]; then
    fail "$(rel "$f"): $lines lines / $bytes bytes exceeds the registry's hard limit for a Challenge module (1000 lines, 100 KiB)"
  elif [ "$lines" -gt 300 ] || [ "$bytes" -gt 32768 ]; then
    warn "$(rel "$f"): $lines lines / $bytes bytes -- a Challenge module should be small and readable (preferably <= 300 lines and <= 32 KiB)"
  else
    info "challenge: $(rel "$f") ($lines lines, $bytes bytes)"
  fi
  text="$(strip_comments "$f")"
  # imports: every token after `import` (modifiers public/private/meta/all skipped) must have an allowed root
  bad=""
  while IFS= read -r imports; do
    for tok in $imports; do
      case "$tok" in import|public|private|meta|all) continue ;; esac
      root="${tok%%.*}"; ok=false
      for a in $allowed_import_roots; do [ "$root" = "$a" ] && ok=true; done
      $ok || bad="$bad $tok"
    done
  done < <(grep -E '^[[:space:]]*((public|private|meta)[[:space:]]+)*import[[:space:]]' <<<"$text" || true)
  if [ -n "$bad" ]; then
    fail "$(rel "$f"): imports outside Lean core / Mathlib / TauCeti:$bad (a Challenge module may not import project modules; inline the definitions it needs)"
  fi
  if ! grep -qE "$decl_re" <<<"$text"; then
    fail "$(rel "$f"): no theorem/def declarations found -- the Challenge module must state the compared results"
  fi
  if ! grep -qw sorry <<<"$text"; then
    warn "$(rel "$f"): contains no sorry -- Palomar expects the Challenge module to state each result with a sorry placeholder and the proof to live in the Solution module"
  fi
  if grep -qE "$axiom_re" <<<"$text"; then
    fail "$(rel "$f"): declares an axiom -- state hypotheses as explicit arguments instead"
  fi
}

check_solution() {  # <abs file>
  local f="$1" text
  info "solution: $(rel "$f")"
  text="$(strip_comments "$f")"
  if grep -qw sorry <<<"$text"; then fail "$(rel "$f"): contains sorry -- the Solution module must be fully proved"; fi
  if grep -qwE 'native_decide|ofReduceBool' <<<"$text"; then
    fail "$(rel "$f"): uses native_decide / Lean.ofReduceBool, which the registry does not permit (plain decide is fine)"
  fi
  if grep -qE "$axiom_re" <<<"$text"; then
    fail "$(rel "$f"): declares an axiom -- only propext, Classical.choice and Quot.sound may be used; state hypotheses as explicit arguments"
  fi
}

for c in "${configs[@]}"; do
  ch_mod=""; so_mod=""; names=()
  while IFS= read -r line; do
    kind="${line%% *}"; msg="${line#* }"
    case "$kind" in
      CHALLENGE) ch_mod="$msg" ;;
      SOLUTION) so_mod="$msg" ;;
      NAME) names+=("$msg") ;;
      WARN) warn "$c: $msg" ;;
      ERR) fail "$c: $msg" ;;
    esac
  done < <(read_config "$P/$c")
  [ -n "$ch_mod" ] && [ -n "$so_mod" ] || continue
  if [ "${#names[@]}" -eq 0 ]; then
    fail "$c: names no declaration -- theorem_names (and definition_names) must list every theorem and definition to compare"
  fi

  # Resolve the two modules to source files: lakefile source dirs, then the formalization.yaml override,
  # for the conventional module names only.
  ch_file="$(resolve_module "$ch_mod" || true)"
  if [ -z "$ch_file" ] && [ -n "$yaml_challenge" ] && [ -f "$P/$yaml_challenge" ]; then ch_file="$(cd "$P" && realpath "$yaml_challenge")"; fi
  so_file="$(resolve_module "$so_mod" || true)"
  if [ -z "$so_file" ] && [ -n "$yaml_solution" ] && [ -f "$P/$yaml_solution" ]; then so_file="$(cd "$P" && realpath "$yaml_solution")"; fi

  if [ -z "$ch_file" ]; then
    fail "$c: Challenge module '$ch_mod' has no source file (looked for ${ch_mod//.//}.lean under: ${srcdirs[*]})"
  elif [ -z "${checked_challenge[$ch_file]:-}" ]; then
    checked_challenge[$ch_file]=1; challenge_files+=("$ch_file"); check_challenge "$ch_file"
  fi
  if [ -z "$so_file" ]; then
    fail "$c: Solution module '$so_mod' has no source file (looked for ${so_mod//.//}.lean under: ${srcdirs[*]})"
  elif [ -z "${checked_solution[$so_file]:-}" ]; then
    checked_solution[$so_file]=1; solution_files+=("$so_file"); check_solution "$so_file"
  fi

  # Every compared declaration must be stated in the Challenge and proved under the same name in the Solution.
  if [ "${#names[@]}" -gt 0 ] && [ -n "$ch_file" ] && [ -n "$so_file" ]; then
    ch_text="$(strip_comments "$ch_file")"; so_text="$(strip_comments "$so_file")"
    missing_ch=(); missing_so=(); found_so=0
    for name in "${names[@]}"; do
      last="${name##*.}"
      grep -qwF -- "$last" <<<"$ch_text" || missing_ch+=("$name")
      if grep -qwF -- "$last" <<<"$so_text"; then found_so=$((found_so + 1)); else missing_so+=("$name"); fi
    done
    if [ "${#missing_ch[@]}" -gt 0 ]; then
      fail "$c: declaration(s) not found in $(rel "$ch_file"): ${missing_ch[*]}"
    fi
    if [ "$found_so" -eq 0 ]; then
      fail "$c: none of the ${#names[@]} named declaration(s) occurs in $(rel "$so_file")"
    elif [ "${#missing_so[@]}" -gt 0 ]; then
      warn "$c: declaration(s) not found textually in $(rel "$so_file") (they must be proved under exactly these names somewhere in the Solution module's closure): ${missing_so[*]}"
    fi
    info "config: $c -> $ch_mod / $so_mod, ${#names[@]} declaration(s)"
  fi
done

# ---- project-wide sweep (warnings only, comments stripped) ---------------------------------------
sweep_axiom=(); sweep_native=()
while IFS= read -r line; do
  kind="${line%% *}"; f="${line#* }"
  case "$kind" in
    AXIOM) sweep_axiom+=("$(rel "$f")") ;;
    NATIVE) sweep_native+=("$(rel "$f")") ;;
  esac
done < <(find "$P" \( -name .lake -o -name .git -o -name build \) -prune -o -type f -name '*.lean' -print0 \
  | python3 -c '
import re, sys
skip = set(sys.argv[1:])
axiom_re = re.compile(r"^\s*(@\[[^\]]*\]\s*)*((private|protected)\s+)*axiom\s", re.M)
native_re = re.compile(r"\b(native_decide|ofReduceBool)\b")
def strip(s):
    out, i, n, depth = [], 0, len(s), 0
    while i < n:
        if s.startswith("/-", i): depth += 1; i += 2; continue
        if depth:
            if s.startswith("-/", i): depth -= 1; i += 2
            else: i += 1
            continue
        if s.startswith("--", i):
            j = s.find("\n", i); i = n if j < 0 else j; continue
        out.append(s[i]); i += 1
    return "".join(out)
for f in sys.stdin.buffer.read().split(b"\0"):
    f = f.decode("utf-8", "replace")
    if not f or f in skip: continue
    try: t = strip(open(f, encoding="utf-8", errors="replace").read())
    except OSError: continue
    if axiom_re.search(t): print("AXIOM", f)
    if native_re.search(t): print("NATIVE", f)
' "${challenge_files[@]}" "${solution_files[@]}")
first_n() { local n="$1"; shift; local all=("$@"); printf '%s' "${all[*]:0:$n}"; [ "${#all[@]}" -le "$n" ] || printf ' ... and %d more' "$(( ${#all[@]} - n ))"; }
if [ "${#sweep_axiom[@]}" -gt 0 ]; then
  warn "axiom declarations in ${#sweep_axiom[@]} project file(s) (comparator decides whether the compared theorems depend on them): $(first_n 8 "${sweep_axiom[@]}")"
fi
if [ "${#sweep_native[@]}" -gt 0 ]; then
  warn "native_decide / ofReduceBool in ${#sweep_native[@]} project file(s) (not permitted in the closure of a compared theorem; comparator is the gate): $(first_n 8 "${sweep_native[@]}")"
fi
artefacts=()
while IFS= read -r -d '' f; do artefacts+=("$(rel "$f")"); done < <(find "$P" \( -name .lake -o -name .git \) -prune -o -type f \( -name '*.olean' -o -name '*.ilean' -o -name '*.trace' -o -name '*.o' -o -name '*.a' -o -name '*.so' \) -print0)
if [ "${#artefacts[@]}" -gt 0 ]; then
  fail "compiled artefacts outside .lake (must not be committed): $(first_n 8 "${artefacts[@]}")"
fi

# ---- 7. LICENSE at the repository root ---------------------------------------------------------------
licenses=()
while IFS= read -r f; do licenses+=("$f"); done < <(find "$R" -maxdepth 1 -type f -regextype posix-egrep -iregex '.*/(license|licence|copying|unlicense|ofl)(\.(md|markdown|txt))?' | sort)
if [ "${#licenses[@]}" -eq 0 ]; then
  fail "no licence file at the repository root (LICENSE; it covers the submitted snapshot and stays at the root even for a nested project)"
elif [ "${#licenses[@]}" -gt 1 ]; then
  fail "more than one licence file at the repository root: $(for f in "${licenses[@]}"; do rel "$f"; done | tr '\n' ' ')(exactly one is allowed)"
elif [ ! -s "${licenses[0]}" ]; then
  fail "$(rel "${licenses[0]}") is empty"
else
  info "licence: $(rel "${licenses[0]}") (repository root)"
fi

# ---- report ------------------------------------------------------------------------------------------
gha="${GITHUB_ACTIONS:-}"
echo "Palomar structure check: $(rel "$P")  (repository root: $R)"
for m in "${infos[@]}"; do echo "  ok    $m"; done
for m in "${warns[@]}"; do if [ -n "$gha" ]; then echo "::warning::$(rel "$P"): $m"; else echo "  WARN  $m"; fi; done
for m in "${fails[@]}"; do if [ -n "$gha" ]; then echo "::error::$(rel "$P"): $m"; else echo "  FAIL  $m"; fi; done
if [ "${#fails[@]}" -gt 0 ]; then
  echo "Palomar structure check FAILED for $(rel "$P"): ${#fails[@]} violation(s), ${#warns[@]} warning(s)."
  exit 1
fi
echo "Palomar structure check OK for $(rel "$P"): lakefile, toolchain, Challenge/Solution, ${#configs[@]} comparator configuration(s), formalization.yaml, LICENSE (${#warns[@]} warning(s))."
