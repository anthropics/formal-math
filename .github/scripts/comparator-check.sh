#!/usr/bin/env bash
# Palomar acceptance bar for one Lake project.
#
# leanprover/comparator -- with a lean4export matching the project's toolchain, the independent nanoda
# kernel, and the landrun sandbox -- must accept every comparator configuration the project declares,
# i.e. print "Your solution is okay!": each Solution theorem has exactly the statement of its trusted
# Challenge namesake, uses only the standard axioms, and replays in both kernels.
#
# Run from a project directory (the one holding lakefile.toml / lean-toolchain), after `lake exe cache get`:
#     cd <project> && bash ../.github/scripts/comparator-check.sh
# Needs elan (lean, lake), git, go, cargo and jq; Linux for landrun.
#
# Configurations checked, relative to the project directory:
#     comparator*.json            (Palomar template layout: comparator.json next to the lakefile)
#     comparator/config*.json     (a comparator/ directory of trusted statement files with per-topic configs)
#
# Tool pins default to those of the Palomar registry's verifier
# (https://github.com/PalomarRegistry/PalomarSubmission, .github/workflows/submission.yml); lean4export is
# taken at the release tag named after the project's Lean version unless LEAN4EXPORT_COMMIT is set.
set -euo pipefail

COMPARATOR_COMMIT="${COMPARATOR_COMMIT:-575674928e239f5bc452aab72d1dd7b0f1326494}"
NANODA_COMMIT="${NANODA_COMMIT:-68d5ca9db226849b41a6fff59d796ff19d0a8840}"
LANDRUN_COMMIT="${LANDRUN_COMMIT:-811cfff51ceaf3d9843708aa6d22e9b84ccac8b4}"
TOOLS_DIR="${TOOLS_DIR:-$HOME/.cache/lean-ci-tools}"
LOG_DIR="${LOG_DIR:-$PWD/.lake/comparator-logs}"

die() { echo "error: $*" >&2; exit 1; }

[ -f lean-toolchain ] || die "run this from a project directory containing lean-toolchain"
for tool in git go cargo jq lean lake; do
  command -v "$tool" >/dev/null 2>&1 || die "$tool is required"
done

toolchain="$(tr -d '[:space:]' < lean-toolchain)"
tag="v${toolchain#*:v}"
if [ -z "${LEAN4EXPORT_COMMIT:-}" ]; then
  refs="$(git ls-remote https://github.com/leanprover/lean4export "refs/tags/$tag" "refs/tags/$tag^{}")"
  LEAN4EXPORT_COMMIT="$(awk -v t="refs/tags/$tag^{}" '$2==t {print $1}' <<<"$refs")"
  [ -n "$LEAN4EXPORT_COMMIT" ] || LEAN4EXPORT_COMMIT="$(awk -v t="refs/tags/$tag" '$2==t {print $1}' <<<"$refs")"
  [ -n "$LEAN4EXPORT_COMMIT" ] || die "leanprover/lean4export has no release $tag for toolchain $toolchain"
fi

shopt -s nullglob
configs=(comparator*.json comparator/config*.json)
shopt -u nullglob
[ "${#configs[@]}" -gt 0 ] || die "no comparator configuration found (comparator*.json or comparator/config*.json)"
echo "project $(pwd), toolchain $toolchain, configurations: ${configs[*]}"

mkdir -p "$TOOLS_DIR/bin" "$LOG_DIR"

checkout_at() {  # <url> <dir> <commit>
  if [ ! -d "$2/.git" ]; then
    git clone --quiet --filter=blob:none "$1" "$2"
  fi
  if [ "$(git -C "$2" rev-parse HEAD)" != "$3" ]; then
    git -C "$2" fetch --quiet --depth 1 origin "$3"
    git -C "$2" checkout --quiet --detach "$3"
  fi
}

echo "== comparator @ $COMPARATOR_COMMIT"
checkout_at https://github.com/leanprover/comparator.git "$TOOLS_DIR/comparator" "$COMPARATOR_COMMIT"
(cd "$TOOLS_DIR/comparator" && lake build comparator)
comparator_bin="$TOOLS_DIR/comparator/.lake/build/bin/comparator"

echo "== lean4export @ $LEAN4EXPORT_COMMIT (release $tag)"
checkout_at https://github.com/leanprover/lean4export.git "$TOOLS_DIR/lean4export" "$LEAN4EXPORT_COMMIT"
export_toolchain="$(tr -d '[:space:]' < "$TOOLS_DIR/lean4export/lean-toolchain")"
[ "$export_toolchain" = "$toolchain" ] \
  || die "lean4export $LEAN4EXPORT_COMMIT targets $export_toolchain but the project uses $toolchain"
(cd "$TOOLS_DIR/lean4export" && lake build lean4export)
lean4export_bin="$TOOLS_DIR/lean4export/.lake/build/bin/lean4export"

echo "== nanoda_lib @ $NANODA_COMMIT"
checkout_at https://github.com/robsimmons/nanoda_lib.git "$TOOLS_DIR/nanoda" "$NANODA_COMMIT"
cargo build --release --locked --quiet --manifest-path "$TOOLS_DIR/nanoda/Cargo.toml"
nanoda_bin="$TOOLS_DIR/nanoda/target/release/nanoda_bin"

echo "== landrun @ $LANDRUN_COMMIT"
landrun_bin="$TOOLS_DIR/bin/landrun"
if [ ! -x "$landrun_bin" ] || [ "$(cat "$landrun_bin.commit" 2>/dev/null)" != "$LANDRUN_COMMIT" ]; then
  GOBIN="$TOOLS_DIR/bin" CGO_ENABLED=0 go install "github.com/zouuup/landrun/cmd/landrun@$LANDRUN_COMMIT"
  echo "$LANDRUN_COMMIT" > "$landrun_bin.commit"
fi

for bin in "$comparator_bin" "$lean4export_bin" "$nanoda_bin" "$landrun_bin"; do
  [ -x "$bin" ] || die "missing tool $bin"
done

# Comparator runs `lake build <module>` and lean4export inside landrun sandboxes that may execute only the
# toolchain directory, so resolve lake/lean to the toolchain's own binaries rather than the elan shims.
lean_prefix="$(lean --print-prefix)"
export PATH="$lean_prefix/bin:$PATH"
export COMPARATOR_LANDRUN="$landrun_bin"
export COMPARATOR_LEAN4EXPORT="$lean4export_bin"
export COMPARATOR_NANODA="$nanoda_bin"
export LEAN_ABORT_ON_PANIC=1

failures=0
for cfg in "${configs[@]}"; do
  name="$(tr '/' '_' <<<"${cfg%.json}")"
  log="$LOG_DIR/$name.log"
  # As in the registry: only the three standard axioms may be permitted, and the nanoda re-check is always
  # on (comparator is handed a copy of the configuration with enable_nanoda forced to true).
  jq -e '.permitted_axioms - ["propext", "Quot.sound", "Classical.choice"] == []' "$cfg" >/dev/null \
    || die "$cfg: permitted_axioms must be a subset of propext, Quot.sound, Classical.choice"
  checked_cfg="$LOG_DIR/$name.json"
  jq '.enable_nanoda = true' "$cfg" > "$checked_cfg"

  echo "== comparator $cfg  (log: $log)"
  set +e
  lake env "$comparator_bin" "$checked_cfg" 2>&1 | tee "$log"
  status="${PIPESTATUS[0]}"
  set -e
  if [ "$status" -eq 0 ] && grep -qxF 'Your solution is okay!' "$log"; then
    echo "PASS $cfg"
  else
    echo "::error::comparator did not accept $cfg (exit status $status)"
    failures=$((failures + 1))
  fi
done

[ "$failures" -eq 0 ] || die "$failures comparator configuration(s) not accepted"
echo "All ${#configs[@]} comparator configuration(s) accepted."
