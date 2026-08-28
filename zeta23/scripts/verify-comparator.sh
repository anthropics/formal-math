#!/usr/bin/env bash
# Runs Comparator on one of this project's configurations with pinned revisions of Comparator,
# lean4export, NanoDa and Landrun (the layout of PalomarRegistry/PalomarTemplate's script, with the
# pins moved to this project's toolchain, leanprover/lean4:v4.33.0-rc2).
#
#   ./scripts/verify-comparator.sh                         # comparator.json (Theorems A–E, 17 statements)
#   ./scripts/verify-comparator.sh comparator-xiprime.json # the zeros of ξ′ (6 statements)
#
# Requires Linux, git, go, cargo, python3, lake (elan) and a working Landrun sandbox. Tool checkouts
# and binaries are cached under .cache/palomar-comparator (or $PALOMAR_COMPARATOR_CACHE).
set -euo pipefail

repository_root=$(cd "$(dirname "$0")/.." && pwd)
config_path=${1:-comparator.json}
case "$config_path" in
  /*) ;;
  *) config_path="$repository_root/$config_path" ;;
esac
cache_root=${PALOMAR_COMPARATOR_CACHE:-"$repository_root/.cache/palomar-comparator"}
bin_dir="$cache_root/bin"
comparator_dir="$cache_root/comparator"
lean4export_dir="$cache_root/lean4export"
nanoda_dir="$cache_root/nanoda"

# leanprover/comparator and leanprover/lean4export at their v4.33.0-rc2 tags — the tags matching
# lean-toolchain. Landrun and NanoDa are the revisions pinned by PalomarTemplate.
comparator_commit=75c730e9b6ef5c2c3b334fad7c3d51fe20624c88
lean4export_commit=9fb131bb100eb32ccf6836f14e4f8328d13b6792
landrun_commit=811cfff51ceaf3d9843708aa6d22e9b84ccac8b4
nanoda_commit=68d5ca9db226849b41a6fff59d796ff19d0a8840

for required_command in cargo git go lake python3; do
  if ! command -v "$required_command" >/dev/null 2>&1; then
    echo "error: $required_command is required to run Comparator" >&2
    exit 1
  fi
done

python3 - "$config_path" <<'PY'
import json
import pathlib
import sys

config_path = pathlib.Path(sys.argv[1])
try:
    config = json.loads(config_path.read_text(encoding="utf-8"))
except (OSError, UnicodeError, json.JSONDecodeError) as error:
    print(f"error: cannot read valid Comparator config {config_path}: {error}", file=sys.stderr)
    raise SystemExit(1)

if not isinstance(config, dict) or config.get("enable_nanoda") is not True:
    print(
        f"error: {config_path}: enable_nanoda must be exactly true; "
        "the NanoDa replay is required",
        file=sys.stderr,
    )
    raise SystemExit(1)
PY

mkdir -p "$cache_root" "$bin_dir"

checkout_exact() {
  local repository=$1
  local destination=$2
  local commit=$3
  if [ ! -d "$destination/.git" ]; then
    git clone --filter=blob:none "$repository" "$destination"
  fi
  git -C "$destination" fetch --depth 1 origin "$commit"
  git -C "$destination" checkout --detach "$commit"
}

checkout_exact https://github.com/leanprover/lean4export.git "$lean4export_dir" "$lean4export_commit"

if [ ! -f "$lean4export_dir/lean-toolchain" ]; then
  echo "error: pinned lean4export revision $lean4export_commit has no lean-toolchain file" >&2
  echo "select a lean4export revision that declares its Lean toolchain" >&2
  exit 1
fi

project_toolchain=$(tr -d '[:space:]' < "$repository_root/lean-toolchain")
lean4export_toolchain=$(tr -d '[:space:]' < "$lean4export_dir/lean-toolchain")
if [ "$project_toolchain" != "$lean4export_toolchain" ]; then
  echo "error: project toolchain $project_toolchain does not match" >&2
  echo "the pinned lean4export toolchain $lean4export_toolchain" >&2
  echo "update lean4export_commit when changing lean-toolchain, then review" >&2
  echo "Comparator and NanoDa compatibility with the export format" >&2
  exit 1
fi

checkout_exact https://github.com/leanprover/comparator.git "$comparator_dir" "$comparator_commit"
checkout_exact https://github.com/robsimmons/nanoda_lib.git "$nanoda_dir" "$nanoda_commit"

GOBIN="$bin_dir" go install "github.com/zouuup/landrun/cmd/landrun@$landrun_commit"

(cd "$comparator_dir" && lake build comparator)
(cd "$lean4export_dir" && lake build lean4export)
(cd "$nanoda_dir" && cargo build --release --locked)

cd "$repository_root"
lake exe cache get
PALOMAR_LANDRUN_BIN="$bin_dir/landrun" \
COMPARATOR_LEAN4EXPORT="$lean4export_dir/.lake/build/bin/lean4export" \
COMPARATOR_NANODA="$nanoda_dir/target/release/nanoda_bin" \
COMPARATOR_LANDRUN="$repository_root/scripts/landrun-wrapper.sh" \
  lake env "$comparator_dir/.lake/build/bin/comparator" "$config_path"
