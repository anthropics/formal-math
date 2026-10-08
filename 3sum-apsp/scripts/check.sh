#!/bin/sh
# Copyright (c) 2026 Anthropic, PBC. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# SPDX-License-Identifier: Apache-2.0
#
# Runs the checks that need only Python and Lean, one after the other, and stops at the first failure.
# It does not run Comparator; see README.md, "How to check it".
set -eu
CDPATH= cd -- "$(dirname -- "$0")/.."

python3 scripts/generate.py --check          # the lists comparator-*.json name every theorem of Challenge/
python3 scripts/index.py --check --names     # the generated documents are up to date; every name in the documents exists
python3 scripts/layers.py --check            # the folders of the library import each other in the stated order
lake exe cache get                           # Mathlib's compiled files
lake build --wfail EndStatement PaperStatements ThreeSumApsp Solution     # no error and no warning
lake build Challenge                         # one theorem for each statement, with sorry in place of its proof
echo "The scripts and the build passed. Comparator was not run."
