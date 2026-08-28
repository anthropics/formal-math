#!/bin/bash
# Forbidden-construct scan over the new certificate modules (exit 1 if any hit).
W=$(git -C "$(dirname "$0")" rev-parse --show-toplevel)
cd "$W" || exit 1
FILES="Zeta23/ThmD/Sextuple/Macro Zeta23/ThmD/Sextuple/Certificate.lean Zeta23/ThmD/Sextuple/Unconditional.lean Zeta23/ThmD/Sextuple/LineDecimal.lean Zeta23/ThmD/Sextuple/A1275 comparator/Solution/Sextuple.lean comparator/Solution/SextupleA1275.lean"
PAT='sorry|admit|^axiom |[^a-zA-Z_]axiom |unsafe|native_decide|ofReduceBool|sorryAx|implemented_by|partial def|opaque |extern'
HITS=$(grep -rEn "$PAT" $FILES | grep -v "^.*:[0-9]*:.*--" )
if [ -n "$HITS" ]; then echo "$HITS"; echo "FORBIDDEN HITS"; exit 1; fi
echo "forbidden scan clean over $(find $FILES -name '*.lean' | wc -l | tr -d ' ') files"
