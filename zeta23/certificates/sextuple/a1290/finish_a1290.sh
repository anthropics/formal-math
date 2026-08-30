#!/bin/bash
# Post-chunk completion flow for the A1290 target (run from the repository root after all chunks are built).
set -u
LAKE=/Users/mdumitrean/.elan/bin/lake
L=certificates/sextuple/logs
cd "$(git rev-parse --show-toplevel)/zeta23" || exit 1
missing=$(python3 -c "
import glob;src=len(glob.glob('Zeta23/ThmD/Sextuple/A1290/Chunks/Chunk*.lean'));ol=len(glob.glob('.lake/build/lib/lean/Zeta23/ThmD/Sextuple/A1290/Chunks/Chunk*.olean'));print(src-ol)")
echo "chunks missing: $missing"; [ "$missing" = "0" ] || exit 2
echo "== assembly chain"; LEAN_NUM_THREADS=6 "$LAKE" build +Zeta23.ThmD.Sextuple.A1290.LineDecimal > $L/a1290-assembly-build.log 2>&1; echo "assembly exit=$?"
grep -qE 'Build completed successfully' $L/a1290-assembly-build.log || { grep -E 'error' $L/a1290-assembly-build.log | head; exit 3; }
echo "== axiom audit"; LEAN_NUM_THREADS=4 "$LAKE" env lean Zeta23/ThmD/Sextuple/A1290/AxiomAudit.lean > $L/a1290-axiom-audit.log 2>&1; echo "axiom-audit exit=$?"
echo "== comparator"; LEAN_NUM_THREADS=4 "$LAKE" build Challenge.SextupleA1290 Solution.SextupleA1290 > $L/lake_comparator_sextuple_a1290.log 2>&1; echo "comparator exit=$?"
LEAN_NUM_THREADS=4 "$LAKE" env lean scripts/PrintAxioms/SextupleA1290.lean > $L/printaxioms_sextuple_a1290.log 2>&1; echo "printaxioms exit=$?"
echo "== root build"; LEAN_NUM_THREADS=6 "$LAKE" build > $L/a1290-root-build.log 2>&1; echo "root exit=$?"
echo "== audits"; bash certificates/sextuple/tools/run_audits.sh > /dev/null 2>&1; grep -E 'exit=|forbidden scan' $L/audit-report.txt
echo "== axiom summary"; cat $L/a1290-axiom-audit.log $L/printaxioms_sextuple_a1290.log | tr '\n' ' ' | sed "s/'Zeta23/\n'Zeta23/g; s/'sextuple/\n'sextuple/g" | grep -c 'depends on axioms: \[propext, Classical.choice, Quot.sound\]'
cat $L/a1290-axiom-audit.log $L/printaxioms_sextuple_a1290.log | grep -c sorryAx
