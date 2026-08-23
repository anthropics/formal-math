#!/bin/bash
# Post-build audits: axiom scan, forbidden-token scan, hashes. Writes bench/audit-report.txt
W=$(git -C "$(dirname "$0")" rev-parse --show-toplevel)
B=$W/certificates/sextuple/logs
OUT=$B/audit-report.txt
cd "$W" || exit 1
{
echo "# audit $(date -u +%Y-%m-%dT%H:%M:%SZ)"
echo "## git"; git rev-parse HEAD; git status --short --branch | head -20
echo "## axioms (lake env lean AxiomAudit.lean)"
LEAN_NUM_THREADS=4 lake env lean Zeta23/ThmD/Sextuple/AxiomAudit.lean 2>&1
echo "axiom-audit exit=$?"
echo "## forbidden scan"; $B/forbidden_scan.sh; echo "scan exit=$?"
echo "## hashes"
shasum -a 256 Zeta23/ThmD/Sextuple/Macro/*.lean Zeta23/ThmD/Sextuple/Certificate.lean Zeta23/ThmD/Sextuple/Unconditional.lean Zeta23/ThmD/Sextuple/LineDecimal.lean Zeta23/ThmD/Sextuple/AxiomAudit.lean
echo "chunks: $(ls Zeta23/ThmD/Sextuple/Macro/Chunks | wc -l | tr -d ' ') files, concatenated sha256 $(cat Zeta23/ThmD/Sextuple/Macro/Chunks/*.lean | shasum -a 256 | cut -d' ' -f1)"
echo "oleans: $(ls .lake/build/lib/lean/Zeta23/ThmD/Sextuple/Macro/Chunks/*.olean 2>/dev/null | wc -l | tr -d ' ')"
} > "$OUT" 2>&1
cat "$OUT"
