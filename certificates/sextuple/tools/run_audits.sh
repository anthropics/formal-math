#!/bin/bash
# Post-build audits: axiom scan, forbidden-token scan, hashes. Writes bench/audit-report.txt
W=$(git -C "$(dirname "$0")" rev-parse --show-toplevel)
B=$W/certificates/sextuple/logs
T=$W/certificates/sextuple/tools
LAKE=${LAKE:-$(command -v lake || echo "$HOME/.elan/bin/lake")}
OUT=$B/audit-report.txt
cd "$W" || exit 1
{
echo "# audit $(date -u +%Y-%m-%dT%H:%M:%SZ)"
echo "## git"; git rev-parse HEAD; git status --short --branch | head -20
echo "## axioms (lake env lean AxiomAudit.lean)"
LEAN_NUM_THREADS=4 "$LAKE" env lean Zeta23/ThmD/Sextuple/AxiomAudit.lean 2>&1
echo "axiom-audit exit=$?"
echo "## axioms A1275 (lake env lean A1275/AxiomAudit.lean)"
LEAN_NUM_THREADS=4 "$LAKE" env lean Zeta23/ThmD/Sextuple/A1275/AxiomAudit.lean 2>&1
echo "axiom-audit-a1275 exit=$?"
echo "## axioms A1285 (lake env lean A1285/AxiomAudit.lean)"
LEAN_NUM_THREADS=4 "$LAKE" env lean Zeta23/ThmD/Sextuple/A1285/AxiomAudit.lean 2>&1
echo "axiom-audit-a1285 exit=$?"
echo "## axioms A1290 (lake env lean A1290/AxiomAudit.lean)"
LEAN_NUM_THREADS=4 "$LAKE" env lean Zeta23/ThmD/Sextuple/A1290/AxiomAudit.lean 2>&1
echo "axiom-audit-a1290 exit=$?"
echo "## forbidden scan"; "$T/forbidden_scan.sh"; echo "scan exit=$?"
echo "## hashes"
shasum -a 256 Zeta23/ThmD/Sextuple/Macro/*.lean Zeta23/ThmD/Sextuple/Certificate.lean Zeta23/ThmD/Sextuple/Unconditional.lean Zeta23/ThmD/Sextuple/LineDecimal.lean Zeta23/ThmD/Sextuple/AxiomAudit.lean
echo "chunks: $(ls Zeta23/ThmD/Sextuple/Macro/Chunks | wc -l | tr -d ' ') files, concatenated sha256 $(cat Zeta23/ThmD/Sextuple/Macro/Chunks/*.lean | shasum -a 256 | cut -d' ' -f1)"
echo "oleans: $(ls .lake/build/lib/lean/Zeta23/ThmD/Sextuple/Macro/Chunks/*.olean 2>/dev/null | wc -l | tr -d ' ')"
echo "## A1275 hashes"
shasum -a 256 Zeta23/ThmD/Sextuple/A1275/*.lean Zeta23/ThmD/Sextuple/A1275/WordData/*.lean
echo "A1275 chunks: $(ls Zeta23/ThmD/Sextuple/A1275/Chunks | wc -l | tr -d ' ') files, concatenated sha256 $(cat Zeta23/ThmD/Sextuple/A1275/Chunks/*.lean | shasum -a 256 | cut -d' ' -f1)"
echo "A1275 parts: $(ls Zeta23/ThmD/Sextuple/A1275/Assembly | wc -l | tr -d ' ') files, concatenated sha256 $(cat Zeta23/ThmD/Sextuple/A1275/Assembly/*.lean | shasum -a 256 | cut -d' ' -f1)"
echo "A1275 chunk oleans: $(ls .lake/build/lib/lean/Zeta23/ThmD/Sextuple/A1275/Chunks/*.olean 2>/dev/null | wc -l | tr -d ' ')"
echo "## A1285 hashes"
shasum -a 256 Zeta23/ThmD/Sextuple/A1285/*.lean
echo "A1285 word data: $(ls Zeta23/ThmD/Sextuple/A1285/WordData | wc -l | tr -d ' ') files, concatenated sha256 $(cat Zeta23/ThmD/Sextuple/A1285/WordData/*.lean | shasum -a 256 | cut -d' ' -f1)"
echo "A1285 chunks: $(ls Zeta23/ThmD/Sextuple/A1285/Chunks | wc -l | tr -d ' ') files, concatenated sha256 $(find Zeta23/ThmD/Sextuple/A1285/Chunks -name '*.lean' | sort | xargs cat | shasum -a 256 | cut -d' ' -f1)"
echo "A1285 parts: $(ls Zeta23/ThmD/Sextuple/A1285/Assembly | wc -l | tr -d ' ') files, concatenated sha256 $(find Zeta23/ThmD/Sextuple/A1285/Assembly -name '*.lean' | sort | xargs cat | shasum -a 256 | cut -d' ' -f1)"
echo "A1285 chunk oleans: $(find .lake/build/lib/lean/Zeta23/ThmD/Sextuple/A1285/Chunks -name '*.olean' 2>/dev/null | wc -l | tr -d ' ')"
echo "## A1290 hashes"
shasum -a 256 Zeta23/ThmD/Sextuple/A1290/*.lean
for d in WordData Chunks Assembly; do echo "A1290 $d: $(ls Zeta23/ThmD/Sextuple/A1290/$d | wc -l | tr -d ' ') files, concatenated sha256 $(find Zeta23/ThmD/Sextuple/A1290/$d -name '*.lean' | sort | xargs cat | shasum -a 256 | cut -d' ' -f1)"; done
echo "A1290 chunk oleans: $(find .lake/build/lib/lean/Zeta23/ThmD/Sextuple/A1290/Chunks -name '*.olean' 2>/dev/null | wc -l | tr -d ' ')"
} > "$OUT" 2>&1
cat "$OUT"
