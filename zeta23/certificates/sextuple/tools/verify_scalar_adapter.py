#!/usr/bin/env python3
"""Independent exact re-verification of the 871 MacroScalarCert checks.

Reimplements, literally from the Lean text:
  Interval.lean      : RatInterval.scale / RatInterval.add
  PieceCert.lean     : LowerPiece.absLower
  AffineAdapter.lean : wellSlope / wellOffset
  ScalarAdapter.lean : macroAffineOne / affineOneImage / macroModelMin /
                       MacroScalarSegment.check / scalarSegmentsCoverFrom /
                       MacroScalarCert.check
and cross-checks EnvelopeData.lean (56 pieces) against macro-data-exact.json and
ScalarData.lean (871 certs) against scalar-certificates.json.
"""
import json, re, sys, time, hashlib
from fractions import Fraction as F
from pathlib import Path

LEAN = Path(__file__).resolve().parents[3] / 'Zeta23' / 'ThmD' / 'Sextuple' / 'Macro'
ART = Path(__file__).resolve().parents[1]
t0 = time.monotonic()

def q(s):
    s = s.strip()
    if s.startswith('(') and s.endswith(')'): s = s[1:-1].strip()
    return F(s.replace(' ', ''))

NUM = r'\(?-?\d+(?:/\d+)?\)?'
def iv(txt):
    m = re.match(r'⟨\s*(' + NUM + r')\s*,\s*(' + NUM + r')\s*⟩', txt.strip())
    assert m, txt
    return (q(m.group(1)), q(m.group(2)))

# ---------------------------------------------------------------- Lean defs
def scale(c, i):                       # Interval.lean:28-29
    lo, hi = i
    return (c*lo, c*hi) if 0 <= c else (c*hi, c*lo)
def add(i, j):                         # Interval.lean:25
    return (i[0]+j[0], i[1]+j[1])
def absLower(i):                       # PieceCert.lean:39-40
    lo, hi = i
    if 0 <= lo: return lo
    if hi <= 0: return -hi
    return F(0)
def wellSlope(p):                      # AffineAdapter.lean:30-33
    return -p['m'] if p['side'] == 'left' else p['m']
def wellOffset(p):                     # AffineAdapter.lean:36-39
    return p['v'] + p['m']*p['q'] if p['side'] == 'left' else p['v'] - p['m']*p['q']
def macroAffineOne(p):                 # ScalarAdapter.lean:18-20  (base, weight, slope, offset)
    if p['ctor'] == 'base':
        return (p['a'], p['c'], F(1), -p['q'])
    return (F(0), F(2), wellSlope(p), wellOffset(p))
def affineOneImage(m, i):              # ScalarAdapter.lean:35-36
    base, weight, slope, offset = m
    return add(scale(slope, i), (offset, offset))
def macroModelMin(p, i):               # ScalarAdapter.lean:39-41
    m = macroAffineOne(p)
    return m[0] + m[1] * absLower(affineOneImage(m, i))**2
def segment_check(table, a, s):        # ScalarAdapter.lean:72-78
    box = s['box']; p = table[s['pieceIndex']]
    c1 = box[0] <= box[1]
    c2 = p['box'][0] <= box[0]
    c3 = box[1] <= p['box'][1]
    c4 = 0 <= macroAffineOne(p)[1]
    c5 = a <= macroModelMin(p, box)
    return (c1, c2, c3, c4, c5)
def coverFrom(cur, last, segs):        # ScalarAdapter.lean:93-97
    for s in segs:
        if not (s['box'][0] == cur and s['box'][0] <= s['box'][1]): return False
        cur = s['box'][1]
    return cur == last
def cert_check(table, cert):           # ScalarAdapter.lean:130-135
    return (cert['box'][0] <= cert['box'][1], 0 <= cert['a'], len(cert['segments']) != 0,
            coverFrom(cert['box'][0], cert['box'][1], cert['segments']),
            all(all(segment_check(table, cert['a'], s)) for s in cert['segments']))

# ---------------------------------------------------------------- parse EnvelopeData.lean
env = (LEAN/'EnvelopeData.lean').read_text()
pieces_lean = {}
for m in re.finditer(r'^def macroPiece(\d+) : MacroPiece := \.(base|well) \{(.*?)(?=\ndef |\nlemma |\n\n|\n#print)', env, re.M | re.S):
    n, ctor, body = int(m.group(1)), m.group(2), m.group(3)
    d = {'ctor': ctor}
    d['box'] = iv(re.search(r'box := (⟨[^⟩]*⟩)', body).group(1))
    if ctor == 'base':
        d['q'] = q(re.search(r'\bq := (' + NUM + ')', body).group(1))
        d['a'] = q(re.search(r'\ba := (' + NUM + ')', body).group(1))
        d['c'] = q(re.search(r'\bc := (' + NUM + ')', body).group(1))
        km = re.search(r'kind := \.(low|zero|numeric)', body); d['kind'] = km.group(1)
        if d['kind'] == 'numeric':
            cells = re.findall(r'\{ box := (⟨[^⟩]*⟩), turn := (\d+) \}', body)
            d['cells'] = [(iv(b), int(t)) for b, t in cells]
    else:
        d['side'] = re.search(r'side := \.(left|right)', body).group(1)
        d['positive'] = re.search(r'positive := (true|false)', body).group(1) == 'true'
        for k in ('q', 'v', 'm'):
            d[k] = q(re.search(r'\b' + k + r' := (' + NUM + ')', body).group(1))
        d['turn'] = int(re.search(r'turn := (\d+)', body).group(1))
    pieces_lean[n] = d
assert sorted(pieces_lean) == list(range(56)), sorted(pieces_lean)
table = [pieces_lean[i] for i in range(56)]

# cross-check against macro-data-exact.json
md = json.load(open(ART/'macro-data-exact.json'))['pieces']
assert len(md) == 56
piece_mismatch = []
for i, pj in enumerate(md):
    pl = table[i]
    ok = pl['box'] == (q(pj['lo']), q(pj['hi']))
    if pj['kind'] == 'low':
        ok &= pl['ctor']=='base' and pl['kind']=='low' and pl['q']==0 and pl['a']==F(1,4) and pl['c']==0 and q(pj['a'])==F(1,4)
    elif pj['kind'] == 'zero':
        ok &= pl['ctor']=='base' and pl['kind']=='zero' and pl['q']==0 and pl['a']==0 and pl['c']==0
    elif pj['kind'] == 'barrier':
        ok &= pl['ctor']=='base' and pl['kind']=='numeric' and pl['q']==0 and pl['c']==0 and pl['a']==q(pj['a'])
        ok &= [( (q(c['lo']),q(c['hi'])), c['turn']) for c in pj['cells']] == pl['cells']
    elif pj['kind'] == 'well':
        ok &= pl['ctor']=='well' and pl['side']==pj['side'] and pl['positive']==pj['positive'] \
              and pl['q']==q(pj['q']) and pl['v']==q(pj['v']) and pl['m']==q(pj['m']) and pl['turn']==pj['turn']
    else: ok = False
    if not ok: piece_mismatch.append(i)
# envelope tiling
env_tiling = all(table[i]['box'][1] == table[i+1]['box'][0] for i in range(55)) and table[0]['box'][0]==0 and table[55]['box'][1]==59

# stableMacroTable arms
sm = re.search(r'def stableMacroTable \(i : Fin 56\) : MacroPiece :=\n  match i.val with\n(.*?)\n\n', (LEAN/'ScalarData.lean').read_text(), re.S).group(1)
arms = re.findall(r'\| (\d+|_) => macroPiece(\d+)', sm)
stable_arms_ok = [(a, int(b)) for a, b in arms] == [(str(i), i) for i in range(55)] + [('_', 55)]
smc = re.search(r'theorem stableMacroTable_check \(i : Fin 56\).*?fin_cases i\n(.*?)\n\n', (LEAN/'ScalarData.lean').read_text(), re.S).group(1)
stable_check_ok = [int(x) for x in re.findall(r'· exact macroPiece(\d+)_check', smc)] == list(range(56))

# ---------------------------------------------------------------- parse ScalarData.lean
sd = (LEAN/'ScalarData.lean').read_text()
certs_lean = {}
for m in re.finditer(r'^def scalarCert(\d+) : MacroScalarCert 56 := \{\n  box := (⟨[^⟩]*⟩)\n  a := (' + NUM + r')\n  segments := \[\n(.*?)\n  \]\n\}', sd, re.M | re.S):
    n = int(m.group(1))
    segs = re.findall(r'\{ box := (⟨[^⟩]*⟩), pieceIndex := (\d+) \}', m.group(4))
    certs_lean[n] = {'box': iv(m.group(2)), 'a': q(m.group(3)),
                     'segments': [{'box': iv(b), 'pieceIndex': int(k)} for b, k in segs]}
    assert len(segs) == m.group(4).count('{ box'), n
assert sorted(certs_lean) == list(range(871)), (len(certs_lean), 'parse count')
assert len(re.findall(r'^def scalarCert\d+ ', sd, re.M)) == 871

# lemma scripts: one per cert, simp set mentions exactly the pieces used
lemma_ok = 0; lemma_bad = []
for m in re.finditer(r'^lemma scalarCert(\d+)_check : scalarCert(\d+)\.check stableMacroTable = true := by\n  norm_num \[scalarCert(\d+), MacroScalarCert\.check, MacroScalarSegment\.check,\n    scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage,\n    RatInterval\.scale, RatInterval\.add, LowerPiece\.absLower, MacroPiece\.box,\n    wellSlope, wellOffset, List\.cons_ne_nil, stableMacroTable, ((?:macroPiece\d+(?:, )?)+)\]', sd, re.M):
    a, b, c = int(m.group(1)), int(m.group(2)), int(m.group(3))
    used = sorted(int(x) for x in re.findall(r'macroPiece(\d+)', m.group(4)))
    need = sorted({s['pieceIndex'] for s in certs_lean[a]['segments']})
    if a == b == c and used == need: lemma_ok += 1
    else: lemma_bad.append(a)
assert len(re.findall(r'^lemma scalarCert\d+_check', sd, re.M)) == 871

# scalarCertTable arms and fin_cases order
tbl = re.search(r'def scalarCertTable \(i : Fin 871\) : MacroScalarCert 56 :=\n  match i.val with\n(.*?)\n\n', sd, re.S).group(1)
arms = re.findall(r'\| (\d+|_) => scalarCert(\d+)', tbl)
table_arms_ok = [(a, int(b)) for a, b in arms] == [(str(i), i) for i in range(870)] + [('_', 870)]
tc = re.search(r'theorem scalarCertTable_check \(i : Fin 871\) :\n    \(scalarCertTable i\)\.check stableMacroTable = true := by\n  fin_cases i\n(.*?)\n\n', sd, re.S).group(1)
table_check_ok = [int(x) for x in re.findall(r'· exact scalarCert(\d+)_check', tc)] == list(range(871))

# ---------------------------------------------------------------- JSON cross-check
cj = json.load(open(ART/'macro-scalar-tree'/'scalar-certificates.json'))
assert cj['data_sha256'] == hashlib.sha256((ART/'macro-data-exact.json').read_bytes()).hexdigest()
cjs = cj['certificates']; assert len(cjs) == 871
json_mismatch = []
for i, c in enumerate(cjs):
    L = certs_lean[i]
    ok = L['box'] == (q(c['lo']), q(c['hi'])) and L['a'] == q(c['a']) and len(L['segments']) == len(c['segments'])
    if ok:
        for sl, sj in zip(L['segments'], c['segments']):
            ok &= sl['box'] == (q(sj['lo']), q(sj['hi'])) and sl['pieceIndex'] == sj['piece_index']
    if not ok: json_mismatch.append(i)

# ---------------------------------------------------------------- exact checks (on the Lean literals)
A, B = F(1, 80), F(1094977, 5000000000)
CUTOFF = A / B
macroCutoff = F(62500000, 1094977)
counts = dict(certs=0, segments=0, cover_ok=0, inside_piece_ok=0, model_min_ok=0, a_pos=0, a_nonneg=0, lo_le_hi=0,
              weight_nonneg=0, cert_check_true=0, py_model_min_eq=0, a_eq_min=0, hi_le_cutoff=0,
              seg_is_full_intersection=0, well_segments=0, base_segments=0, tight_segments=0)
fails = []
min_slack = None; min_slack_cert = None
def py_model_min(p, lo, hi):   # replay_exact_5d_bnb.model_min on the generator's Piece conversion
    if p['ctor'] == 'base': qq, a, c = p['q'], p['a'], p['c']
    else:
        e, v, m = p['q'], p['v'], p['m']
        qq = e + v/m if p['side'] == 'left' else e - v/m; a = F(0); c = 2*m*m
    point = qq if lo <= qq <= hi else (lo if qq < lo else hi)
    return a + c*(point - qq)**2
for i in range(871):
    c = certs_lean[i]; counts['certs'] += 1
    lo, hi = c['box']; a = c['a']
    if lo <= hi: counts['lo_le_hi'] += 1
    if a > 0: counts['a_pos'] += 1
    if a >= 0: counts['a_nonneg'] += 1
    if hi <= CUTOFF: counts['hi_le_cutoff'] += 1
    if coverFrom(lo, hi, c['segments']): counts['cover_ok'] += 1
    else: fails.append((i, 'cover'))
    mins = []
    for s in c['segments']:
        counts['segments'] += 1
        p = table[s['pieceIndex']]
        c1, c2, c3, c4, c5 = segment_check(table, a, s)
        if c2 and c3: counts['inside_piece_ok'] += 1
        else: fails.append((i, 'inside', s))
        if c4: counts['weight_nonneg'] += 1
        mm = macroModelMin(p, s['box']); mins.append(mm)
        if c5: counts['model_min_ok'] += 1
        else: fails.append((i, 'model_min', s, mm, a))
        if mm == py_model_min(p, *s['box']): counts['py_model_min_eq'] += 1
        if p['ctor'] == 'well': counts['well_segments'] += 1
        else: counts['base_segments'] += 1
        # segment equals the full intersection of the cert box with the piece box?
        if s['box'] == (max(lo, p['box'][0]), min(hi, p['box'][1])): counts['seg_is_full_intersection'] += 1
        slack = mm - a
        if min_slack is None or slack < min_slack: min_slack, min_slack_cert = slack, (i, s['pieceIndex'])
        if slack == 0: counts['tight_segments'] += 1
    if min(mins) == a: counts['a_eq_min'] += 1
    if all(cert_check(table, c)): counts['cert_check_true'] += 1
    else: fails.append((i, 'cert_check', cert_check(table, c)))

elapsed = time.monotonic() - t0
report = dict(
    elapsed_seconds=round(elapsed, 3),
    pieces_parsed=len(pieces_lean), piece_json_mismatches=piece_mismatch, envelope_tiles_0_59=env_tiling,
    stableMacroTable_arms_ok=stable_arms_ok, stableMacroTable_check_order_ok=stable_check_ok,
    scalarCertTable_arms_ok=table_arms_ok, scalarCertTable_check_order_ok=table_check_ok,
    lemma_scripts_ok=lemma_ok, lemma_scripts_bad=lemma_bad,
    json_cert_mismatches=json_mismatch,
    macroCutoff_equals_A_over_B=(macroCutoff == CUTOFF), CUTOFF=str(CUTOFF),
    counts=counts, failures=fails[:20], failure_count=len(fails),
    min_slack=str(min_slack), min_slack_float=float(min_slack), min_slack_cert=min_slack_cert,
    segments_per_cert=dict(min=min(len(c['segments']) for c in certs_lean.values()),
                           max=max(len(c['segments']) for c in certs_lean.values())),
    a_min=str(min(c['a'] for c in certs_lean.values())), a_max=str(max(c['a'] for c in certs_lean.values())),
    sha256=dict(ScalarData=hashlib.sha256((LEAN/'ScalarData.lean').read_bytes()).hexdigest(),
                EnvelopeData=hashlib.sha256((LEAN/'EnvelopeData.lean').read_bytes()).hexdigest(),
                scalar_certificates_json=hashlib.sha256((ART/'macro-scalar-tree'/'scalar-certificates.json').read_bytes()).hexdigest(),
                macro_data_exact_json=hashlib.sha256((ART/'macro-data-exact.json').read_bytes()).hexdigest()),
)
out = Path(__file__).with_name('verify_scalar_adapter_report.json')
out.write_text(json.dumps(report, indent=2, default=str) + '\n')
print(json.dumps(report, indent=2, default=str))
