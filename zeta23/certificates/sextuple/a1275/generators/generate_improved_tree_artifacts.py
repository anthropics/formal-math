#!/usr/bin/env python3
from __future__ import annotations
import hashlib, json, struct, sys, os
from pathlib import Path

def require(condition, message):
    if not condition:
        raise ValueError(message)
sys.setrecursionlimit(1000000)
sys.set_int_max_str_digits(0)
HERE = Path(os.environ.get('A1275_OUTPUT_DIR', str(Path(__file__).resolve().parent)))
RAW = Path(os.environ.get('A1275_RAW_DIR', '/Users/mdumitrean/Desktop/dev/aigent/math/prime/post-anthropic-rh-artifacts/checkers/sextuple-improvement/refined-A-0p01275'))
ART = HERE / 'tree-artifacts'
WORD_DIR = HERE / 'ImprovedWordData'
LEAF_BITS = 321
BLOCK_SIZE = 256
BLOCK_BYTES = LEAF_BITS * BLOCK_SIZE // 8
TABLE_COUNT = 272
SCALAR_COUNT = 1383
MAX_TOKENS = 100
FUEL = 90
BLOCKS_PER_MODULE = 25
CHUNKS_PER_MODULE = 100
ASSEMBLY_PER_MODULE = 100
EXPECTED_MANIFEST_SHA256 = '732a99cf5c4755ee18686f4a14669c61162bf6bdf87d7ca2d2564098e3346c30'
EXPECTED_STREAM_SHA256 = {'topology': 'cc1dc05c152a218d4a44466d102db703a60e819cd83eccaf4196fed19ba8352b', 'kinds': 'a2df050738a1bc4052da743ea26a8e8aa56373b7bcd23ac9b6aed3bfa5fd0aab', 'anchors': 'e6dbe9ca333f8757b5ba39ab62fd902e02662b5e412ad688d0890e7664677394', 'terms': '0f8c90f474e75f9dd41d29b4e2a2df77883250c8a1882258e62b6c7f28d6748f'}

def sha(p: Path) -> str:
    return hashlib.sha256(p.read_bytes()).hexdigest()

def canonical_json(obj) -> bytes:
    return (json.dumps(obj, sort_keys=True, separators=(',', ':')) + '\n').encode()

class Node:
    __slots__ = ('id', 't0', 'p0', 't1', 'p1', 'depth', 'axis', 'path', 'children', 'tokens')

def validate_manifest_fields(m):
    require(m['A'] == '51/4000' and m['B'] == '1094977/5000000000', 'wrong A/B')
    require(m['cutoff'] == '63750000/1094977', 'wrong cutoff')
    require(m['catalog_piece_count'] == TABLE_COUNT, 'wrong catalog count')
    require(m['scalar_certificate_count'] == SCALAR_COUNT, 'wrong scalar count')
    require(m['fuel'] == FUEL and m['maximum_depth'] + 1 == FUEL, 'wrong fuel/depth')
    require(m['full_stack_exhaustion'] is True, 'manifest lacks full stack exhaustion')

def validate_topology_words(m, words, tokens):
    require(len(words) == (m['token_count'] + 19) // 20, 'topology word count mismatch')
    require(len(tokens) == m['token_count'], 'topology token count mismatch')
    require(all(0 <= w < 2 ** 60 for w in words), 'topology word exceeds 60 physical bits')
    rem = m['token_count'] % 20
    if rem:
        require(words[-1] < 2 ** (3 * rem), 'nonzero final topology padding')
    require(all(0 <= token <= 5 for token in tokens), 'topology token outside terminal/axis range')

def load():
    mp = RAW / 'manifest.json'
    require(sha(mp) == EXPECTED_MANIFEST_SHA256, 'invariant line 42: sha(mp) == EXPECTED_MANIFEST_SHA256')
    m = json.loads(mp.read_text())
    validate_manifest_fields(m)
    names = {'topology': 'topology-u64le.bin', 'kinds': 'terminal-kinds-u8.bin', 'anchors': 'anchors-u16le.bin', 'terms': 'term-codes-u16le.bin'}
    for k, n in names.items():
        require(sha(RAW / n) == EXPECTED_STREAM_SHA256[k], 'invariant line 52: sha(RAW / n) == EXPECTED_STREAM_SHA256[k]')
    top = (RAW / names['topology']).read_bytes()
    kinds = (RAW / names['kinds']).read_bytes()
    anchors_b = (RAW / names['anchors']).read_bytes()
    terms_b = (RAW / names['terms']).read_bytes()
    require(len(top) == 8 * m['topology_word_count'], "invariant line 57: len(top) == 8 * m['topology_word_count']")
    require(len(kinds) == m['leaves'], "invariant line 58: len(kinds) == m['leaves']")
    words = list(struct.unpack('<' + 'Q' * m['topology_word_count'], top))
    tokens = [words[i // 20] >> 3 * (i % 20) & 7 for i in range(m['token_count'])]
    validate_topology_words(m, words, tokens)
    require(all((w < 2 ** 60 for w in words)), 'invariant line 61: all((w < 2 ** 60 for w in words))')
    rem = m['token_count'] % 20
    if rem:
        require(words[-1] < 2 ** (3 * rem), 'invariant line 63: words[-1] < 2 ** (3 * rem)')
    anchors = list(struct.unpack('<' + 'H' * (len(anchors_b) // 2), anchors_b))
    terms = list(struct.unpack('<' + 'H' * (len(terms_b) // 2), terms_b))
    require(len(anchors) == 5 * m['quadratic_leaves'], "invariant line 66: len(anchors) == 5 * m['quadratic_leaves']")
    require(len(terms) == 15 * m['quadratic_leaves'], "invariant line 67: len(terms) == 15 * m['quadratic_leaves']")
    return (m, words, tokens, kinds, anchors, terms)

def encode_leaves(m, kinds, anchors, terms):
    require(len(kinds) == m['leaves'], 'leaf kind length mismatch')
    require(len(anchors) == 5 * m['quadratic_leaves'], 'anchor length mismatch')
    require(len(terms) == 15 * m['quadratic_leaves'], 'term length mismatch')
    out = []
    q = 0
    piece = scalar = zero = refinement = 0
    for kind in kinds:
        require(kind in (0, 1), 'invariant line 73: kind in (0, 1)')
        if kind == 0:
            out.append(0)
            continue
        w = 1
        for i in range(5):
            x = anchors[5 * q + i]
            require(0 <= x <= 16384, 'anchor outside relative-resolution range 0..16384')
            w |= x << 1 + 16 * i
        for i in range(15):
            x = terms[15 * q + i]
            ok_piece = x < TABLE_COUNT
            ok_scalar = 32768 <= x < 32768 + SCALAR_COUNT
            ok_zero = x == 65535
            require(ok_piece or ok_scalar or ok_zero, 'invariant line 85: ok_piece or ok_scalar or ok_zero')
            piece += ok_piece
            scalar += ok_scalar
            zero += ok_zero
            refinement += 56 <= x < TABLE_COUNT
            w |= x << 1 + 16 * (5 + i)
        require(w & 1 == 1 and w < 2 ** LEAF_BITS, 'invariant line 89: w & 1 == 1 and w < 2 ** LEAF_BITS')
        out.append(w)
        q += 1
    require(q == m['quadratic_leaves'], "invariant line 91: q == m['quadratic_leaves']")
    require(refinement == m['refinement_term_count'], "invariant line 92: refinement == m['refinement_term_count']")
    require(scalar == m['scalar_term_count'] and zero == m['zero_term_count'], "invariant line 93: scalar == m['scalar_term_count'] and zero == m['zero_term_count']")
    require(piece + scalar + zero == 15 * q, 'invariant line 94: piece + scalar + zero == 15 * q')
    return (out, {'piece': piece, 'refinement': refinement, 'scalar': scalar, 'zero': zero})

def encode_blocks(leaves):
    blocks = []
    for start in range(0, len(leaves), BLOCK_SIZE):
        block = 0
        for j, w in enumerate(leaves[start:start + BLOCK_SIZE]):
            block |= w << LEAF_BITS * j
        require(block < 2 ** (LEAF_BITS * min(BLOCK_SIZE, len(leaves) - start)), 'invariant line 102: block < 2 ** (LEAF_BITS * min(BLOCK_SIZE, len(leaves) - start))')
        blocks.append(block)
    padding = -len(leaves) % BLOCK_SIZE
    if padding:
        require(blocks[-1] < 2 ** (LEAF_BITS * (len(leaves) % BLOCK_SIZE)), 'invariant line 105: blocks[-1] < 2 ** (LEAF_BITS * (len(leaves) % BLOCK_SIZE))')
    return (blocks, padding)

def validate_blocks(leaves, blocks, padding):
    require(len(blocks) == (len(leaves) + BLOCK_SIZE - 1) // BLOCK_SIZE, 'leaf block count mismatch')
    require(padding == (-len(leaves)) % BLOCK_SIZE, 'leaf padding count mismatch')
    require(all(block < 2 ** (LEAF_BITS * BLOCK_SIZE) for block in blocks), 'leaf block physical bound failure')
    if padding:
        valid = len(leaves) % BLOCK_SIZE
        require(blocks[-1] < 2 ** (LEAF_BITS * valid), 'nonzero final leaf padding')
        for slot in range(valid, BLOCK_SIZE):
            require(((blocks[-1] >> (LEAF_BITS * slot)) & (2 ** LEAF_BITS - 1)) == 0, 'nonzero padded leaf word')

def validate_root(root, maxdepth, nodes, tokens, kinds):
    require(root.t0 == 0 and root.p0 == 0, 'root does not start at zero cursors')
    require(root.t1 == len(tokens) and root.p1 == len(kinds), 'root cursor exhaustion mismatch')
    require(root.tokens == len(tokens) and nodes == len(tokens), 'root/node topology count mismatch')
    require(maxdepth + 1 == FUEL, 'root fuel/depth mismatch')

def build_tree(tokens, kinds):
    tc = pc = nid = 0
    maxdepth = 0

    def rec(depth, path):
        nonlocal tc, pc, nid, maxdepth
        require(tc < len(tokens), 'invariant line 112: tc < len(tokens)')
        n = Node()
        n.id = nid
        nid += 1
        n.t0 = tc
        n.p0 = pc
        n.depth = depth
        n.path = path
        n.children = []
        maxdepth = max(maxdepth, depth)
        tok = tokens[tc]
        tc += 1
        require(0 <= tok <= 5, 'invariant line 115: 0 <= tok <= 5')
        if tok:
            n.axis = tok - 1
            n.children = [rec(depth + 1, path + [(False, n.axis)]), rec(depth + 1, path + [(True, n.axis)])]
        else:
            n.axis = None
            require(pc < len(kinds), 'kind/payload underflow')
            require(kinds[pc] in (0, 1), 'invariant line 120: kinds[pc] in (0, 1)')
            pc += 1
        n.t1 = tc
        n.p1 = pc
        n.tokens = tc - n.t0
        return n
    root = rec(0, [])
    require(tc == len(tokens) and pc == len(kinds), 'invariant line 124: tc == len(tokens) and pc == len(kinds)')
    return (root, maxdepth, nid)

def partition(root):
    chunks = []
    internal = []

    def rec(n):
        if n.tokens <= MAX_TOKENS or not n.children:
            chunks.append(n)
        else:
            internal.append(n)
            rec(n.children[0])
            rec(n.children[1])
    rec(root)
    require(all((1 <= n.tokens <= MAX_TOKENS for n in chunks)), 'invariant line 134: all((1 <= n.tokens <= MAX_TOKENS for n in chunks))')
    require([n.t0 for n in chunks] == sorted((n.t0 for n in chunks)), 'invariant line 135: [n.t0 for n in chunks] == sorted((n.t0 for n in chunks))')
    covered = []
    for n in chunks:
        covered.extend(range(n.t0, n.t1))
    covered.extend((n.t0 for n in internal))
    require(sorted(covered) == list(range(root.t1)), 'invariant line 140: sorted(covered) == list(range(root.t1))')
    require(chunks[0].p0 == 0 and chunks[-1].p1 == root.p1, 'invariant line 142: chunks[0].p0 == 0 and chunks[-1].p1 == root.p1')
    require(all((a.p1 == b.p0 for a, b in zip(chunks, chunks[1:]))), 'invariant line 143: all((a.p1 == b.p0 for a, b in zip(chunks, chunks[1:])))')
    return (chunks, internal)

def make_plan(m, root, maxdepth, nodes, chunks):
    chunk_idx = {n.id: i for i, n in enumerate(chunks)}
    order = []

    def post(n):
        if n.id in chunk_idx:
            return
        post(n.children[0])
        post(n.children[1])
        order.append(n)
    post(root)
    node_idx = {n.id: i for i, n in enumerate(order)}

    def ref(n):
        return ['chunk', chunk_idx[n.id]] if n.id in chunk_idx else ['node', node_idx[n.id]]
    cdata = []
    for n in chunks:
        cdata.append({'id': n.id, 't0': n.t0, 'p0': n.p0, 't1': n.t1, 'p1': n.p1, 'depth': n.depth, 'tokens': n.tokens, 'payloads': n.p1 - n.p0, 'fuel': FUEL - n.depth, 'path': [[1 if up else 0, a] for up, a in n.path]})
    adata = []
    for n in order:
        adata.append({'id': n.id, 't0': n.t0, 'p0': n.p0, 't1': n.t1, 'p1': n.p1, 'depth': n.depth, 'axis': n.axis, 'fuel_after_split': FUEL - n.depth - 1, 'left': ref(n.children[0]), 'right': ref(n.children[1])})
    require(ref(root) == ['node', len(order) - 1], "invariant line 165: ref(root) == ['node', len(order) - 1]")
    return {'schema': 1, 'source_manifest_sha256': EXPECTED_MANIFEST_SHA256, 'constants': {'A': '51/4000', 'B': '1094977/5000000000', 'cutoff': '63750000/1094977', 'table_count': TABLE_COUNT, 'scalar_count': SCALAR_COUNT, 'fuel': FUEL, 'max_tokens_per_kernel_reduction': MAX_TOKENS}, 'tree': {'token_count': m['token_count'], 'leaf_count': m['leaves'], 'quadratic_leaves': m['quadratic_leaves'], 'tail_leaves': m['tail_leaves'], 'maximum_depth': maxdepth, 'node_count': nodes}, 'module_grouping': {'chunks_per_module': CHUNKS_PER_MODULE, 'assembly_per_module': ASSEMBLY_PER_MODULE}, 'chunks': cdata, 'assembly': adata, 'root': ref(root)}

def validate_plan_integrity(plan, root, chunks, internal):
    require(len(plan['chunks']) == len(chunks), 'plan chunk count mismatch')
    require(len(plan['assembly']) == len(internal), 'plan assembly count mismatch')
    chunk_idx = {n.id: i for i, n in enumerate(chunks)}
    order = []
    def post(n):
        if n.id in chunk_idx:
            return
        post(n.children[0]); post(n.children[1]); order.append(n)
    post(root)
    node_idx = {n.id: i for i, n in enumerate(order)}
    def ref(n):
        return ['chunk', chunk_idx[n.id]] if n.id in chunk_idx else ['node', node_idx[n.id]]
    for c, n in zip(plan['chunks'], chunks):
        require((c['id'], c['t0'], c['p0'], c['t1'], c['p1'], c['depth'], c['tokens'], c['payloads'], c['fuel']) ==
            (n.id, n.t0, n.p0, n.t1, n.p1, n.depth, n.tokens, n.p1 - n.p0, FUEL - n.depth), 'chunk cursor/fuel mismatch')
        require(c['path'] == [[1 if up else 0, axis] for up, axis in n.path], 'chunk path mismatch')
    require(len(order) == len(internal), 'assembly traversal mismatch')
    for a, n in zip(plan['assembly'], order):
        require((a['id'], a['t0'], a['p0'], a['t1'], a['p1'], a['depth'], a['axis'], a['fuel_after_split']) ==
            (n.id, n.t0, n.p0, n.t1, n.p1, n.depth, n.axis, FUEL - n.depth - 1), 'assembly cursor/axis/fuel mismatch')
        require(a['left'] == ref(n.children[0]) and a['right'] == ref(n.children[1]), 'assembly DAG edge mismatch')
    require(plan['root'] == ref(root), 'root DAG reference mismatch')

def emit_words(m, topology_words, blocks):
    WORD_DIR.mkdir(exist_ok=True)
    modules = []
    for start in range(0, len(blocks), BLOCKS_PER_MODULE):
        idx = start // BLOCKS_PER_MODULE
        vals = blocks[start:start + BLOCKS_PER_MODULE]
        name = f'ImprovedLeafBlocks{idx:03d}'
        modules.append(name)
        text = f'namespace Zeta23.ThmD.Sextuple.MacroPrototype\n\nset_option maxRecDepth 100000 in\ndef improvedLeafBlocksChunk{idx:03d} : Array Nat := #[\n  ' + ',\n  '.join(map(str, vals)) + '\n]\n\nend Zeta23.ThmD.Sextuple.MacroPrototype\n'
        (WORD_DIR / f'{name}.lean').write_text(text)
    imports = '\n'.join(['import ImprovedTreeReader', 'import Zeta23.ThmD.Sextuple.Macro.TreeReader'] + [f'import ImprovedWordData.{n}' for n in modules])
    append = ' ++\n    '.join((f'improvedLeafBlocksChunk{i:03d}' for i in range(len(modules))))
    text = f"{imports}\n\nnoncomputable section\nnamespace Zeta23.ThmD.Sextuple.MacroPrototype\nopen Zeta23.ThmD.Sextuple\n\ndef improvedTokenCount : ℕ := {m['token_count']}\ndef improvedLeafCount : ℕ := {m['leaves']}\n\nset_option maxRecDepth 100000 in\ndef improvedTopologyWords : Array Nat := #[\n  {',\n  '.join(map(str, topology_words))}\n]\n\ndef improvedLeafBlocks : Array Nat :=\n  {append}\n\ndef improvedTopologyStream : CursorStream AffineTreeToken :=\n  packedTopologyStream improvedTokenCount improvedTopologyWords\n\ndef improvedPayloadStream : CursorStream (AffineLeafPayload (MacroScalarLeaf 272 1383)) :=\n  improvedPackedLeafStream improvedLeafCount improvedLeafBlocks\n\ndef improvedRootBox : GapBox := initialGapBox 59\n\nend Zeta23.ThmD.Sextuple.MacroPrototype\nend\n"
    (HERE / 'ImprovedTreeWords.lean').write_text(text)
    layout = 'import ImprovedTreeWords\nimport Zeta23.ThmD.Sextuple.Macro.Layout\n\nset_option maxHeartbeats 0\nset_option maxRecDepth 1000000\n\nnamespace Zeta23.ThmD.Sextuple.MacroPrototype\n\nlemma improvedTopologyLayoutBool_check :\n    topologyLayoutBool improvedTokenCount improvedTopologyWords = true := by\n  decide +kernel\n\nlemma improvedLeafLayoutBool_check :\n    leafLayoutBool improvedLeafCount improvedLeafBlocks = true := by\n  decide +kernel\n\ntheorem improvedTopologyLayoutValid :\n    PackedTopologyLayoutValid improvedTokenCount improvedTopologyWords :=\n  topologyLayoutBool_sound improvedTopologyLayoutBool_check\n\ntheorem improvedLeafLayoutValid :\n    PackedLeafLayoutValid improvedLeafCount improvedLeafBlocks :=\n  leafLayoutBool_sound improvedLeafLayoutBool_check\n\n#print axioms improvedTopologyLayoutValid\n#print axioms improvedLeafLayoutValid\n\nend Zeta23.ThmD.Sextuple.MacroPrototype\n'
    (HERE / 'ImprovedLayout.lean').write_text(layout)
    return modules

def lean_path(path):
    items = [f"({('true' if up else 'false')}, ⟨{axis}, by decide⟩)" for up, axis in reversed(path)]
    return '[' + ', '.join(items) + ']'

def emit_calibration(plan):
    max_tokens = max((c['tokens'] for c in plan['chunks']))
    candidates = [(i, c) for i, c in enumerate(plan['chunks']) if c['tokens'] == max_tokens]
    i, c = max(candidates, key=lambda z: (z[1]['payloads'], -z[0]))
    path = [(bool(up), a) for up, a in c['path']]
    pexpr = lean_path(path)
    text = f"import ImprovedTreeWords\n\nset_option maxHeartbeats 0\nset_option maxRecDepth 100000\n\nnamespace Zeta23.ThmD.Sextuple.MacroPrototype\nopen Zeta23.ThmD.Sextuple\n\n/-- Calibration chunk {i}: exactly {c['tokens']} topology tokens, {c['payloads']} payloads. -/\ntheorem improvedChunkCalibration :\n    replayAffineTree improvedConcreteLeafCheck improvedTopologyStream improvedPayloadStream\n      {c['fuel']} {c['t0']} {c['p0']} (improvedPathBox improvedRootBox {pexpr}) =\n      some ({c['t1']}, {c['p1']}) := by\n  decide +kernel\n\n#print axioms improvedChunkCalibration\nend Zeta23.ThmD.Sextuple.MacroPrototype\n"
    (HERE / 'ImprovedChunkCalibration.lean').write_text(text)
    return (i, c)

def main():
    ART.mkdir(exist_ok=True)
    report_path = ART / 'generation-report.json'
    report_stage = ART / 'generation-report.json.new'
    report_stage.unlink(missing_ok=True)
    report_path.unlink(missing_ok=True)
    m, topology_words, tokens, kinds, anchors, terms = load()
    leaves, term_counts = encode_leaves(m, kinds, anchors, terms)
    blocks, padding = encode_blocks(leaves)
    validate_blocks(leaves, blocks, padding)
    binary = b''.join((x.to_bytes(BLOCK_BYTES, 'little') for x in blocks))
    require(len(binary) == len(blocks) * BLOCK_BYTES, 'physical payload byte length mismatch')
    root, maxdepth, nodes = build_tree(tokens, kinds)
    require(maxdepth == m['maximum_depth'] and FUEL == maxdepth + 1, "invariant line 287: maxdepth == m['maximum_depth'] and FUEL == maxdepth + 1")
    validate_root(root, maxdepth, nodes, tokens, kinds)
    chunks, internal = partition(root)
    plan = make_plan(m, root, maxdepth, nodes, chunks)
    validate_plan_integrity(plan, root, chunks, internal)
    bp = ART / 'leaf-blocks-10272le.bin'
    pp = ART / 'bounded-replay-plan.json'
    bp.write_bytes(binary)
    pp.write_bytes(canonical_json(plan))
    modules = emit_words(m, topology_words, blocks)
    cal_i, cal = emit_calibration(plan)
    report = {'schema': 1, 'status': 'PASS', 'generator_sha256': sha(Path(__file__)), 'source_manifest_sha256': EXPECTED_MANIFEST_SHA256, 'source_replay_report_sha256': sha(RAW / 'exact-replay-report.json'), 'catalog_sha256': m['refinements_sha256'], 'scalar_table_sha256': m['scalar_certificates_sha256'], 'raw_stream_sha256': EXPECTED_STREAM_SHA256, 'logical': {'token_count': m['token_count'], 'topology_word_count': len(topology_words), 'topology_physical_bytes': 8 * len(topology_words), 'topology_physical_sha256': EXPECTED_STREAM_SHA256['topology'], 'topology_final_valid_tokens': m['token_count'] % 20, 'topology_zero_padding_token_slots': -m['token_count'] % 20, 'leaf_count': len(leaves), 'quadratic_leaves': m['quadratic_leaves'], 'tail_leaves': m['tail_leaves']}, 'packed': {'leaf_word_bits': LEAF_BITS, 'leaf_block_size': BLOCK_SIZE, 'leaf_block_bytes': BLOCK_BYTES, 'leaf_block_count': len(blocks), 'final_valid_leaf_words': len(leaves) % BLOCK_SIZE, 'zero_padding_leaf_words': padding, 'physical_payload_bytes': len(binary), 'physical_payload_sha256': sha(bp)}, 'term_counts': term_counts, 'tree': {'node_count': nodes, 'maximum_depth': maxdepth, 'fuel': FUEL, 'full_cursor_exhaustion': root.t1 == len(tokens) and root.p1 == len(leaves)}, 'bounded_plan': {'max_tokens': MAX_TOKENS, 'chunk_count': len(chunks), 'assembly_node_count': len(internal), 'chunk_module_count': (len(chunks) + CHUNKS_PER_MODULE - 1) // CHUNKS_PER_MODULE, 'assembly_module_count': (len(internal) + ASSEMBLY_PER_MODULE - 1) // ASSEMBLY_PER_MODULE, 'plan_sha256': sha(pp), 'plan_bytes': pp.stat().st_size, 'calibration_chunk_index': cal_i, 'calibration_tokens': cal['tokens'], 'calibration_payloads': cal['payloads'], 'subtree_size_histogram': {str(k): sum((c['tokens'] == k for c in plan['chunks'])) for k in sorted({c['tokens'] for c in plan['chunks']})}, 'root_assembly_ref': plan['root']}, 'lean': {'word_data_module_count': len(modules), 'tree_words_sha256': sha(HERE / 'ImprovedTreeWords.lean'), 'layout_sha256': sha(HERE / 'ImprovedLayout.lean'), 'calibration_sha256': sha(HERE / 'ImprovedChunkCalibration.lean'), 'word_data_sha256': {n: sha(WORD_DIR / f'{n}.lean') for n in modules}}}
    report_bytes = canonical_json(report)
    with report_stage.open('wb') as handle:
        handle.write(report_bytes)
        handle.flush()
        os.fsync(handle.fileno())
    os.replace(report_stage, report_path)
    require(not report_stage.exists(), 'report staging file survived atomic publication')
    print(json.dumps(report, indent=2, sort_keys=True))
if __name__ == '__main__':
    main()
