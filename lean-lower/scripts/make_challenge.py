"""Generate the three-hole Mathlib-only Z4 challenge from public statement files.
Copied and adapted from the natural-rule release generator. All five statement
hashes are asserted; the four whole copies are reconstructed byte for byte
(except imports), and the hard-model excerpts are re-extracted and checked.
Run python -I -B scripts/make_challenge.py on Windows, or
python3 -I -B scripts/make_challenge.py --package . in the release workspace.
The file-by-file public source identity is recorded by relay/pack_public_cores.py.
"""
from pathlib import Path
import argparse, hashlib, json, re

ap = argparse.ArgumentParser()
ap.add_argument('--package', type=Path)
A = ap.parse_args()

REPO = Path(__file__).resolve().parents[1]
FILE = {'FNE': 'FixedNoiseErgodicity/Statements.lean', 'UPD': 'UndecidablePhaseDiagram/Statements.lean',
        'UND': 'UncomputableNoiseDiagram/Statements.lean', 'FNR': 'ForgettingNaturalRule/Statements.lean', 'FLD': 'ForgettingLower/Statements.lean'}
CORE = {'FNE': 'FixedNoiseErgodicity', 'UPD': 'UndecidablePhaseDiagram', 'UND': 'UncomputableNoiseDiagram', 'FNR': 'ForgettingNaturalRule'}
PUBLIC_ROOT = Path('C:/Infanox')
PUBLIC = {'FNE': PUBLIC_ROOT / 'fixed-noise-ergodicity-release/lean',
          'FNR': PUBLIC_ROOT / 'fixed-noise-ergodicity-release/lean-natural',
          'UND': PUBLIC_ROOT / 'uncomputable-noise-diagram-release/lean',
          'UPD': PUBLIC_ROOT / 'undecidable-phase-diagram-release/lean'}
if A.package:
    P = A.package.resolve()
    SRC = {k: P / 'vendor' / CORE[k] / FILE[k] for k in CORE}
    SRC['FLD'] = P / FILE['FLD']
    REF = {}
    OUT = P / 'Challenge.lean'
else:
    SRC = {k: PUBLIC[k] / FILE[k] for k in CORE}
    SRC['FLD'] = REPO / FILE['FLD']
    REF = {}
    OUT = REPO / 'Challenge.lean'
FROZEN = {'FNE': '351c3058f66fc99235677f99d04f8b35af1d365f80153d9644c6b13d207b4879',
          'UPD': 'ef3ebe7fc60c792f1297dcf9a4596504f5a365de5e45012df84da227fa01482b',
          'UND': 'b5c9e965b2ffbb39d2817ab4c3a41b3a71d463cbe1a0f6f186a8cc8833d0aa2c',
          'FNR': '3e4f73e3bc4a71ac041e45186e4d992abcd294f33ad7cfe5f4c337b8c479b5d4',
          'FLD': '58cb7388400f05f2986d2b2cc9154a99a554eed4b384f10c8809b706d3b244c4'}
H = lambda s: hashlib.sha256(s.encode()).hexdigest()

text = {k: p.read_bytes().decode('utf-8') for k, p in SRC.items()}
for k, h in FROZEN.items():
    assert H(text[k]) == h, f'{k}: sha256 {H(text[k])} differs from the frozen statement file'
for k, r in REF.items():
    assert r.read_bytes() == text[k].encode('utf-8'), f'{k}: vendored statement file differs from {r}'
lines = {k: t.split('\n') for k, t in text.items()}


def span(k, first, last):
    L = lines[k]
    i = [n for n, l in enumerate(L) if l == first]
    j = [n for n, l in enumerate(L) if l == last]
    assert len(i) == 1 and len(j) == 1 and i[0] <= j[0], (k, first, last, i, j)
    return i[0], j[0]


def decl(k, prefix):
    L = lines[k]
    d = [n for n, l in enumerate(L) if l.startswith(prefix)]
    assert len(d) == 1, (k, prefix, d)
    i = d[0]
    while not L[i].startswith('/--'):
        i -= 1
        assert L[i] != '', (k, prefix)
    j = d[0]
    while L[j + 1] != '':
        j += 1
    return i, j


UPD_EXCERPTS = [
    ('header: options, section, opens, namespace', span('UPD', 'set_option autoImplicit false', 'namespace UPD')),
    ('Section 2.2: UPD.Machine, State, Symbol, Cfg, step, start, run, HaltsOn',
     span('UPD', '/-! ## Section 2.2: Turing machines -/', 'end Machine')),
    ('UPD.Universal', decl('UPD', 'def Universal ')),
]


def without_imports(k, expected):
    L = lines[k]
    idx = [n for n, l in enumerate(L) if l.startswith('import ')]
    assert idx == list(range(idx[0], idx[-1] + 1)), (k, idx)
    assert [L[n] for n in idx] == expected, (k, [L[n] for n in idx])
    head, body = '\n'.join(L[:idx[0]]), '\n'.join(L[idx[-1] + 1:])
    assert head + '\n' + '\n'.join(L[n] for n in idx) + '\n' + body == text[k]
    return head + '\n' + body.rstrip('\n')


copies = {
    'FNE': without_imports('FNE', [l for l in lines['FNE'] if l.startswith('import ')]),
    'UND': without_imports('UND', ['import FixedNoiseErgodicity.Statements',
                                   'import UndecidablePhaseDiagram.Statements']),
    'FNR': without_imports('FNR', ['import UncomputableNoiseDiagram.Statements']),
    'FLD': without_imports('FLD', ['import ForgettingNaturalRule.Statements']),
}
imports = []
for k in ('FNE', 'UPD'):
    for l in lines[k]:
        if l.startswith('import ') and l not in imports:
            imports.append(l)
assert all(l.startswith('import Mathlib.') for l in imports), imports


def begin(k):
    return f'-- BEGIN verbatim copy of {FILE[k]} (the whole file except its import lines)'


def end_(k):
    return f'-- END verbatim copy of {FILE[k]}'


upd_recs = []
for what, (i, j) in UPD_EXCERPTS:
    body = '\n'.join(lines['UPD'][i:j + 1])
    b = f'-- BEGIN verbatim excerpt of {FILE["UPD"]}, lines {i + 1}-{j + 1} ({what})'
    e = f'-- END verbatim excerpt of {FILE["UPD"]}, lines {i + 1}-{j + 1}'
    upd_recs.append({'file': FILE['UPD'], 'what': what, 'first_line': i + 1, 'last_line': j + 1,
                     'begin_marker': b, 'end_marker': e, 'sha256': H(body), 'text_utf8': body})

SET_MAIN = 'run_cmd Lean.modifyEnv (fun env => env.setMainModule `{})'
RESET_AUX = 'run_cmd Lean.modifyEnv (fun env => Lean.Meta.auxLemmasExt.modifyState env fun _ => {})'

# The release targets (QB, 12 Nov 2026): hypothesis-free; name, statement, source module.
HOLES = [('z4_classification', 'Z4Classification', 'Main.lean'),
         ('z4_machine_corollary', 'Z4MachineCorollary', 'Reduction.lean'),
         ('z4_raw_undecidable', 'Z4RawUndecidable', 'Reduction.lean')]
holes = [f'theorem {n} : {t} := by sorry' for n, t, _ in HOLES]

header = '''/-
# Challenge for the natural Wang rule on Z4 (Theorem 12.5).
Imports only Mathlib. Verbatim statement copies and UPD excerpts are generated from
the four vendored public cores and the frozen FLD statement file. The module-name,
auxiliary-proof-cache and matcher-cache handling is copied from the natural-rule
release generator. The three final holes have no hypotheses.
-/'''

parts = [header, '\n'.join(imports), '',
         '/-! ## 1. The forgetting core\'s statement file -/', '',
         'section', '',
         'set_option bootstrap.genMatcherCode false', '',
         SET_MAIN.format('FixedNoiseErgodicity.Statements'), RESET_AUX, '',
         begin('FNE'), copies['FNE'], end_('FNE'), 'end', '', 'end', '',
         '/-! ## 2. From the hard-model core: `UPD.Machine`, `UPD.Machine.HaltsOn`, `UPD.Universal` -/', '',
         'section', '',
         'set_option backward.isDefEq.respectTransparency false',
         'set_option bootstrap.genMatcherCode false', '',
         SET_MAIN.format('UndecidablePhaseDiagram.Statements'), RESET_AUX, '',
         *[x for r in upd_recs for x in (r['begin_marker'], r['text_utf8'], r['end_marker'], '')],
         'end UPD', '', 'end', '', 'end', '',
         '/-! ## 3. The noise-diagram core\'s statement file -/', '',
         SET_MAIN.format('UncomputableNoiseDiagram.Statements'), RESET_AUX, '',
         begin('UND'), copies['UND'], end_('UND'), 'end', '',
         '/-! ## 4. The public natural-rule statement file -/', '',
         SET_MAIN.format('ForgettingNaturalRule.Statements'), RESET_AUX, '',
         begin('FNR'), copies['FNR'], end_('FNR'), 'end', '',
         '/-! ## 5. The frozen Z4 statement file -/', '',
         SET_MAIN.format('ForgettingLower.Statements'), RESET_AUX, '',
         begin('FLD'), copies['FLD'], end_('FLD'), 'end', '',
         '/-! ## The three holes (the release targets) -/', '',
         SET_MAIN.format('Challenge'), '',
         'namespace FLD', '',
         *[h + '\n' for h in holes],
         'end FLD', '']
out = '\n'.join(parts)

o = out.split('\n')
for k in copies:
    i, j = o.index(begin(k)), o.index(end_(k))
    assert '\n'.join(o[i + 1:j]) == copies[k], k
for r in upd_recs:
    i, j = o.index(r['begin_marker']), o.index(r['end_marker'])
    assert '\n'.join(o[i + 1:j]) == r['text_utf8'] and r['text_utf8'] in text['UPD']
assert out.count('sorry') == len(holes)
for bad in ['native_decide', 'implemented_by', '@[extern', 'decide +native']:
    assert bad not in out, bad
assert not re.search(r'^\s*axiom\s', out, re.M)
OUT.write_bytes(out.encode('utf-8'))
print('Challenge.lean', len(out.encode()), 'bytes, sha256', H(out), 'holes', len(holes))
print('statement files', {FILE[k]: H(text[k])[:16] for k in text})

if A.package:
    rec = {
        'challenge_sha256': H(out),
        'challenge_imports': [l.split()[1] for l in imports],
        'challenge_imports_only_mathlib': True,
        'frozen_statement_file': {'path': FILE['FLD'], 'sha256': H(text['FLD']),
                                  'note': 'frozen in session 3 (12 Nov 2026) after the blind fidelity read; '
                                          'recorded in STATUS.md as the statement of record'},
        'statement_files': {FILE[k]: {'sha256': H(text[k]), 'source': str(SRC[k]),
                                      'reference': str(REF[k]) if k in REF else None,
                                      'identical_to_reference': True if k in REF else None,
                                      'sha256_asserted': FROZEN[k]} for k in text},
        'copies': {FILE[k]: {'what': 'whole file except its import lines', 'sha256': H(copies[k]),
                             'reconstruction_check': 'head + import lines + body == file (asserted)'}
                   for k in copies},
        'excerpts': upd_recs,
        'fld_statements_lean_utf8': text['FLD'],
        'targets': [{'name': 'FLD.' + n, 'statement_utf8': f'theorem {n} : {t}', 'type': 'FLD.' + t,
                     'source': f'ForgettingLower/{m} (namespace FLD)', 'hypotheses': []}
                    for n, t, m in HOLES],
        'not_in_challenge': [],
        'auxiliary_proof_cache': RESET_AUX + ' before each copy: empties the local (not persisted) per-file cache '
                                 'of auxiliary proofs, as at the start of a separate module (noise-diagram release, '
                                 'auxiliary command (d), accepted by QB on 12 Nov 2026)',
        'options': {
            'forgetting_copy': ['bootstrap.genMatcherCode = false (fresh matcher cache, as in a separate module)'],
            'hard_model_excerpt': ['backward.isDefEq.respectTransparency = false (the option UndecidablePhaseDiagram/'
                                   'Statements.lean is compiled with)',
                                   'bootstrap.genMatcherCode = false (fresh matcher cache, as in a separate module)'],
            'scope': 'set inside sections that also enclose the copies; restored at their ends',
        },
        'independence': 'Only Mathlib imports; byte-identical copies/excerpts checked against the sources; no type_of%; '
                        'generated/private names aligned by selecting the original module (setMainModule) while '
                        'elaborating each copy.',
    }
    E = P.parent / 'evidence'
    E.mkdir(exist_ok=True)
    (E / 'FROZEN-STATEMENT.json').write_text(json.dumps(rec, indent=2, ensure_ascii=False) + '\n', encoding='utf-8')
    print('wrote', E / 'FROZEN-STATEMENT.json')
