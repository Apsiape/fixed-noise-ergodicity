"""Generate Challenge.lean for the release package from the four statement files.

  Windows (development):  python -I -B scripts/make_challenge.py
      sources: the precedent release workspaces through \\\\wsl.localhost (read only) and this repository;
      writes ./Challenge.lean.
  WSL (release workspace): python3 -I -B scripts/make_challenge.py --package /opt/<workspace>/project
      sources: the vendored statement files under project/vendor/ and project/ForgettingNaturalRule/Statements.lean,
      each vendored one also compared byte for byte with its precedent workspace; writes project/Challenge.lean
      and ../evidence/FROZEN-STATEMENT.json.

Adapted from the noise-diagram release's `relay/make_challenge.py` (read only). Challenge.lean imports only
Mathlib (the Mathlib imports of the forgetting and hard-model statement files). It then contains, between
BEGIN/END markers:
  1. `FixedNoiseErgodicity/Statements.lean` byte for byte except its import lines (the natural-rule statements
     use `FNE.Tile`, `FNE.WangSet`, `FNE.Plane`, `FNE.TuringMachine` with its step, halting and `Primcodable`
     instances, and, through the noise-diagram statements, `FNE.flagLaw`, `FNE.WeakTendsto`);
  2. verbatim excerpts of `UndecidablePhaseDiagram/Statements.lean` (header, Section 2.2 "Turing machines",
     `UPD.Universal`), exactly as in the noise-diagram challenge (the noise-diagram statements use them);
  3. `UncomputableNoiseDiagram/Statements.lean` byte for byte except its two import lines;
  4. `ForgettingNaturalRule/Statements.lean` (frozen) byte for byte except its import line;
then the five holes of the release: `FNR.natural_classification`, `FNR.theorem_A`, `FNR.machine_corollary`,
`FNR.domino_reduction`, `FNR.domino_undecidable`.
Each copy is preceded by `run_cmd ... setMainModule` and by an emptied auxiliary-proof cache
(`Lean.Meta.auxLemmasExt`), as in the noise-diagram challenge. The forgetting copy and the hard-model excerpt
are elaborated with `bootstrap.genMatcherCode = false` inside a `section` (a fresh matcher cache, as in a
separate module): `FNE.run`, `UPD.Machine.run` and `UND.CA.run` all match on `0` / `t + 1`, and within one
file Lean reuses an identical matcher made earlier; the hard-model excerpt also gets
`backward.isDefEq.respectTransparency = false`, as in the noise-diagram challenge.

The script asserts the recorded sha256 of the four statement files (the three released ones and this core's
frozen one) and re-extracts every copy from the generated text.
"""
from pathlib import Path
import argparse, hashlib, json, re

ap = argparse.ArgumentParser()
ap.add_argument('--package', type=Path)
A = ap.parse_args()

REPO = Path(__file__).resolve().parents[1]
FILE = {'FNE': 'FixedNoiseErgodicity/Statements.lean', 'UPD': 'UndecidablePhaseDiagram/Statements.lean',
        'UND': 'UncomputableNoiseDiagram/Statements.lean', 'FNR': 'ForgettingNaturalRule/Statements.lean'}
CORE = {'FNE': 'FixedNoiseErgodicity', 'UPD': 'UndecidablePhaseDiagram', 'UND': 'UncomputableNoiseDiagram'}
PRECEDENT = {'FNE': '/opt/forgetting-arxiv-2026-11-10/project',
             'UPD': '/opt/undecidable-phase-diagram-arxiv-2026-11-11/project',
             'UND': '/opt/uncomputable-noise-diagram-arxiv-2026-11-12/project'}
if A.package:
    P = A.package.resolve()
    SRC = {k: P / 'vendor' / CORE[k] / FILE[k] for k in CORE}
    SRC['FNR'] = P / FILE['FNR']
    REF = {k: Path(PRECEDENT[k]) / FILE[k] for k in CORE}
    OUT = P / 'Challenge.lean'
else:
    WSL = Path(r'\\wsl.localhost\lean-comparator')
    SRC = {k: WSL / PRECEDENT[k].lstrip('/') / FILE[k] for k in CORE}
    SRC['FNR'] = REPO / FILE['FNR']
    REF = {}
    OUT = REPO / 'Challenge.lean'
FROZEN = {'FNE': '351c3058f66fc99235677f99d04f8b35af1d365f80153d9644c6b13d207b4879',
          'UPD': 'ef3ebe7fc60c792f1297dcf9a4596504f5a365de5e45012df84da227fa01482b',
          'UND': 'b5c9e965b2ffbb39d2817ab4c3a41b3a71d463cbe1a0f6f186a8cc8833d0aa2c',
          'FNR': '3e4f73e3bc4a71ac041e45186e4d992abcd294f33ad7cfe5f4c337b8c479b5d4'}
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
HOLES = [('natural_classification', 'NaturalClassification', 'Main.lean'),
         ('theorem_A', 'TheoremA', 'Reduction.lean'),
         ('machine_corollary', 'MachineCorollary', 'Reduction.lean'),
         ('domino_reduction', 'DominoReduction', 'Reduction.lean'),
         ('domino_undecidable', 'DominoUndecidable', 'Reduction.lean')]
holes = [f'theorem {n} : {t} := by sorry' for n, t, _ in HOLES]

header = '''/-
# Challenge (comparator) for the Lean core of the natural Wang rule: S. Douglas and N. Mghirbi,
# "Forgetting under noise is undecidable", v2.0.0 (Theorem D and Theorem A on ℤ⁶)

This file imports only Mathlib (the Mathlib imports of the forgetting and hard-model statement files) and
no module of the development or of the reused cores. Between BEGIN/END markers it copies, byte for byte:
the whole of `FixedNoiseErgodicity/Statements.lean` except its import lines; verbatim excerpts of
`UndecidablePhaseDiagram/Statements.lean` (its header lines, the block "Section 2.2: Turing machines" and
`UPD.Universal`, as in the noise-diagram challenge); the whole of `UncomputableNoiseDiagram/Statements.lean`
except its two import lines; and the whole of the frozen `ForgettingNaturalRule/Statements.lean` except its
import line. Nothing else defines a statement. The structural lines between the copies only open and close
sections, select the module name under which the copied definitions are recorded (`setMainModule`), empty
Lean's per-file cache of auxiliary proofs before each copy (`auxLemmasExt`), and set
`bootstrap.genMatcherCode = false` for the forgetting copy and the hard-model excerpt (with
`backward.isDefEq.respectTransparency = false` for the latter), restored by the enclosing `section`s. The
five holes at the end are the release targets, with the same binders: Theorem D
(`FNR.natural_classification`), Theorem A as printed (`FNR.theorem_A`), Corollary `nw:machine`
(`FNR.machine_corollary`), the domino reduction (`FNR.domino_reduction`) and Berger's theorem
(`FNR.domino_undecidable`). None of them has a hypothesis.
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
         '/-! ## 4. The statement file of this development (frozen) -/', '',
         SET_MAIN.format('ForgettingNaturalRule.Statements'), RESET_AUX, '',
         begin('FNR'), copies['FNR'], end_('FNR'), 'end', '',
         '/-! ## The five holes (the release targets) -/', '',
         SET_MAIN.format('Challenge'), '',
         'namespace FNR', '',
         *[h + '\n' for h in holes],
         'end FNR', '']
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
        'frozen_statement_file': {'path': FILE['FNR'], 'sha256': H(text['FNR']),
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
        'fnr_statements_lean_utf8': text['FNR'],
        'targets': [{'name': 'FNR.' + n, 'statement_utf8': f'theorem {n} : {t}', 'type': 'FNR.' + t,
                     'source': f'ForgettingNaturalRule/{m} (namespace FNR)', 'hypotheses': []}
                    for n, t, m in HOLES],
        'not_in_challenge': ['FNR.theorem_A_from_domino : FNR.TheoremAFromDomino (conditional form, Main.lean)',
                             'FNR.theorem_A_undecidable : FNR.TheoremAUndecidable (conditional form, Main.lean)',
                             'FNR.ergodicity_reduction : FNR.ErgodicityReduction (= FNR.theorem_A, Reduction.lean)',
                             'FNR.ergodicity_undecidable (Reduction.lean)'],
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
