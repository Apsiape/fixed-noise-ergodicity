"""Collect the release evidence (run in WSL with python3 -I -B after build, comparator, export, kernels).
(Adapted from the noise-diagram relay's make_evidence.py.) Writes evidence/{BUILD,COMPARATOR,KERNEL-REPLAY,
AXIOM-AUDIT,SOURCE-AUDIT,CHOICES,ORIGINAL-SOURCE,BINARY-DIGESTS,DEPENDENCY-CHECK,VENDOR-CORES}.json,
evidence/AXIOMS.txt and evidence/AXIOMS-DEV-AUDIT.txt. FROZEN-STATEMENT.json is written by make_challenge.py.
Session 3b: the forgetting and hard-model cores are vendored from their PUBLIC releases' lean/ folders
(public-cores-receipt.json, written by relay/pack_public_cores.py); VENDOR-CORES.json checks the vendored trees
against those releases file by file and compares the rebuilt objects with the precedent relays'.
"""
from pathlib import Path
import hashlib, json, re, subprocess, time

D = Path(__file__).resolve().parent   # the release workspace (this script sits at its root)
P, O, E, R, K = D / 'project', D / 'original', D / 'evidence', D / 'results', D / 'kernels'
F = Path('/opt/forgetting-arxiv-2026-11-10')
U = Path('/opt/undecidable-phase-diagram-arxiv-2026-11-11')
N = Path('/opt/uncomputable-noise-diagram-arxiv-2026-11-12')
DEV_UND = Path('/opt/uncomputable-noise-diagram-lean/project')
DEV_FNR = Path('/opt/forgetting-natural-rule-lean/project')
S3 = Path('/opt/forgetting-natural-rule-arxiv-2026-11-12')   # the session-3 workspace (relay trees), kept as its record
E.mkdir(exist_ok=True)
COMMIT = '386de0d'
ML = '56a005855ea17e0b0958f73ec801ae140b0a1679'
FROZEN_SHA = '3e4f73e3bc4a71ac041e45186e4d992abcd294f33ad7cfe5f4c337b8c479b5d4'
SESSION_START = '2026-11-12 11:36:00'   # WSL clock; session 3b began after the session-3 commit dac2a90 (11:36:00)
DEPS = ['plausible', 'LeanSearchClient', 'importGraph', 'proofwidgets', 'aesop', 'Qq', 'batteries', 'Cli', 'mathlib']
# the precedent relay workspaces (whose objects the development build linked against); compared, not vendored,
# for the forgetting and hard-model cores
CORES = {'FixedNoiseErgodicity': F / 'project', 'UndecidablePhaseDiagram': U / 'project',
         'UncomputableNoiseDiagram': N / 'project'}
PUBLIC = json.loads((D / 'public-cores-receipt.json').read_text())['cores']
FINAL = ['FNR.natural_classification', 'FNR.theorem_A', 'FNR.machine_corollary', 'FNR.domino_reduction',
         'FNR.domino_undecidable']
TYPES = {'FNR.natural_classification': 'FNR.NaturalClassification', 'FNR.theorem_A': 'FNR.TheoremA',
         'FNR.machine_corollary': 'FNR.MachineCorollary', 'FNR.domino_reduction': 'FNR.DominoReduction',
         'FNR.domino_undecidable': 'FNR.DominoUndecidable'}


def sha_file(p):
    h = hashlib.sha256()
    with open(p, 'rb') as f:
        for b in iter(lambda: f.read(1 << 20), b''):
            h.update(b)
    return h.hexdigest()


def strip_comments(text):
    """Blank out comments (nested /- -/, --) and string literals, keeping line structure (as sorry_census.py)."""
    out, i, n, depth = [], 0, len(text), 0
    while i < n:
        c = text[i]
        if depth == 0 and text.startswith('--', i):
            j = text.find('\n', i)
            j = n if j < 0 else j
            out.append(' ' * (j - i)); i = j; continue
        if text.startswith('/-', i):
            depth += 1; out.append('  '); i += 2; continue
        if depth > 0 and text.startswith('-/', i):
            depth -= 1; out.append('  '); i += 2; continue
        if depth > 0:
            out.append('\n' if c == '\n' else ' '); i += 1; continue
        if c == '"':
            j = i + 1
            while j < n and text[j] != '"':
                j += 2 if text[j] == '\\' else 1
            seg = text[i:j + 1]
            out.append(''.join('\n' if ch == '\n' else ' ' for ch in seg)); i = j + 1; continue
        out.append(c); i += 1
    return ''.join(out)


def dump(name, obj):
    (E / name).write_text(json.dumps(obj, indent=2, ensure_ascii=False) + '\n', encoding='utf-8')


version = subprocess.check_output([str(D / 'toolchain/bin/lean'), '--version'], text=True).strip()
mods = json.loads((P / 'scripts/modules.json').read_text())
pkg_mods = mods + ['Challenge', 'Solution', 'Audit']

# ---------------- BUILD.json
hist = [json.loads(l) for l in (P / '.lake/replay/history.ndjson').read_text().splitlines() if l.strip()]
end_first = next(i for i, r in enumerate(hist) if r['module'] == 'Audit' and r['exit'] == 0)
fresh, later = hist[:end_first + 1], hist[end_first + 1:]
final = {}
for r in hist:
    if r['exit'] == 0:
        final[r['module']] = r
core_mods = sorted({r['module'] for r in fresh if r['kind'] == 'core'})
cache = json.loads((P / '.lake/replay/completed.json').read_text())
missing = [m for m in pkg_mods if m not in final]
dev_olean = []
for m in mods:
    rel = m.replace('.', '/') + '.olean'
    a, b = P / '.lake/build/lib/lean' / rel, DEV_FNR / '.lake/build/lib/lean' / rel
    dev_olean.append([m, b.is_file() and a.is_file() and sha_file(a) == sha_file(b)])
build = {
    'status': 'PASS' if not missing and all(r['exit'] == 0 for r in fresh) and all(m in cache for m in pkg_mods) else 'FAIL',
    'lean_version': version, 'mathlib_commit': ML,
    'source_commit': COMMIT,
    'clean_copy': 'project/ = git archive of the source commit (no build outputs), plus the package files; the three '
                  'cores vendored as sources under vendor/: the forgetting core (whole) and the hard-model core as the '
                  'lean/ folders of their public releases v1.4.0 and v1.2.0, the noise-diagram core as its release '
                  'package workspace (no public Lean release yet); no object of the development or of the cores was '
                  'reused; LEAN_PATH = this package\'s .lake/build/lib/lean and the nine pinned dependency packages only',
    'project_modules': len(mods), 'package_modules': len(pkg_mods), 'core_modules_compiled': len(core_mods),
    'core_modules_compiled_by_core': {c: sum(1 for m in core_mods if m.split('.')[0] == c) for c in CORES},
    'core_modules': core_mods,
    'one_compiler_at_a_time': True, 'lean_heap_MiB': 5000, 'lean_threads': 1, 'timeout_seconds_per_module': 1800,
    'linux_process_tree_stop_rss_bytes': 9000000000,
    'peak_observed_tree_rss_bytes': max(r['peak_tree_bytes'] for r in hist),
    'minimum_available_before_build_bytes': min(r['free_before_bytes'] for r in hist),
    'memory_floor_bytes': 8 * 1024 ** 3,
    'module_options': {'UndecidablePhaseDiagram.Statements': ['-Dbackward.isDefEq.respectTransparency=false']},
    'records_note': 'Each peak is the cumulative process-tree peak of its replay invocation, hence an upper bound for '
                    'the module. free_before_bytes = min(Linux MemAvailable, Windows host heartbeat ullAvailPhys). '
                    'fresh_full_replay = one replay from an empty build directory (no --resume) of every module '
                    'reachable from the package roots; later_records = any module rebuilt afterwards.',
    'missing_modules': missing,
    'fresh_full_replay_records': len(fresh),
    'fresh_full_replay_all_exit_0': all(r['exit'] == 0 for r in fresh),
    'fresh_full_replay_seconds_total': round(sum(r['seconds'] for r in fresh), 3),
    'fresh_full_replay_warnings_total': sum(r.get('warnings', 0) for r in fresh),
    'fresh_full_replay_longest': max(fresh, key=lambda r: r['seconds'])['module'],
    'development_oleans_byte_identical_to_dev_build': dev_olean,
    'development_oleans_note': f'each .olean of the development compiled here against the one of the development '
                               f'build {DEV_FNR} (which linked the precedent cores\' prebuilt objects)',
    'later_records': later,
    'final_by_module': {m: final[m] for m in [*core_mods, *pkg_mods] if m in final},
}
dump('BUILD.json', build)

# ---------------- COMPARATOR.json
cr = json.loads((R / 'comparator-receipt.json').read_text())
inv = [json.loads(l) for l in (D / 'bwrap-invocations.ndjson').read_text().splitlines() if l.strip()]
cfg = json.loads((P / 'comparator.json').read_text())
log = (R / 'comparator.log').read_text(errors='replace')
challenge = (P / 'Challenge.lean').read_text(encoding='utf-8')
# imports from the comment-stripped text: the header docstring has a wrapped line starting with "import"
cimps = re.findall(r'^import\s+(\S+)', strip_comments(challenge), re.M)
cr.update({
    'date_client': time.strftime('%Y-%m-%d'), 'mathlib_commit': ML,
    'comparator_command': 'lake comparator --config comparator.json',
    'theorem_names': cfg['theorem_names'], 'permitted_axioms': cfg['permitted_axioms'],
    'sandbox_observed': len(inv) > 0 and all('--unshare-all' in i['arguments'] for i in inv),
    'sandbox_invocations': len(inv),
    'sandbox_network_shared_invocations': sum('--share-net' in i['arguments'] for i in inv),
    'sandbox_invocation_commands': [i['arguments'][i['arguments'].index('--') + 1:] for i in inv],
    'default_kernel_accepts': 'Lean default kernel accepts the solution' in log,
    'comparator_verdict_line': 'Your solution is okay!' if 'Your solution is okay!' in log else None,
    'challenge_imports': cimps, 'challenge_imports_only_mathlib': all(i.startswith('Mathlib.') for i in cimps),
    'challenge_sha256': sha_file(P / 'Challenge.lean'), 'solution_sha256': sha_file(P / 'Solution.lean'),
    'transparent_definition_copy': True,
    'log': 'results/comparator.log', 'sandbox_invocation_log': 'bwrap-invocations.ndjson',
})
cr['status'] = 'PASS' if cr['exit'] == 0 and cr['default_kernel_accepts'] and cr['comparator_verdict_line'] and cr['sandbox_observed'] else 'FAIL'
dump('COMPARATOR.json', cr)

# ---------------- KERNEL-REPLAY.json
xr = json.loads((R / 'export-receipt.json').read_text())
kr = {'export_sha256': xr['sha256'], 'export_bytes': xr['bytes'], 'export_receipt': 'results/export-receipt.json',
      'export_command': xr['command'], 'export_lean_path': xr.get('lean_path'), 'export_seconds': xr['seconds'],
      'export_peak_tree_rss_bytes': xr['peak_tree_rss_bytes'], 'roots': xr['roots'], 'kernel_replays': {}}
s3x = S3 / 'results/export-receipt.json'
if s3x.is_file():
    s3xr = json.loads(s3x.read_text())
    kr['session_3_export'] = {'sha256': s3xr['sha256'], 'bytes': s3xr['bytes'],
                              'identical_to_this_export': s3xr['sha256'] == xr['sha256'],
                              'note': 'the export of the session-3 package (relay trees vendored)'}
for k in ('leanchecker', 'nanoda', 'nanoda-negative-control'):
    p = K / (k + '-receipt.json')
    if p.exists():
        kr['kernel_replays'][k] = json.loads(p.read_text())
kr['note'] = ('Both replays use the Linux binaries of the pinned toolchain (cp -a of the forgetting relay\'s toolchain, '
              'as in the hard-model and noise-diagram relays). Each runs serially under the process-tree RSS watchdog '
              '(stop at 9.0 GB); neither tool has a memory-cap option. nanoda runs with num_threads 1 and a 128 MiB '
              'main-thread stack (RLIMIT_STACK), with the precedent relays\' axiom policy. The negative control reruns '
              'nanoda on the same export with Classical.choice not permitted and must be rejected.')
kv = kr['kernel_replays']
kr['status'] = 'PASS' if (kv.get('leanchecker', {}).get('exit') == 0 and kv.get('nanoda', {}).get('exit') == 0
                          and kv.get('nanoda-negative-control', {}).get('exit', 0) != 0) else 'FAIL'
dump('KERNEL-REPLAY.json', kr)

# ---------------- AXIOMS.txt / AXIOM-AUDIT.json
ax = (P / 'AXIOMS.txt').read_text(encoding='utf-8')
(E / 'AXIOMS.txt').write_text(ax, encoding='utf-8')
dev = (P / '.lake/replay/ForgettingNaturalRule.Audit.log').read_text(encoding='utf-8')
(E / 'AXIOMS-DEV-AUDIT.txt').write_text(dev, encoding='utf-8')


def decl_lines(tag):
    return [(lambda x: [x[0], x[1][0], x[1][1]])(json.loads(l.split(tag + ':', 1)[1]))
            for l in ax.splitlines() if l.startswith(tag + ':')]


fnr_decls, core_decls = decl_lines('FNR_DECL'), decl_lines('CORE_DECL')
count = int(re.search(r'FNR_DECL_COUNT:(\d+)', ax).group(1))
ccount = int(re.search(r'CORE_DECL_COUNT:(\d+)', ax).group(1))
roots = re.findall(r'^#print axioms (\S+)$', (P / 'Audit.lean').read_text(encoding='utf-8'), re.M)
std = {'propext', 'Classical.choice', 'Quot.sound'}
printed = dict(re.findall(r"^'?([^'\s]+)'? depends on axioms: \[([^\]]*)\]", ax, re.M))
final_axioms = {n: [a.strip() for a in printed.get(n, '').split(',') if a.strip()] for n in FINAL}
bad = [d for d in fnr_decls + core_decls if not set(d[2]) <= std]
errors = [l for l in ax.splitlines() if ': error' in l or 'error:' in l]
prefix_line = next((l for l in dev.splitlines() if l.startswith('audit_prefix FNR')), None)
core_mod_list = sorted({d[1] for d in core_decls})
dump('AXIOM-AUDIT.json', {
    'status': 'PASS' if (not bad and not errors and count == len(fnr_decls) and ccount == len(core_decls)
                         and 'FNR_FINAL_TYPES_OK' in ax and 'FNR_CONDITIONAL_TYPES_OK' in ax
                         and all(set(v) == std for v in final_axioms.values())) else 'FAIL',
    'run': 'fresh: the package Audit.lean was compiled in the fresh full replay (BUILD.json)',
    'permitted_axioms': sorted(std), 'final_theorem_axioms': final_axioms,
    'final_theorem_types': TYPES,
    'final_theorem_types_checked': 'FNR_FINAL_TYPES_OK' in ax,
    'conditional_forms_types_checked': 'FNR_CONDITIONAL_TYPES_OK' in ax,
    'explicit_print_axioms_roots_count': len(roots),
    'development_declarations_count': count,
    'development_private_declarations': sum(1 for d in fnr_decls if d[0].startswith('_private')),
    'development_declarations_without_axioms': sum(1 for d in fnr_decls if not d[2]),
    'imported_core_declarations_count': ccount,
    'imported_core_declarations_by_core': {c: sum(1 for d in core_decls if d[1].startswith(c)) for c in CORES},
    'imported_core_modules_count': len(core_mod_list),
    'imported_core_modules': core_mod_list,
    'including_generated_and_private': True,
    'unexpected': bad, 'error_lines': errors,
    'dev_audit_prefix_line': prefix_line,
    'dev_audit_identical_to_committed_AXIOMS_txt': dev == (O / 'AXIOMS.txt').read_text(encoding='utf-8'),
    'dev_audit_note': 'evidence/AXIOMS-DEV-AUDIT.txt is the fresh output of ForgettingNaturalRule/Audit.lean '
                      '(#print axioms and #audit_axioms_strict lines and #audit_prefix FNR), compiled in the same replay.',
    'declarations': fnr_decls, 'core_declarations': core_decls,
    'axioms_text_sha256': sha_file(E / 'AXIOMS.txt'), 'source_census': 'SOURCE-AUDIT.json'})

# ---------------- SOURCE-AUDIT.json
lean_files = sorted([p for p in P.rglob('*.lean') if 'vendor' not in p.relative_to(P).parts
                     and '.lake' not in p.relative_to(P).parts and p.name != 'lakefile.lean'])


forb = re.compile(r'(^|[^`])(native_decide|implemented_by|@\[extern)|^[ \t]*axiom[ \t]|(^|[^`])autoImplicit[ \t]+true|decide[ \t]+\+native', re.M)
hits, sorries, noimp, mentions = [], [], [], []
for p in lean_files:
    t = p.read_text(encoding='utf-8')
    code = strip_comments(t)
    rel = str(p.relative_to(P))
    for m in forb.finditer(code):
        hits.append({'file': rel, 'line': code[:m.start()].count('\n') + 1, 'text': m.group(0).strip()})
    for m in re.finditer(r'(?<![\w.])sorry(?![\w])', code):
        sorries.append({'file': rel, 'line': code[:m.start()].count('\n') + 1})
    for m in re.finditer(r'\bsorry\b', t):
        ln = t[:m.start()].count('\n') + 1
        if not any(s['file'] == rel and s['line'] == ln for s in sorries):
            mentions.append({'file': rel, 'line': ln})
    if 'set_option autoImplicit false' not in t and rel != 'Solution.lean':
        noimp.append(rel)
ro = {}
for path in [F, Path('/opt/forgetting-arxiv-2026-11-10-runtime.tar.zst'), Path('/opt/forgetting-arxiv-2026-11-10-runtime.tar.json'),
             Path('/opt/package-forgetting-arxiv.py'), U, N, DEV_UND.parent, S3]:
    if not path.exists():
        ro[str(path)] = 'absent'
        continue
    out = subprocess.run(['find', str(path), '-newermt', SESSION_START, '-print'], capture_output=True, text=True)
    ro[str(path)] = out.stdout.split()
lint = subprocess.run(['bash', 'scripts/lint.sh'], cwd=P, capture_output=True, text=True)
census = subprocess.run(['python3', '-I', '-B', 'scripts/sorry_census.py'], cwd=P, capture_output=True, text=True)
dump('SOURCE-AUDIT.json', {
    'lean_files_checked': [str(p.relative_to(P)) for p in lean_files],
    'method': 'comments and string literals blanked out first (as scripts/sorry_census.py); lakefile.lean excluded',
    'forbidden_constructs': hits, 'sorry_tokens': sorries,
    'sorry_mentions_in_comments': mentions,
    'sorry_only_in_challenge_holes': all(s['file'] == 'Challenge.lean' for s in sorries) and len(sorries) == 5,
    'files_without_autoImplicit_false': noimp,
    'lint_sh_output': lint.stdout.strip(), 'lint_sh_exit': lint.returncode,
    'sorry_census_output': census.stdout.strip(),
    'read_only_inputs_modified_after_session_start': ro,
    'read_only_inputs_note': f'find -newermt "{SESSION_START}" (WSL clock; session 3b began after the session-3 '
                             'commit at 11:36:00) over the forgetting relay, its runtime archive and receipt, its '
                             'packaging script, the hard-model relay, the noise-diagram relay, the noise-diagram '
                             'development folder and the session-3 workspace of this package: empty lists mean no file '
                             'there was created or modified during this session. This core\'s own development folder '
                             f'{DEV_FNR.parent} is written by this session (scratch inputs) and is not listed. The public '
                             'release folders on Windows were read with git rev-parse/ls-tree/cat-file/show only.',
})

# ---------------- CHOICES.json, ORIGINAL-SOURCE.json (source identity)
ch = []
for p in sorted(O.rglob('*.lean')):
    for i, l in enumerate(p.read_text(encoding='utf-8').splitlines(), 1):
        if '[choice]' in l:
            ch.append({'file': str(p.relative_to(O)), 'line': i, 'text': l.strip()})
dump('CHOICES.json', {'scope': f'Every [choice] occurrence in the development\'s Lean source (commit {COMMIT}; '
                      'Challenge.lean repeats the statement file\'s). Rows S1-S20, F1-F9 and D1-D18 are in STATUS.md; '
                      'the release adds no fidelity choice.',
                      'count': len(ch), 'choices': ch})
orig = [{'path': str(p.relative_to(O)), 'sha256': sha_file(p)} for p in sorted(O.rglob('*')) if p.is_file()]
diff_in_project = [r['path'] for r in orig if not (P / r['path']).is_file() or sha_file(P / r['path']) != r['sha256']]
EXPECTED = {'AXIOMS.txt': 'replaced by the output of the package Audit.lean (scripts/replay.py copies it); the '
                         'development audit output of this replay is evidence/AXIOMS-DEV-AUDIT.txt'}
dump('ORIGINAL-SOURCE.json', {'commit': COMMIT, 'archive': 'source.tar (git archive of the commit)',
                              'archive_sha256': sha_file(D / 'source.tar'),
                              'frozen_statement_sha256': sha_file(O / 'ForgettingNaturalRule/Statements.lean'),
                              'frozen_statement_sha256_as_recorded': sha_file(O / 'ForgettingNaturalRule/Statements.lean') == FROZEN_SHA,
                              'challenge_regenerated_identical_to_commit': sha_file(P / 'Challenge.lean') == sha_file(O / 'Challenge.lean'),
                              'project_files_identical_to_commit_except_expected': all(x in EXPECTED for x in diff_in_project),
                              'differences': diff_in_project, 'expected_differences': EXPECTED,
                              'files': orig})

# ---------------- BINARY-DIGESTS.json
recs = []
for b in ['lean', 'lake', 'leanexport', 'leanchecker', 'nanoda_bin']:
    p = D / 'toolchain/bin' / b
    recs.append({'path': str(p), 'bytes': p.stat().st_size, 'sha256': sha_file(p),
                 'same_as_forgetting_relay_binary': sha_file(p) == sha_file(F / 'toolchain/bin' / b),
                 'same_as_hard_model_relay_binary': sha_file(p) == sha_file(U / 'toolchain/bin' / b),
                 'same_as_noise_diagram_relay_binary': sha_file(p) == sha_file(N / 'toolchain/bin' / b)})
p = D / 'bubblewrap/usr/bin/bwrap'
recs.append({'path': str(p), 'bytes': p.stat().st_size, 'sha256': sha_file(p),
             'same_as_forgetting_relay_binary': sha_file(p) == sha_file(F / 'bubblewrap/usr/bin/bwrap'),
             'same_as_hard_model_relay_binary': sha_file(p) == sha_file(U / 'bubblewrap/usr/bin/bwrap'),
             'same_as_noise_diagram_relay_binary': sha_file(p) == sha_file(N / 'bubblewrap/usr/bin/bwrap')})
dump('BINARY-DIGESTS.json', {'records': recs, 'toolchain': 'cp -a of /opt/forgetting-arxiv-2026-11-10/toolchain (Lean 4.35.0, eb6cafb7290e8bd5f2937522d8d804f58f02bafc)'})

# ---------------- DEPENDENCY-CHECK.json (the nine pinned packages)
refp = P / 'vendor/FixedNoiseErgodicity/pins/DEPENDENCY-SOURCES.json'   # public: lean/pins/ of release v1.4.0
ref_relay = F / 'evidence/DEPENDENCY-SOURCES.json'
ref = json.loads(refp.read_text())
listed = {f['path']: f for f in ref['files']}
mism = []
for path, f in listed.items():
    q = P / 'vendor' / path
    if not q.is_file() or q.stat().st_size != f['bytes'] or sha_file(q) != f['sha256']:
        mism.append(path)
unlisted = []
for d in DEPS:
    for q in (P / 'vendor' / d).rglob('*.lean'):
        rel = str(q.relative_to(P / 'vendor'))
        if '.lake' not in q.parts and rel not in listed:
            unlisted.append(rel)
hl = subprocess.run(['find', str(P / 'vendor'), '-type', 'f', '-links', '+1'], capture_output=True, text=True).stdout.split()
dump('DEPENDENCY-CHECK.json', {
    'expected_mathlib_commit': ML,
    'vendor_copy': 'cp -a of /opt/forgetting-arxiv-2026-11-10/project/vendor/<package> for the nine packages of lake-manifest.json',
    'hard_links_in_vendor': len(hl),
    'reference': str(refp) + ' (lean/pins/DEPENDENCY-SOURCES.json of the public forgetting release v1.4.0, vendored '
                             'here; the forgetting relay\'s manifest, whose model package compared the mathematical '
                             'Mathlib sources byte for byte with the official commit archive)',
    'reference_sha256': sha_file(refp),
    'reference_identical_to_forgetting_relay_manifest': sha_file(refp) == sha_file(ref_relay),
    'checked_dependency_source_files': len(listed), 'mismatches': mism,
    'unlisted_lean_source_files_outside_build_dirs': unlisted,
    'status': 'PASS' if not mism and not unlisted and not hl and sha_file(refp) == sha_file(ref_relay) else 'FAIL',
})

# ---------------- VENDOR-CORES.json (the three reused cores)


def tree(root, skip=()):
    return {q.relative_to(root).as_posix(): sha_file(q) for q in sorted(root.rglob('*'))
            if q.is_file() and q.relative_to(root).parts[0] not in skip
            and q.name not in ('.host-memory.json', '.host-memory.stop')}


def olean_cmp(mods_, other):
    out = []
    for m in mods_:
        rel = m.replace('.', '/') + '.olean'
        a, b = P / '.lake/build/lib/lean' / rel, other / rel
        out.append([m, b.is_file() and sha_file(a) == sha_file(b)])
    return out


vc = {}
for name, src in CORES.items():
    V = P / 'vendor' / name
    have = tree(V)
    compiled = [m for m in core_mods if m.split('.')[0] == name]
    used_lean = [m.replace('.', '/') + '.lean' for m in compiled]
    prec = tree(src, ('vendor', '.lake'))
    olean_prec = olean_cmp(compiled, src / '.lake/build/lib/lean')
    rec = {'compiled_modules_from_vendored_sources': compiled}
    if name in PUBLIC:
        c = PUBLIC[name]
        want = {k: v['sha256'] for k, v in c['files'].items()}
        rec = {
            'vendored_from': {k: c[k] for k in ('paper', 'version', 'doi', 'public_url', 'release_repo', 'commit',
                                                'version_commit', 'tag', 'lean_tree', 'origin_main')},
            'copy': 'the lean/ folder of the release commit, from its git blobs (relay/pack_public_cores.py, '
                    'public-' + name + '.tar, sha256 ' + c['tar_sha256'] + '), extracted whole',
            'files': len(have), 'public_release_files': len(want),
            'byte_identical_to_public_release_tree': have == want,
            'files_differing_from_public_release': [k for k in want if k in have and have[k] != want[k]],
            'public_release_files_absent': [k for k in want if k not in have],
            'files_not_in_public_release': [k for k in have if k not in want],
            'release_cross_checks': {
                'lean_tree_same_at_version_commit': c['lean_tree_same_at_version_commit'],
                'commit_is_origin_main': c['commit_is_origin_main'], 'local_tag_present': c['local_tag_present'],
                'citation_version_and_doi_match': c['citation_matches'],
                'working_tree_mismatches': c['working_tree_mismatches'],
                'release_SHA256SUMS_mismatches': c['sha256sums_mismatches'],
                'release_SHA256SUMS_lean_entries': c['sha256sums_count'],
                'release_cores_json_mismatches': c['release_cores_json_mismatches'],
                'release_cores_json_files': c['release_cores_json_count']},
            **rec,
            'compiled_module_sources_identical_to_public_release': all(want.get(k) == have.get(k) for k in used_lean),
            'precedent_relay_workspace': str(src) + ' (not vendored; the development build linked its objects)',
            'compiled_module_sources_differing_from_precedent_workspace': [k for k in used_lean if prec.get(k) != have.get(k)],
            'lean_files_differing_from_precedent_workspace': sorted(k for k in set(have) | set(prec) if k.endswith('.lean')
                                                                    and k in have and k in prec and have[k] != prec[k]),
        }
    else:
        # the noise-diagram core: no public Lean release yet; vendored from its release package workspace, and
        # compared with its release package's source archive (git archive ec67163, the noise-diagram relay's original/)
        ref_root = N / 'original'
        lean_ref = {k: v for k, v in tree(ref_root).items() if k.endswith('.lean')}
        rec = {
            'vendored_from': str(src),
            'copy': 'rsync -a (cp -a semantics) excluding vendor/, .lake/ and the relay heartbeat files',
            'files': len(have), 'files_differing_from_source_workspace': [k for k in have if prec.get(k) != have[k]],
            'source_files_absent': [k for k in prec if k not in have],
            'public_release': None,
            'public_release_note': 'no public Lean release: the public release v1.1.0 (DOI 10.5281/zenodo.24152233, '
                                   'commit a0b903e of uncomputable-noise-diagram-release) has no lean/ folder',
            'reference': str(ref_root) + ' (git archive of commit ec67163 of the noise-diagram repository; its release '
                                         'package, REPORT.md commit 5bdaeaa)',
            'reference_lean_files': len(lean_ref),
            'reference_lean_files_identical': sum(1 for k, h in lean_ref.items() if have.get(k) == h),
            'reference_lean_files_different_or_absent': [k for k, h in lean_ref.items() if have.get(k) != h],
            **rec,
            'compiled_module_sources_identical_to_reference': all(lean_ref.get(k) == have.get(k) for k in used_lean),
        }
    rec['compiled_oleans_byte_identical_to_precedent_oleans'] = olean_prec
    rec['all_compiled_oleans_byte_identical_to_precedent_oleans'] = all(x[1] for x in olean_prec)
    rec['compiled_oleans_differing_from_precedent_oleans'] = [x[0] for x in olean_prec if not x[1]]
    vc[name] = rec
vc['UncomputableNoiseDiagram']['compiled_oleans_byte_identical_to_dev_build_oleans'] = olean_cmp(
    vc['UncomputableNoiseDiagram']['compiled_modules_from_vendored_sources'], DEV_UND / '.lake/build/lib/lean')
vc['UncomputableNoiseDiagram']['dev_build'] = str(DEV_UND) + ' (the objects the development build of this core linked against)'
vc['FixedNoiseErgodicity']['precedent_difference_note'] = (
    'The forgetting relay workspace (vendored in session 3, and linked by the development build) differs from the '
    'public v1.4.0 lean/ folder in five Lean files, in comments and docstrings only (the release removed internal '
    'reviewer references): Hypotheses.lean, Main.lean, Section2/Ergodic.lean, Three/Corner.lean, Three/CornerCheck.lean '
    '(evidence/VENDOR-FNE-vs-release-v1.4.0.diff); four of them are compiled here. compiled_oleans_differing_from_'
    'precedent_oleans lists the objects that differ from the relay\'s as a result (docstrings are stored in .olean '
    'files; plain comments are not). The release v1.4.0 has no git tag in the local release repository (the public '
    'link names tree/v1.4.0); its commit is origin/main, and its lean/ tree equals that of the commit "Version 1.4.0".')
vc['UndecidablePhaseDiagram']['precedent_difference_note'] = (
    'Every Lean file of the hard-model relay workspace is byte-identical to the public v1.2.0 lean/ folder; the folder '
    'adds the relay records (evidence/, relay/, README.md, REPORT.md), the workspace had development notes instead.')
# against the session-3 package (relay trees vendored): every object compiled here
s3 = S3 / 'project/.lake/build/lib/lean'
all_mods = core_mods + pkg_mods
s3cmp = olean_cmp(all_mods, s3) if s3.is_dir() else []
vc['comparison_with_session_3_package'] = {
    'workspace': str(S3) + ' (session 3: the forgetting and hard-model cores vendored from their relay workspaces)',
    'objects_compared': len(s3cmp),
    'objects_identical': sum(1 for x in s3cmp if x[1]),
    'objects_differing': [x[0] for x in s3cmp if not x[1]],
}
dump('VENDOR-CORES.json', vc)
print('evidence written:', sorted(x.name for x in E.iterdir()))
print('BUILD', build['status'], 'COMPARATOR', cr['status'], 'KERNELS', kr['status'], 'FNR decls', count,
      'core decls', ccount, 'bad', len(bad), 'DEPS', 'PASS' if not mism and not unlisted and not hl else 'FAIL')
print('dev oleans identical', all(x[1] for x in dev_olean),
      {k: v['all_compiled_oleans_byte_identical_to_precedent_oleans'] for k, v in vc.items() if k in CORES},
      {k: vc[k]['byte_identical_to_public_release_tree'] for k in PUBLIC},
      'objects differing from session 3', vc['comparison_with_session_3_package']['objects_differing'])

