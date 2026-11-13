"""Generate the package's root Audit.lean (run in WSL with python3 -I -B).

Model: the noise-diagram relay's make_audit.py (itself modelled on the hard-model and forgetting relays'
Audit.lean). The file imports the root module (the whole development, which imports the reused cores' modules
it needs, through `ForgettingLower.Reduction` the whole forgetting core) and the audit commands, prints
and strictly audits every root of `ForgettingLower/Audit.lean` (the three release targets first), then
checks the axioms of every imported declaration of the development AND of the imported modules of the four
reused cores, including private and generated ones (only `propext`, `Classical.choice`, `Quot.sound` allowed;
no project or core declaration is an axiom), and checks the types of the three release targets against the statements.
"""
from pathlib import Path
import re

D = Path(__file__).resolve().parent   # the release workspace (this script sits at its root)
P = D / 'project'
src = (P / 'ForgettingLower' / 'Audit.lean').read_text(encoding='utf-8')
roots = []
for m in re.finditer(r'^#audit_axioms(?:_strict)?\s+(\S+)\s*$', src, re.M):
    if m.group(1) not in roots:
        roots.append(m.group(1))
final = ['FLD.z4_classification', 'FLD.z4_machine_corollary', 'FLD.z4_raw_undecidable']
for f in final:
    assert f in roots, f
ordered = final + [r for r in roots if r not in final]
lines = [
    '/-',
    '# Complete axiom audit (release package, Lean v4.35.0, Mathlib 56a0058)',
    '',
    'Prints and strictly audits every root of `ForgettingLower/Audit.lean` (the three release targets',
    'first), then checks the axioms of every imported declaration of the development and of the imported',
    'modules of the four reused cores (`FixedNoiseErgodicity.*`, `UndecidablePhaseDiagram.*`,',
    '`UncomputableNoiseDiagram.*`, `ForgettingNaturalRule.*`), including private and generated ones: only `propext`, `Classical.choice`,',
    '`Quot.sound` are allowed, and no such declaration is an axiom. Finally it checks the types of the three',
    'release targets against their exact frozen types.',
    '(Modelled on the noise-diagram, hard-model and forgetting relays\' package `Audit.lean`.)',
    '-/',
    'import ForgettingLower',
    'import UncomputableNoiseDiagram.AuditCommand',
    '',
    'set_option autoImplicit false',
    '',
]
for r in ordered:
    lines.append(f'#print axioms {r}')
    lines.append(f'#audit_axioms_strict {r}')
lines += [
    '',
    '/-! Complete imported audit, including generated and private declarations. -/',
    'set_option maxHeartbeats 20000000',
    'open Lean Elab Command',
    'run_cmd do',
    '  let env ← getEnv',
    '  let standard := [``propext, ``Classical.choice, ``Quot.sound]',
    '  let mut count := 0',
    '  let mut coreCount := 0',
    '  for (n, ci) in env.constants.toList do',
    '    if let some idx := env.getModuleIdxFor? n then',
    '      let mod := env.allImportedModuleNames[idx]!',
    '      let s := mod.toString',
    '      let own := s.startsWith "ForgettingLower"',
    '      let core := s.startsWith "FixedNoiseErgodicity" || s.startsWith "UndecidablePhaseDiagram" ||',
    '        s.startsWith "UncomputableNoiseDiagram" || s.startsWith "ForgettingNaturalRule"',
    '      if own || core then',
    '        if ci matches .axiomInfo _ then throwError "Axiom declaration {n} in {mod}"',
    '        let ax := (← Lean.collectAxioms n).toList',
    '        for a in ax do',
    '          unless standard.contains a do throwError "Unexpected axiom {a} in {n}"',
    '        if own then',
    '          logInfo m!"FLD_DECL:{toJson (n.toString, s, ax.map Name.toString) |>.compress}"',
    '          count := count + 1',
    '        else',
    '          logInfo m!"CORE_DECL:{toJson (n.toString, s, ax.map Name.toString) |>.compress}"',
    '          coreCount := coreCount + 1',
    '  let check (n : Name) (t : Expr) : CommandElabM Unit := do',
    '    let some ci := env.find? n | throwError "Missing {n}"',
    '    unless ci matches .thmInfo _ do throwError "{n} is not a theorem"',
    '    unless ci.type == t do throwError "{n} statement changed"',
    '  check ``FLD.z4_classification (mkConst ``FLD.Z4Classification)',
    '  check ``FLD.z4_machine_corollary (mkConst ``FLD.Z4MachineCorollary)',
    '  check ``FLD.z4_raw_undecidable (mkConst ``FLD.Z4RawUndecidable)',
    '  logInfo m!"FLD_FINAL_TYPES_OK"',
    '  logInfo m!"FLD_DECL_COUNT:{count}"',
    '  logInfo m!"CORE_DECL_COUNT:{coreCount}"',
    '',
]
(P / 'Audit.lean').write_text('\n'.join(lines), encoding='utf-8', newline='\n')
print('roots', len(ordered))
