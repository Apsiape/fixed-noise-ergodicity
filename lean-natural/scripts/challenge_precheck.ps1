<#
Pre-check of Challenge.lean (not the comparator). Appends the command of
scripts/dump_reach.lean.txt to Challenge.lean (scratch/ChDump.lean) and to `import ForgettingNaturalRule`
(scratch/DevDump.lean), elaborates both through scripts/wsl.ps1 check (one Lean process at a time, with the
guards of build.py), and compares the dumps: every project constant (prefixes FNE, UPD, UND, FNR)
reachable from the five release targets, with its kind, the hash of its type and, for definitions, the
hash of its value. Prints "PRECHECK OK" when the two lists agree.

  powershell -NoProfile -File scripts/challenge_precheck.ps1
#>
$ErrorActionPreference = 'Stop'
$Repo = Split-Path -Parent $PSScriptRoot
Set-Location $Repo
$enc = New-Object System.Text.UTF8Encoding $false
$cmd = [System.IO.File]::ReadAllText((Join-Path $Repo 'scripts/dump_reach.lean.txt'))
$ch = [System.IO.File]::ReadAllText((Join-Path $Repo 'Challenge.lean'))
New-Item -ItemType Directory -Force (Join-Path $Repo 'scratch') | Out-Null
[System.IO.File]::WriteAllText((Join-Path $Repo 'scratch/ChDump.lean'), $ch + "`n" + $cmd, $enc)
[System.IO.File]::WriteAllText((Join-Path $Repo 'scratch/DevDump.lean'),
  "import ForgettingNaturalRule`n`nset_option autoImplicit false`n" + $cmd, $enc)
powershell -NoProfile -File scripts/wsl.ps1 check scratch/DevDump.lean |
  Out-File -FilePath scratch/devdump.out -Encoding utf8
powershell -NoProfile -File scripts/wsl.ps1 check scratch/ChDump.lean |
  Out-File -FilePath scratch/chdump.out -Encoding utf8
python -I -B -c @'
import sys
def get(p):
    t = open(p, encoding='utf-8', errors='replace').read()
    i, j = t.index('DUMP-BEGIN'), t.index('DUMP-END')
    return {l.strip() for l in t[i:j].split('\n')[1:] if l.strip()}
a, b = get('scratch/devdump.out'), get('scratch/chdump.out')
print('dev', len(a), 'challenge', len(b))
for x in sorted(a - b): print('only dev:', x)
for x in sorted(b - a): print('only challenge:', x)
print('PRECHECK OK' if a == b else 'PRECHECK FAILED')
'@
