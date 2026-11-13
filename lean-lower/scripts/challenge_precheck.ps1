<# Release pre-check, adapted from the natural-rule core. Both elaborations use
the copied replay.py serial/memory guards. Complete logs are retained in WSL. #>
$ErrorActionPreference = 'Stop'
$free = (Get-CimInstance Win32_OperatingSystem).FreePhysicalMemory * 1KB
if ($free -lt 8GB) { throw 'REFUSE: below 8 GiB host memory' }
if (Get-Process -Name lean,lake,leanexport,leanchecker,nanoda_bin -ErrorAction SilentlyContinue) {
  throw 'REFUSE: another Lean tool is running on Windows'
}
wsl.exe -d lean-comparator -- bash -lc 'cd /opt/forgetting-lower-arxiv-2026-11-12 && python3 -I -B precheck.py'
if ($LASTEXITCODE -ne 0) { throw 'Challenge pre-check failed' }
