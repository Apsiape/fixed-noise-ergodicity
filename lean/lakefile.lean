import Lake
open Lake DSL
package FixedNoiseErgodicity where
  moreLeanArgs := #["-j1", "-M6144"]
require plausible from "vendor/plausible"
require LeanSearchClient from "vendor/LeanSearchClient"
require importGraph from "vendor/importGraph"
require proofwidgets from "vendor/proofwidgets"
require aesop from "vendor/aesop"
require Qq from "vendor/Qq"
require batteries from "vendor/batteries"
require Cli from "vendor/Cli"
require mathlib from "vendor/mathlib"
lean_lib FixedNoiseErgodicity where
  globs := #[`FixedNoiseErgodicity, `FixedNoiseErgodicity.+]

target Challenge pkg : Unit := do
  Job.async do
    proc { cmd := if System.Platform.isWindows then "python" else "python3"
           args := #["-I", "-B", (pkg.dir / "scripts" / "replay.py").toString, "--resume"]
           cwd := some pkg.dir }

target Solution pkg : Unit := do
  Job.async do
    proc { cmd := if System.Platform.isWindows then "python" else "python3"
           args := #["-I", "-B", (pkg.dir / "scripts" / "replay.py").toString, "--resume"]
           cwd := some pkg.dir }

target Audit pkg : Unit := do
  Job.async do
    proc { cmd := if System.Platform.isWindows then "python" else "python3"
           args := #["-I", "-B", (pkg.dir / "scripts" / "replay.py").toString, "--resume"]
           cwd := some pkg.dir }

@[default_target]
target core pkg : Unit := do
  Job.async do
    proc { cmd := if System.Platform.isWindows then "python" else "python3"
           args := #["-I", "-B", (pkg.dir / "scripts" / "replay.py").toString, "--resume"]
           cwd := some pkg.dir }
