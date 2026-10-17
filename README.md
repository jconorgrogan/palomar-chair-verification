# C087 core-only preflight: reviewed activation candidate

This package tests only new helper/control sources against the authenticated
Lean 4.35.0-rc2 runtime. It compiles and independently checks ten modules, then
runs the exact fixed auditor against a four-module synthetic serialized fixture.
It loads no research objects, downloads no proof artifacts and uses no Mathlib.
Synthetic project names exist only in a dedicated fixture object namespace.

The profile is explicit: one Ubuntu 22 job, one CPU, -j1/-M768, 120 seconds per
Lean/checker command, AS/RSS 8 GiB, 1,800-second aggregate and 1,860-second outer
supervisor. Seven helper companions include generated C, matching the reviewed
core sandbox/admission implementation; the later C087 target A/B profile instead
requires its original six companions. No target source/profile repair is adopted.
Every source, command, complete log and output map is pinned/rechecked, with
per-command1MiB/aggregate8MiB logs,64MiB outputs,32MiB uploaded evidence.

Expected23 commands:2 boundary controls,10 compile/check pairs and1 serialized
auditor run. All45 negative PASS lines,2 source-shape records,2 option markers
and both exact raw-auditor JSON rows plus final marker are mandatory. Native
kernel checking occurs separately for all10 synthetic/helper modules. The raw
auditor records do not assert research provenance or independent kernel work.

The contract is enabled for the reviewed preflight. Publication and dispatch
require the separate exact release. Actual compilation, cloud runtime, terminal job success,
unique upload marker and independently reconciled evidence are still required.
A successful preflight only opens the later exact85-stage native-admission and
C087 default/async-off diagnostic gates; it proves no hierarchy endpoint.
