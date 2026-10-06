#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
export LEAN_NUM_THREADS=1
export MATHLIB_NO_CACHE_ON_UPDATE=1
for command in lean lake bwrap python3; do
  command -v "$command" >/dev/null || { echo "Missing prerequisite: $command" >&2; exit 2; }
done
prefix=$(lean --print-prefix)
for tool in lake leanexport leanchecker nanoda_bin con-ron; do
  test -x "$prefix/bin/$tool" || { echo "Toolchain lacks $tool" >&2; exit 2; }
done
for directory in /root /home /run/user; do
  test -d "$directory" || { echo "Compatible Linux runner needs $directory" >&2; exit 2; }
done
# Use the official sandbox unchanged. Fail closed on incompatible hosts.
bwrap --ro-bind / / --tmpfs /home --tmpfs /root --tmpfs /run/user \
  --tmpfs /tmp --dir /tmp/home --dev /dev --proc /proc --clearenv \
  --unshare-all --die-with-parent --new-session -- /bin/true
python3 scripts/verify-source-manifest.py
lake exe cache get $(cat scripts/cache-targets.txt)
# Builds legitimate Lake targets; no fabricated cache/trace state.
# At most two dependency-ready targets, each with explicit -j1 compiler flags.
# Runtime available-memory admission keeps a 1.5 GiB reserve and falls back
# to serial on smaller hosts. Export and independent verification remain serial.
python3 scripts/build-project-bounded.py
lake build Challenge
lake build Solution
lake build VerificationAudit
python3 scripts/verify-source-manifest.py
config=$(mktemp)
trap 'rm -f "$config"' EXIT
python3 - comparator.json "$config" "$prefix" <<'PY'
import json,pathlib,sys
source,destination,prefix=sys.argv[1:]
x=json.loads(pathlib.Path(source).read_text())
if 'external_kernels' in x: raise SystemExit('Submitted config must not select external commands')
x['external_kernels']={'nanoda':[str(pathlib.Path(prefix)/'bin/nanoda_bin')],
                       'con-ron':[str(pathlib.Path(prefix)/'bin/con-ron'),'--verified','--jobs=2']}
pathlib.Path(destination).write_text(json.dumps(x,indent=2)+'\n')
PY
# The unmodified bundled Comparator builds/exports in its own sandbox and
# checks the selected main statement with Lean plus both independent kernels.
lake comparator --config "$config"
python3 scripts/verify-source-manifest.py
