#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
for command in lean lake bwrap python3; do
  command -v "$command" >/dev/null || { echo "Missing prerequisite: $command" >&2; exit 2; }
done
prefix=$(lean --print-prefix)
for tool in lake leanexport leanchecker nanoda_bin con-ron; do
  test -x "$prefix/bin/$tool" || { echo "Toolchain lacks $tool" >&2; exit 2; }
done
# Fail closed. Never disable namespaces, alter sysctls, or use Comparator's
# --inadvisably-no-sandbox option to make this preflight pass.
for directory in /root /home /run/user; do
  test -d "$directory" || { echo "Compatible Linux runner needs $directory as an existing directory" >&2; exit 2; }
done
bwrap --ro-bind / / --tmpfs /home --tmpfs /root --tmpfs /run/user \
  --tmpfs /tmp --dir /tmp/home --dev /dev --proc /proc --clearenv \
  --unshare-all --die-with-parent --new-session -- /bin/true
python3 scripts/check-lean-sources.py
lake exe cache get $(cat scripts/cache-targets.txt)
lake build Challenge Solution
config=$(mktemp)
trap 'rm -f "$config"' EXIT
python3 - comparator.json "$config" "$prefix" <<'PY'
import json,pathlib,sys
source,destination,prefix=sys.argv[1:]
x=json.loads(pathlib.Path(source).read_text())
if 'external_kernels' in x: raise SystemExit('external_kernels is not a submitted-config field')
x.pop('enable_nanoda',None)
x['external_kernels']={'nanoda':[str(pathlib.Path(prefix)/'bin/nanoda_bin')],
                       'con-ron':[str(pathlib.Path(prefix)/'bin/con-ron'),'--verified','--jobs=2']}
pathlib.Path(destination).write_text(json.dumps(x,indent=2)+'\n')
PY
# This is the unmodified bundled Comparator, with its own sandbox enabled.
lake comparator --config "$config"
