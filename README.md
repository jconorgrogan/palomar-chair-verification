# Tiny read-only namespace probe

This package tests the standard Ubuntu runner's read-only source, runtime,
predecessor and cache mounts, writable compiler quarantine, isolated import
paths, exact object admission and read-only kernel checker. It builds two isolated copies of three
small `Init`-based modules sharing a namespace. It makes no research theorem or
full-C replay claim.

The official Lean v4.35.0-rc2 archive and its complete inventory are authenticated
before use. A failure aborts the probe; no unsandboxed fallback is permitted.
The package is inactive until its contract, workflow and source commit are
reviewed for execution. The workflow uses one standard Ubuntu 22.04 job with a
20-minute outer limit; the entrypoint has a 900-second total deadline. Complete
probe evidence, including its hash inventory, is limited to 16 MiB.

`ci/fresh_stage.py` is the separately prepared committed-read-only C-stage
prototype. `ci/toolchain_install.py` preserves the previously reviewed official
runtime installer without changes. Both are vendored and SHA-256 pinned by the
contract. The first chain uses the C-stage topology without a nested `--new-session`.
The second uses the exact copied conditional sandbox and admission functions
with `--new-session` and an explicit bounded-runner session allowance. Each has
its own write-denial and cleanup receipts. The conditional copy retains all
seven companions including generated C; the C-stage copy retains six.

Sources and helpers are provided under the accompanying Apache-2.0 license.
The downloaded Lean distribution retains its upstream license and provenance.
