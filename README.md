# Modern hierarchy C continuation: work in progress

This branch contains a source-only snapshot for a repaired, verified-continuation experiment. It does not claim that hierarchy C or the unconditional physical monotile theorems have passed. No verification workflow is installed in this source commit.

The snapshot retains all 6,369 modules and the existing 93-stage proof scope. Relative to modern source commit 4a0cbd71ba9cd318620e11694037d956d2393d06, the sole source change is a 47-byte plain meta import of SpectreFinite.RadiusFiveFamilyData in SpectreFinite.RadiusFivePrivateFamilyExport. Its existing public import and diagnostic #eval body are preserved. This addresses the actual build_054 module-visibility failure; the repaired research diagnostic still awaits compilation.

The original run 38860226136 remains failed: 37 stages passed, build_054 failed, 55 stages did not execute, and all six final checks were skipped. A separately reviewed continuation may reuse only the exact 37 authenticated, dependency-closed original stage artifacts while freshly building the remaining 56 stages and repeating all final type, standard-axiom, expanded-source, fresh-kernel, export and independent-checker gates. Reused artifacts retain their original identities and must be fully revalidated in CI. Even a successful continuation leaves a separate clean-source replay pending.

SOURCE_MANIFEST.json pins each source, its ordered imports, the archive, the exact theorem contract and official Lean 4.35.0-rc2 release. hierarchy-c-sources.tar.gz contains the full regular-file source tree. The sparse SpectreFinite/RadiusFivePrivateFamilyExport.lean file makes the repair directly inspectable and is byte-identical to its archive member. No compiled objects, caches, credentials or machine-specific state are included.

The original 2026-10-22 06:15:54 UTC six-day deadline and original artifact expiries remain binding. Proposed execution retains standard Ubuntu 22.04 runners, maximum four concurrent jobs, existing process limits and a 4 GiB aggregate raw-archive restore cap. Final storage fit and completion within the deadline are unproven; exceeding a bound must report incomplete.

Owned proof code remains Apache-2.0. Existing third-party notices are preserved. The official Lean distribution is separately pinned rather than republished here. This is an incomplete verification snapshot, not a Palomar submission or a final theorem claim.
