# Full modern hierarchy-C verification attempt (work in progress)

This separate attempt freshly rebuilds the exact6,369 modern-interface modules in source commit `4a0cbd71ba9cd318620e11694037d956d2393d06`, using the pinned official Lean4.35.0-rc2 release. It preserves all original source snapshots and previous verification branches. It makes no completed proof claim before every required live gate passes.

## Exact scope and source lineage

The source manifest is `401320e96ea5a511678892c359af43131fae75494a55d8ea1df0e1dc606a326f`; the source archive is `c0695b86ae8566f76f88795b7c6856d82a88e7bfde0c2f51420198ccff0a3be1`. The exact original legacy manifest is preserved. The audited modern migration adds module/public-import/exposure headers while preserving definition/proof bodies and explicit private declarations. Real elaboration remains necessary: byte preservation alone is not proof of modern compatibility.

Only same-run, same-attempt objects from this source commit and pipeline identity are admitted. No legacy, C333, cache-backed geometry, or local objects count as this fresh replay. Owned source remains under Apache2.0 with the original third-party notices preserved.

## Stages and resource limits

There are100 job instances: prepare,93 build stages in25 sequential matrix waves, and six final roles. At most four ordinary public ubuntu-22.04 runners execute in parallel. All jobs have350-minute outer bounds; builds retain330-minute aggregate guards. The per-module ceiling sums may exceed a stage's aggregate guard, so a slow stage ends incomplete rather than receiving an automatic extension. These are ceilings, not ETA predictions or a promise to fit a separate Palomar consumer deadline.

Profiles retain the reviewed limits and modern six-companion output contract with compiler.postponeCompile=false. The only additional module-specific heap change is RadiusFivePruningRounds from M768 to M1536, preserving120-second compile/check and8GiB OS limits. A same-body legacy control motivated this finite cap, but does not establish modern success or cold timing.

The aggregate predecessor archive cap stays4GiB, own-stage outputs512MiB, artifact1GiB, command logs16MiB, and run acceptance deadline six days. Artifacts expire after seven days. Measured disk-space guards remain mandatory. No paid runner, billing change, host security-policy change, or automatic indefinite retry is used.

## Storage risk remains open

The partial measured evidence at06:00:36UTC comprises43 legacy stage ZIPs totaling2,101,555,497 bytes and one modern C333128-module ZIP of202,559,114 bytes. The blocks are not matched, so these values cannot justify a full-tree multiplier. The unchanged4GiB restore cap or measured disk guard may stop the run late. Completion is not guaranteed. See STORAGE_FEASIBILITY.md and its pinned public metadata receipt for copy accounting and decision boundaries. Any storage-management change requires a separately tested proposal; none is adopted here.

## Final acceptance

Every source compile is followed by official leanchecker. All six final roles are required: exact target export and trusted expanded-type/axiom audit, full fresh kernel replay, from-export/Lake checking, NanoDa, verified con-ron, and the final joined verdict. They bind identical source/runtime/object/export hashes. The exact declaration is SpectreFinite.HexSearch.RadiusFivePruning.certifiedParentOccurrenceTheorem with type SpectreFinite.HexSearch.NativeHierarchy.ParentOccurrenceTheorem, including its audited expanded occurrence contract. Allowed axioms are only propext, Classical.choice, Quot.sound.

Each stage uploads only its own new outputs. Failed-command tails use separate incomplete artifacts and never count as successful inputs. Missing, expired, changed, failed or incomplete evidence fails closed. Even a complete exact-C verdict still leaves unconditional physical integration, independent submission contracts, Comparator and submission-profile checks to complete separately.
