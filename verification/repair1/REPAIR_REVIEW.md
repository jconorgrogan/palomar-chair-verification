# Independent HENRY clean-build diagnosis and repair review

## Verdict
PASS for the minimal local repair and targeted fresh replay. No full clean official acceptance is established.

## Cause
Official run 37725422679, trigger 0d7c1977466067b09d994496edb3f608ccf2102b, failed source compilation. The published HENRYProof2 assignment disabled autoImplicit. The original wallDiscrepancy definition implicitly bound an undeclared p. Under that assignment its definition fails; error-recovery terms then cause the displayed omega and unsolved-goal failures. The official diagnostic excerpt omitted the earlier unknownIdentifier messages; the exact local reproduction exposes them.

The unchanged source passes with autoImplicit=true. Adding only `{p : Nat}` to wallDiscrepancy passes with the exact published autoImplicit=false flags. There are no theorem-statement changes, added assumptions, proof-body edits, exemptions, or weaker conclusions.

## Earlier evidence and correction
The prior final recipe table classified CoarseWalls as `declared_fresh_rebuild_recipe_historical_command_unavailable`, with no preserved command receipt in that table. Its fallback recipe was not a tested historical compiler command. The earlier local final review expressly established checked object/evidence consistency, not clean Lake compilation.

Historical fresh_replay/BUILD.json in compact_t7_atlas_inclusion_20261007/bundle binds the same source hash and reused CoarseWalls object hashes to a successful compile. Its replay script used -j1 -M1536, leaving autoImplicit at true. Source copies inspected were byte-identical; the historical object bytes still match. Lean/toolchain commit and binary hashes match the official toolchain, as do the selected dependency manifest and published Lake configuration. There is no evidence that stale or mismatched CoarseWalls objects caused this failure.

Any broader claim that the selected source pack had already freshly compiled under the final flags must be corrected. The carefully bounded prior local kernel/evidence claim remains supported.

## Verified repair
- Original source SHA-256: 8bf4107cdb0181224fb188cc6ba872ad2df75bb4f79995b1c7daebdc49ee4bf2.
- Corrected source SHA-256: 030cf4c624087ad06d477a3ff6e6670bfaf46d127c0f2fc8af7acd93f08292ff.
- Old and new object signatures are identical: `{p : Nat} → Pose p → Fin p → Mask p`.
- Identical rfl definition-body probes compiled and passed default kernel checking, with no axioms.
- All 910 selected fresh target modules compiled from source using their exact final per-module flags, including all 889 selected fallback modules.
- All 105 prerequisite/affected modules passed default leanchecker invocations without extra flags.
- The initial absence of all fresh target object parts was independently observed before execution. All 1,015 successful process receipts were independently checked against command, source, object, log, process identity, dependency, plan, and runner hashes.
- Endpoint and expanded statement axiom reports use only propext, Classical.choice, and Quot.sound.
- The targeted run intentionally reused 3,462 untouched project objects and package caches. It was not a full clean project build.

## Remaining verification
After authorized publication of the single-line correction, the exact resulting commit still needs a clean official Solution build, Comparator, export, independent kernel checks, and official acceptance. The failed run never reached those later stages. Do not claim an official pass from this local targeted result.

Machine-readable evidence: DIAGNOSIS.json, STATIC_REPLAY_REVIEW.json, SIGNATURE_REVIEW.json, FRESH_COARSEWALLS_REVIEW.json, FINAL_REPAIR_REVIEW.json. Repeatable independent receipt verifier: review_fresh.py.
