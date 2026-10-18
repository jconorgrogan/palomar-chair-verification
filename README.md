# Hierarchy C production continuation

This runtime prepares a bounded continued verification attempt. Its reusable native stage artifacts and final verdict must come from the authenticated attempt itself. The source snapshot remains `5d0612a09e3b7d440be16e7b1dc511ae73035bbb`, with 6,369 modules in 93 stages.

## Selected origins and remaining work

The static selection retains 37 original stages from run 38860226136, 11 prior-successor stages from run 38917565694, and 42 successful stages from terminal run 38978663241. Each historical stage keeps its original identity, source, profile, descriptor, receipt, payload digest and predecessor chain. A failed overall historical run is not treated as successful; only its precisely selected successful producers are eligible.

The three remaining stages are sequential:

1. build_087: SpectreFinite.RadiusFivePruningCertified
2. build_091: SpectreFinite.RadiusFiveParentCoverage
3. build_092: SpectreFinite.RadiusFivePruningHierarchy

Only the build_087 compiler profile disables asynchronous elaboration. Historical profiles and the other current module profiles retain their selected bytes. Diagnostic run [39083350247](https://github.com/jconorgrogan/palomar-chair-verification/actions/runs/39083350247) passed the unchanged target source's async-off compile, kernel checker and exact raw theorem auditor. That diagnostic supplied evidence, not a reusable production build_087 artifact.

After build_092, export_target and fresh_kernel run independently. lean_export, nanoda and conron depend on export_target. The verdict requires all five final evidence producers. A prepare job establishes the current identity and toolchain inventory before the three builds. This is ten workflow jobs, with at most four substantive jobs overlapping.

The 90 selected raw archives total 3,438,714,880 bytes. The unchanged 4 GiB raw cap leaves 856,252,416 bytes for the three new native stages. The original deadline, 2026-10-22T06:15:54Z, and all earlier artifact expiries remain binding. Actual available disk and inode capacity remain live gates.

## Runtime and invocation

The pipeline, immutable research source, prior pipeline `fca406f6c52a622762d9c75167a92f895c3ddd00`, and latest historical pipeline `bc3f977237bee905dafb4f13eeb6564a4a338b42` are separate clean checkouts. The prior and latest native validation graphs remain separately pinned.

The dedicated workflow is `.github/workflows/hierarchy-c-production-continuation.yml` on branch `verify/hierarchy-c-production-continuation-20261018`. It invokes:

    /usr/bin/timeout --signal=TERM --kill-after=30s 19800s /usr/bin/python3 -I -S -B pipeline/ci/four_context_driver.py ROLE --contract-sha256 HASH --pipeline CURRENT --source SOURCE --prior PRIOR --latest LATEST

Build roles additionally specify --stage build_087, build_091 or build_092. Current verifier/upload steps are 8/9. Historical producer step maps stay unchanged at 7/8.

## Transport and evidence

The complete fixed 90-stage selection is authenticated before native reuse. Historical run/job snapshots are compared at the beginning and end of the transfer batch. Every artifact retains individual metadata, ZIP and raw descriptor/receipt/payload checks; the native validators still decide whether an object can be reused.

Current bootstrap, historical acquisition and later current-artifact reads share one actual paced opener. Its lifetime allowance is 1,000 authenticated attempts, charged before dispatch and never replenished by changing server Date/reset headers. Minimum spacing remains 3.7 seconds. The ordinary historical-only synthetic paths take 297 authenticated attempts with single-page jobs, or 327 with six-page jobs. Current/fresh requests consume the same balance. Retries, waits, network latency and deadlines can cause refusal; these figures are not completion guarantees.

Successful build jobs publish their new delta.tar and upload-candidate.json; final producers publish their original bounded payload and descriptor. A failed driver may retain only FAILURE.json and, after successful native safety and cleanup acceptance, complete bounded native.stdout/native.stderr. The workflow uploads those three literal failure paths. It never invokes the old raw-capture collector. A failure artifact does not confer success.

The resource baseline is the original production trusted parent and original native child profiles. Historical create_session runs in-process; it does not claim the diagnostic standalone acquisition CLI's parent affinity/address-space envelope. Original final child address-space limits remain 12 GiB with phase-specific sampled tree RSS; stage child limits remain their selected original profiles. The existing source/runtime checks, six-companion coverage, nominal final command caps, 19,800-second original job budget, transfer/request/ZIP/raw/disk/inode bounds and 350-minute outer job ceiling remain required. The external watchdog alone does not prove descendant cleanup. Native safety and cleanup evidence, exact output validation and final terminal reconciliation are separate mandatory conditions.

## Result boundary

Local tests use bounded synthetic data and do not establish research theorem success. Every new production stage must pass actual compile/check/native receipt validation. All six final roles, including independent readers and the verdict, remain required. A successful continued result still leaves the separately required clean replay and Palomar preflight/submission conditions.
