# Historical artifact admission verification

This package prepares one bounded Ubuntu 22.04 job to authenticate and semantically validate the 48 proposed historical stage payloads: original run 38860226136 stages 000–035 and 055, plus prior run 38917565694 stages 036–042, 049, 051, 054 and 056. The earlier failed successor 38911944324 is excluded. The original failed contracts and native receipts remain unchanged.

The exact 48-stage set covers 3,153 modules and leaves 45 stages / 3,216 modules for a future current run. Payload-dependent prior pins remain unresolved until this job succeeds and its evidence receives independent reconciliation. Both specifications are enabled only for this reviewed bounded admission job. The workflow is ready for its separately authorized publication and actual terminal verification.

## What executes

1. Authenticate the fixed old and prior terminal runs, workflow source, producers, verifier/upload steps, prepare bytes and all 48 ZIPs. The six-file acquisition helper runs in its own process with only the read-only Actions token and allowlisted environment.
2. Start a separate Python `-I -S -B` child under the previously supported bubblewrap read-only/no-network boundary. Mask private roots first, then restore only exact read-only code/source/context/archive inputs and one fresh writable semantic root. The token is absent.
3. Load the exact historical `fresh_stage`, `original.fresh_stage`, `continuation_policy`, and `continuation_runner` modules from the pinned fca406f6c52a622762d9c75167a92f895c3ddd00 checkout. Verify paths, bytes and references before and after use. The prior c5ba1401 transport remains pinned; the later status-wait implementation is not substituted into the historical context.
4. Map only outer `PriorSuccessorOrigin` wrappers to the frozen validator's native `CurrentOrigin` view. Preserve every native identity, raw descriptor, raw receipt, predecessor descriptor and object hash. The unchanged original validator authenticates old payloads; the unchanged prior readonly validator authenticates prior payloads against their full retained predecessor closure.
5. Rehash all retained objects/evidence, source files, raw archives, acquired inputs and historical implementation bytes before emitting candidate evidence. Every original tar remains available locally. No executable proof tree is published or accepted by this job.

The runtime inventory is authenticated exactly. No Lean installation is materialized. The exercised native admission call graph consults inventory hashes and historical receipt path strings; it never opens runtime binaries. An empty canonical runtime placeholder, audit traps and disabled executor refuse runtime-file opens, process/network calls and the native run/command entrypoints. This is receipt/payload admission, not an independent kernel check.

## Resources and deadline

- One CPU, 8 GiB address-space/RSS-tree bounds, standard Ubuntu 22.04.
- One entry-time 19,800-second budget across source setup, acquisition, semantic admission and controller completion. Workflow ceiling: 350 minutes.
- Invoke under `/usr/bin/timeout --signal=TERM --kill-after=30s 19800s`. The controller records TERM during the entire frozen child/cleanup call and rejects after it returns; host work fails immediately. Children receive only the remaining shared budget. No success is accepted after expiry. Final host rehashing and durable result writes also preserve the original expiry and reject backward wall-clock movement.
- Original deadline remains 2026-10-22T06:15:54Z, tightened by any earlier artifact expiry. No age or retention reset.
- Raw archives share the unchanged 4 GiB cap. The original 37 consume 1,861,550,080 bytes; prior raw sizes must be measured from authenticated payloads. ZIP sizes are not substituted.
- Physical admission preflight uses the frozen allocation-rounded mixed-storage budget, including the original validator's temporary second copy, all objects/logs/receipts/journals/directories and 512 MiB reserve, plus a 64 MiB evidence allowance. Existing ZIP/tar/source/context allocations already reduce observed filesystem free space; no future cleanup credit is taken. An additional conservative inode ceiling is checked.
- Small evidence is capped at 64 MiB; no delta tar, `.olean` or other proof companion enters the upload. Oversized or incomplete evidence is labeled partial, with bounded log tails only.

## Integrated command

```
/usr/bin/timeout --signal=TERM --kill-after=30s 19800s \
  /usr/bin/python3 -I -S -B code/three_context_job.py \
  --spec inputs/JOB_SPEC.json --spec-sha256 REVIEWED_HASH \
  --workspace NEW_RUNNER_TEMP_ROOT --prior-root PINNED_PRIOR_CHECKOUT \
  --acquisition-root acquisition/ci --source-package PINNED_SOURCE_CHECKOUT
```

The admission step receives `GH_TOKEN`, scoped to read-only contents/actions. Source checkout is 5d0612a09e3b7d440be16e7b1dc511ae73035bbb. Prior checkout is fca406f6c52a622762d9c75167a92f895c3ddd00. The workflow must verify exact clean checkout identities and pin the final specification hash. The activation reseal changes only the specification review statuses, their derived hashes, the workflow filename/hash pins and this status text.

Always-run evidence collection:

```
/usr/bin/python3 -I -S -B code/three_context_evidence.py \
  --workspace CONTROLLER_ROOT --output NEW_SEPARATE_UPLOAD_ROOT
```

A `COMPLETION.json` by itself is insufficient. Later eligibility must authenticate the exact published pipeline/spec, successful controller step, unique upload marker, ZIP bytes and terminal successful job, then reconcile the complete native evidence independently. The workflow owner prepares that envelope separately.

## Deliberately pending

- Actual prior prepare bytes and all 48 payloads under this integrated job.
- Independent reconciliation of the candidate selection/native maps and aggregate raw cap.
- The future three-context execution/checked-transfer/final-gate adapter and its activation seal. This admission package cannot activate any proof workflow; all `activation_status` results remain false.
- All 45 fresh stages and all fresh final theorem/type/axiom/export/kernel/NanoDa/con-ron gates. No clean replay or unconditional theorem claim is made.

## Offline controls

The standalone pure policy tests use authenticated original JSON and explicitly synthetic prior JSON. Native validator tests use toy source/object bytes and mock only the full research context seam; original/readonly parsing, import, command, cleanup and object/evidence checks run unchanged. They are not research compilation. Acquisition tests are separate offline fixtures. Frozen files and runtime source snapshots are never edited by these tests.

## Publication envelope

The proposed new branch is `verify/hierarchy-c-origin-admission-20261016`, based on prior commit `fca406f6c52a622762d9c75167a92f895c3ddd00`. Its clean tree carries only the reviewed admission implementation, fixed inputs, license/notices and the admission workflow. All proof sources and historical pipeline code are obtained through the two exact read-only checkouts above. Existing branches and failed run evidence remain intact. The workflow has read-only contents/actions permissions, no security-policy changes, one standard Ubuntu job, and seven-day retention for bounded evidence only. The successful post-upload marker must be bound to the exact terminal job/run/commit before any later selection is eligible.
