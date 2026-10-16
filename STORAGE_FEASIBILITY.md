# Storage feasibility: measured partial evidence, unchanged guards

Checked 2026-10-16. No payload-set download, runner alteration, cap increase or
source/proof modification was performed for this assessment.

## Measured evidence and limits of comparison

`evidence/PARTIAL_ARTIFACT_STORAGE.json` (SHA256
`f01ba9150347783b6535e90a44a7b6327d4abf78448f46c0bc8992d4e7dd623d`)
records authoritative artifact metadata at 06:00:36 UTC:

- 43 legacy C stage artifacts: 2,101,555,497 ZIP bytes, with 50 stages outstanding.
- Modern C333 first 128-source stage: 202,559,114 ZIP bytes.
- Legacy build_000: 56,249,994 ZIP bytes, but it is not a matched source block.
  The C333 block contains ten modules from legacy build_000, two from build_042
  and 116 from build_056. A modern/legacy size multiplier cannot be derived.

Uploads use compression level zero, but ZIP metadata byte counts are still not
identical to the stage descriptor's raw delta-tar byte count. Current metadata is
not a complete-size estimate. No linear extrapolation to all 6,369 modules or to
ordinary Lake storage is justified.

## Retained and transient copies in the current reviewed runner

Let A be the sum of raw predecessor delta-tar bytes; O their companion payload
bytes; Q the largest currently expanded predecessor quarantine; N the new stage
outputs and logs. O is no larger than A. Additional fixed storage includes the
595,391,556-byte official compressed release, the approximately 3,145,390,820-byte
installed official file inventory, source extraction, immutable checkouts, metadata
and current logs.

1. The transport downloads one ZIP, authenticates it, expands the exact permitted
   members, then removes only that verified temporary ZIP. Its transient peak
   includes the current ZIP and its extracted delta tar. Previously downloaded
   delta tar files remain; they are not removed after restore.
2. Restore retains all downloaded delta tar archives (A), creates one quarantine
   at a time (Q), and copies verified companions into deps (O). The quarantine is
   removed after its receipt and all files are validated.
3. Build then makes the unified objects search tree by copying predecessors from
   deps. Steady imported data therefore includes A + 2*O, plus fresh outputs N.
4. Stage packing retains fresh files and writes a separate own-output delta tar.
   The new artifact contains only that stage's output, not predecessor objects.
5. Final restore keeps A + O, with one transient quarantine. It does not make the
   second unified object copy. Export jobs additionally retain their exact target
   export and its packed evidence; maximum final evidence is separately bounded.

The source runner's measured-free-space check is deliberately conservative and is
performed after predecessor downloads:

- Build: `free >= 3*A + 2*max_stage_output_bytes + minimum_free_disk_bytes`.
- Final restore: `free >= 2*A + minimum_free_disk_bytes`.

With unchanged 512-MiB stage-output and 512-MiB free-reserve caps, an A=4-GiB build
would require another 13.5 GiB free after its downloads and fixed inputs already
exist; final restore would require 8.5 GiB. Hence the logical 4-GiB aggregate
restore cap is not a guarantee that a runner has enough disk to reach it. The
actual measured-free-space guard may stop earlier. GitHub's published standard
public ubuntu-22.04 table lists 4 CPUs, 16-GB RAM and 14-GB SSD; measured workspace
availability must be checked rather than inferred from the label. Some official
consumer profiles separately require more available workspace. [GitHub runner
specifications](https://docs.github.com/en/actions/reference/runners/github-hosted-runners).

## Decision boundary

Storage viability for the full modern successor is unmeasured. Current exact guards
remain unchanged and fail closed. This report does not silently expand any limit,
assert inevitable failure from partial metadata, or conflate distributed artifact
copies with a native Lake build's output tree.

If measurements show a guard failure, review a separate storage-management change
before retrying. Possible designs include releasing only verified current-run
transport copies after preserving their authenticated descriptor lineage, or
avoiding a redundant predecessor copy while retaining pinned per-file immutability
checks. Neither design is adopted here. Any implementation needs negative tamper,
source/run identity, fresh-output and interrupted-restore tests; it must not weaken
receipt checks or admit old artifacts. Increasing limits alone does not create disk
space and is not an acceptable substitute for measured accounting.
