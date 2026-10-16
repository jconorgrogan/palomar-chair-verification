# Modern pre-C333 prerequisite attempt (work in progress)

This separate five-job pipeline compiles and checks exactly 333 modern-interface finite prerequisite modules from source commit `74af951d38ff967ee1fbb10a0ad075bceea337fa`. It does not claim the hierarchy-C theorem, either physical monotile theorem, or Palomar submission acceptance.

## Execution and limits

- One preparation job, three strictly serial build jobs (128, 128, 77 modules), one authenticated collection job. Maximum one simultaneous job for this workflow. Standard public `ubuntu-22.04` runners only; no paid or larger runner, billing change, or host security policy change.
- Exact official Lean 4.35.0-rc2 archive and full canonical runtime inventory, source manifest, migration lineage, stage DAG, implementation files, and resource profiles are pinned. Sandbox preparation must pass with the reviewed isolation flags.
- Every module is freshly compiled and checked with the reviewed modern six-companion adapter, including `compiler.postponeCompile=false`. Compiler/checker resource caps are ceilings, not forecasts or prior successful measurements of these migrated modules.
- Each build has a 330-minute aggregate guard, with 350-minute GitHub job limit. The sum of per-module ceilings in a 128-module stage exceeds 330 minutes. A slow stage must therefore end incomplete; this is not a claim that every worst-case command can fit or that timeout is mathematical failure.
- The entire run has a six-day acceptance deadline. Artifacts expire after seven days. Missing, expired, failed, mismatched, or incomplete dependencies never count as acceptance; there are no automatic indefinite retries.

## Evidence and trust

Only same-run, same-attempt artifacts from this exact pipeline/source identity are admitted. Each stage uploads its own new companion objects and receipts, never copies of predecessor outputs. The final collector restores all 1,998 companion files and checks source/object/receipt hashes, then uploads only a capped 16-MiB prerequisite manifest referencing the original three delta artifacts. It does not upload duplicate objects or issue a final theorem verdict.

Bounded failed-command tails and incomplete receipts use separate artifact names and are never accepted as successful stages. The existing legacy hierarchy run and all earlier source snapshots remain untouched. No Mathlib object cache is needed for these selected finite prerequisite modules.

The original eight source-publication files are unchanged. Apache-2.0 applies to owned source; existing third-party notices are preserved. This CI attempt does not establish source-level clean reproducibility of any separate cache-backed geometry run.
