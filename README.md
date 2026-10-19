# Inactive Root7 import-cut experiment

This source-only test package has not run Lean, native project code, network acquisition, publication, or dispatch. It is separate from the five-helper visibility test and makes no official acceptance or runtime-fit claim. The sole CI publisher owns a later authorized activation. The contract is inactive; the workflow has one false guard and two zero contract tokens.

Run: `python3 -I -B root7_import_cut.py --contract-sha256 SHA --work ABSOLUTE_NEW_WORK`

Always-run collection adds `--collect`, writes `WORK/upload/**`, and has the inherited separate 120-second bound. The fixed workflow path is `.github/workflows/palomar-root7-import-cut-smoke.yml`; work is `${{ runner.temp }}/palomar-root7-import-cut-smoke`; artifact is `root7-import-cut-smoke-evidence-${{ github.run_id }}-${{ github.run_attempt }}`. The normalized workflow SHA256 is `d3dcb4426616426da1d263dfcb150e94fc9c098a92f7cd9717aa2ea6f59ea1cf`. Activation changes only its single guard and two contract slots, together with the reviewed active contract; no self-referential raw workflow hash is used.

## Exact scope and inputs

- The original source archive is SHA256 `93f6a8e91e30e26685b456aa0346c73dbb14def9a825e88a72f8d70e455cebb1`.
- The two-file source contract is T0049 `e3587f1687af0f58e1b7a307b463b845500545e933315d90a90a997cc378fe3a`, retained as `provenance/TEST_CONTRACT.json`. Its source bodies, declarations and proofs are unchanged. Part32 imports Part1 instead of Part31; Cover explicitly imports Part31.
- The canonical archive contains all 388 candidate owned sources, with exact source and direct-import hashes. Full Solution's 9,656-file closure remains outside this focused test. The exact 59 downstream modules requiring new compile/check evidence remain in the retained T0049 source contract.
- Original Part32 source is separately pinned. All 325 original prerequisites are freshly compiled and checked first, using bytes shared by both variants. Candidate Part32 sees exactly its 286 prerequisites. Both variants retain canonical module identity `SpectreFinite.RadiusFiveRoot7Part32` under separate source/search/output roots.
- Official Lean 4.35.0-rc2 runtime archive identity, acquisition caps and canonical runtime inventory are unchanged from the reviewed visibility driver. No Mathlib/cache/dependency acquisition path is called. Runtime/core imports are only Init and Init.Data.List.OfFn for project sources; the test-only tool uses official Lean runtime modules.

## Finite command plan

There are exactly 790 managed commands:

1. Two sandbox/read-only boundary preflights.
2. One interface tool source compilation/execution in API self-test mode. It checks changed constant references, exact binder names, binder annotations and recursor RHS strengthening of alpha-equivalent `BEq` values.
3. Six isolated real-source `Fixture` compilations, all with the same canonical module identity, followed by one fixture suite. This requires an identical positive pair and changed-value, changed-theorem-type, changed-inventory and unpermitted-axiom dependency rejection.
4. 388 candidate compile calls and 388 candidate leanchecker calls, with outputs provisionally promoted read-only for their own checker and downstream dependency eligibility granted only after checker success; original Part32 has one additional isolated compile and one checker call.
5. One strict Part32 comparator call, immediately after its candidate compile/check, and one required Cover axiom traversal after all 388 modules compile/check.

Compiler and tool/self-test/fixture calls have 180 seconds, kernel and Cover-axiom calls 120 seconds, preflights 30 seconds. The sum of requested command maxima is 118,500 seconds. The inherited absolute 7,200-second controller deadline still governs the entire actual test, including imports and host I/O, with its existing five-second failure-only evidence grace. This is a bounded optimization experiment, not a promise that all maxima can be consumed. Workflow TERM is 7,260 seconds, kill-after 30 seconds, outer job 130 minutes. The 389 leanchecker invocations retain upstream module-prefix matching semantics; they do not imply exactly 389 internal replay operations.

The inherited native profile is unchanged: 12 GiB address space, 8 GiB sampled process-tree RSS, 4,096 MiB Lean heap guard, one thread, async elaboration off, 512 MiB per created file, 1 MiB combined capture per command, 64 MiB total admitted logs, 124 MiB evidence and 128 MiB upload including a 4 MiB collection-manifest reserve. Sources are bounded at 32 MiB, accepted owned outputs at 6 GiB, and each source/view/output copy and compile checks the 1.5 GiB disk reserve as applicable. Runtime extraction retains its larger measured-disk bound. The comparator keeps its two before/after environments and raw loaded regions alive through process exit; no claim that file size equals RSS is made. A resource-limit termination is incomplete evidence.

## Comparison and provenance

`tools/ImportCut.lean` reads all three olean parts and uses the most-private constant inventory. Each context independently imports its actual prerequisite environment, then its target module, with extensions disabled. The exact introduced inventory is post-environment minus pre-environment, checked against every most-private module constant. No private/generated constant filter is applied. Exact imported constant identities and fields must remain unchanged across each load.

Comparison uses structural Lean Name equality, declaration constructor identity, all constructor-specific non-expression fields from derived ConstantInfo equality, and explicit `Expr.equal` for every type, available value/theorem proof/opaque value and recursor-rule RHS. `Expr`'s ordinary `BEq` is alpha equivalence and is not represented as exact structural equality. Types/proofs are never compared by pretty printing, string names, hashes or normalization. All 239 explicit Part32 declarations (10 definitions, 229 theorems) must be present with their exact source-derived names/kinds; generated/private declarations are additional mandatory comparisons.

A cycle-safe transitive traversal follows type/value references and inductive/constructor/recursor relations. Each introduced declaration's axiom set must match and be contained in propext, Quot.sound and Classical.choice. Missing referenced constants fail closed. Cover's 213 explicit theorem names/kinds, including `SpectreFinite.HexSearch.RadiusFive.root7_table_cover`, must appear in the report; every additional introduced declaration is checked too.

`extraConstNames` can describe code-generator identities intentionally absent from the kernel constant map in this Lean version. This first bounded comparator explicitly rejects such an unavailable generated identity rather than silently excluding it. This can make a legitimate candidate inconclusive and requires review. Any field/inventory mismatch rejects the experiment and reports bounded differing field names, canonical names/counts, or axiom sets. Entire differing expressions are not serialized or claimed preserved. A strict mismatch does not establish unsoundness.

Original/candidate Part32 prerequisite copies are complete finite same-run artifact maps. Baseline outputs never enter common or candidate search roots. Their source/artifact identities and loaded owned module sets are verified before/after controls. All final candidate artifact families, original controls, helper/fixture inputs, source/archive/contract/distribution and runtime identities are revalidated. Native cleanup receipts with typed fields are persisted before any native capture read/hash; unsafe or unreceipted captures are omitted without reading. The inherited bounded collector cannot upgrade incomplete work into success.

## Exact API evidence and limits

The pinned Lean commit is `11acb17ec6b07a8f9e9173e6845197929540936b`. Four newly inspected API files and raw base64 readbacks are retained under provenance; their bundle manifest SHA256 is `8841ec0297b5e9e7ee71aec34b3457056d52773dccf4ecc8b8be30055d018071`. Declaration/Expr/SMap/PersistentHashMap exact source hashes and Git blob identities are in SOURCE_READBACK/MAP_SOURCE_READBACK. Retained Environment, upstream checker and Lake.Check.Util source patterns supply private-module loading, imported environment APIs, and axiom traversal. Original copyright/license headers and adaptation attribution are retained.

Runtime acquisition/decompression and direct Git metadata reads are inherited unchanged and remain outside the managed command ledger, under their existing finite bounds and the global HostDeadline. No project object reuse, external kernel, full Solution exporter/comparator, or complete original 388-module rebuild is claimed.

## Inert controls

`python3 -I -B tests/run_guarded.py` and its `-O` variant install the permanent audit guard before loading target code. The guard refuses process/native/network events and remains installed after tests. The actual-loop fixture is synthetic: it runs real source extraction, graph validation, all 388 admission iterations, exact view copies, command/capture validation, terminal checks and bounded collection, while substituting runtime acquisition, native execution, checkout metadata and activation validation. Its fabricated logs and artifact bytes never constitute Lean elaboration or kernel evidence. Actual helper typing, real fixtures and the project test remain unexecuted until separate authorization and source review.

## Narrow syntax-repair successor

The earlier published attempt 39257136601 at commit 9221f12f2a9a577e71505a12f470bb868450e894 failed its first interface API/self-test command before fixture or owned-project compilation. Its retained 891-byte diagnostic is pinned in provenance. This successor is unexecuted and inactive on branch `verify/palomar-root7-import-cut-syntax-20261019`.

The helper changes exactly four paired loops to the retained pinned upstream grammar `for left in xs, right in ys do`, plus whitespace/layout in the diagnosed DefinitionVal literal. An adjacent RecursorVal literal with the same layout pattern receives an explicitly identified preventive whitespace-only correction; it was not separately diagnosed. Every field, expression, comparison, axiom traversal, rejection, source fixture, command count and resource bound is preserved. The source controls reverse all six sites to the exact predecessor helper and scan the complete helper for remaining instances of both confirmed pattern families. These are static regression controls, not local Lean elaboration evidence. The exact API/self-test remains the first native Lean gate. No pinned local toolchain was found in the checked workspace/system locations; no local Lean execution or acquisition was performed.

Branch selection, normalized workflow-template pin, inactive activation fields, provenance/test additions and resulting input hashes are itemized separately from the six helper syntax sites. Activation must bind a new independent review and exactly this new branch/template. The prior published active packet is preserved.
