# Conditional geometry replay: C remains an explicit assumption

This is a reviewed, bounded conditional verification attempt. The workflow runs only on the verify/conditional-geometry-20261016 branch, using one standard Ubuntu runner. Successful source publication or startup does not certify an unconditional theorem; C remains an explicit assumption throughout.

## Exact scope

One fresh, sequential job compiles and kernel-checks the exact source union reachable from:

- NativeFinalAssembly.CurvedOfParent / NativeFinalAssembly.curved_monotile_of_parent
- NativeFinalAssembly.KeyedProductOfParent / NativeFinalAssembly.keyed_product_monotile_of_parent

There are 2,481 owned modules: 2,142 ordinary geometry/support modules, 333 finite-C prerequisites, four ordinary bridge replacements, and two conditional assemblies. Both assemblies are last. The commonly quoted 2,144 owned geometry modules already include those two assemblies. All 333 prerequisites are rebuilt in this job; no object from a prior run is admitted.

The exact named premise remains SpectreFinite.HexSearch.NativeHierarchy.ParentOccurrenceTheorem. Its definition is checked against: for every f : Position → State, GloballyLegal f implies OccurrenceComplete f (hexRegion 5) ParentOwnership.certifiedParentFamily. Each endpoint has exactly one explicit C binder and no universe parameters. Its conclusion is nonempty interior and IsAperiodicMonotile for the exact curved planar body or exact keyed four-dimensional body. The latter model states compactness, tiling existence, and translational aperiodicity. This candidate does not assert the separate hierarchy theorem C, a ball homeomorphism, a Euclidean symmetry bound, infinitely many inequivalent shapes, or every dimension.

SpectreFinite.RadiusFivePruningHierarchy, ClosedCurvedFinal, ClosedKeyedProductFinal, and independent Challenge theorem holes are excluded. The four bridge sources are ordinary Lean theorems; original object-generating programs and historical proof objects are not executed or restored.

## Source provenance and the explicit visibility exception

The frozen modern source map is bound by locks/source-lineage.json, which retains selected original-to-modern hashes and insertion descriptions. Original source snapshots remain unchanged. locks/owned-sources.json pins every exact selected file, role, ordered imports and topological position. The runner re-parses each actual source header and recomputes the endpoint-reachable union before acquiring dependencies.

One explicit source variant is layered over that frozen map: SpectreGeometry.PolygonProductKeyBody, SHA256 c4859ed11b299786f0412b26172ff0c3f997f1322936d641778f09e73d5b9758. Exactly two command-local `set_option backward.privateInPublic true in` insertions retain the private keyword, kernel name, and source proof/type bodies while changing the helper’s export visibility at those two declarations. The exception is not global and does not disable warnings. locks/visibility-exception.json records the original variant and the successful 69-module body/model diagnostic, run 38860127094 at commit 5add4d229849d61853b3456d40efdc5031f35916. That result establishes the tested body/model equalities, not successful elaboration of the remaining geometry or exact raw identity of every migrated declaration.

Four further modules carry a separately reviewed, source-only prediction overlay in locks/visibility-predictions.json: DeformationHomeomorphism (2 scopes), PhysicalGridRealization (2), ReverseClusterCocycleIntegration (4), and PolygonProductKeyFactorTransition (6). Those fourteen command-local lines add exactly 616 bytes. Every original byte, declaration name, import, source type/proof body, and private keyword is preserved; helper export visibility changes explicitly. Synthetic core-chain controls support the pattern, but these actual research variants have not been elaborated or shown raw-expression-identical. Two unnecessary theorem-level scopes were removed before review. DeformationHomeomorphism has no owned dependencies and is the first owned compile/check pair, so the fresh run tests this new pattern immediately. The two previously proven PolygonProductKeyBody scopes remain unchanged. There are sixteen local option lines across five modules in total.

## Explicitly trusted official cache boundary

The official Lean v4.35.0-rc2 archive, full runtime inventory, nine exact official Git dependency revisions, authenticated source blobs, pinned cache-client source, official source-symlink exceptions, clean environment, bubblewrap isolation, and master/legacy cache flags are inherited from the reviewed body diagnostic.

The needed external union contains 2,786 cached modules, from 97 direct package imports; the two direct runtime imports are Init and Init.Data.Rat. All cache providers and modern companions are required. Cache bytes are explicitly trusted official binaries and are inventoried; they are not claimed to have been rebuilt or cryptographically authenticated from those source bytes. The original clean-source requirement is not silently relabeled. No cache server override, fork, unsafe cache mode, prior owned artifact, or hidden fallback is admitted.

## Compiler and checker changes

The old 69-module body runner is extended, rather than replaced by a new distributed build system:

1. First require an inert sandbox boundary preflight to reject predecessor overwrite, chmod, and shadow-directory creation while allowing a quarantine write. Then build the pinned official cache client and acquire the exact official cache closure, with candidate sources absent from the network-enabled namespace. Record the complete cache/build/runtime inventories. Download archives can then be deleted; admitted package builds remain read-only.
2. Keep exactly one complete committed owned-object root on LEAN_PATH. This provides every owned namespace, including the shared SpectreFinite and SpectreGeometry prefixes. No quarantine or partial alternate root is ever on LEAN_PATH.
3. For each source, run Lean with -j1, -M4096, and -Dcompiler.postponeCompile=false. The compiler can write only its new quarantine, home, and temporary directories. Runtime, package builds, source, and every committed predecessor object are read-only in its sandbox. Required outputs are exactly .olean, .olean.private, .olean.server, .ilean, .ir.sig, .ir, and .c.
4. The host validates that exact quarantine tree, rejects symlinks, hardlinks, unexpected files/directories and overwrite attempts, and moves those seven companions into the complete committed root. Then leanchecker imports the module from that root read-only. A failed checker immediately ends the run; it cannot be converted into an accepted predecessor.
5. Record each source hash, ordered direct-import companion hashes/provider, command indexes and output hashes in append-only module receipts. Cache imports bind the exact admitted cached companion hashes; runtime imports bind the pinned runtime and direct object hash. Every owned predecessor must already have a successful checker receipt.
6. Compile and check two core-only auditors against only the official runtime. Execute them against the read-only fresh owned closure and trusted package roots. They use importModules with trustLevel 0 and loadExts false; no project extension is executed by those imports. Per-module leanchecker success remains a separate required gate.
7. Rehash the complete owned outputs and all external build/source inputs once at the end. Verify every compile/check pair and both raw audits, preserve complete bounded logs, and only then issue the terminal conditional-success receipt.

This removes the old quadratic whole-output rehash around every command. The replacement security boundary is read-only predecessor mounts plus an exact, host-only admission operation, per-current-module post-check hashes, import receipts, and a final whole-tree comparison. This boundary has passed independent static review and the separate tiny shared Ubuntu probe described below. Synthetic tests specifically exercise same-prefix imports and checker resolution without a quarantine search path.

Owned .ir and .ir.sig files are freshly emitted interpreter/native-compilation interfaces. Generated .c is retained as a compiler output but is not compiled or linked into owned shared libraries. There are no owned native_decide, #eval, run_tac, run_cmd, unsafe or implemented_by commands in the selected source scan. Cached package elaborators and native libraries remain part of the explicit official-cache trust boundary. Original bridge generators are replaced by four fresh ordinary theorem sources.

## Audit gates and limits of the result

The endpoint auditor checks exact raw Expr.equal types, binder identity and annotation, closed theorem proofs, universe lists, the named and expanded C definition, module ownership, the exact expected target set, and transitive axiom subsets of {propext, Classical.choice, Quot.sound}. The bridge auditor retains the four explicit proof-application constructions and adds strict module ownership and Expr.equal checks. Its original predecessor used mathematical alpha-equivalence (`==`); that was a meaningful mathematical check but did not establish the stricter representation identity. Original helper provenance is retained separately.

A successful run still does not establish an unconditional result, independently replay an exported entire final closure, or certify all paper claims. The expected status is CACHE_BACKED_CONDITIONAL_GEOMETRY_REPLAY_COMPLETED, with conditional_C_remains_explicit=true and both final_C_proof_certified and unconditional_monotile_proof_certified=false. Ordinary per-module leanchecker results must not be described as a successful `leanchecker --fresh` or export-mode replay of an unconditional final theorem.

## Bounded resource proposal

- One standard public Ubuntu 22.04 job, no matrix or parallel owned builds
- Outer job maximum: 330 minutes; aggregate runner deadline: 19,200 seconds (320 minutes)
- Owned compiler: at most 180 seconds per module; checker: at most 120 seconds per module
- Each of two audit helpers: compiler 180 seconds, checker 120 seconds, audit execution 600 seconds
- Lean heap: 4,096 MiB; process-tree RSS cap: 8 GiB; address-space limit: 12 GiB; one Lean thread
- Owned source cap: 32 MiB; owned companions: 6 GiB; a module's quarantine: 512 MiB aggregate and per-file cap
- Cache acquisition: 3 GiB download inventory; up to 5 GiB aggregate package builds, 4 GiB per package; cache downloads are removed only after admission/inventory
- Minimum measured disk reserve: 9 GiB before cache acquisition, 1.5 GiB before each owned module; failures preserve failure status rather than resizing billing or deleting unrelated files
- Complete command logs: 1 MiB per stdout/stderr-limited command invocation, 64 MiB aggregate; runner evidence cap: 124 MiB, plus a 4 MiB collection-manifest reserve inside a 128 MiB upload envelope; seven-day evidence retention; no owned objects uploaded

These are refusal/time-out bounds, not a claim that all modules will finish within them. Per-module compiler/checker caps sum to 744,300 seconds (206.75 hours), far above the aggregate budget; the 320-minute aggregate deadline always wins. Full-closure time and output-size distributions remain unmeasured.

Measured neighboring evidence: the successful 69-module body diagnostic spent 445.224236 seconds in its compile/check commands and 519.145654 seconds across all recorded commands; its fresh companions were 23,746,481 bytes and cached package builds 2,378,205,512 bytes. The first 128 modules in the successful 333-prerequisite run spent 432.75208 seconds compiling and 161.71637 seconds checking, with 200,614,080 object bytes and maximum sampled RSS 622,039,040 bytes. That finite stage is atypically large. Neither sample is representative enough to guarantee a 2,481-module replay. A simple body-average extrapolation alone is approximately 267 minutes before full audit/collection overhead and tail effects; it is illustrative arithmetic, not a forecast or launch justification.

## Review and reproduction

Run the static/synthetic suite without loading research objects:

    PYTHONDONTWRITEBYTECODE=1 python3 -B -m unittest discover -s tests -v

The pinned runner command is:

    python3 -I -B ci/cache_diagnostic.py --contract-sha256 <reviewed contract hash> --work <new empty workspace>

The frozen metadata-size estimate exercises all 2,481 production-loop pairs with synthetic outputs. With inflated size fields, observed external inventories, additional metadata reserves, and the full 64 MiB log budget, it estimates 122,828,207 bytes of runner evidence, leaving 7,195,217 bytes below the 124 MiB cap. This is not a runtime admission guarantee. The collector verifies contract identity, exact ordered pair coverage, adjacent indexes, source/output maps, complete log hashes, inventory hashes, and terminal status. Copying all files from a failed or interrupted run never means acceptance evidence is complete.

The workflow pins the reviewed contract hash and checkout/upload action commits. The activation changes only review metadata, this documentation and the exact-branch push trigger. The reviewed read-only/quarantine architecture, receipt semantics, resource bounds, raw auditors and complete source identities remain unchanged. Actual research elaboration and endpoint audits are still pending. Source, static tests and tiny controls are not research replay success.

## Source-archive distribution variant

This distribution keeps the 25 non-source files in ordinary plaintext and replaces the 2,481 individual source blobs with one deterministic source-only archive, `owned-sources.tar.gz`. The original reviewed candidate and all source bytes remain unchanged. The contract retains every original source path, size and SHA-256 pin; it separately lists the exact 26-file distribution tree and archive identity.

After exact-tree and clean-Git checks, the host authenticates the complete compressed archive before bounded single-gzip decompression. It accepts only canonical USTAR regular-file records, in exact manifest order, with exact per-file hashes and sizes. Links, directories, extensions, duplicates, aliases, traversal, unlisted files, oversized data and trailing gzip/tar payload are refused. No tar extraction API is used. Files are created exclusively in a new `work/source-input` root, then the existing modern source-header, import graph, reachable-union and per-file checks run against that root before any runtime acquisition, cache acquisition or research compilation. A failed partial extraction cannot be resumed. An extraction receipt is retained in the evidence.

The compiler/checker sandbox, ordinary bridges, conditional endpoint auditors, mathematical scope, resource limits and official-cache trust are unchanged. The additional bounded extraction can hold at most 8 MiB of compressed data and 64 MiB of tar framing in host memory; pinned source content is still bounded by 32 MiB. The shared Ubuntu boundary probe passed before this activation; its exact run and evidence hashes are bound in contract.json.

## Shared boundary preflight

The prerequisite probe succeeded at https://github.com/jconorgrogan/palomar-chair-verification/actions/runs/38866342200, commit 0038bfec18995c396224f70acb2565db8a811dfd. It checked both the C-stage session configuration and this conditional runner's explicit new-session configuration, with six tiny compile/check pairs, write-denial controls and successful process cleanup for all sixteen commands. Eighteen C companion payloads were independently rehashed; twenty-one conditional companion hash receipts were validated, with those conditional payload bytes absent from the diagnostic artifact. This small Init-only test establishes the exercised execution boundary, not any research theorem. The conditional runner's seven sandbox/admission functions are byte-identical to those exercised by the probe.
