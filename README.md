# Aperiodic monotiles in every dimension d ≥ 2

Conor Grogan, author and responsible maintainer

We construct one aperiodic tile shape for each Euclidean dimension d ≥ 2: copies fill space, but no tiling repeats under a nonzero translation. Rotations and reflections are allowed. The all-dimensional Lean proof compiles, including the four-dimensional JACKIE construction.

[Read the current paper: Aperiodic Monotiles in Every Dimension (22 October 2026, PDF)](papers/all-dimensions/aperiodic-monotiles-every-dimension-2026-10-22.pdf)

JACKIE is the exact 56-key product body used for d = 4 in the compiled all-dimensional Lean theorem. It has nonempty interior, is compact, admits a physical tiling, and excludes every nonzero translational period in every tiling. See the [exact body](https://github.com/jconorgrogan/palomar-chair-verification/blob/048bb245b60abce79f1a2d0c82336ff8508ec752/src/SpectreGeometry/PolygonProductKeyBody.lean#L24-L26), [four-dimensional proof](https://github.com/jconorgrogan/palomar-chair-verification/blob/048bb245b60abce79f1a2d0c82336ff8508ec752/src/NativeFinalAssembly/KeyedProductOfParent.lean#L16-L30), and [selected d = 4 branch](https://github.com/jconorgrogan/palomar-chair-verification/blob/048bb245b60abce79f1a2d0c82336ff8508ec752/src/NativeFinalAssembly/AllDimensionsOfParent.lean#L26-L29). JACKIE is separate from the odd-prime construction family.

CLARK, the original sparse five-dimensional T5 body, is Lean-formalized, independently verified, and [registered in Palomar as PALOMAR-2026-10-07-000006 v1](https://palomar-registry.org/entry?id=PALOMAR-2026-10-07-000006&version=1). Its stronger theorem proves that every tiling has a finite full Euclidean symmetry group of at most 3,840 elements. [Exact registered proof](https://github.com/jconorgrogan/palomar-chair-verification/blob/5f5ceedee770b76c21e8f1105e5e4e3b84b8d676/Solution.lean).

For every integer d ≥ 2, the [compiled Lean endpoint](https://github.com/jconorgrogan/palomar-chair-verification/blob/048bb245b60abce79f1a2d0c82336ff8508ec752/src/PalomarAllDimensionsSolution.lean#L19-L41) proves the existence of a compact tile with nonempty interior, a physical tiling, and universal translation aperiodicity in each dimension. The former parent-occurrence premise C is [proved and supplied internally](https://github.com/jconorgrogan/palomar-chair-verification/blob/048bb245b60abce79f1a2d0c82336ff8508ec752/src/NativeFinalAssembly/AllDimensions.lean#L16-L23); it is no longer a premise of the selected theorem.

The all-dimensional submission, including JACKIE, exhausted Palomar's 19,800-second (5½-hour) worker budget and needs additional compute to finish the independent checks. Its [official preflight](https://github.com/jconorgrogan/palomar-chair-verification/actions/runs/39294694136) built all 12,476 Lake jobs in the selected Solution and exported both Challenge and Solution proofs. The final statement/definition comparison, external-kernel checks, and final-endpoint axiom audit remain unfinished. The all-dimensional result has compiled but has not completed Palomar verification or registration. CLARK's separate registration is complete.

[Construction and proof](#construction-and-proof) · [Finite full symmetry](#finite-full-symmetry) · [Papers](#papers) · [Verification evidence](#verification-evidence) · [Reproduction](#reproduction) · [Verification history](#verification-history)

## Construction and proof

A physical tiling is a collection of isometric copies of the tile that covers Euclidean space and has disjoint interiors for distinct tile sets. A period must preserve the tile collection; preserving its union is insufficient. No lattice registration, matching labels, orientation restriction, or hierarchy is assumed in this physical statement. The shape may depend on the dimension.

### JACKIE and the four-dimensional branch

JACKIE is the keyed product of two planar polygonal carriers, defined in Lean as `SpectreGeometry.polygonProductKeyBody`. Its 56 pyramidal keys enforce the structure used in the physical tiling proof.

The Lean proof uses these modules:

1. [KeyedProductOfParent.lean](https://github.com/jconorgrogan/palomar-chair-verification/blob/048bb245b60abce79f1a2d0c82336ff8508ec752/src/NativeFinalAssembly/KeyedProductOfParent.lean) supplies the four-dimensional theorem with the parent-occurrence premise C.
2. [RadiusFivePruningHierarchy.lean](https://github.com/jconorgrogan/palomar-chair-verification/blob/048bb245b60abce79f1a2d0c82336ff8508ec752/src/SpectreFinite/RadiusFivePruningHierarchy.lean#L11-L16) proves C as `certifiedParentOccurrenceTheorem`.
3. [AllDimensionsOfParent.lean](https://github.com/jconorgrogan/palomar-chair-verification/blob/048bb245b60abce79f1a2d0c82336ff8508ec752/src/NativeFinalAssembly/AllDimensionsOfParent.lean#L18-L30) selects JACKIE in dimension four, and [AllDimensions.lean](https://github.com/jconorgrogan/palomar-chair-verification/blob/048bb245b60abce79f1a2d0c82336ff8508ec752/src/NativeFinalAssembly/AllDimensions.lean#L16-L23) supplies the proved C theorem to the assembly.
4. [PalomarAllDimensionsSolution.lean](https://github.com/jconorgrogan/palomar-chair-verification/blob/048bb245b60abce79f1a2d0c82336ff8508ec752/src/PalomarAllDimensionsSolution.lean#L36-L41) exposes the resulting theorem with only d and 2 ≤ d as arguments.

A separate source-level geometric and exact-arithmetic review counts 362 connected flat three-dimensional boundary pieces for JACKIE. Exact-body polyhedrality and this boundary count are not completed Lean theorems and are not part of the selected all-dimensional endpoint.

### The other dimensions

The assembly uses the exact curved planar body in dimension two and the repeatable keyed-product compiler in dimension three and every dimension at least five. The compiler adds certified dimensions while rebuilding registration keys and preserving tiling existence and universal aperiodicity. See the [dimension-addition proof](https://github.com/jconorgrogan/palomar-chair-verification/blob/048bb245b60abce79f1a2d0c82336ff8508ec752/src/ProductClosure/ProductDimensions.lean), [three-dimensional seed](https://github.com/jconorgrogan/palomar-chair-verification/blob/048bb245b60abce79f1a2d0c82336ff8508ec752/src/ProductClosure/CertifiedDimensions.lean), and [coverage of every dimension at least five](https://github.com/jconorgrogan/palomar-chair-verification/blob/048bb245b60abce79f1a2d0c82336ff8508ec752/src/ClarkSeed/PhysicalDimensions.lean#L23-L55).

The compiler's five-dimensional seed is a dense body derived from CLARK certificates. The development does not identify this seed with the original sparse registered CLARK body, or its seven-dimensional seed with the sparse HENRY construction.

### CLARK and its registered theorem

CLARK stands for Chair with Local Asymmetric Registration Keys. Its Lean identifier is `T5`.

![Planar section of a level-five CLARK carrier patch with matching-key zooms](CLARK_overview.png)

The main panel shows carrier sections. Matching keys are resolved in the 12× and 690× zooms of the same plane. Colours count negative coordinate signs; all displayed full frames preserve orientation. The small target ring is enlarged 2.2× for visibility. See [figure details and the sections/key diagrams](figures/README.md).

The tile modifies a chair made from 31 unit five-cubes with 256 rational pyramidal keys. Translated, rotated, and reflected copies are allowed. The Lean theorem proves that this exact body is compact, admits a physical tiling, and has no nonzero translational period in any such tiling, without assuming lattice registration or matching rules. Every tiling also has a finite full Euclidean symmetry group of at most 3,840 elements. Here, strongly aperiodic means finite full symmetry group; a trivial symmetry group is not asserted. See the [exact tile definition](https://github.com/jconorgrogan/palomar-chair-verification/blob/5f5ceedee770b76c21e8f1105e5e4e3b84b8d676/Challenge.lean), the [selected theorem proof](https://github.com/jconorgrogan/palomar-chair-verification/blob/5f5ceedee770b76c21e8f1105e5e4e3b84b8d676/Solution.lean), and the [complete physical monotile theorem](https://github.com/jconorgrogan/palomar-chair-verification/blob/5f5ceedee770b76c21e8f1105e5e4e3b84b8d676/SparseMonotiles/T5Monotile.lean).

## Finite full symmetry

The mathematical extension dated 22 October 2026 uses existing source lemmas to prove that the constructed monotiles in every integer dimension d > 2 have finite full Euclidean symmetry groups in every admitted tiling. This excludes all infinite-order screw and glide symmetries; it does not assert trivial symmetry groups. For the compiler witnesses in d = 3 and d ≥ 5, the argument gives |Sym(T)| ≤ 2^d d!. Dimension 4 uses a separate planar-factor argument; no numerical bound is claimed for that branch.

The argument has received a separate AI mathematical/source review. The new finite-symmetry deductions and stronger all-dimensional endpoint have not been implemented in Lean, compiled, independently kernel-checked, or registered in Palomar.

[Read the mathematical extension](papers/FINITE_SYMMETRY_EXTENSION_2026-10-22.md) · [Read the AI source review and its limits](papers/FINITE_SYMMETRY_SOURCE_REVIEW_2026-10-22.md)

## Papers

- Current all-dimensional paper, 22 October 2026: [Aperiodic Monotiles in Every Dimension (PDF)](papers/all-dimensions/aperiodic-monotiles-every-dimension-2026-10-22.pdf), [Word](papers/all-dimensions/aperiodic-monotiles-every-dimension-2026-10-22.docx), [editable text](papers/all-dimensions/aperiodic-monotiles-every-dimension-2026-10-22.md), and [manuscript source and document-generation files (ZIP)](papers/all-dimensions/aperiodic-monotiles-every-dimension-2026-10-22-source.zip). It covers the compiled Lean result, JACKIE, and the mathematical finite-symmetry proof. This revision has no new Zenodo version or DOI.
- Archived all-dimensional working paper, 16 October 2026 snapshot: [PDF](papers/all-dimensions-working/aperiodic-monotiles-every-dimension-working-v1.pdf), [Word](papers/all-dimensions-working/aperiodic-monotiles-every-dimension-working-v1.docx), [editable text](papers/all-dimensions-working/aperiodic-monotiles-every-dimension-working-v1.md), and [dated claim scope](papers/all-dimensions-working/README.md). Its pending-C and pending-uniform-theorem statements predate the successful build and proof exports.
- Finite full symmetry in every dimension d > 2, 22 October 2026: [mathematical extension](papers/FINITE_SYMMETRY_EXTENSION_2026-10-22.md) and [separate AI mathematical/source review](papers/FINITE_SYMMETRY_SOURCE_REVIEW_2026-10-22.md). The stronger endpoint is not implemented in Lean.
- Earlier CLARK/HENRY and odd-prime paper: [An Arithmetic Family of Aperiodic Tilings in Odd Prime Dimensions, version 2 (PDF)](CLARK_paper.pdf?raw=1), [Zenodo record 23197680](https://zenodo.org/records/23197680), DOI [10.5281/zenodo.23197680](https://doi.org/10.5281/zenodo.23197680). The [CFF](CITATION.cff) and [BibTeX](CITATION.bib) files cite this earlier paper, as does the Zenodo DOI.

The earlier paper gives a written computer-assisted proof for the sparse seven-dimensional HENRY body and a hierarchy theorem for registered chair matching rules in every odd-prime dimension. Complete Lean verification of that exact HENRY body remains unfinished. The [historical mathematical account](https://github.com/jconorgrogan/palomar-chair-verification/blob/9008dec3afc006a62d3d2fd6b49b12f189248f33/README.md#broader-program) describes those results.

## Verification evidence

The all-dimensional source, including JACKIE, is frozen at [`048bb245b60abce79f1a2d0c82336ff8508ec752`](https://github.com/jconorgrogan/palomar-chair-verification/tree/048bb245b60abce79f1a2d0c82336ff8508ec752). The [independent Challenge](https://github.com/jconorgrogan/palomar-chair-verification/blob/048bb245b60abce79f1a2d0c82336ff8508ec752/src/PalomarAllDimensionsChallenge.lean) fixes the physical statement; the [Solution](https://github.com/jconorgrogan/palomar-chair-verification/blob/048bb245b60abce79f1a2d0c82336ff8508ec752/src/PalomarAllDimensionsSolution.lean) proves it without importing Challenge. Challenge intentionally contains a statement-only hole; the proof is in Solution.

The [official full preflight run 39294694136](https://github.com/jconorgrogan/palomar-chair-verification/actions/runs/39294694136) used Lean 4.35.0-rc2, the official reusable workflow pinned at `d4e41c1d5b0d114c4859e6e5831dc6d3ad1d0d44`, and the `palomar-standard-v1` profile. It records:

- `solution-build`: exit 0, 12,476 Lake jobs, 12,190.542 seconds.
- `challenge-export`: exit 0, 9.374 seconds.
- `solution-export`: exit 0, 72.796 seconds.
- Overall report: `status: error`, `stage: resource-exhausted`; Comparator was the last active stage when the shared 19,800-second worker budget ran out.

The final statement/definition comparison, external-kernel verification, and final-endpoint axiom audit remain unfinished. The existing axiom output covers helper C only. The run retained no resumable build/export checkpoint. Whether the remaining checks will pass is still unknown.

See the [verification note](verification/ALL_DIMENSIONS_STATUS_2026-10-20.md), [mechanical report](verification/ALL_DIMENSIONS_MECHANICAL_REPORT_39294694136.json), and [original report artifact](https://github.com/jconorgrogan/palomar-chair-verification/actions/runs/39294694136/artifacts/12227932621). The report mirror's SHA-256 is `a1681ef51911a64f4bfe975e283396cd7ef3f8f4fd2aac5130ecdd3c5ef23ec6`.

### CLARK verification

CLARK was [registered in Palomar as PALOMAR-2026-10-07-000006 v1](https://palomar-registry.org/entry?id=PALOMAR-2026-10-07-000006&version=1) on 7 October 2026. The registered result is `PalomarMonotiles.T5_strongAperiodicity` at immutable source commit `5f5ceedee770b76c21e8f1105e5e4e3b84b8d676`. The registry records successful mechanical verification and an automated review with no problems identified.

The selected theorem, independent Challenge, Solution and axiom audit passed local Lean 4.35.0-rc2 checks. The whole statement-definition comparison passed with no exemptions. The audited theorem depends only on `propext`, `Classical.choice`, and `Quot.sound`. The [extension evidence](https://github.com/jconorgrogan/palomar-chair-verification/blob/5f5ceedee770b76c21e8f1105e5e4e3b84b8d676/verification/STRONG_EXTENSION.md) records these local checks and their scope.

The [official full Palomar mechanical preflight passed](https://github.com/jconorgrogan/palomar-chair-verification/actions/runs/37544058631) for immutable source commit `5f5ceedee770b76c21e8f1105e5e4e3b84b8d676`. Lean's default kernel, NanoDa and verified con-ron all accepted the Solution; con-ron checked 69,558 declarations. The clean build completed 4,137 Lake jobs, and the source audit checked 1,357 Lean files. The [full mechanical report](verification/STRONG_MECHANICAL_REPORT_37544058631.json) records `status: pass`, `stage: complete`, and no errors or warnings. The [verification receipt](verification/STRONG_PREFLIGHT_PASS_37544058631.json) binds the source, report and checker results; the [original GitHub artifact](https://github.com/jconorgrogan/palomar-chair-verification/actions/runs/37544058631/artifacts/11454083416) remains available. Report JSON SHA-256: `82711b9d865e0441d453decdfebf5b4d071292f46b52a5e5ca77c385ed498884`.

The run used the reusable workflow pinned at `d4e41c1d5b0d114c4859e6e5831dc6d3ad1d0d44` under `palomar-standard-v1`, with no definition exemptions. The selected statement, `T5StrongClaim`, includes the 3,840 symmetry bound and the original compactness, tiling-existence and translation-aperiodicity claim as a conjunct. The independent Challenge fixes the exact shape and physical statement; Solution proves it without importing Challenge.

The complete stronger source is on [the T5 verification branch](https://github.com/jconorgrogan/palomar-chair-verification/tree/verification/palomar-strong1-20261006), frozen at commit [`5f5ceedee770b76c21e8f1105e5e4e3b84b8d676`](https://github.com/jconorgrogan/palomar-chair-verification/tree/5f5ceedee770b76c21e8f1105e5e4e3b84b8d676).

- [Full mathematical account and reproduction instructions](https://github.com/jconorgrogan/palomar-chair-verification/blob/5f5ceedee770b76c21e8f1105e5e4e3b84b8d676/README.md)
- [Finite full-symmetry proof](https://github.com/jconorgrogan/palomar-chair-verification/blob/5f5ceedee770b76c21e8f1105e5e4e3b84b8d676/SparseMonotiles/FiniteSymmetry.lean)
- [Independent Challenge](https://github.com/jconorgrogan/palomar-chair-verification/blob/5f5ceedee770b76c21e8f1105e5e4e3b84b8d676/Challenge.lean) and [actual Solution](https://github.com/jconorgrogan/palomar-chair-verification/blob/5f5ceedee770b76c21e8f1105e5e4e3b84b8d676/Solution.lean)
- [Structured metadata, source relationships, automation and review account](https://github.com/jconorgrogan/palomar-chair-verification/blob/5f5ceedee770b76c21e8f1105e5e4e3b84b8d676/formalization.yaml)
- [Exact source manifest](https://github.com/jconorgrogan/palomar-chair-verification/blob/5f5ceedee770b76c21e8f1105e5e4e3b84b8d676/SOURCE_MANIFEST.json)
- [Verification runs](https://github.com/jconorgrogan/palomar-chair-verification/actions)

The source manifest has SHA-256 `ec0ed3ed9927fe13aa654c713ce9eb83e2a52da7b3d6c6c6cea07efcebb998f3`. The snapshot contains the full proof development. The `main` branch is the public index and retains the earlier history.

## Reproduction

[Download the complete pinned all-dimensional source ZIP](https://github.com/jconorgrogan/palomar-chair-verification/archive/048bb245b60abce79f1a2d0c82336ff8508ec752.zip). The immutable snapshot includes the [Lean toolchain pin](https://github.com/jconorgrogan/palomar-chair-verification/blob/048bb245b60abce79f1a2d0c82336ff8508ec752/lean-toolchain), [Lake configuration](https://github.com/jconorgrogan/palomar-chair-verification/blob/048bb245b60abce79f1a2d0c82336ff8508ec752/lakefile.lean), [dependency manifest](https://github.com/jconorgrogan/palomar-chair-verification/blob/048bb245b60abce79f1a2d0c82336ff8508ec752/lake-manifest.json), [Comparator selection](https://github.com/jconorgrogan/palomar-chair-verification/blob/048bb245b60abce79f1a2d0c82336ff8508ec752/comparator.json), and [formalization metadata](https://github.com/jconorgrogan/palomar-chair-verification/blob/048bb245b60abce79f1a2d0c82336ff8508ec752/formalization.yaml). The selected Solution module is `PalomarAllDimensionsSolution`. The frozen source's "unexecuted" comments predate the successful build in run 39294694136.

For independent verification, use the [pinned official pipeline](https://github.com/PalomarRegistry/PalomarSubmission/tree/d4e41c1d5b0d114c4859e6e5831dc6d3ad1d0d44) and preserve the exact Challenge, Solution, dependency pins, and physical definitions. The independent checks still need to finish on a supported route with sufficient compute.

### Reproduce the registered CLARK source

[Download the complete pinned source ZIP](https://github.com/jconorgrogan/palomar-chair-verification/archive/5f5ceedee770b76c21e8f1105e5e4e3b84b8d676.zip).

Use a Linux host meeting the official standard-profile floor: at least 14 GiB RAM and 20 GiB free disk. Install Bash, Git, Python 3, curl 7.81 or newer with working TLS/network access, standard Unix utilities, and Bubblewrap with usable namespaces. The sandbox expects `/root`, `/home` and `/run/user` to exist. Use the official prebuilt Lean 4.35.0-rc2 toolchain (directly or through Elan), with `lean`, `lake`, `leanexport`, `leanchecker`, `nanoda_bin`, `con-ron` and `leantar` available from that toolchain. Rust, Cargo and CMake are not required for this prebuilt route.

From a directory without an existing `clark-replay` folder, run:

```sh
COMMIT=5f5ceedee770b76c21e8f1105e5e4e3b84b8d676; git clone https://github.com/jconorgrogan/palomar-chair-verification.git clark-replay && cd clark-replay && git checkout --detach "$COMMIT" && bash scripts/verify-t5-on-linux.sh
```

The script checks the exact source manifest, builds the selected proof and runs the bundled Comparator with Lean, NanoDa and verified con-ron. It requires Bubblewrap namespaces and can take an hour or more. This reproduces the proof, Comparator and kernel checks. The full Palomar workflow also checks metadata, Challenge provenance, execution-profile limits and its mechanical report.

## Verification history

The original CLARK theorem's [official full Palomar mechanical preflight passed](https://github.com/jconorgrogan/palomar-chair-verification/actions/runs/37520435323) for immutable source commit `9008dec3afc006a62d3d2fd6b49b12f189248f33`. The selected original T5 theorem covers compactness, tiling existence and no nonzero translation period in any physical tiling. Lean's default kernel, NanoDa and verified con-ron all accepted the Solution; con-ron checked 69,348 declarations. The [mechanical report artifact](https://github.com/jconorgrogan/palomar-chair-verification/actions/runs/37520435323/artifacts/11444507885) records `status: pass`, `stage: complete`, and no errors or warnings. The report JSON has SHA-256 `43edc2c785ceaa7ecff4b231a0a9738a5e320d6fd5b0461d6de88491f482f027`. This run used the full pinned reusable workflow under `palomar-standard-v1` for the original theorem, before the finite-symmetry extension. The registered version is the stronger snapshot cited above.

The [first full run](https://github.com/jconorgrogan/palomar-chair-verification/actions/runs/37509737027) clean-built all 4,135 Lake jobs but rejected a generated statement-helper proof before the independent main kernels. The repair replaced only two bound-proof blocks with explicit terms; the complete helper function is definitionally unchanged. Local whole-statement dependency comparison and affected-binding/Solution checks passed before the successful official retry. The [repair evidence](https://github.com/jconorgrogan/palomar-chair-verification/blob/9008dec3afc006a62d3d2fd6b49b12f189248f33/verification/COMPARATOR_REPAIR.md) records the changes and checks.

An [earlier four-result compatibility pilot](https://github.com/jconorgrogan/palomar-chair-verification/actions/runs/37466588417) passed the official Comparator and three kernels. That pilot checked four supporting statements, not the full T5 theorem.

### All-dimensional milestones

- 16 October 2026: the working paper recorded accepted native two- and four-dimensional results with C explicit, plus unconditional verification for dimension three and every dimension at least five. The [dated manuscript](papers/all-dimensions-working/aperiodic-monotiles-every-dimension-working-v1.md) records that stage of the work.
- 19 October 2026: the selected all-dimensional Solution built and both proof exports succeeded in [run 39294694136](https://github.com/jconorgrogan/palomar-chair-verification/actions/runs/39294694136); the remaining independent verification exhausted the worker budget. The [20 October verification note](verification/ALL_DIMENSIONS_STATUS_2026-10-20.md) reconciles the newer source and run with older metadata.
- 22 October 2026: the [revised all-dimensional manuscript](papers/all-dimensions/aperiodic-monotiles-every-dimension-2026-10-22.pdf) contains the construction, compiled translation-aperiodicity result, and mathematical finite-symmetry proof. The [finite-full-symmetry extension](papers/FINITE_SYMMETRY_EXTENSION_2026-10-22.md) and [AI source review](papers/FINITE_SYMMETRY_SOURCE_REVIEW_2026-10-22.md) give the argument and identify the Lean lemmas still to implement.

The [clean hierarchy-C campaign](https://github.com/jconorgrogan/palomar-chair-verification/actions/runs/39179019728), [174-module visibility test](https://github.com/jconorgrogan/palomar-chair-verification/actions/runs/39265576764), and [388-module import-optimization test](https://github.com/jconorgrogan/palomar-chair-verification/actions/runs/39279478084) are supporting checks; none completed the final all-dimensional verification.

## Attribution, production, and license

Adam Scherlis previously formulated the all-dimensional keyed-product program, including the four-dimensional construction and 56-key count, in his [pinned primary note](https://github.com/AdamScherlis/adamscherlis.github.io/blob/e05cee7245124a705ca68be3a8f641d290c664b4/static/monotiles-every-dimension/index.html). No priority is claimed here for that general idea, four-dimensional idea, count, or all-dimension formulation. Attribution is separate from verification of any particular argument.

AI systems made substantive contributions to mathematical analysis, Lean proofs, exact certificate generation, audits, migration and exposition. The metadata records those contributions separately from human authorship. No independent human mathematical peer review or novelty certification is claimed.

The companion preprint (`CLARK_paper.pdf`) and its figures are licensed under [Creative Commons Attribution 4.0 International (CC BY 4.0)](https://creativecommons.org/licenses/by/4.0/). The proof code is licensed under [Apache License 2.0](https://github.com/jconorgrogan/palomar-chair-verification/blob/9008dec3afc006a62d3d2fd6b49b12f189248f33/LICENSE). Lean, Mathlib and other dependencies retain their own licenses and notices.

