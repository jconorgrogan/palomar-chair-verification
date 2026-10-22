# Aperiodic Monotiles in Every Dimension d ≥ 2

Conor Grogan, author and responsible maintainer

We construct one aperiodic tile shape for each Euclidean dimension **d ≥ 2**: copies fill space, but no tiling repeats under a nonzero translation. Rotations and reflections are allowed. **The all-dimensional Lean proof compiles, including the four-dimensional JACKIE construction.**

[Read the current paper: Aperiodic Monotiles in Every Dimension (22 October 2026, PDF)](papers/all-dimensions/aperiodic-monotiles-every-dimension-2026-10-22.pdf)

## Main results

- **JACKIE in four dimensions.** The exact 56-key product body is formalized in Lean and is the explicit d = 4 case of the compiled all-dimensional theorem. It has nonempty interior, is compact, admits a physical tiling, and excludes every nonzero translational period in every tiling. See the [exact body](https://github.com/jconorgrogan/palomar-chair-verification/blob/048bb245b60abce79f1a2d0c82336ff8508ec752/src/SpectreGeometry/PolygonProductKeyBody.lean#L24-L26), [four-dimensional proof](https://github.com/jconorgrogan/palomar-chair-verification/blob/048bb245b60abce79f1a2d0c82336ff8508ec752/src/NativeFinalAssembly/KeyedProductOfParent.lean#L16-L30), and [selected d = 4 branch](https://github.com/jconorgrogan/palomar-chair-verification/blob/048bb245b60abce79f1a2d0c82336ff8508ec752/src/NativeFinalAssembly/AllDimensionsOfParent.lean#L26-L29). JACKIE is separate from the odd-prime construction family.
- **CLARK in five dimensions.** The original sparse T5 body is Lean-formalized, independently verified, and [registered in Palomar as PALOMAR-2026-10-07-000006 v1](https://palomar-registry.org/entry?id=PALOMAR-2026-10-07-000006&version=1). Its stronger theorem proves that every tiling has a finite full Euclidean symmetry group of at most **3,840** elements. [Exact registered proof](https://github.com/jconorgrogan/palomar-chair-verification/blob/5f5ceedee770b76c21e8f1105e5e4e3b84b8d676/Solution.lean).
- **Every integer dimension d ≥ 2.** The [compiled Lean endpoint](https://github.com/jconorgrogan/palomar-chair-verification/blob/048bb245b60abce79f1a2d0c82336ff8508ec752/src/PalomarAllDimensionsSolution.lean#L19-L41) proves the existence of a compact tile with nonempty interior, a physical tiling, and universal translation aperiodicity in each dimension. This includes every dimension above two, not only odd primes. The former parent-occurrence premise C is [proved and supplied internally](https://github.com/jconorgrogan/palomar-chair-verification/blob/048bb245b60abce79f1a2d0c82336ff8508ec752/src/NativeFinalAssembly/AllDimensions.lean#L16-L23), not assumed by the selected theorem.

**Verification boundary.** The all-dimensional submission, including JACKIE, is awaiting additional compute for its remaining independent checks after exhausting Palomar's **19,800-second (5½-hour) worker budget**. Its [official preflight](https://github.com/jconorgrogan/palomar-chair-verification/actions/runs/39294694136) successfully built all **12,476 Lake jobs** in the selected Solution and exported both Challenge and Solution proofs. The final statement/definition comparison, external-kernel checks, and final-endpoint axiom audit remain unfinished. This is a compiled Lean result, not yet a fully verified or registered all-dimensional Palomar result; CLARK's separate registration is complete.

[Construction and proof](#construction-and-proof) · [Finite full symmetry](#finite-full-symmetry) · [Papers](#papers) · [Verification evidence](#verification-evidence) · [Reproduction](#reproduction) · [Verification history](#verification-history)

## Construction and proof

A physical tiling is a collection of isometric copies of the tile that covers Euclidean space and has disjoint interiors for distinct tile sets. Aperiodicity tests the tile collection, not its union. No lattice registration, matching labels, orientation restriction, or hierarchy is assumed in this physical statement. The shape may depend on the dimension.

### JACKIE and the four-dimensional branch

JACKIE is the literal keyed product of two planar polygonal carriers, retaining the Lean name `SpectreGeometry.polygonProductKeyBody`. Its **56 pyramidal keys** enforce the structure used in the physical tiling proof. The source theorem proves compactness, nonempty interior, existence, and universal translation aperiodicity for this exact body.

The proof chain is explicit:

1. [KeyedProductOfParent.lean](https://github.com/jconorgrogan/palomar-chair-verification/blob/048bb245b60abce79f1a2d0c82336ff8508ec752/src/NativeFinalAssembly/KeyedProductOfParent.lean) supplies the four-dimensional theorem with the parent-occurrence premise C.
2. [RadiusFivePruningHierarchy.lean](https://github.com/jconorgrogan/palomar-chair-verification/blob/048bb245b60abce79f1a2d0c82336ff8508ec752/src/SpectreFinite/RadiusFivePruningHierarchy.lean#L11-L16) proves C as `certifiedParentOccurrenceTheorem`.
3. [AllDimensionsOfParent.lean](https://github.com/jconorgrogan/palomar-chair-verification/blob/048bb245b60abce79f1a2d0c82336ff8508ec752/src/NativeFinalAssembly/AllDimensionsOfParent.lean#L18-L30) selects JACKIE in dimension four, and [AllDimensions.lean](https://github.com/jconorgrogan/palomar-chair-verification/blob/048bb245b60abce79f1a2d0c82336ff8508ec752/src/NativeFinalAssembly/AllDimensions.lean#L16-L23) supplies the proved C theorem to the assembly.
4. [PalomarAllDimensionsSolution.lean](https://github.com/jconorgrogan/palomar-chair-verification/blob/048bb245b60abce79f1a2d0c82336ff8508ec752/src/PalomarAllDimensionsSolution.lean#L36-L41) exposes the resulting theorem with only d and 2 ≤ d as arguments.

Thus four dimensions is covered by the selected compiled development, not a conjectural extension of the odd-prime family. Older source comments and the 16 October manuscript describe earlier verification stages; the completed build and exports are recorded in the later official run.

A separate source-level geometric and exact-arithmetic review counts **362 connected flat three-dimensional boundary pieces** for JACKIE. Exact-body polyhedrality and this boundary count are not completed Lean theorems and are not part of the selected all-dimensional endpoint.

### The other dimensions

The assembly uses the exact curved planar body in dimension two and the repeatable keyed-product compiler in dimension three and every dimension at least five. The compiler adds certified dimensions while rebuilding registration keys and preserving tiling existence and universal aperiodicity. See the [dimension-addition proof](https://github.com/jconorgrogan/palomar-chair-verification/blob/048bb245b60abce79f1a2d0c82336ff8508ec752/src/ProductClosure/ProductDimensions.lean), [three-dimensional seed](https://github.com/jconorgrogan/palomar-chair-verification/blob/048bb245b60abce79f1a2d0c82336ff8508ec752/src/ProductClosure/CertifiedDimensions.lean), and [coverage of every dimension at least five](https://github.com/jconorgrogan/palomar-chair-verification/blob/048bb245b60abce79f1a2d0c82336ff8508ec752/src/ClarkSeed/PhysicalDimensions.lean#L23-L55).

The compiler's five-dimensional seed is a dense body derived from CLARK certificates, not an identification with the original sparse registered CLARK body. Its seven-dimensional seed is not identified with the separately named sparse HENRY construction. These body identities and their verification scopes must not be conflated.

### CLARK and its registered theorem

We call the five-dimensional construction **CLARK**, for **Chair with Local Asymmetric Registration Keys**. It retains the Lean identifier **T5**.

![Planar section of a level-five CLARK carrier patch with matching-key zooms](CLARK_overview.png)

The main panel shows carrier sections. Matching keys are resolved in the 12× and 690× zooms of the same plane. Colours count negative coordinate signs; all displayed full frames preserve orientation. The small target ring is enlarged 2.2× for visibility. See [figure details and the sections/key diagrams](figures/README.md).

We give an explicit compact tile in five-dimensional Euclidean space and prove that it admits tilings but no periodic tiling. The construction modifies a chair made from 31 unit five-cubes with 256 rational pyramidal keys. Copies may be translated, rotated, or reflected. The theorem states that every tiling by these copies has no nonzero translation preserving its tile collection. It also proves that the full Euclidean symmetry group of every such tiling is finite, with at most **3,840** elements. Here, strongly aperiodic means finite full symmetry group; a trivial symmetry group is not asserted. The Lean formalization fixes the exact body and proves compactness, existence, and aperiodicity without assuming lattice registration or matching rules. See the [exact tile definition](https://github.com/jconorgrogan/palomar-chair-verification/blob/5f5ceedee770b76c21e8f1105e5e4e3b84b8d676/Challenge.lean), the [selected theorem proof](https://github.com/jconorgrogan/palomar-chair-verification/blob/5f5ceedee770b76c21e8f1105e5e4e3b84b8d676/Solution.lean), and the [complete physical monotile theorem](https://github.com/jconorgrogan/palomar-chair-verification/blob/5f5ceedee770b76c21e8f1105e5e4e3b84b8d676/SparseMonotiles/T5Monotile.lean).

## Finite full symmetry

The mathematical extension of 22 October 2026 uses the existing source lemmas to give an ordinary mathematical proof that the constructed monotiles in every integer dimension d > 2 have finite full Euclidean symmetry groups in every admitted tiling. This excludes all infinite-order screw and glide symmetries; it does not assert trivial symmetry groups. For the compiler witnesses in d = 3 and d ≥ 5, the argument gives |Sym(T)| ≤ 2^d d!. Dimension 4 uses a separate planar-factor argument; no numerical bound is claimed for that branch.

The argument has received a separate AI mathematical/source review. The new finite-symmetry deductions and stronger all-dimensional endpoint have not been implemented in Lean, compiled, independently kernel-checked, or registered in Palomar. This documentation extension does not change the compiled-result verification boundary above or the separately registered original T5 result.

[Read the mathematical extension](papers/FINITE_SYMMETRY_EXTENSION_2026-10-22.md) · [Read the AI source review and its limits](papers/FINITE_SYMMETRY_SOURCE_REVIEW_2026-10-22.md)

## Papers

- **Current all-dimensional paper, 22 October 2026:** [Aperiodic Monotiles in Every Dimension (PDF)](papers/all-dimensions/aperiodic-monotiles-every-dimension-2026-10-22.pdf), [Word](papers/all-dimensions/aperiodic-monotiles-every-dimension-2026-10-22.docx), and [editable text](papers/all-dimensions/aperiodic-monotiles-every-dimension-2026-10-22.md). This revision presents the compiled Lean result, JACKIE's four-dimensional branch, and the full mathematical finite-symmetry argument, with the remaining independent verification and formalization limits stated explicitly. No new Zenodo version or DOI is claimed.
- **Archived all-dimensional working paper, 16 October 2026 snapshot:** [PDF](papers/all-dimensions-working/aperiodic-monotiles-every-dimension-working-v1.pdf), [Word](papers/all-dimensions-working/aperiodic-monotiles-every-dimension-working-v1.docx), [editable text](papers/all-dimensions-working/aperiodic-monotiles-every-dimension-working-v1.md), and [dated claim scope](papers/all-dimensions-working/README.md). Its pending-C and pending-uniform-theorem language describes that earlier snapshot; the compiled source and official build evidence linked above are newer.
- **Finite full symmetry in every dimension d > 2, 22 October 2026:** [mathematical extension](papers/FINITE_SYMMETRY_EXTENSION_2026-10-22.md) and [separate AI mathematical/source review](papers/FINITE_SYMMETRY_SOURCE_REVIEW_2026-10-22.md). This extension is not a new compiled Lean endpoint.
- **Earlier CLARK/HENRY and odd-prime paper:** [An Arithmetic Family of Aperiodic Tilings in Odd Prime Dimensions, version 2 (PDF)](CLARK_paper.pdf?raw=1), [Zenodo record 23197680](https://zenodo.org/records/23197680), DOI [10.5281/zenodo.23197680](https://doi.org/10.5281/zenodo.23197680). The [CFF](CITATION.cff) and [BibTeX](CITATION.bib) files cite this earlier paper. This Zenodo version is not the current all-dimensional paper.

The earlier paper gives a written computer-assisted proof for the sparse seven-dimensional HENRY body and a hierarchy theorem for registered chair matching rules in every odd-prime dimension. Complete Lean verification of that exact HENRY body remains unfinished. Those claims have their own scope and do not limit the newer all-dimensional compiled theorem. The [historical mathematical account](https://github.com/jconorgrogan/palomar-chair-verification/blob/9008dec3afc006a62d3d2fd6b49b12f189248f33/README.md#broader-program) preserves the original distinctions.

## Verification evidence

### Compiled all-dimensional result, including JACKIE

The selected source is frozen at [`048bb245b60abce79f1a2d0c82336ff8508ec752`](https://github.com/jconorgrogan/palomar-chair-verification/tree/048bb245b60abce79f1a2d0c82336ff8508ec752). The [independent Challenge](https://github.com/jconorgrogan/palomar-chair-verification/blob/048bb245b60abce79f1a2d0c82336ff8508ec752/src/PalomarAllDimensionsChallenge.lean) fixes the physical statement; the [actual Solution](https://github.com/jconorgrogan/palomar-chair-verification/blob/048bb245b60abce79f1a2d0c82336ff8508ec752/src/PalomarAllDimensionsSolution.lean) proves it without importing Challenge. The Challenge's statement-only hole is intentional and is not the proof.

The [official full preflight run 39294694136](https://github.com/jconorgrogan/palomar-chair-verification/actions/runs/39294694136) used Lean **4.35.0-rc2**, the official reusable workflow pinned at `d4e41c1d5b0d114c4859e6e5831dc6d3ad1d0d44`, and the `palomar-standard-v1` profile. It records:

- `solution-build`: exit 0, **12,476 Lake jobs**, 12,190.542 seconds.
- `challenge-export`: exit 0, 9.374 seconds.
- `solution-export`: exit 0, 72.796 seconds.
- Overall report: `status: error`, `stage: resource-exhausted`; Comparator was the last active stage when the shared **19,800-second** worker budget ran out.

The unfinished stages are the final statement/definition comparison, external-kernel verification, and final-endpoint axiom audit. The helper-specific C axiom output does not replace a final-endpoint audit. The run retained no resumable build/export checkpoint, and additional compute is not a guarantee that the remaining checks will pass. No all-dimensional Palomar acceptance is claimed.

Read the [precise verification note](verification/ALL_DIMENSIONS_STATUS_2026-10-20.md), [unchanged mechanical report](verification/ALL_DIMENSIONS_MECHANICAL_REPORT_39294694136.json), and [original report artifact](https://github.com/jconorgrogan/palomar-chair-verification/actions/runs/39294694136/artifacts/12227932621). The report mirror's SHA-256 is `a1681ef51911a64f4bfe975e283396cd7ef3f8f4fd2aac5130ecdd3c5ef23ec6`.

### Independently verified and registered CLARK result

**[Registered in Palomar as PALOMAR-2026-10-07-000006 v1](https://palomar-registry.org/entry?id=PALOMAR-2026-10-07-000006&version=1) on 7 October 2026.** The registered result is `PalomarMonotiles.T5_strongAperiodicity` at immutable source commit `5f5ceedee770b76c21e8f1105e5e4e3b84b8d676`. The registry records successful mechanical verification and an automated review with no problems identified. This is not human peer review or a novelty certificate.

The stronger selected theorem, independent Challenge, actual Solution and axiom audit have passed local Lean **4.35.0-rc2** checks. The whole statement-definition comparison passed with no exemptions. The audited theorem depends only on `propext`, `Classical.choice`, and `Quot.sound`. The [extension evidence](https://github.com/jconorgrogan/palomar-chair-verification/blob/5f5ceedee770b76c21e8f1105e5e4e3b84b8d676/verification/STRONG_EXTENSION.md) records these local checks and their scope.

**The stronger theorem’s [official full Palomar mechanical preflight passed](https://github.com/jconorgrogan/palomar-chair-verification/actions/runs/37544058631)** for immutable source commit `5f5ceedee770b76c21e8f1105e5e4e3b84b8d676`. Lean’s default kernel, NanoDa and verified con-ron all accepted the Solution; con-ron checked **69,558 declarations**. The clean build completed **4,137 Lake jobs**, and the source audit checked **1,357 Lean files**. The [full mechanical report](verification/STRONG_MECHANICAL_REPORT_37544058631.json) records `status: pass`, `stage: complete`, and no errors or warnings. The [verification receipt](verification/STRONG_PREFLIGHT_PASS_37544058631.json) binds the source, report and checker results; the [original GitHub artifact](https://github.com/jconorgrogan/palomar-chair-verification/actions/runs/37544058631/artifacts/11454083416) remains available. Report JSON SHA-256: `82711b9d865e0441d453decdfebf5b4d071292f46b52a5e5ca77c385ed498884`.

This is the full reusable-workflow check pinned at `d4e41c1d5b0d114c4859e6e5831dc6d3ad1d0d44` under `palomar-standard-v1`, with no definition exemptions. It verifies the selected finite full-symmetry statement, including the **3,840** bound; a trivial symmetry group is not asserted. Registration and automated review are recorded in the versioned Palomar entry above.

The selected result is `PalomarMonotiles.T5_strongAperiodicity`, with statement `T5StrongClaim`. It retains the original compactness, tiling-existence and translation-aperiodicity claim as a conjunct. The independent Challenge fixes the exact shape and the physical tiling statement; the Solution proves that statement without importing Challenge. The Comparator has no definition exemptions.

### Exact registered CLARK source

The complete stronger source is on [the T5 verification branch](https://github.com/jconorgrogan/palomar-chair-verification/tree/verification/palomar-strong1-20261006), frozen at commit [`5f5ceedee770b76c21e8f1105e5e4e3b84b8d676`](https://github.com/jconorgrogan/palomar-chair-verification/tree/5f5ceedee770b76c21e8f1105e5e4e3b84b8d676).

- [Full mathematical account and reproduction instructions](https://github.com/jconorgrogan/palomar-chair-verification/blob/5f5ceedee770b76c21e8f1105e5e4e3b84b8d676/README.md)
- [Finite full-symmetry proof](https://github.com/jconorgrogan/palomar-chair-verification/blob/5f5ceedee770b76c21e8f1105e5e4e3b84b8d676/SparseMonotiles/FiniteSymmetry.lean)
- [Independent Challenge](https://github.com/jconorgrogan/palomar-chair-verification/blob/5f5ceedee770b76c21e8f1105e5e4e3b84b8d676/Challenge.lean) and [actual Solution](https://github.com/jconorgrogan/palomar-chair-verification/blob/5f5ceedee770b76c21e8f1105e5e4e3b84b8d676/Solution.lean)
- [Structured metadata, source relationships, automation and review account](https://github.com/jconorgrogan/palomar-chair-verification/blob/5f5ceedee770b76c21e8f1105e5e4e3b84b8d676/formalization.yaml)
- [Exact source manifest](https://github.com/jconorgrogan/palomar-chair-verification/blob/5f5ceedee770b76c21e8f1105e5e4e3b84b8d676/SOURCE_MANIFEST.json)
- [Verification runs](https://github.com/jconorgrogan/palomar-chair-verification/actions)

The source manifest has SHA-256 `ec0ed3ed9927fe13aa654c713ce9eb83e2a52da7b3d6c6c6cea07efcebb998f3`. The full source contains the substantive proof development, not only a theorem wrapper. The `main` branch serves as this public index and retains its earlier history.

## Reproduction

### All-dimensional source and build configuration

[Download the complete pinned all-dimensional source ZIP](https://github.com/jconorgrogan/palomar-chair-verification/archive/048bb245b60abce79f1a2d0c82336ff8508ec752.zip). The immutable snapshot includes the [Lean toolchain pin](https://github.com/jconorgrogan/palomar-chair-verification/blob/048bb245b60abce79f1a2d0c82336ff8508ec752/lean-toolchain), [Lake configuration](https://github.com/jconorgrogan/palomar-chair-verification/blob/048bb245b60abce79f1a2d0c82336ff8508ec752/lakefile.lean), [dependency manifest](https://github.com/jconorgrogan/palomar-chair-verification/blob/048bb245b60abce79f1a2d0c82336ff8508ec752/lake-manifest.json), [Comparator selection](https://github.com/jconorgrogan/palomar-chair-verification/blob/048bb245b60abce79f1a2d0c82336ff8508ec752/comparator.json), and [formalization metadata](https://github.com/jconorgrogan/palomar-chair-verification/blob/048bb245b60abce79f1a2d0c82336ff8508ec752/formalization.yaml). The selected Solution module is `PalomarAllDimensionsSolution`; its successful official build is the one documented above. Historical “unexecuted” comments in this frozen source predate that run and do not erase its completed stages.

For independent verification, use the [pinned official pipeline](https://github.com/PalomarRegistry/PalomarSubmission/tree/d4e41c1d5b0d114c4859e6e5831dc6d3ad1d0d44) and preserve the exact Challenge, Solution, dependency pins, and physical definitions. A supported route with sufficient compute must still finish the independent checks. Do not substitute the separately passing CLARK report for this all-dimensional verdict.

### Reproduce the registered CLARK source

[Download the complete pinned source ZIP](https://github.com/jconorgrogan/palomar-chair-verification/archive/5f5ceedee770b76c21e8f1105e5e4e3b84b8d676.zip).

Use a Linux host meeting the official standard-profile floor: at least **14 GiB RAM and 20 GiB free disk**. Install Bash, Git, Python 3, curl 7.81 or newer with working TLS/network access, standard Unix utilities, and Bubblewrap with usable namespaces. The sandbox expects `/root`, `/home` and `/run/user` to exist. Use the official prebuilt **Lean 4.35.0-rc2** toolchain (directly or through Elan), with `lean`, `lake`, `leanexport`, `leanchecker`, `nanoda_bin`, `con-ron` and `leantar` available from that toolchain. Rust, Cargo and CMake are not required for this prebuilt route.

From a directory without an existing `clark-replay` folder, run:

```sh
COMMIT=5f5ceedee770b76c21e8f1105e5e4e3b84b8d676; git clone https://github.com/jconorgrogan/palomar-chair-verification.git clark-replay && cd clark-replay && git checkout --detach "$COMMIT" && bash scripts/verify-t5-on-linux.sh
```

The script checks the exact source manifest, builds the selected proof and invokes the unchanged bundled Comparator with Lean, NanoDa and verified con-ron. It requires a host that supports Bubblewrap namespaces and can take an hour or more. The official reusable workflow additionally checks metadata, Challenge provenance, execution-profile limits and its mechanical report. The command above reproduces the proof/Comparator/kernel portion; it does not by itself replace the required full Palomar workflow report.

## Verification history

### Earlier CLARK checks and comparator repair

**The original theorem’s [official full Palomar mechanical preflight passed](https://github.com/jconorgrogan/palomar-chair-verification/actions/runs/37520435323)** for immutable source commit `9008dec3afc006a62d3d2fd6b49b12f189248f33`. The selected original T5 theorem covers compactness, tiling existence and no nonzero translation period in any physical tiling. Lean’s default kernel, NanoDa and verified con-ron all accepted the Solution; con-ron checked 69,348 declarations. The [mechanical report artifact](https://github.com/jconorgrogan/palomar-chair-verification/actions/runs/37520435323/artifacts/11444507885) records `status: pass`, `stage: complete`, and no errors or warnings. The report JSON has SHA-256 `43edc2c785ceaa7ecff4b231a0a9738a5e320d6fd5b0461d6de88491f482f027`. This is the full pinned reusable-workflow preflight under `palomar-standard-v1` for the original theorem, without the finite-symmetry extension. Palomar registration applies to the stronger snapshot cited above; this original preflight remains part of the verification history.

The [first full run](https://github.com/jconorgrogan/palomar-chair-verification/actions/runs/37509737027) clean-built all 4,135 Lake jobs but rejected a generated statement-helper proof before the independent main kernels. The repair replaced only two bound-proof blocks with explicit terms; the complete helper function is definitionally unchanged. Local whole-statement dependency comparison and affected-binding/Solution checks passed before the successful official retry. The exact [repair evidence](https://github.com/jconorgrogan/palomar-chair-verification/blob/9008dec3afc006a62d3d2fd6b49b12f189248f33/verification/COMPARATOR_REPAIR.md) preserves that history.

An [earlier four-result compatibility pilot](https://github.com/jconorgrogan/palomar-chair-verification/actions/runs/37466588417) passed the official Comparator and three kernels. That result concerns four supporting statements and is separate from the full T5 preflight.

### All-dimensional milestones

- **16 October 2026:** the working paper recorded accepted native two- and four-dimensional results with C explicit, plus retained unconditional verification for dimension three and every dimension at least five. The [dated manuscript](papers/all-dimensions-working/aperiodic-monotiles-every-dimension-working-v1.md) preserves that historical scope.
- **19 October 2026:** the selected all-dimensional Solution built and both proof exports succeeded in [run 39294694136](https://github.com/jconorgrogan/palomar-chair-verification/actions/runs/39294694136); the remaining independent verification exhausted the worker budget. The [20 October verification note](verification/ALL_DIMENSIONS_STATUS_2026-10-20.md) reconciles the newer source and run with older metadata.
- **22 October 2026:** the [revised all-dimensional manuscript](papers/all-dimensions/aperiodic-monotiles-every-dimension-2026-10-22.pdf) consolidates the construction, compiled translation-aperiodicity result, and full finite-symmetry proof. The [finite-full-symmetry extension](papers/FINITE_SYMMETRY_EXTENSION_2026-10-22.md) and [AI source review](papers/FINITE_SYMMETRY_SOURCE_REVIEW_2026-10-22.md) establish the new mathematical argument and identify the formal glue still to implement. They do not change either existing Lean verification scope.

The [clean hierarchy-C campaign](https://github.com/jconorgrogan/palomar-chair-verification/actions/runs/39179019728), [174-module visibility test](https://github.com/jconorgrogan/palomar-chair-verification/actions/runs/39265576764), and [388-module import-optimization test](https://github.com/jconorgrogan/palomar-chair-verification/actions/runs/39279478084) retain their separate scopes. They do not supply the missing final all-dimensional verdict.

## Attribution, production, and license

Adam Scherlis previously formulated the all-dimensional keyed-product program, including the four-dimensional construction and 56-key count, in his [pinned primary note](https://github.com/AdamScherlis/adamscherlis.github.io/blob/e05cee7245124a705ca68be3a8f641d290c664b4/static/monotiles-every-dimension/index.html). No priority is claimed here for that general idea, four-dimensional idea, count, or all-dimension formulation. Attribution is separate from verification of any particular argument.

AI systems made substantive contributions to mathematical analysis, Lean proofs, exact certificate generation, audits, migration and exposition. The metadata records those contributions separately from human authorship. No independent human mathematical peer review or novelty certification is claimed.

The companion preprint (`CLARK_paper.pdf`) and its figures are licensed under [Creative Commons Attribution 4.0 International (CC BY 4.0)](https://creativecommons.org/licenses/by/4.0/). The proof code is licensed under [Apache License 2.0](https://github.com/jconorgrogan/palomar-chair-verification/blob/9008dec3afc006a62d3d2fd6b49b12f189248f33/LICENSE). Lean, Mathlib and other dependencies retain their own licenses and notices.

The repository URL remains `jconorgrogan/palomar-chair-verification`, preserving existing source and registry links. This public index distinguishes immutable proof snapshots, later explanatory documents, and unfinished verification work.
