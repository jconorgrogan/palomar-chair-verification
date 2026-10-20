# All-dimensional Lean verification status

Updated 20 October 2026 (UTC). This note distinguishes the compiled Lean theorem from the unfinished full independent verification process.

## Mathematical claim in the selected source

The development states and supplies a Lean proof of an aperiodic monotile in every integer dimension **d ≥ 2**. More precisely, the selected theorem asserts a set T in d-dimensional Euclidean space that is compact, has nonempty interior, admits a tiling, and admits no valid tiling with a nonzero translational period.

The precise definitions and endpoint are in [PalomarAllDimensionsSolution.lean, lines 19–41](https://github.com/jconorgrogan/palomar-chair-verification/blob/048bb245b60abce79f1a2d0c82336ff8508ec752/src/PalomarAllDimensionsSolution.lean#L19-L41). The tiling definition allows copies under all Euclidean isometries, including reflections, requires coverage, and requires disjoint interiors for distinct tiles. Aperiodicity here concerns translational periods; this note does not assert trivial full symmetry groups or infinitely many distinct tile shapes within each dimension.

The earlier parent-occurrence premise C is **discharged internally**, not assumed as an additional hypothesis of this selected endpoint:

- [NativeCoarsening.lean, lines 19–21](https://github.com/jconorgrogan/palomar-chair-verification/blob/048bb245b60abce79f1a2d0c82336ff8508ec752/src/SpectreFinite/NativeCoarsening.lean#L19-L21) defines the parent-occurrence property.
- [RadiusFivePruningHierarchy.lean, lines 11–16](https://github.com/jconorgrogan/palomar-chair-verification/blob/048bb245b60abce79f1a2d0c82336ff8508ec752/src/SpectreFinite/RadiusFivePruningHierarchy.lean#L11-L16) supplies `certifiedParentOccurrenceTheorem`.
- [AllDimensionsOfParent.lean, lines 18–29](https://github.com/jconorgrogan/palomar-chair-verification/blob/048bb245b60abce79f1a2d0c82336ff8508ec752/src/NativeFinalAssembly/AllDimensionsOfParent.lean#L18-L29) assembles the dimension cases from that property.
- [AllDimensions.lean, lines 16–23](https://github.com/jconorgrogan/palomar-chair-verification/blob/048bb245b60abce79f1a2d0c82336ff8508ec752/src/NativeFinalAssembly/AllDimensions.lean#L16-L23) supplies the certified theorem to that assembly. The public endpoint takes only d and the bound 2 ≤ d.

The official build log reports the C theorem's axioms as `propext`, `Classical.choice` and `Quot.sound`. That helper-specific output is not a completed axiom audit of the final all-dimensional endpoint.

## Exact official run and successful stages

- Repository: `jconorgrogan/palomar-chair-verification`.
- Selected source: [`048bb245b60abce79f1a2d0c82336ff8508ec752`](https://github.com/jconorgrogan/palomar-chair-verification/tree/048bb245b60abce79f1a2d0c82336ff8508ec752).
- Source tree: `c6111a7d32daf2906275ee1ac265bf6865ebd9a5`.
- [Official full preflight run 39294694136, attempt 1](https://github.com/jconorgrogan/palomar-chair-verification/actions/runs/39294694136), completed 19 October 2026. The workflow's overall conclusion was failure from the capacity limit described below.
- Lean: `leanprover/lean4:v4.35.0-rc2`.
- Official pipeline: [`d4e41c1d5b0d114c4859e6e5831dc6d3ad1d0d44`](https://github.com/PalomarRegistry/PalomarSubmission/tree/d4e41c1d5b0d114c4859e6e5831dc6d3ad1d0d44), mode `full`, profile `palomar-standard-v1`.

The recorded `solution-build` exited **0** after **12,190.542 seconds**. Its log ends with `Build completed successfully (12476 jobs)`. These are Lake build jobs, not a count of theorems or independent verifier checks. This establishes that the selected complete Solution build compiled successfully; it is not a claim that every unrelated file or historical branch was built.

Both export stages exited **0**:

- `challenge-export`: **9.374 seconds**.
- `solution-export`: **72.796 seconds**.

## Why full verification remains pending

The worker exhausted its **shared 19,800-second wall-clock budget (5½ hours)** with `comparator` recorded as the last active stage. The report gives `status: error`, `stage: resource-exhausted`, `phase: verification`, and `error_kind: infrastructure/resource-exhausted`; the comparator supervisor records a timeout.

The retained report does not establish a completed main statement/definition comparison, external-kernel verification or final-endpoint axiom audit. It does not identify which inner comparator subphase was active at the deadline or retain an exact comparator duration. Its zero-valued timeout metrics must not be interpreted as evidence that the comparator used no CPU or memory. No resumable build or export checkpoint was retained by this run.

Compilation and successful export are substantial completed checks. They do not constitute a full passing official report or Palomar acceptance. A supported verification route still has to finish the remaining checks; additional time is not a guarantee of success. This all-dimensional result is not registered in Palomar as of this note.

## Evidence and historical metadata

- [Public run and logs](https://github.com/jconorgrogan/palomar-chair-verification/actions/runs/39294694136).
- [Original report artifact 12227932621](https://github.com/jconorgrogan/palomar-chair-verification/actions/runs/39294694136/artifacts/12227932621), named `mechanical-report-palo26101903` (GitHub artifact access and retention rules apply).
- [Unchanged report mirrored in this repository](ALL_DIMENSIONS_MECHANICAL_REPORT_39294694136.json): **203,813 bytes**, SHA-256 `a1681ef51911a64f4bfe975e283396cd7ef3f8f4fd2aac5130ecdd3c5ef23ec6`.

The mirror preserves the report byte-for-byte, including historical manuscript/provenance descriptions that called C or the unconditional uniform theorem pending. Those descriptions are older than the selected source assembly. The immutable source links above establish that C is supplied internally; the recorded run establishes the completed build/export stages and the unfinished full verification. Neither the old prose nor this documentation update changes the source snapshot.

Earlier successful checks retain their own scopes. The [clean hierarchy-C campaign](https://github.com/jconorgrogan/palomar-chair-verification/actions/runs/39179019728), [174-module visibility test](https://github.com/jconorgrogan/palomar-chair-verification/actions/runs/39265576764), and [388-module import-optimization test](https://github.com/jconorgrogan/palomar-chair-verification/actions/runs/39279478084) are separate from the full all-dimensional preflight. They do not replace its missing final verdict. The original five-dimensional CLARK result remains separately [registered as PALOMAR-2026-10-07-000006 v1](https://palomar-registry.org/entry?id=PALOMAR-2026-10-07-000006&version=1); that registration does not extend to this all-dimensional theorem.

This is a documentation-only update. The checked Lean source, prior verification snapshots, original papers and their licenses are unchanged.
