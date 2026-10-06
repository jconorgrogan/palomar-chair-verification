# The CLARK Tile: An Aperiodic Monotile in Five Dimensions

Conor Grogan, author and responsible maintainer

Companion preprint: [read the paper on Zenodo](https://zenodo.org/records/23197475), DOI [10.5281/zenodo.23197475](https://doi.org/10.5281/zenodo.23197475).

We call the five-dimensional construction **CLARK**, for **Chair with Local Asymmetric Registration Keys**. It retains the Lean identifier **T5**.

![CLARK carrier projection](CLARK_overview.png)

Projection of the carrier; boundary keys omitted. Illustration does not replace exact shape specification.

[Download the CLARK tile illustration (PDF)](Clark_5D_tile.pdf)

We give an explicit compact tile in five-dimensional Euclidean space and prove that it admits tilings but no periodic tiling. The construction modifies a chair made from 31 unit five-cubes with 256 rational pyramidal keys. Copies may be translated, rotated, or reflected. The theorem states that every tiling by these copies has no nonzero translation preserving its tile collection. The Lean formalization fixes the exact body and proves compactness, existence, and aperiodicity without assuming lattice registration or matching rules. See the [exact tile definition](https://github.com/jconorgrogan/palomar-chair-verification/blob/9008dec3afc006a62d3d2fd6b49b12f189248f33/Challenge.lean), the [selected theorem proof](https://github.com/jconorgrogan/palomar-chair-verification/blob/9008dec3afc006a62d3d2fd6b49b12f189248f33/Solution.lean), and the [complete physical monotile theorem](https://github.com/jconorgrogan/palomar-chair-verification/blob/9008dec3afc006a62d3d2fd6b49b12f189248f33/SparseMonotiles/T5Monotile.lean).

## Proof and verification status

The complete theorem, its exact compact-body binding, and the actual Solution have passed local Lean **4.35.0-rc2** checks. The audited theorem depends only on `propext`, `Classical.choice`, and `Quot.sound`.

**The required [official full Palomar mechanical preflight passed](https://github.com/jconorgrogan/palomar-chair-verification/actions/runs/37520435323)** for immutable source commit `9008dec3afc006a62d3d2fd6b49b12f189248f33`. The selected original T5 theorem covers compactness, tiling existence and no nonzero translation period in any physical tiling. Lean’s default kernel, NanoDa and verified con-ron all accepted the Solution; con-ron checked 69,348 declarations. The [mechanical report artifact](https://github.com/jconorgrogan/palomar-chair-verification/actions/runs/37520435323/artifacts/11444507885) records `status: pass`, `stage: complete`, and no errors or warnings. The report JSON has SHA-256 `43edc2c785ceaa7ecff4b231a0a9738a5e320d6fd5b0461d6de88491f482f027`. This is the full pinned reusable-workflow preflight under `palomar-standard-v1`; Palomar editorial review and registry acceptance remain pending.

The [first full run](https://github.com/jconorgrogan/palomar-chair-verification/actions/runs/37509737027) clean-built all 4,135 Lake jobs but rejected a generated statement-helper proof before the independent main kernels. The repair replaced only two bound-proof blocks with explicit terms; the complete helper function is definitionally unchanged. Local whole-statement dependency comparison and affected-binding/Solution checks passed before the successful official retry. The exact [repair evidence](https://github.com/jconorgrogan/palomar-chair-verification/blob/9008dec3afc006a62d3d2fd6b49b12f189248f33/verification/COMPARATOR_REPAIR.md) preserves that history.

The selected result is `PalomarMonotiles.T5_isAperiodicMonotile`. The independent Challenge fixes the exact shape and the physical tiling statement; the Solution proves that statement without importing Challenge. The Comparator has no definition exemptions.

## Exact source snapshot

The complete source is on [the T5 verification branch](https://github.com/jconorgrogan/palomar-chair-verification/tree/verification/palomar-repair1-20261006), frozen at commit [`9008dec3afc006a62d3d2fd6b49b12f189248f33`](https://github.com/jconorgrogan/palomar-chair-verification/tree/9008dec3afc006a62d3d2fd6b49b12f189248f33).

- [Full mathematical account and reproduction instructions](https://github.com/jconorgrogan/palomar-chair-verification/blob/9008dec3afc006a62d3d2fd6b49b12f189248f33/README.md)
- [Independent Challenge](https://github.com/jconorgrogan/palomar-chair-verification/blob/9008dec3afc006a62d3d2fd6b49b12f189248f33/Challenge.lean) and [actual Solution](https://github.com/jconorgrogan/palomar-chair-verification/blob/9008dec3afc006a62d3d2fd6b49b12f189248f33/Solution.lean)
- [Structured metadata, source relationships, automation and review account](https://github.com/jconorgrogan/palomar-chair-verification/blob/9008dec3afc006a62d3d2fd6b49b12f189248f33/formalization.yaml)
- [Exact source manifest](https://github.com/jconorgrogan/palomar-chair-verification/blob/9008dec3afc006a62d3d2fd6b49b12f189248f33/SOURCE_MANIFEST.json)
- [Verification runs](https://github.com/jconorgrogan/palomar-chair-verification/actions)

The source manifest has SHA-256 `40e0be12c33cb719b6afdf7a69e99d69e820ae5af41cbf76bfd246a995de07c2`. The full source contains the substantive proof development, not only a theorem wrapper. The `main` branch serves as this public index and retains its earlier history.

## Reproduce this exact source

[Download the complete pinned source ZIP](https://github.com/jconorgrogan/palomar-chair-verification/archive/9008dec3afc006a62d3d2fd6b49b12f189248f33.zip).

Use a Linux host meeting the official standard-profile floor: at least **14 GiB RAM and 20 GiB free disk**. Install Bash, Git, Python 3, curl 7.81 or newer with working TLS/network access, standard Unix utilities, and Bubblewrap with usable namespaces. The sandbox expects `/root`, `/home` and `/run/user` to exist. Use the official prebuilt **Lean 4.35.0-rc2** toolchain (directly or through Elan), with `lean`, `lake`, `leanexport`, `leanchecker`, `nanoda_bin`, `con-ron` and `leantar` available from that toolchain. Rust, Cargo and CMake are not required for this prebuilt route.

From a directory without an existing `clark-replay` folder, run:

```sh
COMMIT=9008dec3afc006a62d3d2fd6b49b12f189248f33; git clone https://github.com/jconorgrogan/palomar-chair-verification.git clark-replay && cd clark-replay && git checkout --detach "$COMMIT" && bash scripts/verify-t5-on-linux.sh
```

The script checks the exact source manifest, builds the selected proof and invokes the unchanged bundled Comparator with Lean, NanoDa and verified con-ron. It requires a host that supports Bubblewrap namespaces and can take an hour or more. The official reusable workflow additionally checks metadata, Challenge provenance, execution-profile limits and its mechanical report. The command above reproduces the proof/Comparator/kernel portion; it does not by itself replace the required full Palomar workflow report.

## Companion work

This submission formalizes the 5D construction. Companion work gives an ordinary computer-assisted proof for the seven-dimensional construction (T7) and a hierarchy theorem for registered chair matching rules in every odd-prime dimension. Those results are outside the selected T5 verification. This entry does not establish physical monotiles in every odd-prime dimension. The exact distinctions and retained source citations are in the [full mathematical account](https://github.com/jconorgrogan/palomar-chair-verification/blob/9008dec3afc006a62d3d2fd6b49b12f189248f33/README.md#broader-program).

## Production, review and license

AI systems made substantive contributions to mathematical analysis, Lean proofs, exact certificate generation, audits, migration and exposition. The metadata records those contributions separately from human authorship. No independent human mathematical peer review or novelty certification is claimed.

The proof repository is licensed under [Apache License 2.0](https://github.com/jconorgrogan/palomar-chair-verification/blob/9008dec3afc006a62d3d2fd6b49b12f189248f33/LICENSE). Lean, Mathlib and other dependencies retain their own licenses and notices.

An [earlier four-result compatibility pilot](https://github.com/jconorgrogan/palomar-chair-verification/actions/runs/37466588417) passed the official Comparator and three kernels. That result concerns four supporting statements and is separate from the full T5 preflight.
