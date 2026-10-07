# The CLARK Tile: A Strongly Aperiodic Monotile in Five Dimensions

Conor Grogan, author and responsible maintainer

Companion preprint: [read the paper on Zenodo](https://zenodo.org/records/23197680), DOI [10.5281/zenodo.23197680](https://doi.org/10.5281/zenodo.23197680).

Download version 2: [**An Arithmetic Family of Aperiodic Tilings in Odd Prime Dimensions** (PDF)](CLARK_paper.pdf?raw=1). Citation files: [CFF](CITATION.cff) and [BibTeX](CITATION.bib).

We call the five-dimensional construction **CLARK**, for **Chair with Local Asymmetric Registration Keys**. It retains the Lean identifier **T5**.

![Planar section of a level-five CLARK carrier patch with matching-key zooms](CLARK_overview.png)

The main panel shows carrier sections. Matching keys are resolved in the 12× and 690× zooms of the same plane. Colours count negative coordinate signs; all displayed full frames preserve orientation. The small target ring is enlarged 2.2× for visibility. See [figure details and the sections/key diagrams](figures/README.md).

We give an explicit compact tile in five-dimensional Euclidean space and prove that it admits tilings but no periodic tiling. The construction modifies a chair made from 31 unit five-cubes with 256 rational pyramidal keys. Copies may be translated, rotated, or reflected. The theorem states that every tiling by these copies has no nonzero translation preserving its tile collection. It also proves that the full Euclidean symmetry group of every such tiling is finite, with at most **3,840** elements. Here, strongly aperiodic means finite full symmetry group; a trivial symmetry group is not asserted. The Lean formalization fixes the exact body and proves compactness, existence, and aperiodicity without assuming lattice registration or matching rules. See the [exact tile definition](https://github.com/jconorgrogan/palomar-chair-verification/blob/5f5ceedee770b76c21e8f1105e5e4e3b84b8d676/Challenge.lean), the [selected theorem proof](https://github.com/jconorgrogan/palomar-chair-verification/blob/5f5ceedee770b76c21e8f1105e5e4e3b84b8d676/Solution.lean), and the [complete physical monotile theorem](https://github.com/jconorgrogan/palomar-chair-verification/blob/5f5ceedee770b76c21e8f1105e5e4e3b84b8d676/SparseMonotiles/T5Monotile.lean).

## Proof and verification status

The stronger selected theorem, independent Challenge, actual Solution and axiom audit have passed local Lean **4.35.0-rc2** checks. The whole statement-definition comparison passed with no exemptions. The audited theorem depends only on `propext`, `Classical.choice`, and `Quot.sound`. The [extension evidence](https://github.com/jconorgrogan/palomar-chair-verification/blob/5f5ceedee770b76c21e8f1105e5e4e3b84b8d676/verification/STRONG_EXTENSION.md) records these local checks and their scope.

**The stronger theorem’s [official full Palomar mechanical preflight passed](https://github.com/jconorgrogan/palomar-chair-verification/actions/runs/37544058631)** for immutable source commit `5f5ceedee770b76c21e8f1105e5e4e3b84b8d676`. Lean’s default kernel, NanoDa and verified con-ron all accepted the Solution; con-ron checked **69,558 declarations**. The clean build completed **4,137 Lake jobs**, and the source audit checked **1,357 Lean files**. The [full mechanical report](verification/STRONG_MECHANICAL_REPORT_37544058631.json) records `status: pass`, `stage: complete`, and no errors or warnings. The [verification receipt](verification/STRONG_PREFLIGHT_PASS_37544058631.json) binds the source, report and checker results; the [original GitHub artifact](https://github.com/jconorgrogan/palomar-chair-verification/actions/runs/37544058631/artifacts/11454083416) remains available. Report JSON SHA-256: `82711b9d865e0441d453decdfebf5b4d071292f46b52a5e5ca77c385ed498884`.

This is the full reusable-workflow check pinned at `d4e41c1d5b0d114c4859e6e5831dc6d3ad1d0d44` under `palomar-standard-v1`, with no definition exemptions. It verifies the selected finite full-symmetry statement, including the **3,840** bound; a trivial symmetry group is not asserted. Palomar editorial review and registry acceptance remain pending.

**The original theorem’s [official full Palomar mechanical preflight passed](https://github.com/jconorgrogan/palomar-chair-verification/actions/runs/37520435323)** for immutable source commit `9008dec3afc006a62d3d2fd6b49b12f189248f33`. The selected original T5 theorem covers compactness, tiling existence and no nonzero translation period in any physical tiling. Lean’s default kernel, NanoDa and verified con-ron all accepted the Solution; con-ron checked 69,348 declarations. The [mechanical report artifact](https://github.com/jconorgrogan/palomar-chair-verification/actions/runs/37520435323/artifacts/11444507885) records `status: pass`, `stage: complete`, and no errors or warnings. The report JSON has SHA-256 `43edc2c785ceaa7ecff4b231a0a9738a5e320d6fd5b0461d6de88491f482f027`. This is the full pinned reusable-workflow preflight under `palomar-standard-v1` for the original theorem, without the finite-symmetry extension. Palomar editorial review and registry acceptance remain pending.

The [first full run](https://github.com/jconorgrogan/palomar-chair-verification/actions/runs/37509737027) clean-built all 4,135 Lake jobs but rejected a generated statement-helper proof before the independent main kernels. The repair replaced only two bound-proof blocks with explicit terms; the complete helper function is definitionally unchanged. Local whole-statement dependency comparison and affected-binding/Solution checks passed before the successful official retry. The exact [repair evidence](https://github.com/jconorgrogan/palomar-chair-verification/blob/9008dec3afc006a62d3d2fd6b49b12f189248f33/verification/COMPARATOR_REPAIR.md) preserves that history.

The selected result is `PalomarMonotiles.T5_strongAperiodicity`, with statement `T5StrongClaim`. It retains the original compactness, tiling-existence and translation-aperiodicity claim as a conjunct. The independent Challenge fixes the exact shape and the physical tiling statement; the Solution proves that statement without importing Challenge. The Comparator has no definition exemptions.

## Exact source snapshot

The complete stronger source is on [the T5 verification branch](https://github.com/jconorgrogan/palomar-chair-verification/tree/verification/palomar-strong1-20261006), frozen at commit [`5f5ceedee770b76c21e8f1105e5e4e3b84b8d676`](https://github.com/jconorgrogan/palomar-chair-verification/tree/5f5ceedee770b76c21e8f1105e5e4e3b84b8d676).

- [Full mathematical account and reproduction instructions](https://github.com/jconorgrogan/palomar-chair-verification/blob/5f5ceedee770b76c21e8f1105e5e4e3b84b8d676/README.md)
- [Finite full-symmetry proof](https://github.com/jconorgrogan/palomar-chair-verification/blob/5f5ceedee770b76c21e8f1105e5e4e3b84b8d676/SparseMonotiles/FiniteSymmetry.lean)
- [Independent Challenge](https://github.com/jconorgrogan/palomar-chair-verification/blob/5f5ceedee770b76c21e8f1105e5e4e3b84b8d676/Challenge.lean) and [actual Solution](https://github.com/jconorgrogan/palomar-chair-verification/blob/5f5ceedee770b76c21e8f1105e5e4e3b84b8d676/Solution.lean)
- [Structured metadata, source relationships, automation and review account](https://github.com/jconorgrogan/palomar-chair-verification/blob/5f5ceedee770b76c21e8f1105e5e4e3b84b8d676/formalization.yaml)
- [Exact source manifest](https://github.com/jconorgrogan/palomar-chair-verification/blob/5f5ceedee770b76c21e8f1105e5e4e3b84b8d676/SOURCE_MANIFEST.json)
- [Verification runs](https://github.com/jconorgrogan/palomar-chair-verification/actions)

The source manifest has SHA-256 `ec0ed3ed9927fe13aa654c713ce9eb83e2a52da7b3d6c6c6cea07efcebb998f3`. The full source contains the substantive proof development, not only a theorem wrapper. The `main` branch serves as this public index and retains its earlier history.

## Reproduce this exact source

[Download the complete pinned source ZIP](https://github.com/jconorgrogan/palomar-chair-verification/archive/5f5ceedee770b76c21e8f1105e5e4e3b84b8d676.zip).

Use a Linux host meeting the official standard-profile floor: at least **14 GiB RAM and 20 GiB free disk**. Install Bash, Git, Python 3, curl 7.81 or newer with working TLS/network access, standard Unix utilities, and Bubblewrap with usable namespaces. The sandbox expects `/root`, `/home` and `/run/user` to exist. Use the official prebuilt **Lean 4.35.0-rc2** toolchain (directly or through Elan), with `lean`, `lake`, `leanexport`, `leanchecker`, `nanoda_bin`, `con-ron` and `leantar` available from that toolchain. Rust, Cargo and CMake are not required for this prebuilt route.

From a directory without an existing `clark-replay` folder, run:

```sh
COMMIT=5f5ceedee770b76c21e8f1105e5e4e3b84b8d676; git clone https://github.com/jconorgrogan/palomar-chair-verification.git clark-replay && cd clark-replay && git checkout --detach "$COMMIT" && bash scripts/verify-t5-on-linux.sh
```

The script checks the exact source manifest, builds the selected proof and invokes the unchanged bundled Comparator with Lean, NanoDa and verified con-ron. It requires a host that supports Bubblewrap namespaces and can take an hour or more. The official reusable workflow additionally checks metadata, Challenge provenance, execution-profile limits and its mechanical report. The command above reproduces the proof/Comparator/kernel portion; it does not by itself replace the required full Palomar workflow report.

## Companion work

This submission formalizes the 5D construction. Companion work gives an ordinary computer-assisted proof for the seven-dimensional construction (T7) and a hierarchy theorem for registered chair matching rules in every odd-prime dimension. Those results are outside the selected T5 verification. This entry does not establish physical monotiles in every odd-prime dimension. The exact distinctions and retained source citations are in the [full mathematical account](https://github.com/jconorgrogan/palomar-chair-verification/blob/9008dec3afc006a62d3d2fd6b49b12f189248f33/README.md#broader-program).

## Production, review and license

AI systems made substantive contributions to mathematical analysis, Lean proofs, exact certificate generation, audits, migration and exposition. The metadata records those contributions separately from human authorship. No independent human mathematical peer review or novelty certification is claimed.

The companion preprint (`CLARK_paper.pdf`) and its figures are licensed under [Creative Commons Attribution 4.0 International (CC BY 4.0)](https://creativecommons.org/licenses/by/4.0/). The proof code is licensed under [Apache License 2.0](https://github.com/jconorgrogan/palomar-chair-verification/blob/9008dec3afc006a62d3d2fd6b49b12f189248f33/LICENSE). Lean, Mathlib and other dependencies retain their own licenses and notices.

An [earlier four-result compatibility pilot](https://github.com/jconorgrogan/palomar-chair-verification/actions/runs/37466588417) passed the official Comparator and three kernels. That result concerns four supporting statements and is separate from the full T5 preflight.
