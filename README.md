# An Aperiodic Monotile in Five Dimensions

Conor Grogan, author and responsible maintainer

## Verification status

This is the private source staging for one T5 submission. The complete original proof passed Lean 4.19. The complete supported proof, actual Solution composition and axiom audit have now passed Lean 4.35.0-rc2. Full official Comparator and independent main kernel checks remain pending. A successful four-supporting-result pilot is separate evidence. No Palomar acceptance is claimed. This dated status must be replaced by the actual frozen main receipts before release.

## Abstract

We give an explicit compact tile in five-dimensional Euclidean space and prove that it admits tilings but no periodic tiling. The construction modifies a chair made from 31 unit five-cubes with 256 rational pyramidal keys. Copies may be translated, rotated, or reflected. The theorem states that every tiling by these copies has no nonzero translation preserving its tile collection. The Lean formalization fixes the exact body and proves compactness, existence, and aperiodicity without assuming lattice registration or matching rules.

The abstract describes the mathematical result selected for release. The verification status above records which checks have actually finished.

## Exact theorem

Let T5 be the body specified by the final S54 five-dimensional construction. Its carrier is the union of the 31 closed unit five-cubes with binary lower corners other than (1, 1, 1, 1, 1). Its boundary has 256 specified rational pyramidal keys: 128 bumps and 128 dents, each with normal height 1/240. The body is the closure obtained after adding the closed bumps and removing the closed dents.

Then:

1. T5 is compact
2. There is a tiling of all of R⁵ by Euclidean isometric copies of T5
3. For every such tiling, the only translation that preserves its collection of tiles is the zero translation

A tiling here is a collection of unmarked tile sets that covers every point of R⁵, with disjoint interiors for distinct tiles. Any translation, rotation, or reflection is allowed when placing a copy. A period preserves the tile collection, not just the union of the tiles. The theorem has no registration, matching-rule, hierarchy, or finite-certificate assumption.

The selected declaration is `PalomarMonotiles.T5_isAperiodicMonotile`, with statement `T5Claim`. The source specification is `tile5_final_spec.json`, SHA-256 `8c94499b8b9fc89efef794497723f649a188de6a7a5460849dc7989bc61b6094`. The exposed definition in `Challenge.lean` fixes the body independently of the proof implementation. Its 256 placement records retain the source order and exact rational coordinates.

The selected theorem does not assert that T5 is a topological ball, that it is connected, or that every tiling has a finite full Euclidean symmetry group. It makes no first-example or priority claim. Novelty has not been established.

## Broader program

Companion work gives an ordinary computer-assisted proof for the exact compact seven-dimensional construction and an ordinary hierarchy theorem for registered chair matching rules in every odd-prime dimension. The latter concerns a full-frame matching-rule model with the specified empty-role convention; it establishes existence, unique nested hierarchy, and aperiodicity in that model. These are companion results outside this T5 formal entry. A separate ordinary physical-family result concerns a different dense keyed construction in prime dimensions p ≡ 3 mod 4. A physical-monotile theorem for every odd-prime dimension is not established here. Sources: [S54 chain, Sections 1–3 and 6](sources/CHAIN.md), [uniform hierarchy summary](sources/THEOREM_SUMMARY.md), and [separate physical-family theorem](sources/FINAL_THEOREM.md).

The T7 source combines written arguments, exact computations, and cited hierarchy proofs. Its recorded review limitations remain relevant, and the T7 Lean endpoint is incomplete. Neither the T7 result nor the odd-prime companion claims should be described as verified by this T5 submission.

## Relation to earlier work and research interest

The subject is shape-enforced aperiodic tiling. Smith, Myers, Kaplan, and Goodman-Strauss construct planar chiral aperiodic monotiles in [A chiral aperiodic monotile](https://arxiv.org/abs/2305.17743v2). Tsiokos's [A Strongly Aperiodic Monotile in Three Dimensions](https://arxiv.org/abs/2609.19214v1) presents a three-dimensional keyed-chair construction and a geometric registration method. Kamenetsky's [Towards Strongly Aperiodic Monotiles in Higher Dimensions](https://arxiv.org/abs/2610.00916v1) develops a conditional higher-dimensional chair framework and finite contact tests. These sources provide context and methodological antecedents; none is cited as proving the exact S54 T5 statement.

The contribution selected for this entry is an explicit five-dimensional body together with a formal proof of its physical tiling statement. It connects exact rational geometry, unrestricted Euclidean placements, and the absence of translational periods in every admitted tiling. This is relevant to researchers studying aperiodic tilings, geometric matching rules, substitution hierarchies, and formal verification of geometry. The existence clause is essential: the result includes an actual tiling and does not obtain aperiodicity by ruling out all tilings. This explains the mathematical interest without making a novelty or priority claim.

The mathematical inputs are the S54 body and proof chain, the uniform registered hierarchy arguments, and the five-dimensional physical right-symmetry quotient argument. This entry formalizes and adapts those sources. The present development also ports the earlier Lean 4.19 T5 formalization. The metadata identifies retained source versions and relationships. The responsible maintainer confirmed the right to publish the supplied materials; original bibliographic authors and third-party endorsement remain unknown.

## Production and review

AI systems made substantive contributions to mathematical analysis, Lean proofs, exact certificate generation, checking, migration and exposition. Historical model identifiers and aggregate costs were not fully recorded and are not reconstructed. Human authorship and responsibility belong to Conor Grogan. AI systems are not listed as authors.

The recorded review consists of internal AI review and the identified compiler/kernel checks. No independent human expert review, peer review or novelty certification is claimed. The final verification will check the selected declaration with the standard Lean kernel, NanoDa and verified con-ron, through the official unchanged sandboxed Comparator. Only `propext`, `Classical.choice` and `Quot.sound` are permitted. No native-decide trust boundary or extra axiom is authorized.

## Reproducing the selected verification

The pinned toolchain is `leanprover/lean4:v4.35.0-rc2`; Mathlib is pinned at `065356127b1dc0016f66b7283ce0ce2c4055aa55`. On a compatible Linux host with Bubblewrap, run `bash scripts/verify-t5-on-linux.sh`. The script checks the frozen source manifest, obtains only the required Mathlib cache targets, builds dependency-ready project modules with at most two single-thread compiler processes and a 1.5 GiB available-memory reserve, falling back to serial execution on smaller hosts, builds Challenge and Solution independently, audits selected theorem axioms, and invokes the bundled official Comparator with both independent kernels. It fails on incompatible sandbox hosts rather than bypassing sandboxing.

`Challenge.lean` independently fixes the exact body and physical tiling statement. Its one deliberate theorem placeholder is part of the Comparator challenge. `Solution.lean` does not import Challenge and supplies the actual proof. `definition_names` is empty: no body definition is excused from declaration-closure comparison. The historical draft comment in the frozen Challenge predates its successful elaboration receipt.

## License and source responsibility

Conor Grogan approved authorship, responsible maintenance, rights to publish the supplied specifications/manuscripts/proof sources, Apache-2.0 licensing, and publication of this repository and T5 submission after all required checks pass, on 6 October 2026. The root [LICENSE](LICENSE) contains Apache License 2.0. Lean, Mathlib and other dependencies retain their own licenses and notices. No third-party source author's endorsement is inferred. Original bibliographic authors of some supplied manuscript snapshots remain unknown, as recorded in `formalization.yaml`.

This repository includes the substantive proof development. The retained mathematical sources and their exact hashes are under [sources/](sources/source-pins.json). The structured public abstract, provenance, classification, automation and review record are in `formalization.yaml`.
