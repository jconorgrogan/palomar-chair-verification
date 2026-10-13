# Aperiodic Monotiles in Infinitely Many Dimensions

The selected theorem says that for every ordinary prime `p` with `p % 4 = 3`,
there is a compact set in Euclidean `p`-space with nonempty interior which tiles
by arbitrary isometric copies, while every tiling by its unmarked physical
copies has no nonzero translational period. Reflections are allowed.

`Challenge.lean` states this directly using only Mathlib. A tiling is a set of
physical subsets covering all space with pairwise disjoint interiors. A period
preserves that entire tile collection. `Solution.lean` proves the identical
statement. There is no registration, hierarchy, contact-language, or matching
certificate among the theorem's assumptions.

## Construction and proof

The body is a chair made from all binary unit cubes except one, with finitely
many small asymmetric rational tent profiles on every exposed native facet.
The sites retain their full signed-permutation tangent frames. Integer
coefficients are the lexicographically ordered graph-component number times
the determinant orientation of the actual tangent-plus-normal frame.

The formal proof constructs the finite original generated contact language,
proves the full coefficient equations, derives global proper integral
registration from arbitrary physical tilings, classifies all complete profile
matches into the arithmetic atlas, and applies the proved hierarchy's period
descent. A compact-coordinate anchor chooses representatives equivariantly
under every physical translation, so no uniqueness or trivial body-symmetry
assumption enters the period argument.

Nonvacuity is proved separately and then combined: an actual registered
original-language world is realized as a physical tiling. Matched closed tubes
carry complementary literal graph pieces, all other carriers are excluded by
cell ownership, and the assembled bodies cover space with disjoint interiors.

## Scope

The selected result is the `p = 3 mod 4` prime family. It does not settle all
prime dimensions, exclude composite dimensions, prove that the body is a
topological ball, or assert that every tiling has trivial full isometry group.
This is a substantive uniform physical construction; no novelty or human
peer-review claim is made. The source manuscripts and their relationship to
the formalization are described in `formalization.yaml` and `sources/`.

The earlier five-dimensional CLARK development is related work. This project
reuses its unmarked physical-tiling model and compact translation-equivariant
frame construction, with the pinned source recorded in `formalization.yaml`.
Dimension 5 is outside the prime dimensions congruent to 3 modulo 4 treated
here; CLARK and the present family have separately recorded verification.

## Reproducibility and verification status

The project pins Lean `v4.35.0-rc2` and Mathlib commit
`065356127b1dc0016f66b7283ce0ce2c4055aa55`. The proof closure consists of 183
small source modules; `source-port-manifest.json` records the original and
module-system-port hashes. The standalone Challenge has one intentional
statement placeholder; the Solution and its proof closure have none.

The original proof sources and final family theorem passed fresh Lean,
official leanchecker, exact theorem-type and standard-axiom checks. The complete
module-system publication port passed `lake build Solution Challenge`; the
ported Solution also passed official leanchecker and exact type/axiom checks,
using only `propext`, `Classical.choice`, and `Quot.sound`.

The protected Palomar Comparator was attempted with both NanoDa and con-ron
enabled. Both attempts stopped before proof judging because the local host
could not create the required sandbox mount at `/root`. No sandbox or kernel
check was disabled. Comparator and the two external kernels have therefore
not verified this package. The first official remote full-workflow attempt
stopped during input preparation because the caller request identifier had the
wrong length; it did not judge any proof. This revision fixes that identifier.
Full mechanical verification remains pending, and this package has not been
submitted to or registered by Palomar. The preserved initial run is
[38403493227](https://github.com/jconorgrogan/palomar-chair-verification/actions/runs/38403493227). Recorded local
results and exact source hashes are in `verification/LOCAL_VERIFICATION.json`.
The final independent AI source review, including actual tiling existence and
the profile/atlas binding, is in `verification/INDEPENDENT_PACKAGE_REVIEW.md`.

## License and provenance

Project software is licensed under Apache-2.0. Retained manuscript prose has
its separately recorded rights, including CC-BY-4.0 where applicable. Lean,
Mathlib, cited sources and other third-party material retain their own
licenses. `sources/HISTORICAL_LICENSE_SCOPE.md` records the historical release
scope; it does not grant new publication authority for this submission.
