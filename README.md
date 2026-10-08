# HENRY: a strongly aperiodic seven-dimensional monotile

## Repair1 status, 8 October 2026

The first official run 37725422679 passed independent Challenge compilation but failed the clean Solution build. The cause was an undeclared implicit Nat parameter in closure_analysis/CoarseWalls.lean under autoImplicit=false; subsequent arithmetic diagnostics were cascading elaboration errors. This revision adds only the existing implicit binder {p : Nat}. Old/new signatures and definitional-body probes match exactly. No theorem statement, proof tactic, assumption, axiom, compiler option or Comparator exemption was changed.

All 910 targeted fresh compiles and 105 default-kernel checks passed, including all 889 selected modules previously assigned a historical-command-gap fallback and the final public endpoint. These checks reuse 3462 unaffected certified objects and are not a full clean-project build. Independent review passed. The corrected full official run remains required. Complete original failure/recovery history is retained under verification/repair1/.


The selected local theorem is `PalomarMonotiles.T7_strongAperiodicity : PalomarMonotiles.T7StrongClaim` in Solution. For the exact compact T7 body, it establishes an actual tiling, absence of nonzero translational periods in every arbitrary-placement physical tiling, and a finite full Euclidean symmetry group with at most 645,120 elements. Copies may be translated, rotated or reflected. Trivial symmetry is not asserted.

## Verification status

On 8 October 2026 the exact 262,144-pair contact classification completed with 3,144 successful guarded compiler/default-checker receipts. The final composition passed all thirteen required processes and complete input rehash: five inherited compact-interface rechecks and four new compile/check pairs. All twelve final audited declarations use only propext, Classical.choice and Quot.sound. An independent agent reviewed the receipt/source/object/type/guard bindings.

The initial final-composer attempt stopped because the default checker could not discover a symlinked target. A separately reviewed namespace-only recovery materialized twenty-five byte-identical inherited object parts without changing proof sources, the guard, default checker, mathematical plan or search roots. The failed attempt and recovery provenance are preserved. These inherited copies are not claimed as fresh compilations. Preparation comments in unchanged Lean sources describe their historical state; actual dated verification records establish the later local result.

Successful official full Palomar verification of repair1, its clean source build, independent Comparator and NanoDa/con-ron kernels, and HENRY registration remain pending. The first attempt failed at source compilation and is explicitly preserved. This source tree does not claim external acceptance. CLARK is a separate five-dimensional result; its registration is not evidence for HENRY.

## Source and build

The selected Solution import closure contains 4,123 project modules. Challenge is a separate, independent 39,804-byte statement with one deliberate theorem placeholder; Solution does not import it. The implementation closure has zero proof holes and custom axioms. Toolchain: Lean 4.35.0-rc2. Mathlib revision: 065356127b1dc0016f66b7283ce0ce2c4055aa55. Dependency pins are in lake-manifest.json.

The reviewed declarative Lake configuration preserves per-module compiler flags with exact disjoint globs. The synthetic supported-toolchain grouping smoke test passed; a successful clean Lake build of repair1 has not yet been established. All 889 selected historical-command-gap fallback vectors have now been tested by genuine fresh compilation during repair1. verification/COMPILER_OPTIONS.json records actual new receipt hashes for 903 selected recompiled modules and preserves historical receipts for the others. No previously missing historical command is invented; the fresh command is a separate dated result.

Ordinary supported build: `lake build Solution`. The official pipeline independently compiles Challenge and builds Solution in its own controlled source environment. No compiled objects, cache copies or manufactured Lake traces are included here. The official one-shot caller is intentionally withheld until immutable source and metadata are reviewed and remotely verified.

## Sources and authorship

Responsible maintainer: Conor Grogan. Substantive AI mathematical, proof-code, generator, audit and writing contributions are disclosed in formalization.yaml. This is not independent human peer review or a novelty/priority certification. Exact source data and registered-model source context are under sources/. Project software is Apache-2.0; author-controlled prose/data are CC-BY-4.0; third-party terms remain unchanged. See LICENSE_SCOPE.md.
