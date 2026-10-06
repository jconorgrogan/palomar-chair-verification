# Comparator portability repair

The first official full run built the complete Solution successfully but rejected a generated proof constant in the independently compiled statement copies. It did not reach the independent main kernels.

The only changed Lean source blocks are the bound proofs in `tangentIndex` in Challenge and CompactStatement. Explicit natural-number proof terms replace `omega`. The old and new complete functions are definitionally equal (`rfl`); no coordinate, body, theorem quantifier, comparator exemption or permitted axiom changed.

Local checks passed: the original helper reproduces the failure; the repaired helper passes the exact comparator and all three kernels; the full `T5Claim` dependency closure passes exact comparison; all 20 affected compact-binding modules, actual Solution and VerificationAudit compile afresh. The full-statement diagnostic uses a reflexivity theorem and is not a full main-proof independent replay. The official full retry remains required.

Exact source, object, export and log hashes are recorded in [COMPARATOR_REPAIR.json](COMPARATOR_REPAIR.json).
