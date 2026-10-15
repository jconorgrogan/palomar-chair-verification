# Hierarchy C source snapshot: work in progress

This branch publishes an immutable source snapshot for a future clean, cloud-only verification attempt. The proof is incomplete and unverified. Publication is not a successful proof check, a Palomar acceptance result, or a claim that the hierarchy theorem has been established.

## Exact target

- Module: `SpectreFinite.RadiusFivePruningHierarchy`
- Declaration: `SpectreFinite.HexSearch.RadiusFivePruning.certifiedParentOccurrenceTheorem`
- Required type: `SpectreFinite.HexSearch.NativeHierarchy.ParentOccurrenceTheorem`
- Permitted standard axioms: `propext`, `Classical.choice`, `Quot.sound`

The archive contains 6,369 selected Lean source files (98,258,625 bytes before archiving), including the current 2,960-module main pruning inventory, 1,052-module private-table inventory, six final assembly modules, and their shared source dependencies. The name “private” in the mathematical module family is historical; this branch is public.

The per-file SOURCE_MANIFEST.json records SHA-256, size, ordered imports, the exact target contract, and the pinned official Lean 4.35.0-rc2 Linux release. The source files are stored in a deterministic compressed archive to keep publication manageable. This is a CI preparation snapshot; any submission system requiring plaintext source must be handled separately.

## Verification status

This source-only commit contains no active GitHub Actions workflow. A separately reviewed pipeline commit must pin the source commit and manifest and rebuild every selected project module from source on clean standard Ubuntu runners. No previous cache, acceptance receipt, or historical CI result establishes success for this snapshot.

Future success requires all staged compilations and checks, an explicit exact-type and axiom check, a fresh full-closure Lean kernel replay, and independent export-based checker results. A failed, timed-out, missing, expired, or incomplete stage cannot be accepted.

This snapshot covers the finite hierarchy-C target only. It does not establish unconditional 2D/4D downstream results; those require their own checked assembly after C succeeds.

## Licensing and provenance

Owned project code is licensed under Apache License 2.0. See LICENSE and THIRD_PARTY_NOTICES.md. Third-party licenses remain applicable. PROVENANCE.json identifies the selected inventory hashes and exact source-content digest. The Git commit containing these files is the publication source commit; the subsequent pipeline must record its actual SHA rather than using a mutable branch name as source identity.
