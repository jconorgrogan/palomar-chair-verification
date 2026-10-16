# Static review of the independent facet-closure attachment

Review date: 2026-10-16.

## Conclusion and verification level

The attachment is useful as a proposed independent finite regression check of the registered facet-matching relation, especially its supplied `p = 11` result. It also exposes reproducibility and historical-source-link issues worth fixing.

**This review did not execute the supplied Python programs. All numerical enumeration outcomes below are reported by the attachment, not independently reproduced or formally verified.** Static inspection found no mathematical counterexample to the finite claims, but it does not certify the implementation, the outputs, or the uniform theorem. Nothing here changes the verification status of hierarchy C, physical registration, the 5D CLARK result, or other Lean packages.

Recommended immediate change: retain this documentation-only review. Do not import or relicense the attached code, label its outputs verified, or use its finite results to close a separate proof/CI obligation.

## Provenance

- Reviewed archive: `facet_closure_independent.zip`
- Archive SHA-256: `4828784baa5083adb339bf1b2cfa73172fef32a74b523addbd324724d7e49c69`
- Original referenced manuscript: [sources/FINAL_THEOREM.md at 9008dec3afc006a62d3d2fd6b49b12f189248f33](https://github.com/jconorgrogan/palomar-chair-verification/blob/9008dec3afc006a62d3d2fd6b49b12f189248f33/sources/FINAL_THEOREM.md)
- Manuscript Git blob: `cf593f00f02aaad2bccb2f5a2b093bc2dacbcb09`
- The same blob is retained under [sources/UNIFORM_FACET_FINAL_THEOREM.md on verification/prime-three-mod-four-20261013](https://github.com/jconorgrogan/palomar-chair-verification/blob/verification/prime-three-mod-four-20261013/sources/UNIFORM_FACET_FINAL_THEOREM.md), as observed during review.

Archive paths and line numbers below are relative to `facet_closure_independent/`. The archive contains three Python sources, five JSONL logs, and a README; no license or runtime/package lock is included.

Source SHA-256:
- `scripts/common.py`: `fdf029d704498225e2058417c2362f64b8f26650c625bc6eb7f40a8eac497c32`
- `scripts/enumerate_F.py`: `f29f097aff0a156bda6bc96ec1d2c82a7a3217d0f6b8103366cd3b249c24356f`
- `scripts/naive_sites.py`: `d911124c4c508e1d5ed5aeea5540cf8a97a25e7410acccbee1d1b18e5b9ccb8b`

## What is actually tested

The manuscript [lines 9–16](https://github.com/jconorgrogan/palomar-chair-verification/blob/9008dec3afc006a62d3d2fd6b49b12f189248f33/sources/FINAL_THEOREM.md#L9-L16) claims, uniformly for primes `p ≡ 3 (mod 4)`,

`F(E) = CL(E)`, with `|F(E)| = 2(2^p − 1) + 3p² + p`.

The finite relation `F(E)` is expressly restricted to proper signed-permutation frames, integer translations, interior-disjoint carriers, and opposite coefficients at every paired site of every shared unit facet ([manuscript lines 35–39](https://github.com/jconorgrogan/palomar-chair-verification/blob/9008dec3afc006a62d3d2fd6b49b12f189248f33/sources/FINAL_THEOREM.md#L35-L39)).

The attachment transcribes the generating language in `common.py:185–213` and the proposed CL catalog in `common.py:216–235`. Its main route constructs the facet graph and tangent holonomy, generates candidate poses through a matching facet, and tests every shared facet (`enumerate_F.py:33–117,119–313`). It compares complete pose sets, not merely counts (`enumerate_F.py:320–330`). The formula is computed only after enumeration for comparison (`enumerate_F.py:323`).

This is useful evidence about the finite registered relation. However:
- Candidate exhaustiveness relies on the graph/coset characterization of full-profile matching (`enumerate_F.py:12–17`; `README.md:43–44`). It is not a search over arbitrary Euclidean placements.
- CL is transcribed from the manuscript's catalog, not independently derived from child legality or substitution (`common.py:216–235`; `README.md:46`).
- Both implementations share `common.py`, including E, carrier geometry, and the CL catalog. Agreement cannot detect all shared transcription errors.
- The separate explicit-site route avoids the holonomy shortcut only at `p = 3`. It still searches registered signed-permutation/integer poses (`naive_sites.py:100–114`).
- Finite examples do not prove the uniform statement, nonemptiness, arbitrary-copy physical registration, hierarchy, or aperiodicity. The original manuscript separately identifies these inputs at [lines 148–174](https://github.com/jconorgrogan/palomar-chair-verification/blob/9008dec3afc006a62d3d2fd6b49b12f189248f33/sources/FINAL_THEOREM.md#L148-L174).

## Supplied results, not rerun

| p | Reported F and CL size | Hole contacts | Wall contacts | Source |
|---|---:|---:|---:|---|
| 3 | 44 | 14 | 30 | `outputs/out_p3.jsonl:3` |
| 7 | 408 | 254 | 154 | `outputs/out_p7.jsonl:3` |
| 11 | 4,468 | 4,094 | 374 | `outputs/out_p11.jsonl:47` |

Each supplied summary reports both set differences empty. At `p = 11`, wall counts are 121 each for P, positive complement-axis, and negative complement-axis contacts, plus 11 M contacts. The log reports 46,137,344 generated candidates and 499,710 unique candidates after the overlap filter (`outputs/out_p11.jsonl:8`).

The explicit-site `p = 3` log reports 192 sites, 12 site components, all 48 signed permutations and translations in `[-4,4]^3`, 44 proper matching contacts, and no improper contacts (`outputs/naive_p3.jsonl:1`). This is a useful differently structured check, subject to the shared-code limitation.

The `p = 13` control reports 8,530 improper entries in the listed generating contacts including inverses, then does not compute F (`outputs/out_p13.jsonl:1–2`; `enumerate_F.py:37–49,113–116`). This is outside the `p ≡ 3 mod 4` hypothesis; it is not a counterexample to the stated theorem. The number counts list entries, not demonstrated distinct improper poses.

## Corrections and implementation limits

1. **Runtime discrepancy.** `README.md:14` says the `p = 7` run took 2 seconds. Its retained summary says `total_time_s = 44.98`, with candidate generation at 1.99 seconds (`outputs/out_p7.jsonl:2–3`). Correct the table or identify the exact newer run behind it.

2. **Logs are not bound to the included script version.** The p3/p7 logs use `candidates_after_box_prefilter_unique`. The included script emits `candidates_after_box_prefilter` and `candidates_after_exact_overlap_prefilter_unique` (`enumerate_F.py:225–230`), as the p11 log does. Thus the p3/p7 logs cannot be unmodified stdout from this exact script. The archive lacks a run manifest tying source hashes, Python/NumPy versions, commands and outputs together.

3. **The generic parameter interface overstates the safe encoding range.** `enumerate_F.py:142–156` packs p base-16 axis digits plus p sign bits into one uint64, requiring 5p bits for its general layout. It is safe against this width issue for the reported p3/p7/p11, but not generically beyond p12; base-16 axis digits also cannot represent all axes for p greater than 16. The independent base-`2p` signed-permutation key uses int64 arithmetic (`enumerate_F.py:241–248`) and also needs a checked bound. The `p = 13` improper-input guard exits before packing. `README.md:45` should not imply that p19 is merely a runtime problem: the implementation would need changes as well.

4. **The explicit-site route has one floating-point step.** `naive_sites.py:48` uses `round(np.linalg.det(M))` for a signed-permutation determinant. Replace it with exact permutation parity times the product of signs. This is an exactness/reproducibility improvement, not evidence that the reported p3 determinant values are wrong.

5. **Useful hardening before reuse.** Check supported p values explicitly; use collision-free, checked pose keys; make the set-equality and generator-sanity claims fail the run when false; save canonical pose sets and symmetric-difference witnesses. Current equality fields are printed rather than enforced as test assertions (`enumerate_F.py:325–330`; `naive_sites.py:116–120`). Avoid importing the optional pickle artifact into an untrusted deserializer; the script only writes pickle (`enumerate_F.py:332–333`).

## Historical broken links: verified at one snapshot

The [complete recursive tree of commit 9008dec](https://api.github.com/repos/jconorgrogan/palomar-chair-verification/git/trees/9008dec3afc006a62d3d2fd6b49b12f189248f33?recursive=1) contained 1,407 entries and reported `truncated: false`. None of these 11 distinct target paths referenced by the manuscript was present:

- `audit_uniform_facet_closure_20261005/CHECK_OUTPUT.jsonl`
- `audit_uniform_facet_closure_20261005/INDEPENDENT_AUDIT.md`
- `audit_uniform_facet_closure_20261005/independent_check.py`
- `dimension_free_facet_registration_20261005/REGISTRATION_THEOREM.md`
- `uniform_prime_certificate_20261005/HOLE_GRAPH_AND_SYMBOLIC_E.md`
- `uniform_prime_certificate_20261005/NONEMPTINESS_AND_APERIODICITY.md`
- `uniform_prime_certificate_20261005/UNIFORM_COARSE_LEGALITY.md`
- `uniform_prime_certificate_20261005/UNIFORM_REDUCTION_PROOF.md`
- `uniform_prime_certificate_20261005/UNIFORM_STAR_COMPLETION.md`
- `sources/DRAFT.md`
- `sources/FINAL_SOURCE_PINS.txt`

See [manuscript lines 5, 20, 39, and 164–172](https://github.com/jconorgrogan/palomar-chair-verification/blob/9008dec3afc006a62d3d2fd6b49b12f189248f33/sources/FINAL_THEOREM.md#L164-L172). This confirms a reproducibility gap in that historical snapshot. It does **not** establish the attachment's stronger “absent from every commit on every branch” assertion (`README.md:61–75`). Other source documents in later packages must be assessed on their own contents and pins.

## Recommended next steps

1. Preserve this review and its exact source/archive identities without changing existing verification claims.
2. With execution authorized and provenance/license clarified, harden the bounds and exact determinant, then rerun both p3 routes and the p7 holonomy route in a pinned environment; rerun p11 separately if resources permit. Retain commands, versions, hashes, full stdout, canonical pose lists and failure witnesses.
3. Independently check E/CL transcription and document why candidate generation covers the defined registered F. Add adversarial tests for incomplete facet profiles and the empty endpoint.
4. Restore the missing original dependencies, or replace broken links with verified immutable sources and an explicit account of any differences. Do not silently substitute a later proof for a missing historical input.
5. Keep all resulting finite checks separate from the current hierarchy-C clean CI and the physical/uniform proof obligations.

