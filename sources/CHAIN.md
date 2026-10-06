# CHAIN.md: end-to-end chains for T7 and T5 (S51 / agent E, 5 Oct 2026)

Labels. PROVED = argument written out in the named file (every such file is AI-written; none has had a human or proof-assistant
review). COMPUTED = number printed by a command whose log is named. CERTIFIED = UNSAT answer whose proof an independent checker
accepted, checker verdict in the named log. CITED = the other AI's ordinary proof, file and SHA-256 given (AI-reviewed only).
Paths: `s51/...` and `s47/...` are under /home/claude/kernel/paths/; `their/...` is /home/claude/kernel/paths/s50/in/.
Their uniform files live in `their/Chair_hierarchy_X1_cross_dimension_replay_2026-10-05/uniform_prime_certificate_20261005/` (UPC below).

## 1. The two statements

**Theorem T7.** Let T7 be the body specified by `s51/D_proof/final/tile7_final_spec.json` (SHA-256
2d8a6562eb1ee4f7ebeb0af571c783d92fb5c3296bc638848aad13ebcd2230a2). It is the 7D chair P7 = [0,2]^7 minus [1,2]^7 (127 unit cells).
Its 896 exposed unit facets carry 1,024 congruent rational 6D box pyramids of height 1/336: 512 bumps and 512 dents. (a) R^7 has a
tiling by congruent copies of T7. (b) No tiling of R^7 by congruent copies of T7 has a nonzero translational period. Rotations,
reflections and translations are all allowed.

**Theorem T5.** Let T5 be the body specified by `s51/D_proof/final/tile5_final_spec.json` (SHA-256
8c94499b8b9fc89efef794497723f649a188de6a7a5460849dc7989bc61b6094). It is the 5D chair (31 unit cells) with 256 congruent 4D box
pyramids of height 1/240 (128 bumps, 128 dents). (a) R^5 has a tiling by congruent copies of T5. (b) No such tiling has a nonzero
translational period.

Scope. Only these two height-rescaled files are covered. The earlier 1/16-height specs (A_sparse7/tile7_sparse_spec.json,
B_five/tile5_spec.json) are not. D found that the registration hypothesis T5 (sector condition) fails exactly for the 7D key at the
COMMON height scale with four magnitudes, and the 1/16 one-height specs were not checked against T5. Mate sets do not change under
the rescaling (keys are matched by position, frame and height class).
"Finite Euclidean symmetry group" (the other AI's stronger 7D conclusion) is NOT part of these statements.

## 2. Link status, T7

| # | link | status | evidence |
|---|---|---|---|
| L1 | T7 is a compact rational polyhedral body; keys pairwise disjoint, inside their facets with margin 181/672; collars disjoint | PROVED + COMPUTED exactly | s51/D_proof/PROOF.md §1 (E1–E5); s51/D_proof/final/logs/hyp_check.log |
| L2 | Registration: in every tiling of R^7 by copies of T7, after one global isometry each tile is x -> Gx + t applied to T7, G in B_7, t in Z^7; the carriers partition the unit cells of Z^7; each exposed unit facet is shared in full with one tile | PROVED (unreviewed, written 5 Oct) under T1, T2, T4, T5, T6; the hypotheses are COMPUTED true exactly for this file | s51/D_proof/PROOF.md §3–4, §8 (Theorem RS items 1, 3; one-height form), SHA 0f6c04a3…; s51/D_proof/final/logs/hyp_check.log |
| L3 | Contact law: two tiles whose carriers share a unit facet have relative pose in M_geom(T7) (registered, disjoint carriers, every shared-facet key identity holds) | PROVED | PROOF.md §4 item 4, §8 |
| L4 | M_geom(T7) = CL7, 408 poses, all proper | COMPUTED, two independent codes. Not PROVED: one-height separation is false in 7D (D: 196,608 accidental holding triples) | A's JSON-only verifier on this file: D_proof/final/logs/verify_A_tile7.log and my rerun logs/compare_tiles.log. My own code from the spec text, no shared code: logs/indep_t7.log |
| L5 | All tiles of a tiling have the same handedness | COMPUTED (L4 has no improper mate among 360,448 improper key-to-key poses; facet adjacency is connected) | logs/indep_t7.log, logs/compare_tiles.log |
| L6 | M_geom(T7) equals their pinned p7_CL.json = p7_F.json as a set, under the converter K | COMPUTED | logs/compare_tiles.log (§3), logs/compare_sets.log; pins: logs/audited_source_hashes.log (45/45), logs/pins_5d_quotient.log (bundle 354/354) |
| L7 | Converse: every CL7-legal registered framed tiling is a tiling by T7 | PROVED | PROOF.md §4 item 4 (converse) |
| L8 | A full E7-legal framed tiling exists; E7 ⊂ CL7. With L7 this gives (a) | CITED (UPC/NONEMPTINESS_AND_APERIODICITY.md §1, SHA d68af020…); inclusion COMPUTED | logs/compare_tiles.log ("p7_E subset of T7 mates") |
| L9 | (H) Every full CL7-legal registered framed tiling of R^7 has a unique nested hierarchy of complete parent stars | two routes, below | |
| L9(i) | census route: rigid census_gauge on A = CL7, EXIST + UNIQUE | Q0 1/1, Q1 127/127 CERTIFIED; QJ 8,128/8,128 CERTIFIED by DRAT + drat-trim + cake_lpr. Second implementation (mine, from their p7_CL.json): Q0, Q1 127/127 CERTIFIED (DRAT + cake_lpr), QJ 8,128/8,128 CERTIFIED by LIDRUP + lidrup-check (unverified checker). CNF encodes the intended question: NOT certified (two implementations agree, COMPUTED). CL(CL7) = CL7, odd 0: COMPUTED. Census answers -> hierarchy: PROVED (unreviewed) | logs/cert_g_l7_CL*.jsonl, logs/final_cover.log; logs/reenc_all_p7.log; s47/B_shape5d/logs/sets_l7.log; s47/B_shape5d/RESULTS.md "(e) Chain" (SHA f7524527…) |
| L9(ii) | ordinary route | CITED; binding: every input MATCHES (§4) | their/Update_2026-10-05_Readability_Registration/audit_7d_geometric_chain_20261005/END_TO_END_AUDIT.md §5 (SHA 4946af4f…) composing UPC/UNIFORM_REDUCTION_PROOF.md (84f105f6…), HOLE_GRAPH_AND_SYMBOLIC_E.md (72c5d9e8…), UNIFORM_STAR_COMPLETION.md (bb65f0e7…), UNIFORM_COARSE_LEGALITY.md (12d16085…), NONEMPTINESS_AND_APERIODICITY.md (d68af020…), odd_offset/PROOF.md (f1f5492e…) |
| L10 | Unique hierarchy implies a framed tiling has no nonzero period (a period lies in 2^n Z^7 for all n) | PROVED | s47/B_shape5d/RESULTS.md (e); also CITED NONEMPTINESS §2 |
| L11 | A period of an unmarked tiling gives a period of a CL7-legal registered framed tiling | PROVED (§5 below), using Lemma K4 of PROOF.md for arbitrary placements | this file §5; CITED analog END_TO_END_AUDIT §5 last paragraph |

## 3. Link status, T5

| # | link | status | evidence |
|---|---|---|---|
| L1 | body well defined (margin 89/320) | PROVED + COMPUTED exactly | PROOF.md §1; final/logs/hyp_check.log |
| L2 | registration (RS items 1, 3) | PROVED (unreviewed) under T1, T2, T4, T5, T6, all COMPUTED true | PROOF.md §3–4, §8 |
| L3 | contact law: shared-facet pairs have relative pose in M_geom(T5), for every choice of representative frames | PROVED | PROOF.md §4 item 4 |
| L4 | M_geom(T5) = CL5 ∪ CL5·r, 284 poses, all proper | PROVED from Gate data (Lemma S', one height, T3' holds) + COMPUTED (RAW enumeration of 1,539,120 proper + 1,539,120 improper poses from the JSON) | PROOF.md §8; final/logs/verify_B_tile5.log; my rerun logs/compare_tiles.log (§4) |
| L5 | same handedness | PROVED (Lemma P', sign(V)·chi constant COMPUTED) | PROOF.md §8; hyp_check.log |
| L6 | M_geom(T5) = p5_F.json as a set under K; p5_F = K CL5 K in their encoding; our r maps to their R; T5's body symmetries inside the 120 carrier symmetries are exactly {id, r} | COMPUTED | logs/compare_tiles.log (§4: RAW, JSON list, gate_l5 M, p5_F all equal; my own vertex reconstruction for the symmetry group) |
| L7 | converse: every M-legal registered framed tiling is a tiling by T5 | PROVED | PROOF.md §4 item 4 |
| L8 | a full E5-legal framed tiling exists; E5 ⊂ M | CITED (NONEMPTINESS §1, p = 5) + inclusion COMPUTED | logs/compare_tiles.log |
| L9(i) | census route: census_gauge on A = M with frames mod {id, r}, EXIST + UNIQUE | Q0 1/1, Q1 31/31, QJ 496/496 CERTIFIED (DRAT + drat-trim + cake_lpr). Second implementation (mine, their p5_F.json, gauge K): all CERTIFIED (QJ by LIDRUP). Encoding: NOT certified. CL(M) = M, gauge-closed: COMPUTED. Answers -> hierarchy: PROVED (unreviewed) | logs/cert_g_l5_M_gauge.jsonl; logs/reenc_all_p5g.log; s47/B_shape5d/logs/clm_l5.log; s47/B_shape5d/RESULTS.md (d), (e) |
| L9(ii) | ordinary route | CITED; binding: every input MATCHES (§4) | their/Expert_handoff_2026-10-05/p5_physical_quotient_hierarchy_20261005/QUOTIENT_HIERARCHY.md (SHA 74b2e9c1…), plus UPC files above |
| L10 | hierarchy -> no period of the framed (mod r) tiling | PROVED | s47 RESULTS (e); CITED QUOTIENT_HIERARCHY §6 |
| L11 | unmarked -> framed periodic realization | PROVED (§5) | this file §5; CITED QUOTIENT_HIERARCHY §6 |

## 4. Route (ii) binding (Task 2): their inputs against our chain's output

Their 7D hierarchy input (END_TO_END_AUDIT §5, UPC files), written as one hypothesis: *a tiling of all of R^7 by unit chairs P7,
each placed as (a, t) with a a signed permutation and t in Z^7 in one common lattice (pose = image a·P7 + t), such that every pair of
tiles meeting in a positive 6-dimensional boundary piece has relative pose (a^-1 b, a^-1 (u - t)) in CL7 (their p7_CL.json), for the
rule p = 7, mu = 1, g = 6 with the empty outer role at the identity frame.* Our chain's output (L2 + L3 + L4 + L6) is exactly this.

| their input | our side | verdict |
|---|---|---|
| rule p = 7, mu = 1 (square), g = 6 (nonsquare, order 2), centre identity at anchor 1 | our Λ(1,6) children = their 128 children under K | MATCHES (logs/compare_sets.log, logs/binding_checks.log) |
| empty outer role = identity frame at anchor 0 (their stipulated endpoint) | our anchor-0 child is ((0..6), (+1)^7) -> their (1,...,7) at 0 | MATCHES (logs/compare_tiles.log §2) |
| complete tiling of R^p (used in CL -> E and star completion) | RS item 3: carriers partition all unit cells of Z^7 | MATCHES |
| lattice registration, signed-permutation frames, pose = continuous image with lower-corner correction | RS item 1; converter K verified on matrices and on cell sets | MATCHES (logs/compare_sets.log) |
| proper frames (their whole framework) | relative poses: all 408 are proper; absolute: one handedness (L5), so the global isometry can make all frames proper; their proofs use relative poses only | MATCHES (handedness COMPUTED for T7) |
| legality on every face contact (positive (p-1)-measure) | RS item 4 is stated for "carriers share a unit facet"; for unions of lattice unit cells with disjoint interiors these are the same pairs | MATCHES (one-line argument) |
| relative-pose convention norm = (f^-1 g, f^-1 (u - t)) | the verifiers' (G, T) of the copy with the root at the identity is norm(root, copy); K commutes with inversion; CL7 is inverse-closed, so the direction cannot matter | MATCHES (logs/compare_sets.log, logs/binding_checks.log) |
| the set CL7 used inside the proof is the symbolic CL(E) catalog | p7_CL.json = their catalog() code = our geometric CL(E) (s43 geo.child_legal) | MATCHES; this also checks their symbolic CL classification at p = 7 and p = 5 |
| face-to-face contact | not assumed by them, not given by us | MATCHES (not needed) |
| lower-dimensional contacts | unconstrained on both sides | MATCHES |
| unmarked-to-framed step uses a registration theorem for arbitrary placements | our RS / Lemma K4 is stated for arbitrary placements g_A, g_B | MATCHES (§5) |

5D quotient proof (QUOTIENT_HIERARCHY.md) inputs:

| their input | our side | verdict |
|---|---|---|
| p = 5, mu = 1, g = 2, z_empty = 0 | our Λ(1,2) children = theirs (32/32); anchor-0 child identity | MATCHES |
| M = F(E) = p5_F.json, 284 | T5 RAW mates = p5_F under K | MATCHES (logs/compare_tiles.log) |
| M = K CL K, K = {I, R}, R: i -> -i mod 5; M invariant under independent endpoint changes | checked in their encoding | MATCHES (logs/compare_tiles.log) |
| R is a proper self-symmetry of the body; (G, t) and (GR, t) are the same physical tile | r = (0)(1 4)(2 3), all signs +, det +1, fixes P with zero translation; T5's symmetry group in the 120 carrier symmetries is {id, r} (COMPUTED). Every registered self-isometry of T5 is a carrier symmetry (PROVED, one line: it maps lattice cell centres to lattice cell centres; the cell centres lying in T5 are exactly those of P, because P's centres are interior (E3) and keys reach at most 1/240 outside P) | MATCHES |
| full M-legal registered carrier tiling (right-K classes) | RS items 1, 3, 4; M_geom closed under r on both sides | MATCHES |
| existence via "E ⊂ M plus the physical realization theorem for T(E)" | E5 ⊂ M COMPUTED; our converse RS item 4 replaces their realization theorem | MATCHES (with our theorem substituted) |
| output scope: unique hierarchy within each registered right-K realization; no global CL lift | the same scope as our gauge census mod r | MATCHES |

No input is DOES NOT MATCH or UNCLEAR. Reliability, as distinct from binding: route (ii) is an AI-written ordinary proof with AI
reviews only. I did not re-prove it. I verified its pinned files byte for byte, ran cheap exact checks of its stated set
properties (logs/binding_checks.log), and checked that our geometric CL equals its symbolic CL.

## 5. L11, written out (PROVED here; uses only RS / Lemma K4 and L10)

Let 𝒯 be a tiling by copies of T (T7, or T5) with a translation period v ≠ 0. Tiles are bounded, so v acts freely on 𝒯. For each
orbit pick one tile A and any isometry g_A with g_A(T) = A. Set g_{A+nv} = τ_{nv} ∘ g_A. Normalise by Φ = g_{A0}^{-1}. Lemma K4 is
stated for arbitrary placements (PROOF.md: "let A = g_A(T), B = g_B(T), Φ = g_A^{-1} g_B"). So the relative pose of facet-adjacent
tiles is registered, and the RS global step makes every Φ g_A registered: Φ g_A = (G_A, t_A), G_A in B_d, t_A in Z^d. The linear
part of Φ is L. Then Φ g_{A+v} = τ_{Lv} Φ g_A, so (G_{A+v}, t_{A+v}) = (G_A, t_A + Lv). The framed realization has the nonzero period
Lv (integral, as a difference of anchors). Its contacts lie in M_geom (L3), which is CL7 (L4), or 284 = M in 5D. That contradicts L10.
For T5 the frames are taken mod right r, which L10 handles (the anchor does not change under G -> Gr). ∎

## 6. Weakest remaining link

L2 (registration, Theorem RS). It is a new proof, written by one AI agent on 5 Oct, with no second reader. D's referee pass covered
RIGIDITY.md and the other AI's registration theorem, not RS. Unlike L4 and L9 it has no computational cross-check. D's numeric
sanity runs are local 3D motion tests only. The next weakest is L9 in its route (i) form: the certificates prove the CNFs are
UNSAT, but nothing certifies that the CNFs encode (H). Route (ii) covers (H) independently, but only as a cited AI-reviewed proof.
L4 for T7 rests on computation only. Two independent codes now agree on it exactly, including the candidate counts
(917,504 / 360,448 improper / 464,114 overlapping / 302,365 disjoint).
