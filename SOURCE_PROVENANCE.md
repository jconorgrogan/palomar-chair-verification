# Companion evidence location

The exact reproduced record below comes from the private companion evidence archive palomar_table_provenance_20261018T0827.tar.gz (SHA-256 2dbd28ee4538bfd1a6fd4c64fff979c10cacbde6a2bfb7d9428bac63363fe408). Paths and reproduction commands in that record are relative to the unpacked evidence packet, not this project root. The original C source archive is a separately hash-pinned comparison input. The proof sources are unchanged.

# Source provenance for SpectreFinite.ListedPatches

## Status and scope

This is a new, independently reproduced provenance record prepared on 2026-10-18. It is not the historical SOURCE_PROVENANCE.md referenced by the existing Lean header, and it does not claim to reconstruct the original author's extraction process. The historical record was not recovered from the repository locations inspected.

The new reproduction establishes exact equality of the nine edgeWords rows (54 marks) and nine childrenTable rows (71 placed hexagons) with the pinned, unchanged Lean source below. It verifies these finite table data only. It supplies no new proof of completeness, an infinite hierarchy, tiling existence, or aperiodicity, and does not execute Lean.

## Attribution and upstream sources

The mathematical figures are by David Smith, Joseph Samuel Myers, Craig S. Kaplan, and Chaim Goodman-Strauss, *A chiral aperiodic monotile*, Combinatorial Theory 4 (2) (2024), #13, DOI [10.5070/C64264241](https://doi.org/10.5070/C64264241).

- Extraction source: [arXiv:2305.17743v2](https://arxiv.org/html/2305.17743v2), dated 28 September 2024, specifically [Figure 4.2](https://arxiv.org/html/2305.17743v2#S4.F2) and [Figure 5.1](https://arxiv.org/html/2305.17743v2#S5.F1).
- [Author project page](https://cs.uwaterloo.ca/~csk/spectre/) identifies the journal article and arXiv preprint as identical. Its retained HTML is independently hashed below.
- The [official journal PDF](https://escholarship.org/content/qt4xn41982/qt4xn41982_noSplash_faaaf76e05d499e34d4a903a2207b319.pdf), page 1, states: “© The authors. Released under the CC BY license (International 4.0).” License: [Creative Commons Attribution 4.0 International](https://creativecommons.org/licenses/by/4.0/).
- The journal notice was read from the official PDF through the web text service; the full PDF was not retained or byte-hashed here. This is distinct from the retained arXiv HTML's non-exclusive arXiv distribution-license notice. The journal's author-granted CC BY license, not the arXiv transport license, supports the attribution statement.

The adapted representation replaces Greek marks with signed integers, normalizes lattice coordinates and rotation indices, and omits presentation-only colors, underlines and outer supertile annotations. These are newly documented representation changes; the existing Lean bytes and table values have not been changed. No endorsement by the original authors is implied. Existing proof-source licensing and all source headers remain in place.

## Exact retained bytes

SHA-256 hashes:

- arXiv HTML, retained as inputs/arxiv-2305.17743v2.html: 611,500 bytes; 2a02fc0bf345298041af27184105ad6cb2b9c565237f1743d2e3fa61c3daa254. Retrieved 2026-10-18 from https://arxiv.org/html/2305.17743v2. This pins the actual HTML used, since a versioned paper identifier alone need not freeze its HTML rendering.
- Author page, inputs/author-project-page.html: 5,848 bytes; b08c959516a1d844c4ba28dc8fcae24966d3068fd756f6d620040cca665dbbad. Retrieved 2026-10-18.
- Repository snapshot: jconorgrogan/palomar-chair-verification at commit 5d0612a09e3b7d440be16e7b1dc511ae73035bbb.
- Snapshot archive hierarchy-c-sources.tar.gz: 4,684,110 bytes; 0275377e3a3dfb2bc757606334326b327569d8c164c234bb42d5ea9242f51446.
- Exact member SpectreFinite/ListedPatches.lean: 6,147 bytes; e99075e7bcd6513338bb3475b2fd44f6fa4a8e6537f006ba4e97f15a7e6c734d.

The original archive is an external comparison input, not duplicated in this small reproduction packet. Only the named regular-file member is read from it. No Lean module is imported, built, executed, or rewritten.

## Reproduction method

The included extract_tables.py uses only the Python standard library and treats both HTML and Lean as inert data. It verifies the pinned HTML, archive and member hashes before comparison. It does not use values parsed from Lean to choose figure labels, positions or rotations.

Figure 4.2's inline SVG ID is S4.F2.pic1. Its MathML alttext gives each capital tile name followed by six Greek edge labels. Rows are ordered Gamma, Delta, Theta, Lambda, Xi, Pi, Sigma, Phi, Psi. Edges are read west, southwest, southeast, east, northeast, northwest. The parser verifies those directions from each label's plotted position relative to the tile center. Encoding is alpha=1, beta=2, gamma=3, delta=4, epsilon=5, zeta=6, eta=0, theta=8, with the printed plus/minus sign; eta is unsigned and self-complementary.

Figure 5.1's nine inline SVG IDs are S5.F1.sf1.pic1 through S5.F1.sf9.pic1. For each colored hexagon, the parser reads the capital MathML label, the explicit center path and the label group's rotation matrix. The nearest multiple of 60 degrees gives turn in {0,...,5}, counterclockwise in the SVG's internal Cartesian coordinates, with positive y up. Matrix coefficients must differ from that rotation by less than 0.00001; the first polygon edge must independently give the same turn. No reflected child is introduced. Underlines in a label are presentation aids, not additional tile kinds.

Coordinates are relative to the unrotated Gamma child. The q axis points east and the r axis northeast. From the central hexagon's bounding box, the horizontal neighbor spacing is 51.14 and vertical row spacing is 44.2875 SVG units. For center displacement (x,y), r=y/44.2875 and q=x/51.14-r/2 are rounded to integers. SVG coordinates are rounded to 0.01 units; the maximum lattice residual is 0.0002822466836016613, below the enforced 0.001 tolerance. Each recorded center must also agree with the six polygon vertices' centroid within 0.02 units. Thus the Lean direction list is (-1,0), (0,-1), (1,-1), (1,0), (0,1), (-1,1).

Child order is the source SVG drawing order. All retained row values match the Lean list order exactly, without sorting or a set-equality relaxation. The comparison parses only the two literal table blocks with ast.literal_eval, replacing Lean tuple brackets with list brackets. Evidence files record every SVG math ID, label, coordinate and transform, so each result can be traced to retained bytes.

## Reproduced edgeWords

- Gamma: [-1, 1, -3, -4, 2, -2]
- Delta: [3, 2, -5, 1, -3, -6]
- Theta: [3, 2, 8, 2, 0, -2]
- Lambda: [3, 2, -5, 1, -8, -2]
- Xi: [-1, 5, 8, 2, 0, -2]
- Pi: [-1, 5, -5, 1, -8, -2]
- Sigma: [6, 2, -5, 1, -3, 4]
- Phi: [3, 2, -5, 5, 0, -2]
- Psi: [-1, 5, -5, 5, 0, -2]

## Reproduced childrenTable

Each tuple is (kind index, turn, q, r), with the nine kind indices in the order above.

- Gamma: (0, 0, 0, 0), (6, 1, 1, 0), (7, 2, 0, 1), (4, 1, 1, 1), (5, 4, 0, -1), (1, 5, 1, -1), (2, 0, 2, -1)
- Delta: (0, 0, 0, 0), (6, 1, 1, 0), (7, 2, 0, 1), (5, 1, 1, 1), (4, 4, 0, -1), (1, 5, 1, -1), (7, 0, 2, -1), (4, 5, 2, -2)
- Theta: (0, 0, 0, 0), (6, 1, 1, 0), (7, 2, 0, 1), (5, 1, 1, 1), (8, 4, 0, -1), (1, 5, 1, -1), (7, 0, 2, -1), (5, 5, 2, -2)
- Lambda: (0, 0, 0, 0), (6, 1, 1, 0), (7, 2, 0, 1), (5, 1, 1, 1), (8, 4, 0, -1), (1, 5, 1, -1), (7, 0, 2, -1), (4, 5, 2, -2)
- Xi: (0, 0, 0, 0), (6, 1, 1, 0), (7, 2, 0, 1), (8, 1, 1, 1), (8, 4, 0, -1), (1, 5, 1, -1), (7, 0, 2, -1), (5, 5, 2, -2)
- Pi: (0, 0, 0, 0), (6, 1, 1, 0), (7, 2, 0, 1), (8, 1, 1, 1), (8, 4, 0, -1), (1, 5, 1, -1), (7, 0, 2, -1), (4, 5, 2, -2)
- Sigma: (0, 0, 0, 0), (6, 1, 1, 0), (3, 2, 0, 1), (5, 1, 1, 1), (4, 4, 0, -1), (1, 5, 1, -1), (7, 0, 2, -1), (4, 5, 2, -2)
- Phi: (0, 0, 0, 0), (6, 1, 1, 0), (7, 2, 0, 1), (5, 1, 1, 1), (8, 4, 0, -1), (1, 5, 1, -1), (7, 0, 2, -1), (8, 5, 2, -2)
- Psi: (0, 0, 0, 0), (6, 1, 1, 0), (7, 2, 0, 1), (8, 1, 1, 1), (8, 4, 0, -1), (1, 5, 1, -1), (7, 0, 2, -1), (8, 5, 2, -2)

## Verification and historical limits

Run the new local parser as:

    python3 extract_tables.py --archive /path/to/hierarchy-c-sources.tar.gz

The expected TESTS.json has status PASS, edgeWords_exact_equality=true, childrenTable_exact_equality=true, 54 checked edge directions and 71 checked rotations and placements. Detailed outputs are evidence/extracted-tables.json and evidence/extraction-evidence.json. FILES.json hashes every frozen packet file other than itself and the packet seal.

The complete recursive tree at commit 5d0612a09e3b7d440be16e7b1dc511ae73035bbb has eight entries and no SOURCE_PROVENANCE.md. The repository history query for that exact path and pinned commit returns an empty list. The commit-list response contains 17 entries and reaches a parentless initial commit. These observations, retained in evidence/repository-history.json, are scoped to the queried repository/ref/path; they do not prove that the original document never existed elsewhere, under another name, inside a different archive, or in an uncommitted working tree.

The historical extraction record remains unavailable. This new reproduction closes the finite-table comparison gap without relabeling new evidence as historical evidence. Adopting or publishing this candidate record, and any remaining overall verification or attribution review, is outside this source-only preparation.
