# Approved license scopes

Author: Conor Grogan. The author approved these companion-paper release scopes on 6 October 2026. This package contains manuscript material, research data and software with different licenses. A record-level CC BY label for the paper does not override the software or third-party terms below.

| Files or material | License |
|---|---|
| `aperiodic_tilings_from_prime_arithmetic.pdf`, `main.tex`, `sections/*.tex` | Creative Commons Attribution 4.0 International, CC-BY-4.0 |
| Author-controlled ordinary proof prose, README, evidence ledger, explanatory notes and review summaries, including corresponding author-controlled prose within the frozen source archives | CC-BY-4.0, with the original source credits and existing third-party notices retained |
| Author-controlled figures under `figures/` (PNG, PDF and SVG) and their explanatory captions | CC-BY-4.0 |
| Author-controlled `data/*.json`, finite contact tables and certificates, generated receipts/manifests and bibliographic metadata | CC-BY-4.0; this makes no assertion of exclusive rights in mathematical facts |
| Project-owned `.lean`, `.py` and `.sh` proof, checker, replay and build sources, including project-owned software within the frozen source archives | Apache License 2.0, Apache-2.0 |
| Third-party source, external dependencies and material carrying its own copyright/license notice | The applicable existing terms and notices; no third-party rights are relicensed by this scope file |

The full Apache license is in `LICENSES/Apache-2.0.txt`. The Creative Commons notice and canonical legal-code link are in `LICENSES/CC-BY-4.0.txt`.

## Frozen archives

The two Lean archives under `evidence/lean/` are preserved byte-for-byte with their original hashes. This external scope notice applies to the author's rights in the identified project-owned code and author-controlled prose/data inside them; it does not edit, replace or suppress existing third-party terms or notices. Historical metadata inside a frozen archive may record an earlier licensing-review state. Do not infer a blanket CC BY license for all archive contents.

Lean, mathlib and other external packages retain their own licenses. Original copyright and attribution notices must be retained as applicable. This package does not claim ownership of or grant rights in third-party material beyond the author's authority.

## Excluded antecedent

The nonessential supplied copy `chair_nd.py` is not redistributed. Its SHA-256 and verified upstream provenance remain in `EXCLUDED_UPSTREAM_SOURCE.json` and `evidence/uniform_prime/source/PROVENANCE.md`. The linked upstream repository states MIT for its code, but the exact copied file's lineage was not established here. The private original and the two frozen Lean archives remain unchanged. The portable checker does not import that antecedent.
