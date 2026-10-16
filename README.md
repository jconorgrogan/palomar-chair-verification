# Cache-backed physical interface diagnostic (work in progress)

This small diagnostic freshly elaborates four exact modern Lean sources against the official Mathlib cache at commit `065356127b1dc0016f66b7283ce0ce2c4055aa55`, with Lean `4.35.0-rc2`. It does not certify either monotile theorem. The two standalone Challenge files intentionally contain their statement holes; the separate model-bridge smoke only proves two definition equalities.

## Trust and provenance

The official [Palomar verification profile](https://github.com/PalomarRegistry/PalomarSubmission/blob/d4e41c1d5b0d114c4859e6e5831dc6d3ad1d0d44/verification-profile.json) permits fresh submitted Lake state with pinned Mathlib cache artifacts. Its [cache trust note](https://github.com/PalomarRegistry/PalomarSubmission/blob/d4e41c1d5b0d114c4859e6e5831dc6d3ad1d0d44/docs/mathlib-cache-trust.md) explicitly trusts the served compiled bytes. Source-derived cache keys identify requests; they do not authenticate the returned bytes as semantically equivalent to source. Our SHA-256 inventory records the bytes consumed, not a stronger source-equivalence guarantee. The user's separately requested fresh external-source replay remains pending.

Every official dependency is checked out at a full locked commit with canonical origin. The selected Mathlib manifest and cache-client source hashes are checked. The cache executable is freshly bootstrapped with networking disabled and copied to a read-only location. Its pinned current client uses only the official `master,legacy` trust chain. No fork scope, unsafe history search, endpoint override, credential, old Lake object or existing cache is admitted. The network-enabled phase cannot read candidate source files. All diagnostic elaboration/checking is network-disabled with dependencies mounted read-only, unique namespace providers, complete selected cached module/IR companion coverage, and source/output hash checks.

The official Lean release archive is SHA-256 pinned, and its canonical 17,918-file/13-symlink inventory is verified. The four source files are preserved exactly from the reviewed drafts/owned source; `contract.json` binds all inputs. Actual cached archives, builds, generated IR, and available JS assets are inventoried. These inventories identify the official-cache trust boundary, not a fresh build of Mathlib or ProofWidgets.

## Resource and execution limits

One standard public Ubuntu 22.04 job, 90-minute outer bound, 80-minute aggregate command deadline. Cache bootstrap: 15 minutes; acquisition: 30 minutes; each small Lean compile/check: 120 seconds, `-j1 -M4096`, 8 GiB sampled process-tree RSS, 12 GiB per-process address-space ceiling. Acquisition/bootstrap use at most 8 GiB sampled tree RSS. No paid runner, billing change or security-policy change is used. Failure, missing cache, namespace conflict, unsupported modern interface, timeout or disk exhaustion is incomplete diagnostic evidence, never proof acceptance.

After runtime setup, acquisition requires at least 9 GiB (3 GiB downloaded archives + 5 GiB admitted builds + 1 GiB overhead) measured free disk. Downloads and builds have per-file and post-phase aggregate inventory limits; the aggregate limits reject oversized results but are not filesystem quotas or a guarantee that those bytes cannot first consume disk during the bounded phase. Runner disk exhaustion fails closed. The local cloud `/tmp` filesystem is insufficient, so the intended execution is the reviewed GitHub runner. Preserved local proof snapshots are not deleted.

Only bounded logs, source/cache/runtime inventories, fresh diagnostic object hashes and status receipts are uploaded, for seven days. Cache objects are not uploaded or reused across jobs. Workflow and contract remain inactive until independent review. Passing this diagnostic establishes only that these exact sources elaborate and replay under this declared cache trust; it does not close C, a physical monotile proof, clean-source reproducibility, Comparator or independent-kernel certification.

Owned diagnostic sources and adapter are under the repository's Apache-2.0 license. Official dependencies retain their own licenses and notices; they are fetched from their official repositories rather than republished here.

The first authenticated-cache attempt hit Lean's internal 1 GiB heap limit while loading the real modern model (6.41 seconds, 1.44 GB sampled RSS). This four-source retry raises only the internal heap and diagnostic RSS bounds; the original failed run and exact source bytes are preserved.
