# C087 exact-source diagnostic

This branch is a bounded diagnostic for `SpectreFinite.RadiusFivePruningCertified`. It authenticates and restores the exact 85 predecessor stages (6,218 modules), then compiles, kernel-checks and raw-audits the unchanged source with the single additional option `-DElab.async=false`. This run performs no default target attempt; the earlier default-abort evidence remains in its own historical run. It is not a completed hierarchy proof or a Palomar submission.

The workflow checks out four exact trees, installs the original official Ubuntu dependencies, and runs one fixed controller. The controller downloads and verifies the pinned official Lean release under the same original 19,800-second budget. The job limit is 350 minutes. The parent uses one CPU and an 8 GiB address-space limit; the unchanged native supervisor separately enforces the original 8 GiB sampled target-tree RSS and per-command limits. Linux RLIMIT_RSS is not a parent RSS enforcement claim.

Artifact transport authenticates the three terminal producer contexts in fresh start/end batches. Individual artifact metadata, digests, sizes and expiration checks remain mandatory. The complete 48-stage historical raw ledger remains charged against the 4 GiB archive cap, including the one historical stage not restored here. Actual latest raw sizes and filesystem capacity remain execution gates.

Only bounded diagnostic evidence is uploaded, with a 256 MiB local selection cap. Predecessor object archives and extracted objects are excluded. A failed or interrupted producer, a missing completion document, or a nonempty artifact alone cannot establish diagnostic success. Acceptance requires the terminal job and upload records, exact source identities, complete evidence bytes and every native admission and async-off result to reconcile.

The workflow uses the existing trusted fixed-source CI model and original native boundaries. It does not claim a complete physical-write proof, a newly approved sandbox security profile, or that the previously observed system bubblewrap version contains the upstream security fix. The fixed trusted setup trees and no-other-writer assumption remain explicit.

The separate review packets contain the source and inert integration tests; this runtime distribution does not include those test harnesses. Actual diagnostic results must be read from the specific completed run rather than inferred from preparation tests.
