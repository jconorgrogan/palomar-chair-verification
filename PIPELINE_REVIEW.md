# Reviewed clean verification pipeline

The implementation and bounded synthetic tests have passed review. Live preparation must still verify the official archive, same-run artifact transport and runner sandbox support. No project proof result is claimed by publishing this pipeline.

The fixed source commit is c8e274d7833c9e2e1ede5aa61fc042fba8035715. The eventual pipeline commit is separately taken from GitHub's trusted push event. All source files, artifact receipts, toolchain inventory, command profiles and checker code are bound to these identities.

The pipeline uses only standard public ubuntu-24.04 runners, up to four concurrent jobs. It installs bubblewrap and zstd from official Ubuntu package repositories. It does not alter host security settings; sandbox failure is a failed preparation. Each job downloads the SHA-256-pinned official Lean release and derives the same canonical relative inventory from that archive. No prior project object cache is used.

There are 93 grouped compile/check stages in 25 dependency waves, followed by six final jobs. Individual stage execution is limited to 330 minutes inside a 350-minute GitHub job; final fresh replay is limited to 18,000 seconds. These are failure ceilings, not completion estimates. A run older than six days cannot produce accepted evidence. Artifacts contain only new outputs and expire after seven days. Expiry, a timeout, missing evidence or any checker rejection means incomplete or failed, never accepted.

Failures and cancellations get a separate best-effort diagnostic artifact, limited to sixteen 256-KiB log tails and small sanitized command summaries. It is explicitly incomplete and cannot be consumed as successful evidence. VM shutdown may prevent this diagnostic upload.

Artifacts are fetched using the job's ephemeral GitHub token with contents:read and actions:read. Authentication is never forwarded to redirected artifact storage. Same-run/attempt successful producer jobs, GitHub ZIP digests, archive manifests, every file hash, dependency closure and source hashes are checked explicitly. No spending, billing, access-grant, larger-runner or self-hosted-runner setting is changed. Public standard Actions usage is covered by GitHub's public-repository exception; this is not an account-specific billing guarantee.

Final gates require the exact exported theorem and expanded parent-occurrence proposition, standard axioms only, full imported-closure fresh Lean replay, export replay and Lake's axiom audit, NanoDa, and con-ron in verified mode. Final evidence binds the defining module's source hash and all restored object hashes. The resulting scope is finite hierarchy C only; downstream unconditional 2D/4D statements and Palomar acceptance remain separate.
