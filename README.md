# Cache-backed native body equality diagnostic (work in progress)

This extends the successful four-source diagnostic at commit
749d0aea89efd63eda76d58524d9fd1575fcbdcf, run38855692931. It is a bounded
real-source test of two explicit-body equality bridges. It does not prove either
aperiodic-monotile Challenge and does not use hierarchy C.

## Exact source scope and order

1. Rebuild/check the same real Model, two independent Challenges and two model
   equality proofs from the earlier successful run.
2. Rebuild/check the remaining64 native body-dependency sources, in locked
   topological order. Together with Model these are the exact65-source union.
3. Compile/check ContractBodyBridgeSmoke, then require the exact fully qualified
   two body equality axiom reports, containing only propext, Classical.choice,
   Quot.sound (a subset is allowed). Both Challenge sorries are intentional;
   sorryAx in either body/model proof audit fails this diagnostic.

The total is69 freshly compiled source modules,320606 bytes. All65 body union
sources match the frozen migration map byte-for-byte. The migration changes
module/public import/expose headers only; proof and definition bodies are
unchanged. Explicit private helpers remain private. No compatibility option,
private-to-public promotion, semantic rewrite, axiom or proof admission was
added. Real elaboration may expose a migration or body equality error, which
must be corrected and reviewed rather than bypassed.

locks/owned-sources.json binds69 source hashes and all explicit import edges.
The runner rejects duplicate/aliased sources, unresolved or forward imports,
C dependencies, cached shadowing, extra source pins and changed topology.
locks/required-modules.json binds the needed2627 authenticated pinned external
sources,221 more than the successful first stage, reached from29 Mathlib roots.
The source manifest's modern-map envelope hash was already012c126e8cc9c405b859c15c98cc815f9e7e884aee3ac011127206cb349e6a86;
an older handoff's ae77ed… value was stale metadata. All65 source hashes are
unchanged against the independent earlier readback. Both source identities are
recorded in derivation evidence outside this publication candidate.

## Trust and resource limits

The official Lean v4.35.0-rc2 release archive and17918-file inventory pins,
all9 public upstream repository commit pins, cache-client source pin, source
Git-blob verification, sandbox boundaries and cache admission are inherited
unchanged from the successful diagnostic. Mathlib cache bytes are explicitly
trusted under the inspected Palomar policy; they are not certified equivalent
to a fresh external-source build. The candidate sources are absent from the
network-enabled cache acquisition sandbox; compiler/checker runs have no network.
Fresh owned outputs and all required modern private/server/IR companions are
inventoried, prior outputs are rehashed before/after use, dependency/source
snapshots remain immutable, and namespace-provider collisions fail closed.

Unchanged limits: one compilation/check command at a time, lean -j1 -M4096,
8GiB sampled process-tree RSS,12GiB virtual address space,120seconds per owned
compile/check,80minutes aggregate command deadline and90minutes outer job.
The fresh owned-output inventory remains capped at64MiB. Cache files stay on
the ephemeral runner. Only bounded inventories and logs are uploaded, capped
at31MiB; incomplete evidence is explicitly marked. This is not the official
Palomar standard-profile full preflight and is not a full source replay.

## Activation and result

The source, cache admission, resource limits, and actual 69-module output-loop
controls have passed independent review and 74 synthetic tests. This bounded
attempt uses the separate verify/physical-body-20261016 branch, with the exact
reviewed contract SHA pinned by its workflow. Existing verification branches
and the successful original diagnostic remain unchanged. Live compilation and
checking of these body sources is still required; review alone is not proof.

A complete result is CACHE_BACKED_BODY_EQUALITY_DIAGNOSTIC_COMPLETED, with all138
owned compile/check commands successful and explicit standard-only axiom
reports for both model and body pairs. proof_certified and
final_monotile_proof_certified remain false: Challenge theorem holes are still
unfilled, and no final consumer, Comparator, NanoDa or Palomar submission has
been checked here. Any failure retains its logs and must remain a failure.

## Expanded output-loop guard controls

The prior loop checked exact output paths only after compilation and checked
namespace providers only before compilation. A last checker could consequently
add an unexpected file or an empty namespace-shadowing directory without a
following iteration to catch it. The extension now revalidates namespaces after
compiler and checker, and exact output-path equality after every checker.
These are stricter admission checks; source proofs and resource caps did not
change. Non-Lean controls extract the actual production loop AST and run its
full69-module sequence against synthetic command outputs. They cover all seven
missing companions, final compiler/checker extra files, empty-prefix shadowing
in both phases, a later-owned cached namespace collision, checker-phase prior
mutation/removal/current mutation, and escaping symlinks. These synthetic files
are never passed off as Lean proof objects or published as source inputs.
