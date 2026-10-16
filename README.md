# Cache-backed native body equality diagnostic (work-in-progress visibility retry)

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

The total is69 freshly compiled source modules,320694 bytes. The baseline65-body union is retained with one explicit source exception:
PolygonProductKeyBody adds two command-local privateInPublic scopes, one on its
existing private theorem and one on the affected documented public definition.
All original source bytes, declaration names, type/definition/proof bodies and
private keywords are preserved. All other68 sources are byte-identical. This
is an explicit reviewed exception to the earlier header-only/no-options
migration, not a claim that the baseline map already contained it. No private
keywords are removed and no private kernel names change. Helper export visibility
changes only for the two scoped commands. No global option, axiom, admission or
theorem change is added. Real elaboration may expose a migration or body equality error, which
must be corrected and reviewed rather than bypassed.

locks/owned-sources.json binds69 source hashes and all explicit import edges.
The runner rejects duplicate/aliased sources, unresolved or forward imports,
C dependencies, cached shadowing, extra source pins and changed topology.
locks/required-modules.json binds the needed2627 authenticated pinned external
sources,221 more than the successful first stage, reached from29 Mathlib roots.
The source manifest's modern-map envelope hash was already012c126e8cc9c405b859c15c98cc815f9e7e884aee3ac011127206cb349e6a86;
an older handoff's ae77ed… value was stale metadata. The map remains the
unchanged baseline provenance; the one source exception is pinned separately
in locks/visibility-exception.json and reverses exactly to the baseline hash.

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

The baseline adapter and actual 69-module output-loop controls passed independent
review. This separate source visibility variant also passed independent review
and 77 synthetic tests, including exact source-delta checks. The workflow pins
the resealed reviewed contract for its retry on verify/physical-body-20261016.
Actual research compilation and checking remain pending; no cache objects
from the failed run are reused.
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

## Exact failed-run visibility repair

Run38858268822 at commit37fe6fc9d4892c0623a8ad23c4e56e63f1be3758 passed67
fresh compile/leanchecker pairs and then failed at the private theorem reference
in polygonProductKeyBody_local_graph. It was not a timeout or memory failure.
The failure and source are preserved. BodySmoke was never attempted.

locks/visibility-exception.json pins the exact two insertions and hashes. The
helper retains its private keyword and existing kernel name, while its export
visibility changes at the scoped commands. Each option applies only to one
command; the public definition's scope begins before its doc comment.
Warnings remain enabled. Core-only controls show the two-scope pattern passes
and retains exact legacy declaration Expr tuples, while unpatched, helper-only,
def-only and subsequent unscoped-access controls fail. Those controls are not
a raw-expression audit of the actual research module; actual elaboration and
all body equality/axiom checks remain mandatory. No resources, cache boundaries,
runner admission gates, theorem statements or proof bodies change.

Current Palomar source/build rules have no ban on this supported module-porting
option. Lean's own ResolveName/AddDecl code implements visibility export, not a
kernel checking bypass. Full official Comparator and NanoDa remain required.
