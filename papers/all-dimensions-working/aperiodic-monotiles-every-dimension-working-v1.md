# Aperiodic Monotiles in Every Dimension d ≥ 2

Conor Grogan
Working manuscript v1 · 16 October 2026

Status of this version. The title names the intended all-dimension result. Its unconditional uniform theorem is still pending. This working manuscript separates accepted formal results, retained historical verification, source-level geometry, and the future publication abstract. It does not present the unfinished assembly as an accepted theorem.

### Abstract for the current working manuscript

We develop a construction and verification program for one aperiodic monotile in each Euclidean dimension d ≥ 2, with arbitrary rotations and reflections permitted. The accepted modern formal endpoints establish compactness, nonempty interior and physical tiling existence for two exact bodies in dimensions two and four. Their universal aperiodicity conclusions have one explicit parent-occurrence premise C. Separately retained formal verification establishes unconditional physical monotile existence in dimension three and every dimension at least five, using a repeatable keyed-product compiler. The remaining work is to complete C, verify the modern higher-dimensional port, and accept the uniform assembly and independent physical statement. The four-dimensional construction uses 56 pyramidal keys. A source-level geometric and exact-arithmetic review counts 362 connected flat three-dimensional boundary patches; its body-level polyhedrality and count have not yet been established by completed Lean theorems. The completed five-dimensional CLARK registration and the written computer-assisted seven-dimensional HENRY proof are distinguished from the dense seeds used in the product closure.

### Introduction and attribution

A physical aperiodic monotile is a single compact tile shape that admits a tiling and whose every tiling has no nonzero translation period. The tile shape may depend on the ambient dimension. Existence of one aperiodic tiling alone is insufficient: a monotile must also exclude periodic tilings under the allowed placements.

Scherlis previously formulated an all-dimensional keyed-product construction, including the four-dimensional keyed product [1]. The present working manuscript develops explicit geometric specifications and records the formal verification actually achieved for the constructions and interfaces stated here. We claim no priority for the general keyed-product idea, the four-dimensional idea, the 56-key count, or the all-dimension formulation. The prior note itself qualifies the review status of parts of its adapted geometric argument; attribution to that formulation does not certify those arguments.

## 1  Physical statements and the remaining premise

Let E_d be d-dimensional Euclidean space. A tile is a set T ⊆ E_d. A physical tiling is a set of tile sets, denoted 𝒯, such that each member is the image of T under a Euclidean isometry, the members cover E_d, and distinct members have disjoint interiors. Boundary intersections are allowed. No registration, orientation choice, matching label or hierarchy is part of this definition.

A translation vector v is a period of 𝒯 if A ∈ 𝒯 is equivalent to A + v ∈ 𝒯 for every set A. This tests the entire tile collection. Testing its union would be vacuous because the union of a complete tiling is all of E_d.

```text
SparseMonotiles.IsAperiodicMonotile T :=
  IsCompact T ∧ HasTiling T ∧ IsAperiodic T
```

Here HasTiling T asserts the existence of a physical tiling, and IsAperiodic T asserts that every period of every physical tiling is zero. Nonempty interior is stated separately in each selected endpoint. The isometries are unrestricted; reflections are included. The statements select neither homochirality nor a bound on the full Euclidean symmetry group.

### Definition of C

The one remaining premise of the two accepted native endpoints is the following precise proposition in the recovered finite hierarchy model. The names Position, State, GloballyLegal, OccurrenceComplete, hexRegion and certifiedParentFamily retain their source definitions.

```text
def ParentOccurrenceTheorem : Prop :=
  ∀ f : Position → State, GloballyLegal f →
    OccurrenceComplete f (hexRegion 5) certifiedParentFamily
```

Its namespace is SpectreFinite.HexSearch.NativeHierarchy. Thus C concerns certified parent occurrences for every globally legal state field on the radius-five hexagonal region. The accepted conditional proof does not assume compactness or tiling existence through C. C is an explicit theorem parameter, and its complete proof and integration remain unfinished.

### Intended all-dimension statement

For every natural number d ≥ 2, there exists T ⊆ E_d such that T is compact, has nonempty interior, admits a physical tiling, and every physical tiling by T has only the zero translation period. This is the independent uniform contract selected for future completion. It is currently a pending target, not a completed theorem of this manuscript.

The quantifier order is “for each dimension, there exists a shape.” It does not select one fixed shape across ambient dimensions, nor polyhedrality in every dimension, a topological ball, uniqueness of a tiling, or triviality or finiteness of all tiling symmetries.

## 2  Accepted native results in dimensions two and four

### Theorem 1  Exact two-dimensional body conditional on C

For the exact body T₂ = LiteralPlanar.FanBounds.curvedBody, the following declaration has passed the accepted modern source, kernel and raw endpoint audits. Its sole explicit premise is C.

```text
theorem NativeFinalAssembly.curved_monotile_of_parent
    (C : SpectreFinite.HexSearch.NativeHierarchy.ParentOccurrenceTheorem) :
    (interior LiteralPlanar.FanBounds.curvedBody).Nonempty ∧
    SparseMonotiles.IsAperiodicMonotile
      LiteralPlanar.FanBounds.curvedBody
```

The compactness, nonempty interior and unmarked tiling assertion are separately C-free. The exact declaration NativeIndexedExistence.curved_geometry_and_unmarked_tiling returns those three conclusions. The final proof combines that declaration with the C-dependent indexed period-rigidity theorem and the indexed-to-unmarked bridge.

### Theorem 2  Exact four-dimensional body conditional on C

For T₄ = SpectreGeometry.polygonProductKeyBody, the corresponding accepted declaration is:

```text
theorem NativeFinalAssembly.keyed_product_monotile_of_parent
    (C : SpectreFinite.HexSearch.NativeHierarchy.ParentOccurrenceTheorem) :
    (interior SpectreGeometry.polygonProductKeyBody).Nonempty ∧
    SparseMonotiles.IsAperiodicMonotile
      SpectreGeometry.polygonProductKeyBody
```

Compactness and nonempty interior are provided by the exact-body geometry. KernelSeedPilot.existing_physical_product_tiling supplies an indexed physical tiling without C; the unmarked bridge supplies HasTiling. Only the universal period-rigidity step in this endpoint uses C. This separation prevents the aperiodicity conclusion from being made vacuous by missing tiling existence.

### What has actually been accepted

The terminal accepted run is 38952557899 at commit 62da52d4a30561fa933b8ecd0a95f80e7aedbbe1 [4]. The independent final review reconciles 2,481 source/checker lineages and both raw endpoint audits. Each endpoint has exactly one explicit C argument, an empty universe-parameter list, and only propext, Classical.choice and Quot.sound among its transitive axioms. C is not a custom axiom; it remains a hypothesis of the result.

The accepted lineage is cache-backed and joins independently reviewed producer stages. It is not a claim that all 2,481 modules or all external sources were freshly rebuilt in a single run. Stale “source-only” comments in earlier source snapshots are superseded only for these exact accepted endpoints by the terminal evidence. They do not upgrade the separate uniform assembly.

## 3  The exact geometric bodies

### The planar body

The planar endpoint selects the literal body defined by LiteralPlanar.FanBounds.curvedBody = euclideanCoordinates '' Candidate.body. The candidate is the finite union of its specified polynomial fan images. The formal image identification relates the modified fan construction to the original polygonal carrier; this paper does not substitute an arbitrary planar aperiodic shape for that exact set.

### The four-dimensional body

The four-dimensional endpoint uses the literal finite replacement of the polygon product P × P. In source notation, its definition is:

```text
def polygonProductKeyBody : Set EFour :=
  replaceTubes polygonProductBody
    productKeyCollar productKeyHypograph
```

The key-site type is Fin 2 × Fin 14 × Bool. It records the active product factor, one of fourteen indexed polygon edges, and a polarity. Its cardinality is 56. The two active positions on each indexed edge are its quarter and three-quarter points; the passive factor is centered at (1/2, 1/2). The tangent frame consists of the signed active edge and the two positive passive coordinate axes. The normal is the outward edge normal and does not acquire the polarity sign.

The numerical constants are η = ρ = 1/40000 and N = 4357, with prime pairs (3,5), (7,11), (13,17). In local orthonormal tangent coordinates u = (u₀,u₁,u₂) and outward normal coordinate z, the modified boundary is z = h(u), where

```text
h(u) = (η ℓ / N) max(0, min {L_j⁻(u), L_j⁺(u) : j = 0,1,2})
L_j⁻(u) = 1 + p_j⁻ u_j / η
L_j⁺(u) = 1 - p_j⁺ u_j / η
ℓ = τ (b + 1),   b ∈ {0,1},   τ ∈ {+1,-1}
```

The footprint is the rectangular box with coordinate bounds −η/p_j⁻ ≤ u_j ≤ η/p_j⁺. Inside each collar, material lies on the side z ≤ h(u); before modification it lies on z ≤ 0. The literal replacement keeps the prescribed carrier outside the collars and uses these signed hypographs within them. Both positive and negative polarities are included in the 56-key count.

The accepted tiling statement is attached to this exact replacement set. It does not by itself establish a body-level finite-polytope decomposition or the intrinsic boundary-patch count. Those conclusions require their own geometric arguments and formal bindings.

### Why the flat-face claim remains separate

The source-level max-min formula has finitely many affine branches. The unfinished polyhedral addendum must still discharge the reverse-clipping implication, the collar/interior and finite-hull bindings, and the final exact-body instantiation. Piecewise-linear formulas alone are not reported here as a completed Lean proof of those body-level obligations.

## 4  Boundary patches of the four-dimensional construction

Source-level geometric claim, independently reviewed with exact arithmetic. The literal 56-key body has 362 maximal connected flat three-dimensional boundary patches under the convention below. This is not currently a Lean-checked body-level count theorem.

### Counting convention

A patch is the closure of one connected component of the regular planar boundary locus: the boundary points having an ambient neighborhood in which the boundary equals an open part of one affine three-plane. Disconnected coplanar patches count separately. This convention does not count two-dimensional ridges or cells introduced by an arbitrary convex subdivision.

### Carrier contribution

The planar source has fourteen indexed unit edges. Edges 9 and 10 meet at the sole straight vertex, so their union is one maximal straight edge. There are thirteen maximal carrier edges. The two product factors therefore contribute 2 × 13 = 26 carrier regions. Each region is connected before removing key footprints. Every footprint is a strictly smaller closed rectangular box inside its own collar, and the closed collars are disjoint. Paths in each three-dimensional carrier region can be detoured through the larger collar around each removed box. The regular carrier region consequently remains connected.

### Pyramidal contribution

Each nonzero key amplitude gives six genuine three-dimensional side pieces, one for each affine branch. A strict branch witness places one tangent coordinate at −η/(2p_j⁻) or η/(2p_j⁺), with the other coordinates zero. The selected branch equals 1/2 and the other five exceed it. The local frontier identities identify these graph pieces with the actual body boundary for both bumps and dents. The old carrier plane over the interior of a key mouth contributes no extra three-dimensional boundary piece.

```text
26 carrier patches + 56 × 6 pyramidal side patches = 362 patches
```

The modification is strictly inside each collar. Collar compatibility and agreement with the raw carrier outside the graph windows exclude additional collar walls, caps or artificial seams. Different side pieces within a key meet along lower-dimensional nonflat creases. Distinct keys have disjoint collars, so their side patches do not join.

### Why the number of planes is smaller

Exact normalization of the plane equations over ℚ(√3) yields 26 distinct carrier planes and 320 distinct side planes, with no overlap between these classes. Sixteen pairs of side patches are coplanar but disconnected. Hence the 362 patches lie in 346 distinct containing affine hyperplanes. “Containing” does not assert global support for this nonconvex body.

The carrier patches are punctured and generally nonconvex. The word “facets” would require this explicit convention. The preferred descriptive copy is “362 connected flat three-dimensional boundary pieces,” with the maximal-connected-patch definition supplied here. The exact arithmetic and geometric review are evidence for this source-level claim; the separate finite-hull/regular-closure formalization remains pending.

## 5  The repeatable keyed-product construction

The retained higher-dimensional formalization uses concrete finite compiler data. CompilerData m describes a nonempty finite carrier in actual dimension m + 1 ≥ 3 and a finite proper generator language. HasWorld and PeriodFree are separate propositions proved from those data. They are not hidden assumptions that the product already has a physical aperiodic tiling.

### Existence and universal aperiodicity

CompilerData.prod constructs the product carrier and the union of the two lifted generator languages, then rebuilds the boundary keys through the compiler. CompilerData.prod_hasWorld constructs an actual complete full-profile product world from factor worlds. CompilerData.prod_periodFree recovers the factor contact languages from every legal product world and projects any period to factor periods. Both projected periods vanish, forcing the product period to vanish.

The generic physical registration theorem CompilerData.physical_monotile then turns HasWorld and PeriodFree into a compact Euclidean body with nonempty interior, a physical tiling and universal physical aperiodicity. The theorem starts with arbitrary Euclidean placements. Its internal registration is a proved reduction, not an assumption imposed on the user-facing tilings.

### Theorem 3  Addition of certified dimensions

```text
theorem ProductClosure.CertifiedDimension.add {d e : ℕ}
    (hd : CertifiedDimension d) (he : CertifiedDimension e) :
    CertifiedDimension (d + e)
```

Here CertifiedDimension d means that there are finite compiler data D in dimension d together with proofs of D.HasWorld and D.PeriodFree. The certified output is eligible for the same operation again. This is the repeatable dimension-raising rule. No claim is made that the ordinary Cartesian product of arbitrary aperiodic tile shapes automatically has the required property.

### Theorem 4  Retained unconditional higher-dimensional range

```text
theorem ClarkSeed.exists_physical_aperiodic_monotile_of_ge_three_ne_four
    (d : ℕ) (hd : 3 ≤ d) (hne : d ≠ 4) :
    ∃ T : Set (EuclideanSpace ℝ (Fin d)),
      (interior T).Nonempty ∧ SparseMonotiles.IsAperiodicMonotile T
```

The three-dimensional seed comes from the prime family. For the range d ≥ 5, the seeds are dimension 5, dimension 6 = 3 + 3, and dimension 7. Strong induction adds the certified three-dimensional compiler to dimension d − 3 for d ≥ 8. Thus the retained theorem covers exactly dimension three and every dimension at least five, independently of C.

Its complete imported-closure kernel receipt was completed on 13 October 2026; the 980 pinned source entries and the indexed receipts have been rehashed. This is retained verification of the exact historical sources. The proposed modern port and new uniform assembly have not thereby been freshly accepted.

## 6  Uniform assembly and the exact remaining work

### Pending conditional uniform statement

The source-only module NativeFinalAssembly.AllDimensionsOfParent combines the accepted native two- and four-dimensional endpoints with the higher-dimensional theorem. Its case split is d = 2, d = 4, and d ≥ 3 with d ≠ 4. It keeps the same single C premise. This assembly has not yet been elaborated or accepted.

```text
Pending target, with C explicit:
∀ (C : SpectreFinite.HexSearch.NativeHierarchy.ParentOccurrenceTheorem)
  (d : ℕ), 2 ≤ d → ∃ T : Set (EuclideanSpace ℝ (Fin d)),
  IsCompact T ∧ (interior T).Nonempty ∧ HasTiling T ∧ IsAperiodic T
```

The source proposal also expands HasTiling and IsAperiodic into ordinary sets, unrestricted isometries, coverage, pairwise interior-disjointness and tile-collection periods. The independent Palomar challenge uses only those physical definitions. Its selected theorem is PalomarAllDimensions.aperiodic_monotile_in_every_dimension. The challenge hole is intentional; it is not a proof artifact.

### Pending unconditional uniform statement

The proposed NativeFinalAssembly.AllDimensions endpoint applies the intended certifiedParentOccurrenceTheorem to the conditional uniform result. The source spelling of that theorem is not evidence that its complete modern proof closure has passed. The unconditional statement therefore remains pending, as does the independent solution and official comparison/preflight workflow.

### Completion gates

- Complete and independently accept the exact C proof and its source, imported-interface, raw-type and axiom lineage.

- Compile and kernel-check the modern higher-dimensional port and its extended external interface. The 1,138 additional research modules and 247 additive visibility migrations have a static source review, not modern proof acceptance.

- Compile and audit the conditional uniform assembly, including the single explicit C binder and the expanded physical predicate. Then accept the unconditional assembly without hierarchy, geometry or existence premises.

- Compile the independent Challenge and Solution in isolated contexts, compare the selected statement and definitions, and complete the pinned official Comparator and Palomar preflight for the new uniform entry.

- Complete the exact-body four-dimensional polyhedral proof before presenting that part of the publication abstract as achieved. A formally verified count additionally needs an exact-body count theorem. The minimal all-dimension contract does not select either claim.

The static plan counts 3,620 research modules for the conditional uniform union and 9,655 for the unconditional union, before Challenge/Solution and audit helpers. These are source dependency counts, not completed checks or a completion-time estimate. No new official all-dimension registration is claimed.

## 7  Verification provenance and prior results

### The accepted conditional lineage

The accepted 16 October endpoint record binds both exact bodies and their one-premise statements to source commit 62da52d4a30561fa933b8ecd0a95f80e7aedbbe1 and run 38952557899 [4]. Its independent terminal review has SHA-256 ebf3550dd9d5639e6140478e0179dc08533cf450469f73671bb14f659d06e0d2. The review authenticates the accepted stages, exported companion bytes and raw endpoint/bridge audits. The C-free construction and existence statements must be distinguished from the C-dependent period conclusions.

### The retained higher-dimensional lineage

The final historical ClarkSeed.PhysicalDimensions imported closure passed an independent fresh-environment kernel check at 18:42:59 UTC on 13 October 2026, with exit status zero. Its receipt SHA-256 is b7e169fb023764fcc2a563b709d9c59daa7d065636bc7ebbba643f8608c599c5. Rehashing authenticates the retained files; it does not rerun Lean, admit old compiled objects into the new pipeline, or establish a successful modern port.

### CLARK and HENRY

The exact sparse five-dimensional CLARK tile has a completed Lean formalization and official Palomar registration dated 7 October 2026 [2]. The selected registered theorem is PalomarMonotiles.T5_strongAperiodicity at commit 5f5ceedee770b76c21e8f1105e5e4e3b84b8d676. This is a prior completed result with its own selected body and statement, not a registration of the new all-dimension theorem.

The pinned CLARK/HENRY manuscript gives a written computer-assisted proof and exact finite M7 computation for the sparse seven-dimensional HENRY body [3]. Section 7 and the appendix status table explicitly leave its complete Lean verification unfinished. HENRY is consequently described here as supported by a written computer-assisted proof; it is not called Lean-verified or Palomar-registered.

### Dense seed identities

The higher-dimensional closure uses a newly compiled dense five-dimensional body derived from the recovered CLARK contact and hierarchy certificates. Its binding record expressly does not identify this dense body with the original sparse CLARK body. Its seven-dimensional seed is ProductClosure.seven_certified from the proved prime-3-modulo-4 compiler family. No identity with the separate sparse HENRY T7 body is selected. These distinctions are essential to the exact claim-to-source mapping.

### Scope of this editorial update

No Lean proof was executed for this manuscript revision. The accepted statuses above are read from the pinned retained evidence. The uniform source plan has passed a narrow independent static source review with SHA-256 6c782e005ff7adcdf43f607e33ecb2266068645439e707be13f3c7a071565c26; that review explicitly excludes elaboration, kernel, Comparator and Palomar execution. The accompanying claim map records the declarations and remaining gates for every principal claim.

## Appendix A  Reserved publication abstract

Publication draft only. Use this abstract as a statement of achieved results only after the unconditional all-dimension proof, independent verification and stated four-dimensional geometry gates are complete. The current working abstract is on page 1. The following paragraph preserves the selected copy and its two source links.

For each Euclidean dimension d ≥ 2, we construct a tile shape whose copies fill space without gaps or overlaps, yet no such tiling repeats by translation. The shape varies with the dimension; only one tile type is needed in each case, and rotations and reflections are allowed. Our construction combines lower-dimensional examples and rebuilds their boundary keys, forcing every tiling to preserve the underlying aperiodic structure. This repeatable rule adds dimensions while preserving both tiling existence and aperiodicity. Together with the base constructions, it covers every dimension from two upward. A distinguishing feature is a four-dimensional polyhedral tile with 362 connected flat three-dimensional boundary pieces and 56 pyramid-shaped keys. We provide explicit geometric specifications and formal proofs. The work builds on [CLARK in five dimensions, previously formalized in Lean and registered with Palomar](https://palomar-registry.org/entry?id=PALOMAR-2026-10-07-000006&version=1), and [HENRY in seven dimensions, described by a written computer-assisted proof whose complete Lean verification remains unfinished](https://github.com/jconorgrogan/palomar-chair-verification/blob/46c05aaea9e4d1ee51acac23ec2d048b49d0da0e/CLARK_paper.pdf).

### References

[1] Adam Scherlis. Monotiles in every dimension. Pinned primary note, repository revision e05cee7245124a705ca68be3a8f641d290c664b4, modified 24 September 2026. [Scherlis keyed-product note](https://github.com/AdamScherlis/adamscherlis.github.io/blob/e05cee7245124a705ca68be3a8f641d290c664b4/static/monotiles-every-dimension/index.html).

[2] Palomar Registry. CLARK entry PALOMAR-2026-10-07-000006, version 1. Registered 7 October 2026. [CLARK registration](https://palomar-registry.org/entry?id=PALOMAR-2026-10-07-000006&version=1); [CLARK official record](https://data.palomar-registry.org/entries/PALOMAR-2026-10-07-000006-v1.json).

[3] Conor Grogan. An Arithmetic Family of Aperiodic Tilings in Odd Prime Dimensions. Pinned CLARK/HENRY manuscript at revision 46c05aaea9e4d1ee51acac23ec2d048b49d0da0e. HENRY status: Section 7, printed page 17, and appendix status table, printed page 34. [CLARK and HENRY manuscript](https://github.com/jconorgrogan/palomar-chair-verification/blob/46c05aaea9e4d1ee51acac23ec2d048b49d0da0e/CLARK_paper.pdf).

[4] Conditional native two- and four-dimensional verification. Accepted source revision 62da52d4a30561fa933b8ecd0a95f80e7aedbbe1; terminal run 38952557899. [Accepted conditional verification run](https://github.com/jconorgrogan/palomar-chair-verification/actions/runs/38952557899); [Accepted conditional source commit](https://github.com/jconorgrogan/palomar-chair-verification/commit/62da52d4a30561fa933b8ecd0a95f80e7aedbbe1).
