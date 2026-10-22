# Aperiodic Monotiles in Every Dimension

Finite full symmetry in every dimension above two

Conor Grogan
22 October 2026 revision of the all-dimensional working manuscript

### Abstract

We describe a construction of a physical aperiodic monotile in every integer dimension d ≥ 2. For each dimension, one compact shape with nonempty interior admits a tiling, but no tiling by its isometric copies has a nonzero translational period; rotations and reflections are allowed. In particular, the exact four-dimensional keyed-product body JACKIE is a separate branch, not an instance of the odd-prime chair family. A repeatable keyed-product compiler combines certified finite carriers and rebuilds their boundary keys, preserving both tiling existence and universal aperiodicity. Together with exact planar and four-dimensional bodies, it covers every dimension from two upward. The selected all-dimensional Lean proof compiles, with the former parent-occurrence premise supplied by a theorem inside the development. Its official full preflight completed the Solution build and both proof exports, but exhausted its time budget before a completed final comparison, external-kernel check and endpoint axiom audit; all-dimensional Palomar registration remains pending.

We also give an ordinary mathematical deduction from the inspected source lemmas that every admitted tiling by the constructed witnesses in dimensions d > 2 has a finite full Euclidean symmetry group. For the compiler witnesses in d = 3 and d ≥ 5, its order is at most 2^d d!. The four-dimensional body, called JACKIE, requires a separate planar-factor argument; no numerical bound is claimed for that branch. These stronger all-dimensional symmetry deductions are not new Lean-checked endpoints. JACKIE uses 56 pyramidal keys. The retained geometric and exact-arithmetic account counts 362 connected flat three-dimensional boundary patches, but neither exact-body polyhedrality nor this count is reported as a completed Lean theorem. The previously registered sparse five-dimensional CLARK body is kept distinct from the dense compiler witnesses and from the written computer-assisted seven-dimensional HENRY result.

### Introduction and attribution

A physical aperiodic monotile is a single compact tile shape that admits a tiling and whose every tiling has no nonzero translation period. The tile shape may depend on the ambient dimension. Existence of one aperiodic tiling alone is insufficient: a monotile must also exclude periodic tilings under the allowed placements.

Scherlis previously formulated an all-dimensional keyed-product construction, including the four-dimensional keyed product [1]. The present manuscript develops explicit geometric specifications and records the formal verification actually achieved for the constructions and interfaces stated here. We claim no priority for the general keyed-product idea, the four-dimensional idea, the 56-key count, or the all-dimension formulation. The prior note itself qualifies the review status of parts of its adapted geometric argument; attribution to that formulation does not certify those arguments.

This revision consolidates the construction, the compiled all-dimensional translation-aperiodicity theorem, and the finite-symmetry extension. It distinguishes a mathematical deduction from an implemented Lean theorem, a successful build from completed independent verification, and the selected all-dimensional bodies from earlier named examples. The proof architecture is given in Sections 2–6, the full finite-symmetry argument in Section 7, and the exact verification record in Section 8.

### Dimension map

- Dimension 2: the exact curved planar body, LiteralPlanar.FanBounds.curvedBody, supplies the planar branch of the compiled translation-aperiodicity theorem. No finite-full-symmetry extension is claimed here for this curved witness.
- Dimension 3: a certified prime-family compiler body has universal translation aperiodicity and, by the new ordinary deduction, finite full symmetry with the bound 2^3 3! = 48.
- Dimension 4: JACKIE, the exact body SpectreGeometry.polygonProductKeyBody, supplies the compiled four-dimensional aperiodic-monotile branch. Its finite-symmetry proof uses two recovered planar polygon factors; no numerical bound is claimed. This branch does not rely on four being prime.
- Dimension 5: the all-dimensional assembly uses a dense compiler witness. The earlier sparse CLARK body remains a separate Palomar-registered example with a verified symmetry bound of 3,840.
- Dimensions 6 and above: certified compiler seeds and repeatable dimension addition supply every dimension, not just odd primes. All compiler witnesses fall under the ordinary bound 2^d d!.

The odd-prime title and scope of the earlier companion preprint do not describe this full dimension split. Likewise, a negative search in a restricted construction class would not exclude a construction outside that class. No conclusion about an unidentified external search paper is needed for the explicit four-dimensional source statement given here.

## 1  Physical statements and principal results

Let E_d be d-dimensional Euclidean space. A tile is a set T ⊆ E_d. A physical tiling is a set of tile sets, denoted 𝒯, such that each member is the image of T under a Euclidean isometry, the members cover E_d, and distinct members have disjoint interiors. Boundary intersections are allowed. No registration, orientation choice, matching label or hierarchy is part of this definition.

A translation vector v is a period of 𝒯 if A ∈ 𝒯 is equivalent to A + v ∈ 𝒯 for every set A. This tests the entire tile collection. Testing its union would be vacuous because the union of a complete tiling is all of E_d.

The source predicate SparseMonotiles.IsAperiodicMonotile T is the conjunction of compactness, physical tiling existence, and absence of nonzero periods in every physical tiling. Nonempty interior is stated separately. All Euclidean isometries are permitted in the physical definition, including reflections.

Write Sym(𝒯) for the group of Euclidean isometries s such that {s(A) : A ∈ 𝒯} = 𝒯. Finite full symmetry means that this entire group is finite. It does not mean that the group is trivial. Where the term strongly aperiodic is used for the earlier CLARK result, it has this finite-group meaning.

### Theorem 1  Aperiodic monotiles in every dimension

For every natural number d ≥ 2, there exists T ⊆ E_d such that T is compact, has nonempty interior, admits a physical tiling, and every physical tiling by T has only the zero translation period.

This is the statement of the compiled endpoint PalomarAllDimensions.aperiodic_monotile_in_every_dimension at source commit 048bb245b60abce79f1a2d0c82336ff8508ec752 [5]. Its only explicit arguments are d and the inequality 2 ≤ d. The former parent-occurrence premise C is discharged internally. Full independent verification and all-dimensional registration remain incomplete; Section 8 gives the completed and unfinished stages without treating them as equivalent.

The quantifier order is “for each dimension, there exists a shape.” The theorem does not select one fixed shape across ambient dimensions. It does not assert polyhedrality in every dimension, a topological ball, a unique tiling, or any conclusion about the full symmetry group.

### Theorem 2  Finite full symmetry above dimension two

For the construction witnesses in every integer dimension d > 2, every admitted physical tiling has a finite full Euclidean symmetry group. For the compiler witnesses in d = 3 and d ≥ 5,

```text
|Sym(𝒯)| ≤ 2^d d!.
```

For the four-dimensional body T₄ = SpectreGeometry.polygonProductKeyBody, called JACKIE, the symmetry group is finite by a separate planar-factor argument. This revision does not claim a numerical universal bound for that body. Every infinite-order screw or glide symmetry is excluded, but nontrivial finite symmetry groups are not excluded.

Theorem 2 is an ordinary mathematical corollary of the source lemmas identified in Section 7 and Appendix A, conditional on their correctness. Its new general symmetry-lifting, finite-group and planar-factor deductions have not been implemented as a stronger all-dimensional Lean endpoint, compiled or independently kernel-checked. The cited source lemmas are not independently re-verified through their entire dependency closures by this argument. The separate AI mathematical/source review [8] checks the deduction and source interfaces, not those unfinished verification stages.

Theorem 2 makes no claim about the curved two-dimensional witness. The planar polygon lemma used in its four-dimensional proof concerns the recovered polygon factors, not an unproved substitution of those polygons for the curved planar monotile.

## 2  The planar and four-dimensional branches

### The exact parent-occurrence proposition

The earlier manuscript left one explicit premise C in the two native aperiodicity endpoints. It is the following proposition in the recovered finite hierarchy model; Position, State, GloballyLegal, OccurrenceComplete, hexRegion and certifiedParentFamily retain their source definitions.

```text
def ParentOccurrenceTheorem : Prop :=
  ∀ f : Position → State, GloballyLegal f →
    OccurrenceComplete f (hexRegion 5) certifiedParentFamily
```

Its namespace is SpectreFinite.HexSearch.NativeHierarchy. Thus C concerns certified parent occurrences for every globally legal state field on the radius-five hexagonal region. It is not a compactness or tiling-existence assumption.

At the selected source commit, SpectreFinite.HexSearch.RadiusFivePruning.certifiedParentOccurrenceTheorem supplies this proposition by applying RadiusFiveParentBinding.parentFamily_occurrenceComplete. NativeFinalAssembly.AllDimensions passes that theorem into the conditional assembly [5]. Consequently C remains visible as an intermediate theorem parameter, but it is no longer an extra hypothesis of Theorem 1. This is a source and compilation claim, not a completed final-endpoint external-kernel or axiom-audit claim.

### Proposition 2.1  The exact planar body

For T₂ = LiteralPlanar.FanBounds.curvedBody, the conditional interface is:

```text
theorem NativeFinalAssembly.curved_monotile_of_parent
    (C : SpectreFinite.HexSearch.NativeHierarchy.ParentOccurrenceTheorem) :
    (interior LiteralPlanar.FanBounds.curvedBody).Nonempty ∧
    SparseMonotiles.IsAperiodicMonotile
      LiteralPlanar.FanBounds.curvedBody
```

Compactness, nonempty interior and unmarked tiling existence are separately C-free. NativeIndexedExistence.curved_geometry_and_unmarked_tiling returns those conclusions. The proof combines them with the C-dependent indexed period-rigidity theorem and the indexed-to-unmarked bridge. Supplying the certified parent-occurrence theorem yields the planar branch of Theorem 1.

### Proposition 2.2  The exact four-dimensional body

For T₄ = SpectreGeometry.polygonProductKeyBody, the corresponding interface is:

```text
theorem NativeFinalAssembly.keyed_product_monotile_of_parent
    (C : SpectreFinite.HexSearch.NativeHierarchy.ParentOccurrenceTheorem) :
    (interior SpectreGeometry.polygonProductKeyBody).Nonempty ∧
    SparseMonotiles.IsAperiodicMonotile
      SpectreGeometry.polygonProductKeyBody
```

Compactness and nonempty interior come from the exact-body geometry. KernelSeedPilot.existing_physical_product_tiling supplies an indexed physical tiling without C; the unmarked bridge supplies HasTiling. Only universal period rigidity uses C. Supplying the certified parent-occurrence theorem yields the four-dimensional branch of Theorem 1. Tiling existence is proved separately, so aperiodicity is not obtained vacuously from an untileable shape.

JACKIE is the public name for this four-dimensional construction. The exact Lean body identifier remains SpectreGeometry.polygonProductKeyBody; no new body or source-identifier change is implicit in the name.

### Earlier conditional verification

The terminal accepted conditional run is 38952557899 at commit 62da52d4a30561fa933b8ecd0a95f80e7aedbbe1 [4]. Its independent terminal review reconciles 2,481 source/checker lineages and both raw endpoint audits. Each endpoint has one explicit C argument, an empty universe-parameter list, and only propext, Classical.choice and Quot.sound among its transitive axioms. C is a hypothesis of those historical declarations, not a custom axiom.

That lineage is cache-backed and joins independently reviewed producer stages; it is not a claim that all 2,481 modules were freshly rebuilt in one run. The later successful all-dimensional Solution build supplies newer evidence for the selected modern assembly. Neither the older conditional checks nor the later compilation substitutes for the incomplete final independent checks in Section 8.

## 3  The exact geometric bodies

### The planar body

The planar endpoint selects the literal body defined by LiteralPlanar.FanBounds.curvedBody = euclideanCoordinates '' Candidate.body. The candidate is the finite union of its specified polynomial fan images. The formal image identification relates the modified fan construction to the original polygonal carrier; this paper does not substitute an arbitrary planar aperiodic shape for that exact set.

### JACKIE and the exact four-dimensional body

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

The compiled tiling statement is attached to this exact replacement set. It does not by itself establish a body-level finite-polytope decomposition or the intrinsic boundary-patch count. Those conclusions require their own geometric arguments and formal bindings.

### Why the flat-face claim remains separate

The source-level max-min formula has finitely many affine branches. The unfinished polyhedral addendum must still discharge the reverse-clipping implication, the collar/interior and finite-hull bindings, and the final exact-body instantiation. Piecewise-linear formulas alone are not reported here as a completed Lean proof of those body-level obligations.

## 4  Boundary patches of the four-dimensional construction

Source-level geometric claim, retained from [Section 4 of the 16 October manuscript](https://github.com/jconorgrogan/palomar-chair-verification/blob/1da488b0db487ca2fb4873d03857af3cc0fe089b/papers/all-dimensions-working/aperiodic-monotiles-every-dimension-working-v1.md), which records a separate geometric and exact-arithmetic review. The literal 56-key body has 362 maximal connected flat three-dimensional boundary patches under the convention below. This is not currently a Lean-checked body-level count theorem.

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

The higher-dimensional formalization uses concrete finite compiler data. CompilerData m describes a nonempty finite carrier in actual dimension m + 1 ≥ 3 and a finite proper generator language. HasWorld and PeriodFree are separate propositions proved from those data. They are not hidden assumptions that the product already has a physical aperiodic tiling.

### Existence and universal aperiodicity

CompilerData.prod constructs the product carrier and the union of the two lifted generator languages, then rebuilds the boundary keys through the compiler. CompilerData.prod_hasWorld constructs an actual complete full-profile product world from factor worlds. CompilerData.prod_periodFree recovers the factor contact languages from every legal product world and projects any period to factor periods. Both projected periods vanish, forcing the product period to vanish.

The generic physical registration theorem CompilerData.physical_monotile then turns HasWorld and PeriodFree into a compact Euclidean body with nonempty interior, a physical tiling and universal physical aperiodicity. The theorem starts with arbitrary Euclidean placements. Its internal registration is a proved reduction, not an assumption imposed on the user-facing tilings.

### Proposition 5.1  Addition of certified dimensions

```text
theorem ProductClosure.CertifiedDimension.add {d e : ℕ}
    (hd : CertifiedDimension d) (he : CertifiedDimension e) :
    CertifiedDimension (d + e)
```

Here CertifiedDimension d means that there are finite compiler data D in dimension d together with proofs of D.HasWorld and D.PeriodFree. The certified output is eligible for the same operation again. This is the repeatable dimension-raising rule. No claim is made that the ordinary Cartesian product of arbitrary aperiodic tile shapes automatically has the required property.

### Proposition 5.2  The unconditional higher-dimensional range

```text
theorem ClarkSeed.exists_physical_aperiodic_monotile_of_ge_three_ne_four
    (d : ℕ) (hd : 3 ≤ d) (hne : d ≠ 4) :
    ∃ T : Set (EuclideanSpace ℝ (Fin d)),
      (interior T).Nonempty ∧ SparseMonotiles.IsAperiodicMonotile T
```

The three-dimensional seed comes from the prime family. For the range d ≥ 5, the seeds are dimension 5, dimension 6 = 3 + 3, and dimension 7. Strong induction adds the certified three-dimensional compiler to dimension d − 3 for d ≥ 8. Thus this theorem covers exactly dimension three and every dimension at least five, independently of C.

Its complete imported-closure kernel receipt was completed on 13 October 2026; the 980 pinned source entries and the indexed receipts have been rehashed. This is retained verification of the exact historical sources. The modern port and uniform assembly subsequently compiled as dependencies of the selected complete Solution build on 19 October. That compilation does not replace the still-unfinished independent verification of the final all-dimensional endpoint.

## 6  The compiled uniform assembly

The source module NativeFinalAssembly.AllDimensionsOfParent combines the two native interfaces with the higher-dimensional compiler theorem. Its exhaustive case split is d = 2, d = 4, and d ≥ 3 with d ≠ 4. Its intermediate statement retains C explicitly. The module NativeFinalAssembly.AllDimensions then supplies certifiedParentOccurrenceTheorem and expands the compactness, tiling and period predicates.

The independent physical Solution selects the following endpoint [5]:

```text
theorem aperiodic_monotile_in_every_dimension
    (d : ℕ) (hd : 2 ≤ d) :
    ∃ T : Set (Point d),
      IsCompact T ∧ (interior T).Nonempty ∧
      HasTiling T ∧ IsAperiodic T := by
  exact
    NativeFinalAssembly.exists_physical_aperiodic_monotile_in_every_dimension_ge_two d hd
```

Here Point d abbreviates EuclideanSpace ℝ (Fin d). The exact declaration is linked in Appendix A. IsTiling requires ordinary sets, unrestricted isometries, coverage and pairwise disjoint interiors. IsPeriod tests preservation of the tile collection. No hierarchy, registration, chirality, finite certificate, or parent-occurrence assumption appears as an argument of this public endpoint.

Proof of Theorem 1 at the construction level. The certified parent-occurrence theorem supplies C to Propositions 2.1 and 2.2, yielding the exact bodies in dimensions two and four. Proposition 5.2 supplies a physical monotile in dimension three and every dimension at least five. These cases exhaust d ≥ 2, and every selected branch includes nonempty interior, compactness, existence and universal translation aperiodicity. The selected Lean Solution compiles this assembly. Its verification limits are recorded separately below.

The challenge statement and actual Solution remain distinct artifacts. A successful export of each does not itself prove that their expanded statements and definitions have passed the final independent comparison. Older comments describing some source modules as “source-only” or “uncompiled” are historical comments, not the current build verdict; they are superseded only to the extent established by the later recorded checks.

## 7  Finite full symmetry in every dimension above two

This section supplies the ordinary mathematical proof of Theorem 2. The construction-specific hypotheses are conclusions of the inspected source lemmas at the same immutable all-dimensional source commit, not additional restrictions on admitted physical tilings. The new deductions in this section are not represented as newly verified Lean declarations [7, 8].

### Lemma 7.1  A finite linear image controls the full group

Let G be a group of Euclidean symmetries of a tiling of E_d. Suppose the tiling has no nonzero translation symmetry and the linear parts of elements of G lie in a finite subgroup F of O(d). Then the linear-part map G → F is injective. In particular G is finite and |G| ≤ |F|.

Proof. The linear-part map is a group homomorphism. An element of its kernel is a translation. Since it is also a symmetry, translation aperiodicity forces its displacement to be zero. The kernel is trivial, proving injectivity.

A useful sufficient condition is a finite spanning set N of nonzero vectors that every symmetry's linear part permutes. The induced action G → Sym(N) is injective: fixing N pointwise fixes the whole vector space, reducing to a translation. Include both signs when using normals; the action on unoriented axis lines alone would not be faithful. For N = {±e₁, …, ±e_d}, the linear image is in the signed-permutation group B_d, whose order is 2^d d!, rather than merely in a permutation group of order (2d)!.

The argument proves finiteness of the entire group, not just finite order of individual elements. Also, if a symmetry's linear part has order k, its kth power is a translation and hence the identity. Thus infinite-order screw and glide symmetries cannot remain.

### Lemma 7.2  Arbitrary-frame registration lifts to physical symmetries

Let Q be a compact tile in positive-dimensional Euclidean space, and let H be a subgroup of its ambient isometry group. Suppose that, for every admitted physical tiling and every choice of representatives p_X with p_X(Q) = X, all relative placements p_X⁻¹ p_Y belong to H. Fix a root tile A. Then every physical symmetry s satisfies p_A⁻¹ s p_A ∈ H.

Proof. Set B = s(A), and change only B's representative to p′_B = s p_A. This still represents the same physical tile B. There is a tile C distinct from B, since one compact set cannot cover the unbounded ambient Euclidean space. Keep p′_C = p_C. Apply registration to the modified frame system, with root C, and to the original system, with root A. The two conclusions are

```text
p_C⁻¹ s p_A ∈ H,       p_A⁻¹ p_C ∈ H.
```

Their product is p_A⁻¹ s p_A, so it belongs to H. This argument also covers B = A, including symmetries fixing the root tile setwise.

The unchanged tile C aligns the modified representatives with the original root chart. No trivial prototype stabilizer is assumed, and no equivariance of the initial frame choice is needed. The older exact T5 proof already implements this method in T5_symmetry_registered_in_root, followed by the finite signed-permutation embedding [9]. Here the argument is stated for the general source interfaces.

### Dimensions three and at least five

For the compiler bodies, ProductClosure.NativeCompiler.PhysicalTiling.global_integral_registration concludes that every relative placement is an integral signed-permutation pose. Its hypotheses are an actual arbitrary-isometry physical tiling, a nonempty finite carrier, and the compiler dimension condition. Neither registration nor connectedness is assumed. The compiler parameter is m, while the actual dimension is d = m + 1.

The bridge unmarked_representatives_physicalTiling accepts any representatives of an unmarked physical tile family. Consequently registration applies after changing the one representative used in Lemma 7.2. The affine integral signed-permutation poses form a group, so that lemma puts every symmetry in the same group after conjugating into a fixed root chart.

The linear image therefore lies in B_d. Theorem 1 supplies the absence of nonzero translations for each selected compiler witness. Lemma 7.1 now gives

```text
|Sym(𝒯)| ≤ |B_d| = 2^d d!.
```

The required compiler data, HasWorld and PeriodFree proofs are supplied by the three-dimensional certification, the five-, six- and seven-dimensional seeds, and the repeatable addition theorem of Section 5. Thus the argument covers every d = 3 or d ≥ 5, not only odd-prime dimensions. It uses no extra common-orientation assumption on the input tiling. It also does not identify the new dense five-dimensional compiler body with the original sparse CLARK body.

### Lemma 7.3  Translation-free planar polygon tilings have finite symmetry

Let 𝒰 be a tiling of the plane by congruent copies of a compact polygon P with nonempty interior and pairwise disjoint interiors. If 𝒰 has no nonzero translation symmetry, its full Euclidean symmetry group K is finite.

Proof. Choose an open ball of radius r > 0 contained in the interior of P, and let D be the diameter of P. Each placed tile contains the corresponding r-ball, and these balls are pairwise disjoint. If a tile meets a compact set, its ball center lies within a bounded D-neighborhood of that set. Only finitely many disjoint balls of the fixed radius r fit in a bounded region. Thus only finitely many tiles meet any compact set.

Let V be the union of the genuine intrinsic polygon corners of all tiles. Each tile has finitely many corners, so V meets each compact set in finitely many points. Physical symmetries preserve V because isometries of polygonal tile sets preserve their intrinsic corners. Arbitrarily added markings or subdivision points would not justify this conclusion.

Let K⁺ be the orientation-preserving subgroup. Its linear parts lie in the abelian group SO(2). Every commutator in K⁺ therefore has identity linear part and is a translation. Translation freeness makes every such commutator the identity, so K⁺ is abelian.

If K⁺ is trivial, it is already finite. Otherwise choose a nonidentity element q. It is not a translation, so it is a nontrivial rotation with a unique center c. For any h ∈ K⁺, commutativity gives q(h(c)) = h(q(c)) = h(c), whence h(c) = c. Every element of K⁺ is therefore a rotation about c.

Choose v ∈ V with v ≠ c, which is possible because a compact polygon with nonempty interior has more than one genuine corner. The orbit K⁺v lies both in V and in the compact circle centered at c through v. This orbit is finite. A rotation about c is determined by the image of the noncentral point v, so K⁺ injects into that finite orbit. Finally [K : K⁺] ≤ 2, proving that K is finite.

The lemma assumes neither a periodic grid, a common finite list of tile orientations nor a vertex-to-vertex tiling condition. The factor polygon used below has the required compactness, nonempty interior and finite polygonal boundary in the inspected source. This is not an application to the curved body selected in dimension two.

### The separate four-dimensional argument

JACKIE is not a cubic compiler body. Its source provides a global labeled splitting into two planar factors, rather than signed-permutation registration. The following five source facts are used; Appendix A gives their exact locations.

1. For arbitrary physical representatives, physical_product_global_block_splitting supplies ProductGlobalBlockSplitting in the intrinsic labeled product coordinates. Both planar relative maps are proper. The required ProductKeyPairing is produced from the physical tiling by exists_productKeyPairing; it is not an extra hypothesis on the user-facing tiling.

2. physical_product_complete_cartesian_factors supplies two genuine complete homochiral planar polygon tilings, with disjoint interiors, and realizes every Cartesian pair as a raw carrier tile. ProductGlobalBlockSplitting.image_body supplies the converse inclusion, so the raw carrier family is the full Cartesian product family, not merely a collection of complete transverse columns.

3. physical_keyed_range_symmetry_preserves_raw proves that any ambient isometry preserving the actual unmarked keyed tile family preserves the recovered raw carrier family. It is not limited to translations and does not require a symmetry-equivariant choice of tile representatives.

4. cartesian_family_symmetry_projects applies to arbitrary coordinatewise maps and projects preservation of the full Cartesian family to preservation of each factor family. Nonempty factor sets and index types follow from the factor tilings and the polygon's nonempty interior.

5. homochiral_physical_period_eq_zero_of_parent makes each recovered factor tiling translation-free after supplying the same certified parent-occurrence theorem used in Theorem 1. Its other hypotheses are exactly proper planar placements, disjoint interiors and coverage, already supplied by the factor construction.

Fix an arbitrary admitted four-dimensional tiling and an original root chart. Apply Lemma 7.2 with H equal to the labeled product Isom⁺(E₂) × Isom⁺(E₂) in the intrinsic product coordinates. Each modified frame system receives its own pairing and splitting, but all refer to that same labeled subgroup. The unchanged representative in the lemma identifies the conclusion with the original root chart. Every physical symmetry consequently acts as a pair (u, v) of planar isometries in this one chart. Factor swapping is excluded by the labeled splitting theorem, not silently disregarded.

By raw-carrier recovery and full Cartesian consistency, (u, v) preserves the Cartesian family of the two fixed planar tilings. Projection makes u and v genuine symmetries of their respective factor tilings. Each factor group is finite by its translation freeness and Lemma 7.3. The map from the four-dimensional symmetry group to the product of these two finite groups is injective, since the two coordinate maps determine the entire ambient isometry. Hence the four-dimensional group is finite.

This also covers symmetries fixing individual tiles, and it starts from the unrestricted physical tiling definition. It neither assumes away reflections at the outset nor applies a cubic point-group bound to a noncubic construction. No numerical four-dimensional bound follows from the argument as presented. Together with the compiler cases, this proves Theorem 2 at the stated mathematical/source level.

## 8  Verification provenance and prior results

### The selected all-dimensional source and completed stages

The selected source is 048bb245b60abce79f1a2d0c82336ff8508ec752, with source tree c6111a7d32daf2906275ee1ac265bf6865ebd9a5. The official full preflight is run 39294694136, attempt 1, completed on 19 October 2026 [6]. It used Lean 4.35.0-rc2 and the official reusable pipeline at d4e41c1d5b0d114c4859e6e5831dc6d3ad1d0d44 in full mode under palomar-standard-v1.

The Solution build exited 0 after 12,190.542 seconds and reported “Build completed successfully (12476 jobs).” These are Lake build jobs, not a count of theorems or independent checks. Both proof exports exited 0: Challenge in 9.374 seconds and Solution in 72.796 seconds. This establishes successful compilation and export of the selected complete Solution; it does not assert that every unrelated file or historical branch was built.

The build log reports only propext, Classical.choice and Quot.sound for certifiedParentOccurrenceTheorem. That helper-specific output is not a completed axiom audit of the final all-dimensional endpoint.

### The unfinished full verification

The worker exhausted its shared 19,800-second wall-clock budget, or five and a half hours, with Comparator recorded as the last active stage. The report records status error, stage resource-exhausted, phase verification and error_kind infrastructure/resource-exhausted. The workflow's overall conclusion was failure.

The retained report does not establish a completed final statement/definition comparison, external-kernel check or final-endpoint axiom audit. It does not identify which inner Comparator subphase was active at the deadline. No resumable build or export checkpoint was retained by that run. The remaining checks await additional compute because this preflight exhausted its per-run worker budget, not a service-wide Palomar budget. More time is not a guarantee that every remaining check will pass.

The unchanged mechanical report has 203,813 bytes and SHA-256 a1681ef51911a64f4bfe975e283396cd7ef3f8f4fd2aac5130ecdd3c5ef23ec6 [6]. It retains older manuscript metadata describing C or the uniform theorem as pending. That historical prose does not negate the selected source's internal discharge of C, and correcting the prose does not upgrade the unfinished verification verdict. As of this revision, the all-dimensional result has no completed Palomar registration.

### Retained earlier verification

The accepted 16 October conditional endpoint record binds both exact native bodies to commit 62da52d4a30561fa933b8ecd0a95f80e7aedbbe1 and run 38952557899 [4]. Its terminal review has SHA-256 ebf3550dd9d5639e6140478e0179dc08533cf450469f73671bb14f659d06e0d2. The C-free geometry and existence assertions remain distinct from the C-dependent period assertions in those historical endpoints.

The historical ClarkSeed.PhysicalDimensions imported closure passed an independent fresh-environment kernel check at 18:42:59 UTC on 13 October 2026, with exit status zero. Its receipt has SHA-256 b7e169fb023764fcc2a563b709d9c59daa7d065636bc7ebbba643f8608c599c5. Rehashing the 980 pinned source entries and receipts authenticated retained files; it did not rerun Lean or independently verify the later uniform endpoint.

The clean hierarchy-C campaign, the 174-module visibility test and the 388-module import-optimization test are separate runs retained in the dated status note [6]. Their successes keep their own scope and do not replace the missing full all-dimensional verdict.

### CLARK and HENRY

The original sparse five-dimensional CLARK body has a completed Lean formalization and Palomar registration dated 7 October 2026 [2]. The registered theorem is PalomarMonotiles.T5_strongAperiodicity at commit 5f5ceedee770b76c21e8f1105e5e4e3b84b8d676. It includes finite full symmetry and the bound 3,840 = 2^5 5!. Its official full mechanical preflight passed, including statement comparison and the Lean, NanoDa and verified con-ron checks. This is a prior completed result for its own exact body, not a registration of Theorems 1 or 2 for all dimensions.

The pinned CLARK/HENRY manuscript gives a written computer-assisted proof and exact finite M7 computation for the sparse seven-dimensional HENRY body [3]. Its Section 7 and appendix status table leave complete Lean verification unfinished. HENRY is therefore not described here as Lean-verified or Palomar-registered.

### Exact identities of the compiler seeds

The higher-dimensional closure uses a newly compiled dense five-dimensional body derived from the recovered CLARK contact and hierarchy certificates. Its binding record does not identify that dense body with the original sparse CLARK body. Its seven-dimensional seed is ProductClosure.seven_certified from the prime-3-modulo-4 compiler family; no identity with the separate sparse HENRY body is selected.

The names CLARK and HENRY identify those earlier exact bodies and their own evidence. The name JACKIE identifies the exact four-dimensional keyed-product body here. A dimension or shared seed certificate alone does not establish equality between bodies, and a verification claim for one is not transferred to another.

### Status of the finite-symmetry extension

The 22 October extension [7] and separate AI mathematical/source review [8] support the ordinary deduction in Section 7. The review addresses arbitrary-frame registration, the root-fixed symmetry case, both planar factors, full Cartesian consistency, raw-carrier recovery, projection and the discharge of C. It does not freshly verify every deep geometric or certificate dependency.

The new all-dimensional finite-symmetry deductions and stronger endpoint have not been implemented in Lean, compiled, externally kernel-checked, subjected to a final axiom audit, or registered in Palomar. No Lean proof build, Palomar operation or new formal verification was performed in preparing this manuscript revision.

## 9  Remaining formal work and limits of the results

The remaining all-dimensional translation-aperiodicity work is to complete the final comparison, external-kernel checks and endpoint axiom audit for the exact selected source, and to obtain a full passing official verification and registration if those checks succeed. Completing C and merely compiling the uniform Solution are no longer listed as unfinished source tasks.

To formalize the stronger finite-symmetry theorem, the following proof components must be implemented and checked:

- General one-frame symmetry lifting from arbitrary-frame relative registration, including symmetries fixing the root tile.
- Injectivity of the linear-part map when translation symmetries are absent, and the signed-permutation cardinal bound for compiler witnesses.
- The planar polygon finite-symmetry lemma, including local finiteness and symmetry-invariance of intrinsic corners.
- The labeled-block lift, raw-family transport and factor-group injection for the exact four-dimensional body.
- A stronger endpoint assembling the dimension branches, followed by the relevant build, comparison, kernel and axiom checks.

The exact-body four-dimensional polyhedral addendum remains separate. Its reverse-clipping, collar/interior, finite-hull and final-instantiation obligations must be discharged before claiming that part as a completed Lean theorem. A formally verified 362-patch count additionally requires an exact-body count theorem with the convention in Section 4. Neither is a premise of Theorem 1 or of the ordinary finite-symmetry deduction.

No theorem here asserts trivial symmetry groups, a universal numerical bound for JACKIE, uniqueness of a tiling, a topological-ball property, a single fixed shape across dimensions, or physical aperiodicity of arbitrary Cartesian products. The all-dimensional range follows from the specified keyed compiler and the separately supplied native bodies.

## Appendix A  Claim and source map

All source paths in this appendix use the immutable all-dimensional commit 048bb245b60abce79f1a2d0c82336ff8508ec752 unless a different commit is explicit. Source links identify the declarations and proof bodies, not a claim that the complete independent verification has finished.

1. Uniform physical statement: [PalomarAllDimensionsSolution.lean](https://github.com/jconorgrogan/palomar-chair-verification/blob/048bb245b60abce79f1a2d0c82336ff8508ec752/src/PalomarAllDimensionsSolution.lean), definitions IsTiling, IsPeriod, HasTiling and IsAperiodic, and aperiodic_monotile_in_every_dimension.

2. Internal discharge of C: [RadiusFivePruningHierarchy.lean](https://github.com/jconorgrogan/palomar-chair-verification/blob/048bb245b60abce79f1a2d0c82336ff8508ec752/src/SpectreFinite/RadiusFivePruningHierarchy.lean), certifiedParentOccurrenceTheorem; [AllDimensions.lean](https://github.com/jconorgrogan/palomar-chair-verification/blob/048bb245b60abce79f1a2d0c82336ff8508ec752/src/NativeFinalAssembly/AllDimensions.lean), unconditional assembly; [AllDimensionsOfParent.lean](https://github.com/jconorgrogan/palomar-chair-verification/blob/048bb245b60abce79f1a2d0c82336ff8508ec752/src/NativeFinalAssembly/AllDimensionsOfParent.lean), exact dimension case split.

3. Native exact bodies and conditional interfaces: [CurvedOfParent.lean](https://github.com/jconorgrogan/palomar-chair-verification/blob/048bb245b60abce79f1a2d0c82336ff8508ec752/src/NativeFinalAssembly/CurvedOfParent.lean) and [KeyedProductOfParent.lean](https://github.com/jconorgrogan/palomar-chair-verification/blob/048bb245b60abce79f1a2d0c82336ff8508ec752/src/NativeFinalAssembly/KeyedProductOfParent.lean).

4. Compiler inputs and coverage: [CompilerData.lean](https://github.com/jconorgrogan/palomar-chair-verification/blob/048bb245b60abce79f1a2d0c82336ff8508ec752/src/ProductClosure/CompilerData.lean), physical_monotile; [CertifiedDimensions.lean](https://github.com/jconorgrogan/palomar-chair-verification/blob/048bb245b60abce79f1a2d0c82336ff8508ec752/src/ProductClosure/CertifiedDimensions.lean), three_certified; [ProductDimensions.lean](https://github.com/jconorgrogan/palomar-chair-verification/blob/048bb245b60abce79f1a2d0c82336ff8508ec752/src/ProductClosure/ProductDimensions.lean), additive closure; [PhysicalDimensions.lean](https://github.com/jconorgrogan/palomar-chair-verification/blob/048bb245b60abce79f1a2d0c82336ff8508ec752/src/ClarkSeed/PhysicalDimensions.lean), every_dimension_ge_five_certified and the physical endpoints.

5. Arbitrary-frame cubic registration: [NativeUnmarkedPeriods.lean](https://github.com/jconorgrogan/palomar-chair-verification/blob/048bb245b60abce79f1a2d0c82336ff8508ec752/src/ProductClosure/NativeUnmarkedPeriods.lean), unmarked_representatives_physicalTiling; [GlobalRegistration.lean](https://github.com/jconorgrogan/palomar-chair-verification/blob/048bb245b60abce79f1a2d0c82336ff8508ec752/src/ProductClosure/GlobalRegistration.lean), PhysicalTiling.global_integral_registration.

6. Labeled four-dimensional splitting: [PolygonProductGlobalBlocks.lean](https://github.com/jconorgrogan/palomar-chair-verification/blob/048bb245b60abce79f1a2d0c82336ff8508ec752/src/SpectreGeometry/PolygonProductGlobalBlocks.lean), physical_product_global_block_splitting; [PolygonProductKeyPairing.lean](https://github.com/jconorgrogan/palomar-chair-verification/blob/048bb245b60abce79f1a2d0c82336ff8508ec752/src/SpectreGeometry/PolygonProductKeyPairing.lean), exists_productKeyPairing.

7. Genuine complete factors and Cartesian equality: [PolygonProductFactorTilings.lean](https://github.com/jconorgrogan/palomar-chair-verification/blob/048bb245b60abce79f1a2d0c82336ff8508ec752/src/SpectreGeometry/PolygonProductFactorTilings.lean), physical_product_complete_cartesian_factors; [PolygonProductBlockCoordinates.lean](https://github.com/jconorgrogan/palomar-chair-verification/blob/048bb245b60abce79f1a2d0c82336ff8508ec752/src/SpectreGeometry/PolygonProductBlockCoordinates.lean), ProductGlobalBlockSplitting.image_body.

8. Symmetry transport and projection: [PolygonProductRawRangeSymmetry.lean](https://github.com/jconorgrogan/palomar-chair-verification/blob/048bb245b60abce79f1a2d0c82336ff8508ec752/src/SpectreGeometry/PolygonProductRawRangeSymmetry.lean), physical_keyed_range_symmetry_preserves_raw; [CartesianFamilyProjection.lean](https://github.com/jconorgrogan/palomar-chair-verification/blob/048bb245b60abce79f1a2d0c82336ff8508ec752/src/SpectreGeometry/CartesianFamilyProjection.lean), cartesian_family_symmetry_projects.

9. Planar factor geometry and period rigidity: [PolygonBody.lean](https://github.com/jconorgrogan/palomar-chair-verification/blob/048bb245b60abce79f1a2d0c82336ff8508ec752/src/SpectreGeometry/PolygonBody.lean), [PolygonBoundary.lean](https://github.com/jconorgrogan/palomar-chair-verification/blob/048bb245b60abce79f1a2d0c82336ff8508ec752/src/SpectreGeometry/PolygonBoundary.lean), [EuclideanCarrier.lean](https://github.com/jconorgrogan/palomar-chair-verification/blob/048bb245b60abce79f1a2d0c82336ff8508ec752/src/SpectreGeometry/EuclideanCarrier.lean), and [PhysicalHierarchyFromParent.lean](https://github.com/jconorgrogan/palomar-chair-verification/blob/048bb245b60abce79f1a2d0c82336ff8508ec752/src/SpectreGeometry/PhysicalHierarchyFromParent.lean), homochiral_physical_period_eq_zero_of_parent.

10. Previously registered exact T5 finite-symmetry proof: [FiniteSymmetry.lean at the registered commit](https://github.com/jconorgrogan/palomar-chair-verification/blob/5f5ceedee770b76c21e8f1105e5e4e3b84b8d676/SparseMonotiles/FiniteSymmetry.lean). This is a separate source snapshot and exact body.

## Appendix B  Revision history and archival scope

The 16 October all-dimensional working manuscript remains a historical snapshot. Its pending-C and pending-build language described the evidence available at that date. This 22 October revision updates that language using the selected source and official build record, incorporates the ordinary finite-symmetry proof, and replaces the reserved future abstract with a single abstract describing the current claims and limits.

The earlier companion paper, An Arithmetic Family of Aperiodic Tilings in Odd Prime Dimensions, is archived as Zenodo version 2 at DOI 10.5281/zenodo.23197680 [3]. That DOI identifies the historical odd-prime paper, not this all-dimensional manuscript revision. The archive's concept DOI, 10.5281/zenodo.23197474, identifies the version family. A dated manuscript revision is not itself a new published Zenodo version, and no new version DOI is assigned in this document.

The original CLARK paper, its figures, historical source snapshots, verification reports and registration links are preserved. Updating the exposition does not alter their statements or confer their verification status on the new all-dimensional extension.

### Authorship and production

Conor Grogan is the author and responsible maintainer. AI systems made substantive contributions to mathematical analysis, Lean proofs, exact certificate generation, source review and exposition. AI contributions are distinguished from human authorship. No independent human mathematical peer review or novelty certification is claimed.

The companion manuscript and figures retain the project's Creative Commons Attribution 4.0 International license. Proof code retains Apache License 2.0. Lean, Mathlib and other dependencies retain their respective licenses and notices.

## References

[1] Adam Scherlis. Monotiles in every dimension. Pinned primary note, repository revision e05cee7245124a705ca68be3a8f641d290c664b4, modified 24 September 2026. [Keyed-product note](https://github.com/AdamScherlis/adamscherlis.github.io/blob/e05cee7245124a705ca68be3a8f641d290c664b4/static/monotiles-every-dimension/index.html).

[2] Palomar Registry. CLARK entry PALOMAR-2026-10-07-000006, version 1, registered 7 October 2026. [Registration](https://palomar-registry.org/entry?id=PALOMAR-2026-10-07-000006&version=1); [official record](https://data.palomar-registry.org/entries/PALOMAR-2026-10-07-000006-v1.json).

[3] Conor Grogan. An Arithmetic Family of Aperiodic Tilings in Odd Prime Dimensions. Version 2, 6 October 2026. Zenodo, [DOI 10.5281/zenodo.23197680](https://doi.org/10.5281/zenodo.23197680). [Pinned CLARK/HENRY manuscript](https://github.com/jconorgrogan/palomar-chair-verification/blob/46c05aaea9e4d1ee51acac23ec2d048b49d0da0e/CLARK_paper.pdf). HENRY status: Section 7, printed page 17, and appendix status table, printed page 34.

[4] Conditional native two- and four-dimensional verification. Accepted source 62da52d4a30561fa933b8ecd0a95f80e7aedbbe1; terminal run 38952557899. [Run](https://github.com/jconorgrogan/palomar-chair-verification/actions/runs/38952557899); [source commit](https://github.com/jconorgrogan/palomar-chair-verification/commit/62da52d4a30561fa933b8ecd0a95f80e7aedbbe1).

[5] All-dimensional selected Lean source. Commit 048bb245b60abce79f1a2d0c82336ff8508ec752. [Source tree](https://github.com/jconorgrogan/palomar-chair-verification/tree/048bb245b60abce79f1a2d0c82336ff8508ec752); [selected physical endpoint](https://github.com/jconorgrogan/palomar-chair-verification/blob/048bb245b60abce79f1a2d0c82336ff8508ec752/src/PalomarAllDimensionsSolution.lean).

[6] All-dimensional verification record. [Official run 39294694136](https://github.com/jconorgrogan/palomar-chair-verification/actions/runs/39294694136); [20 October status note](https://github.com/jconorgrogan/palomar-chair-verification/blob/1da488b0db487ca2fb4873d03857af3cc0fe089b/verification/ALL_DIMENSIONS_STATUS_2026-10-20.md); [unchanged mechanical report](https://github.com/jconorgrogan/palomar-chair-verification/blob/1da488b0db487ca2fb4873d03857af3cc0fe089b/verification/ALL_DIMENSIONS_MECHANICAL_REPORT_39294694136.json).

[7] Finite full symmetry in every integer dimension d > 2. Mathematical extension, 22 October 2026. [Extension at commit 1da488b](https://github.com/jconorgrogan/palomar-chair-verification/blob/1da488b0db487ca2fb4873d03857af3cc0fe089b/papers/FINITE_SYMMETRY_EXTENSION_2026-10-22.md).

[8] Independent mathematical and source audit of the finite-symmetry extension. Separate AI review, 22 October 2026. [Review and its limits at commit 1da488b](https://github.com/jconorgrogan/palomar-chair-verification/blob/1da488b0db487ca2fb4873d03857af3cc0fe089b/papers/FINITE_SYMMETRY_SOURCE_REVIEW_2026-10-22.md).

[9] Registered CLARK finite-symmetry proof. [FiniteSymmetry.lean](https://github.com/jconorgrogan/palomar-chair-verification/blob/5f5ceedee770b76c21e8f1105e5e4e3b84b8d676/SparseMonotiles/FiniteSymmetry.lean), immutable registered source. [Official passing full preflight 37544058631](https://github.com/jconorgrogan/palomar-chair-verification/actions/runs/37544058631).
