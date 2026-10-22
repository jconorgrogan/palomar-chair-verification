# AI source review: finite full symmetry in every integer dimension d > 2

22 October 2026. Separate AI mathematical/source review of the [finite-symmetry extension](FINITE_SYMMETRY_EXTENSION_2026-10-22.md). This review examines the mathematical deductions and their stated source interfaces. It is not independent human peer review, external kernel verification, a full axiom audit, or Palomar acceptance.

## Verdict

**The proposed argument is a valid ordinary mathematical corollary of the exact inspected source lemmas. No additional geometric registration, Cartesian-product, local-finiteness, or frame-equivariance hypothesis is needed.** It establishes finiteness of the full Euclidean symmetry group of every admitted tiling for the construction witnesses in every integer dimension d > 2, not merely absence of translation periods or finite order of each individual symmetry.

The qualifications in the proposal are essential:

- The selected all-dimensional Lean endpoint currently states translation aperiodicity, not finite full symmetry.
- The generic symmetry-lifting, finite-group injection, planar finiteness, and all-dimensional strengthening are new mathematical deductions in this audit, not newly compiled Lean results.
- The bound 2^d d! applies to the graph-compiled witnesses in d = 3 and d >= 5. It must not be applied to the separate d = 4 witness from this proof.
- The sharper 2^(d-1) d! follows for those same graph-compiled witnesses from the inspected proper-registration theorem. It is optional and is not an existing checked numerical endpoint.
- The older T5 finite-symmetry source concerns its own exact body. Its 3,840 bound should not be silently identified with a bound for the newer recompiled 5D witness.

This audit fetched actual declarations, definitions, and proof bodies at immutable commit `048bb245b60abce79f1a2d0c82336ff8508ec752`, with the older T5 comparison fetched at `5f5ceedee770b76c21e8f1105e5e4e3b84b8d676`. It did not rely on README descriptions for the proof. It did not recompile these sources, inspect the entire transitive proof dependency closure, perform a kernel/axiom audit, or establish a registration status. No Lean source was modified in preparing this extension.

## 1. Exact scope of the existing endpoint

In [PalomarAllDimensionsSolution.lean](https://github.com/jconorgrogan/palomar-chair-verification/blob/048bb245b60abce79f1a2d0c82336ff8508ec752/src/PalomarAllDimensionsSolution.lean#L19-L43), `IsTiling` admits arbitrary Euclidean isometries, with coverage and pairwise disjoint interiors of distinct physical tile sets. `IsAperiodic` quantifies only over vectors satisfying `IsPeriod`. The current theorem thus has the weaker translation-only statement.

The source does **not** thereby demonstrate that an admitted tiling has a screw symmetry. That would require a counterexample. What is established here is that the stronger conclusion can be deduced from additional structure already supplied by the construction's source lemmas.

The case split in [AllDimensionsOfParent.lean](https://github.com/jconorgrogan/palomar-chair-verification/blob/048bb245b60abce79f1a2d0c82336ff8508ec752/src/NativeFinalAssembly/AllDimensionsOfParent.lean) selects `polygonProductKeyBody` in dimension 4 and the compiler witnesses in dimension 3 and every dimension at least 5. It does not obtain the dimension-4 witness by cubic registration.

## 2. Arbitrary physical frames: the crucial lifting argument

Let Q be compact in positive-dimensional Euclidean space and admit the physical tiling under consideration. Let H be a subgroup of its ambient isometry group. Assume that **for every choice** of representatives p_X with p_X(Q) = X, every relative placement p_X^(-1) p_Y belongs to H.

Fix a root tile A and a full physical symmetry s. Put B = s(A). Replace only B's representative by p'_B = s p_A. Choose C different from B and retain p'_C = p_C. Such a C exists: otherwise a single compact tile would cover the unbounded ambient Euclidean space. Registration for the modified representatives gives

    p_C^(-1) s p_A in H.

Registration for the original representatives gives

    p_A^(-1) p_C in H.

Their product is p_A^(-1) s p_A, as required. This is valid when B = A, so root-fixed physical symmetries are included. If B differs from A, C may even equal A without causing a problem.

The proof does not require a trivial prototype stabilizer. It does not presume that the original representative selection is equivariant under s. The unchanged C is what makes the proof work in the root-fixed case.

For compiler bodies, [NativeUnmarkedPeriods.lean, `unmarked_representatives_physicalTiling`](https://github.com/jconorgrogan/palomar-chair-verification/blob/048bb245b60abce79f1a2d0c82336ff8508ec752/src/ProductClosure/NativeUnmarkedPeriods.lean#L16-L32) explicitly accepts arbitrary representatives. Its conclusion is the indexed `PhysicalTiling` required by registration. Inspection of [PhysicalTilingGerms.lean](https://github.com/jconorgrogan/palomar-chair-verification/blob/048bb245b60abce79f1a2d0c82336ff8508ec752/src/ProductClosure/PhysicalTilingGerms.lean#L16-L23) confirms that this predicate has only the two fields, disjoint interiors and coverage.

For dimension 4, [PolygonProductKeyPacking.lean](https://github.com/jconorgrogan/palomar-chair-verification/blob/048bb245b60abce79f1a2d0c82336ff8508ec752/src/SpectreGeometry/PolygonProductKeyPacking.lean#L165-L173) gives the analogous two-field physical-tiling structure. Indexing an unmarked tiling by its physical tile sets and choosing any representatives supplies these fields directly. Changing one representative to another with the same physical image leaves them unchanged. No extra theorem about symmetry-equivariant frame choices is needed.

The inspected older [FiniteSymmetry.lean](https://github.com/jconorgrogan/palomar-chair-verification/blob/5f5ceedee770b76c21e8f1105e5e4e3b84b8d676/SparseMonotiles/FiniteSymmetry.lean) implements this same argument in `T5_symmetry_registered_in_root`, including the distinct unchanged tile. It is an existing formal template, not evidence that the new generic or dimension-4 versions have already been implemented.

## 3. Dimensions 3 and at least 5

### Exact registration hypotheses

[GlobalRegistration.lean, `PhysicalTiling.global_integral_registration`](https://github.com/jconorgrogan/palomar-chair-verification/blob/048bb245b60abce79f1a2d0c82336ff8508ec752/src/ProductClosure/GlobalRegistration.lean#L31-L39) takes:

- the finite cell carrier, with its nonempty-cell instance;
- the compiler dimension condition 2 <= m and `NeZero m`;
- arbitrary isometry representatives f;
- an actual `PhysicalTiling a f`;
- arbitrary root and target indices.

It concludes `HasIntegralSignedPermutation (relativePlacement (f root) (f i))`. There is no supplied registration or connectedness premise. Its proof derives all-index reachability and then applies component registration.

[SignedPermutationRegistration.lean](https://github.com/jconorgrogan/palomar-chair-verification/blob/048bb245b60abce79f1a2d0c82336ff8508ec752/src/ProductClosure/SignedPermutationRegistration.lean#L17-L55) removes any ambiguity about this predicate: it records a permutation of `Fin (m+1)`, one Boolean sign for each basis vector, and an integer translation. In particular it constrains the entire ambient linear part, not only a tangent subspace or unoriented axis lines. The relative placement is exactly f_root^(-1) f_i. [IntegralPoseAlgebra.lean](https://github.com/jconorgrogan/palomar-chair-verification/blob/048bb245b60abce79f1a2d0c82336ff8508ec752/src/ProductClosure/IntegralPoseAlgebra.lean) supplies identity, composition, and inverse closure.

**Dimension convention:** the actual dimension is d = m+1, not m. This is explicit in [CertifiedDimensions.lean](https://github.com/jconorgrogan/palomar-chair-verification/blob/048bb245b60abce79f1a2d0c82336ff8508ec752/src/ProductClosure/CertifiedDimensions.lean#L12-L23) and in the basis index used by `HasIntegralSignedPermutation`. Thus the cardinal bound is 2^d d!.

### Finiteness and bound

The lifting argument puts every full physical symmetry, in one fixed root chart, in the affine integral signed-permutation group. Its linear-part map lands in the finite signed-permutation group B_d.

If two symmetries have the same linear part, their quotient has identity linear part and hence is a translation. It remains a symmetry because the full set-preserving symmetries form a group. Translation aperiodicity makes that quotient the identity. Therefore the linear-part map is injective and

    |Sym(tiling)| <= |B_d| = 2^d d!.

This proves finiteness of the whole group. A separate argument about individual elements is unnecessary. In particular, the kth power of a symmetry whose linear part has order k is a translation and must be the identity, so infinite-order screw and glide symmetries are excluded.

### All required witnesses and period hypotheses are supplied in source

[CompilerData.lean](https://github.com/jconorgrogan/palomar-chair-verification/blob/048bb245b60abce79f1a2d0c82336ff8508ec752/src/ProductClosure/CompilerData.lean#L17-L64) defines concrete finite cells, nonemptiness, dimension, and proper generators. Its `physical_monotile` theorem takes `HasWorld` and `PeriodFree`; these are obligations of that general theorem, not automatic consequences of merely possessing a `CompilerData` record.

For the selected dimension witnesses those obligations are supplied: [CertifiedDimensions.lean](https://github.com/jconorgrogan/palomar-chair-verification/blob/048bb245b60abce79f1a2d0c82336ff8508ec752/src/ProductClosure/CertifiedDimensions.lean) provides dimension 3, [ProductDimensions.lean](https://github.com/jconorgrogan/palomar-chair-verification/blob/048bb245b60abce79f1a2d0c82336ff8508ec752/src/ProductClosure/ProductDimensions.lean) proves the additive compiler closure, and [ClarkSeed/PhysicalDimensions.lean](https://github.com/jconorgrogan/palomar-chair-verification/blob/048bb245b60abce79f1a2d0c82336ff8508ec752/src/ClarkSeed/PhysicalDimensions.lean#L23-L55) proves certification in every dimension at least 5. These existential certification statements include both world existence and universal period freeness. The strengthening is therefore not restricted to odd-prime dimensions.

### Optional proper half-bound

[GlobalRegistration.lean, `compiled_global_proper_integral_registration`](https://github.com/jconorgrogan/palomar-chair-verification/blob/048bb245b60abce79f1a2d0c82336ff8508ec752/src/ProductClosure/GlobalRegistration.lean#L114-L129) additionally proves determinant +1 of every relative placement for `compiledCoefficients hm A hA`. The definition `CompilerData.coefficients` uses precisely that construction, with the record's proof that every generator is proper. The same arbitrary-frame lifting consequently puts the full symmetry linear image in B_d intersect SO(d).

For d >= 1, changing one coordinate sign pairs determinant +1 and determinant -1 signed permutations, so the proper subgroup has order 2^(d-1) d!. Hence the sharper bound is mathematically justified for these compiler witnesses. The conservative 2^d d! bound is safe without using properness.

## 4. The planar finite-symmetry lemma

The planar lemma in the proposal is correct, provided “vertices” means genuine intrinsic polygon corners, not an arbitrary marked or subdivided list of points.

Let a tiling use isometric copies of a fixed compact polygon P with nonempty interior. Choose an open ball of radius r > 0 inside P. Its corresponding images lie in the interiors of the placed tiles and are pairwise disjoint. If a tile meets a compact set K, the center of its chosen ball lies within a fixed bounded neighborhood of K: the distance to a point of intersection is at most the diameter of P. The centers are uniformly separated, so only finitely many lie in that bounded neighborhood. Therefore only finitely many tiles meet K.

Each tile has finitely many intrinsic corners. The union V of all those corner sets has finite intersection with every compact set. Moreover every physical tiling symmetry preserves V, because it maps each polygonal tile set isometrically onto another tile set and preserves its genuine corners. This step would not be justified for arbitrary supplementary markings, which is why the intrinsic interpretation matters.

Let K be the full planar symmetry group and K+ its orientation-preserving subgroup. The linear parts of K+ belong to the abelian group SO(2). Every commutator in K+ therefore has identity linear part, hence is a translation. Translation freeness makes K+ abelian.

If K+ is nontrivial, choose a nonidentity member r. It cannot be a translation, so it is a nontrivial rotation with a unique fixed center c. Every h in K+ commutes with r, so r(h(c)) = h(c). Thus h(c) = c. Every h is consequently a rotation about the same point c.

Choose v in V with v different from c. Such a corner exists because a bounded polygon with nonempty interior has more than one genuine corner. The orbit K+v lies in the compact circle centered at c through v and in V, hence is finite. A rotation about c is determined by its value at v, so K+ embeds in this finite orbit and is finite. If K+ was trivial, it was already finite. Finally [K:K+] <= 2, proving that K is finite.

This proof needs no periodic grid, common finite list of tile orientations, vertex-to-vertex tiling condition, or preexisting local-finiteness hypothesis.

The exact planar factor body used here has the required geometry: [PolygonBody.lean](https://github.com/jconorgrogan/palomar-chair-verification/blob/048bb245b60abce79f1a2d0c82336ff8508ec752/src/SpectreGeometry/PolygonBody.lean) defines a finite union of fourteen triangles and proves compactness and nonempty interior; [PolygonBoundary.lean](https://github.com/jconorgrogan/palomar-chair-verification/blob/048bb245b60abce79f1a2d0c82336ff8508ec752/src/SpectreGeometry/PolygonBoundary.lean#L171-L174) proves that its frontier is exactly the fourteen outer segments; [EuclideanCarrier.lean](https://github.com/jconorgrogan/palomar-chair-verification/blob/048bb245b60abce79f1a2d0c82336ff8508ec752/src/SpectreGeometry/EuclideanCarrier.lean#L21-L30) transports it to the standard Euclidean plane and supplies compactness and nonempty interior there. A formal intrinsic-corner/local-finiteness lemma still needs to be written, but this is not an unproved geometric condition on the particular tilings.

## 5. Dimension 4: exact factor and symmetry audit

### The split is labeled, global, and applies to arbitrary representatives

In [PolygonProductGlobalBlocks.lean](https://github.com/jconorgrogan/palomar-chair-verification/blob/048bb245b60abce79f1a2d0c82336ff8508ec752/src/SpectreGeometry/PolygonProductGlobalBlocks.lean#L81-L106), `ProductGlobalBlockSplitting` provides planar isometries `left i` and `right i`, properness of each, and a placement identity for all points in the two labeled coordinates. It is not an unlabeled assertion that some two-plane decomposition exists.

The theorem takes a physical tiling and a `ProductKeyPairing`. The latter is not an unresolved hypothesis: [PolygonProductKeyPairing.lean, `exists_productKeyPairing`](https://github.com/jconorgrogan/palomar-chair-verification/blob/048bb245b60abce79f1a2d0c82336ff8508ec752/src/SpectreGeometry/PolygonProductKeyPairing.lean#L24-L33) constructs it from the physical tiling alone, including the same-label property.

Apply the arbitrary-frame lifting argument using H = the embedded labeled product Isom+(R^2) x Isom+(R^2). Each modified frame system obtains its own pairing and splitting. These need not equal the original selected pairing and splitting: their conclusions all refer to the same intrinsic labeled prototype coordinates, so they lie in the same subgroup H. The unchanged representative connects them to the original root chart.

Consequently every ambient physical symmetry is coordinatewise in the single fixed root chart. Factor swapping is genuinely excluded by the labeled source conclusion, not ignored. For finiteness alone one could even discard properness and use the full labeled block subgroup.

### There really are two complete factor tilings and the full Cartesian family

[PolygonProductFactorTilings.lean, `physical_product_complete_cartesian_factors`](https://github.com/jconorgrogan/palomar-chair-verification/blob/048bb245b60abce79f1a2d0c82336ff8508ec752/src/SpectreGeometry/PolygonProductFactorTilings.lean#L104-L129) supplies both planar families, proper placements, pairwise interior disjointness, coverage, and realization of every pair as an actual raw carrier.

The reverse inclusion, that each raw carrier is such a product, is supplied by [PolygonProductBlockCoordinates.lean, `ProductGlobalBlockSplitting.image_body`](https://github.com/jconorgrogan/palomar-chair-verification/blob/048bb245b60abce79f1a2d0c82336ff8508ec752/src/SpectreGeometry/PolygonProductBlockCoordinates.lean#L33-L41). Equivalently, [PolygonProductCartesianConsistency.lean, `cartesian_family`](https://github.com/jconorgrogan/palomar-chair-verification/blob/048bb245b60abce79f1a2d0c82336ff8508ec752/src/SpectreGeometry/PolygonProductCartesianConsistency.lean#L113-L128) states the full diagonal-family/product-family equality directly. Thus there is no missing inference from complete transverse columns to global Cartesian consistency.

### Physical symmetries act on the raw family, not merely on selected poses

[PolygonProductRawRangeSymmetry.lean, `physical_keyed_range_symmetry_preserves_raw`](https://github.com/jconorgrogan/palomar-chair-verification/blob/048bb245b60abce79f1a2d0c82336ff8508ec752/src/SpectreGeometry/PolygonProductRawRangeSymmetry.lean#L28-L53) takes an arbitrary ambient isometry and equality of the actual unmarked keyed image families. It concludes equality of the raw image families. It is not restricted to translations, does not require a chosen symmetry-equivariant bijection of tile indices, and does not assume that internal tile symmetries are trivial.

The supporting `physical_equal_keyed_carrier_equal_raw` in [PolygonProductCarrierRecovery.lean](https://github.com/jconorgrogan/palomar-chair-verification/blob/048bb245b60abce79f1a2d0c82336ff8508ec752/src/SpectreGeometry/PolygonProductCarrierRecovery.lean) explicitly proves alternative-frame raw-carrier equality by replacing one representative. This closes the potential hidden-self-symmetry issue at raw recovery as well.

### Projection is for arbitrary coordinate maps

[CartesianFamilyProjection.lean, `cartesian_family_symmetry_projects`](https://github.com/jconorgrogan/palomar-chair-verification/blob/048bb245b60abce79f1a2d0c82336ff8508ec752/src/SpectreGeometry/CartesianFamilyProjection.lean#L50-L77) is stated for arbitrary u and v, not only translations. It requires nonempty factor index types and nonempty factor sets, all supplied by the physical factor tilings and the nonempty polygon interior. It then projects preservation of the full Cartesian tile family to preservation of each factor family.

Thus an arbitrary physical symmetry s gives a pair (u,v) of actual symmetries of the two fixed planar factor tilings. The coordinate pair uniquely determines s, so this assignment is injective. It is not necessary that every pair of factor symmetries lifts back to a symmetry of the keyed body.

### The planar translation-free premise is discharged

[PhysicalHierarchyFromParent.lean, `homochiral_physical_period_eq_zero_of_parent`](https://github.com/jconorgrogan/palomar-chair-verification/blob/048bb245b60abce79f1a2d0c82336ff8508ec752/src/SpectreGeometry/PhysicalHierarchyFromParent.lean#L52-L67) needs proper planar placements, disjoint interiors, coverage, and the parent-occurrence theorem C. These geometric conditions are exactly those of the factor tilings just obtained.

C is an explicit premise of that intermediate theorem, not an axiom that may be silently dropped. At the selected commit, [RadiusFivePruningHierarchy.lean](https://github.com/jconorgrogan/palomar-chair-verification/blob/048bb245b60abce79f1a2d0c82336ff8508ec752/src/SpectreFinite/RadiusFivePruningHierarchy.lean#L11-L15) defines `certifiedParentOccurrenceTheorem` by applying `parentFamily_occurrenceComplete`, and [NativeFinalAssembly/AllDimensions.lean](https://github.com/jconorgrogan/palomar-chair-verification/blob/048bb245b60abce79f1a2d0c82336ff8508ec752/src/NativeFinalAssembly/AllDimensions.lean#L16-L23) supplies it to the assembled endpoint. The same source theorem can be supplied to each planar factor here.

Each factor group is therefore finite by the planar lemma. The injective coordinate map places the dimension-4 group inside their finite product. This completes the dimension-4 finite-full-symmetry proof. No signed-permutation bound for this branch has been established by the argument.

## 6. Closure ledger and remaining formal work

**Supplied by inspected source declarations and proof bodies:** arbitrary-frame physical tiling interfaces; integral signed-permutation registration in compiler dimensions; proper registration for compiler coefficients; dimension coverage and world/period obligations for the chosen compiler witnesses; labeled global two-block splitting; existence of the required key pairing; actual complete planar factor tilings and full Cartesian consistency; arbitrary-isometry raw recovery; general Cartesian projection; planar period rigidity with the parent premise supplied by a source theorem; compactness and nonempty interior of the required bodies.

**New mathematical glue justified here, not newly compiled:** generic one-frame lifting for all symmetries; finite linear-image injection and cardinal bounds; the planar finite-symmetry theorem including locally finite intrinsic corners; the dimension-4 block symmetry lift and factor-group injection; and packaging all branches into a stronger all-dimensional endpoint.

**Not established by this audit:** compilation or external kernel checking of that new glue; an axiom audit of the selected full endpoint; independent re-verification of all deep geometric/certificate dependencies; a new registration/build claim; a dimension-4 numerical symmetry bound; or triviality of all symmetry groups.

## Conclusion

The exact source lemmas support a complete ordinary mathematical proof that the existing construction witnesses in every integer dimension d > 2 have finite full Euclidean symmetry groups in every admitted tiling. This excludes all infinite-order screw and glide symmetries, but does not assert trivial symmetry groups. The stronger all-dimensional Lean endpoint has not yet been implemented or checked in this review.

