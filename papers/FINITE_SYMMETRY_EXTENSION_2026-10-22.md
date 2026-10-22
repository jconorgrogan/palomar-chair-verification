# Finite full symmetry in every integer dimension d > 2

## New work as of 2026-10-22

The existing source lemmas yield an ordinary mathematical proof that the construction witnesses in every integer dimension d > 2 have finite full Euclidean symmetry groups in every admitted tiling. In particular, no infinite-order screw or glide symmetry is possible. Trivial symmetry groups are not asserted.

**Status:** This is a mathematical extension, checked in a [separate AI mathematical/source review](FINITE_SYMMETRY_SOURCE_REVIEW_2026-10-22.md). The new deductions and stronger all-dimensional endpoint have not been implemented in Lean, compiled, independently kernel-checked, or registered in Palomar. The argument is conditional on the correctness of the cited source lemmas at immutable commit `048bb245b60abce79f1a2d0c82336ff8508ec752`; it does not independently re-verify their entire dependency closure. No Lean source or existing verification claim is changed by this documentation extension.

## 1. Scope and existing results

The selected all-dimensional endpoint explicitly asserts translation aperiodicity only:

- `PalomarAllDimensions.aperiodic_monotile_in_every_dimension` in [the exact selected endpoint](https://github.com/jconorgrogan/palomar-chair-verification/blob/048bb245b60abce79f1a2d0c82336ff8508ec752/src/PalomarAllDimensionsSolution.lean#L19-L43). It allows arbitrary Euclidean isometries, including reflections, requires coverage and disjoint interiors, and quantifies over every valid tiling.
- The [20 October status note](https://github.com/jconorgrogan/palomar-chair-verification/blob/main/verification/ALL_DIMENSIONS_STATUS_2026-10-20.md) records successful compilation of the selected complete Solution and exports, but unfinished statement comparison, external-kernel checks, and final-endpoint axiom audit. No all-dimensional registration is established.
- The older exact T5 body already has a finite-full-symmetry theorem with bound 3,840: `T5_finite_euclidean_symmetries`, `T5_euclidean_symmetry_card_le_3840`, and `T5_strong_aperiodic_bound`, in [the immutable finite-symmetry source](https://github.com/jconorgrogan/palomar-chair-verification/blob/5f5ceedee770b76c21e8f1105e5e4e3b84b8d676/SparseMonotiles/FiniteSymmetry.lean). The repository records this stronger T5 result as separately registered. It must not be confused with the newer recompiled 5D material or the all-dimensional endpoint.

Translation-only wording does not establish that a construction actually admits an infinite-order symmetry. It establishes a weaker theorem; a strengthening can still follow from its other proved structure.

## 2. Finite-normal lemma

Let T be a tiling of R^d and G its full group of Euclidean isometries preserving its tile collection. Suppose:

1. No nonzero translation preserves T.
2. There is a finite spanning set N of nonzero vectors such that the linear part A_g of every g in G permutes N.

Then G is finite. Indeed, g -> (n -> A_g n) is a homomorphism G -> Sym(N). An element in its kernel has A_g equal to the identity because N spans R^d, and therefore is a translation. Hypothesis 1 makes it the identity. Thus the homomorphism is injective and |G| <= |N|!.

For a globally registered cubic frame, N = {+/-e_1,...,+/-e_d}; the linear image belongs to the signed-permutation group B_d, giving |G| <= 2^d d!, rather than the coarser (2d)! bound.

Important qualifications:

- Use oriented normals, or include both signs. Permuting unoriented axis lines alone is not a faithful permutation representation: -I fixes every such line.
- The finite normal set must apply to the actual entire tiling and be preserved by its symmetries. A single prototype having finitely many faces does not imply that all its placements in a tiling have finitely many directions.
- Existence of one registered tiling is insufficient for a monotile theorem. Registration must be established for every admitted physical tiling.

Equivalently, the linear-part map G -> O(d) has kernel equal to the translation symmetries. If its image is finite and there are no translations, it is injective and G is finite. This proves finiteness of the whole group, not merely finite order of its individual elements. In particular, if A_g has finite order k then g^k is a translation, hence the identity; screw and glide symmetries of infinite order are excluded.

## 3. Why registered tile frames imply registered global symmetries

The following general frame-replacement lemma closes the possible hidden-self-symmetry loophole.

Let Q be a compact tile with nonempty interior and let H be a subgroup of Isom(R^d). Assume that for every admitted tiling and every choice of representatives p_X with p_X(Q)=X, all relative placements p_X^{-1} p_Y belong to H. Then for any fixed root tile A, every symmetry s satisfies p_A^{-1} s p_A in H.

Proof. Set B=s(A), and change only B's representative to p'_B=s p_A. It is still a representative of the same physical tile. Choose a tile C distinct from B; such a tile exists because a single compact set cannot cover R^d. Leave p'_C=p_C. Apply relative registration to the modified frame system with root C to get p_C^{-1} s p_A in H. Apply it to the original system to get p_A^{-1} p_C in H. Multiplying gives p_A^{-1} s p_A in H. This also works when B=A, so symmetries fixing the root tile setwise are covered.

The unchanged C is essential: it connects the altered representative back to the original root chart. This does not assume that the tile has trivial internal symmetry, nor that a selected frame assignment happens to be symmetry-equivariant.

The existing T5 proof implements precisely this method as `T5_symmetry_registered_in_root`, and then proves injectivity with `symmetry_eq_of_equal_displacements` and `T5_symmetries_embed_signed_permutations` in [FiniteSymmetry.lean](https://github.com/jconorgrogan/palomar-chair-verification/blob/5f5ceedee770b76c21e8f1105e5e4e3b84b8d676/SparseMonotiles/FiniteSymmetry.lean).

## 4. Application to d=3 and every d>=5

The current witnesses in these dimensions are not restricted to odd primes. They are instantiated finite-polycube compilers; product closure supplies the other dimensions.

The decisive geometric theorem is `ProductClosure.NativeCompiler.PhysicalTiling.global_integral_registration` in [GlobalRegistration.lean, lines 31-39](https://github.com/jconorgrogan/palomar-chair-verification/blob/048bb245b60abce79f1a2d0c82336ff8508ec752/src/ProductClosure/GlobalRegistration.lean#L31-L39). Its hypotheses are the actual arbitrary-isometry physical tiling, a nonempty finite cell carrier, and the compiler dimension condition. Its conclusion is `HasIntegralSignedPermutation (relativePlacement (f root) (f i))`, for arbitrary chosen placement representatives f and arbitrary root and i. Neither registration nor connectedness is assumed.

The unmarked-to-indexed bridge `unmarked_representatives_physicalTiling` in [NativeUnmarkedPeriods.lean](https://github.com/jconorgrogan/palomar-chair-verification/blob/048bb245b60abce79f1a2d0c82336ff8508ec752/src/ProductClosure/NativeUnmarkedPeriods.lean) applies to any representatives of the physical tile sets, exactly as required by the frame-replacement lemma.

Therefore the whole symmetry group of every such tiling is conjugate into the integral signed-permutation affine group. The existing universal translation-aperiodicity theorem makes its projection to B_d injective. Consequently:

For each of the current compiler witnesses in dimension d=3 or d>=5, every admitted physical tiling has finite full Euclidean symmetry group, with order at most 2^d d!.

The source even has the stronger `PhysicalTiling.compiled_global_proper_integral_registration` in [GlobalRegistration.lean, lines 114-129](https://github.com/jconorgrogan/palomar-chair-verification/blob/048bb245b60abce79f1a2d0c82336ff8508ec752/src/ProductClosure/GlobalRegistration.lean#L114-L129). `CompilerData.coefficients` always uses proper generators, so the same argument yields the sharper 2^(d-1)d! bound for these graph-compiled witnesses. This is a mathematical deduction, not a newly checked numerical endpoint. Do not silently replace the older T5 body's established bound by this bound for a different recompiled body.

Dimension coverage and period freeness are assembled by:

- `ProductClosure.three_certified` in [CertifiedDimensions.lean](https://github.com/jconorgrogan/palomar-chair-verification/blob/048bb245b60abce79f1a2d0c82336ff8508ec752/src/ProductClosure/CertifiedDimensions.lean).
- `ClarkSeed.every_dimension_ge_five_certified` and `exists_physical_aperiodic_monotile_of_ge_three_ne_four` in [PhysicalDimensions.lean](https://github.com/jconorgrogan/palomar-chair-verification/blob/048bb245b60abce79f1a2d0c82336ff8508ec752/src/ClarkSeed/PhysicalDimensions.lean).
- `CompilerData.physical_monotile` in [CompilerData.lean](https://github.com/jconorgrogan/palomar-chair-verification/blob/048bb245b60abce79f1a2d0c82336ff8508ec752/src/ProductClosure/CompilerData.lean), using the supplied `HasWorld` and `PeriodFree` proofs.

Thus no new geometric registration hypothesis is needed here. New formal glue is needed to generalize the T5 symmetry-lifting and injection lemmas and expose the stronger endpoint.

## 5. Planar finite-symmetry lemma

Let U be a tiling of R^2 by congruent copies of a bounded polygon P with nonempty interior and disjoint interiors. If U has no nonzero translation symmetry, its full symmetry group K is finite.

First, U is locally finite. Fix a radius r>0 and an open r-ball contained in the interior of P, and let D be the diameter of P. Each placed tile contains the corresponding r-ball, and these balls are pairwise disjoint. For tiles meeting a fixed compact set, their ball centers stay within a fixed bounded D-neighborhood of that set. Infinitely many disjoint fixed-radius balls cannot lie in a bounded set, by total boundedness or area. Therefore only finitely many tiles meet any compact set, and the union V of their finite sets of genuine intrinsic polygon corners is locally finite. Here an intrinsic corner is a geometric corner of the tile set, not an arbitrarily marked or subdivided point. Every physical tiling symmetry preserves V because it maps tile sets isometrically to tile sets and therefore preserves these intrinsic corners.

Let K+ be the orientation-preserving subgroup. Its linear parts are in SO(2), an abelian group. Thus the commutator of any two elements of K+ has identity linear part and is a translation. Translation freeness implies every such commutator is the identity: K+ is abelian.

If K+ is trivial there is nothing to prove. Otherwise choose a nonidentity element r of K+. Since it is not a nonzero translation, it is a nontrivial rotation with a unique center c. Every h in K+ commutes with r, hence r(h(c))=h(r(c))=h(c). Uniqueness of r's fixed point gives h(c)=c. All elements of K+ are consequently rotations about c.

Choose a genuine polygon vertex v not equal to c. Such a vertex exists because a bounded polygon with nonempty interior has more than one genuine corner. The orbit K+v lies in V intersected with the compact circle of radius |v-c| about c. This intersection is finite by local finiteness. A rotation about c is uniquely determined by the image of the noncentral point v, so h -> h(v) is injective. Hence K+ is finite. Finally [K:K+]<=2, so K is finite as well.

This explicitly proves finiteness of the whole group. It does not infer it just from each element having finite order.

## 6. The separate d=4 branch

The d=4 witness is `SpectreGeometry.polygonProductKeyBody`, not a cubic compiler. The cubic signed-permutation bound must not be asserted for it without another argument.

The inspected source provides all of the geometric hypotheses for a different finite-symmetry proof:

1. `physical_product_global_block_splitting` in [PolygonProductGlobalBlocks.lean, lines 81-106](https://github.com/jconorgrogan/palomar-chair-verification/blob/048bb245b60abce79f1a2d0c82336ff8508ec752/src/SpectreGeometry/PolygonProductGlobalBlocks.lean#L81-L106) supplies `ProductGlobalBlockSplitting f root` for arbitrary physical representatives f. It preserves the two intrinsic factor labels and makes both planar factors proper. Pairing is supplied by `exists_productKeyPairing T`, not imposed as a restriction on admitted tilings.
2. `physical_product_complete_cartesian_factors` in [PolygonProductFactorTilings.lean, lines 104-129](https://github.com/jconorgrogan/palomar-chair-verification/blob/048bb245b60abce79f1a2d0c82336ff8508ec752/src/SpectreGeometry/PolygonProductFactorTilings.lean#L104-L129) gives two genuine homochiral planar polygon tilings, with disjoint interiors, coverage, and every Cartesian pair realized as a raw tile. Local finiteness follows from the preceding compact-polygon packing argument, not from an unproved factor-grid assumption.
3. `physical_keyed_range_symmetry_preserves_raw` in [PolygonProductRawRangeSymmetry.lean, lines 28-53](https://github.com/jconorgrogan/palomar-chair-verification/blob/048bb245b60abce79f1a2d0c82336ff8508ec752/src/SpectreGeometry/PolygonProductRawRangeSymmetry.lean#L28-L53) proves equivariant recovery of the raw carrier family for an arbitrary ambient isometry preserving the actual unmarked keyed tile family.
4. `cartesian_family_symmetry_projects` in [CartesianFamilyProjection.lean, lines 50-77](https://github.com/jconorgrogan/palomar-chair-verification/blob/048bb245b60abce79f1a2d0c82336ff8508ec752/src/SpectreGeometry/CartesianFamilyProjection.lean#L50-L77) applies to arbitrary coordinatewise maps, not just translations, and says that a symmetry of the full Cartesian family projects to symmetries of both factor families.
5. `homochiral_physical_period_eq_zero_of_parent` in [PhysicalHierarchyFromParent.lean, lines 52-67](https://github.com/jconorgrogan/palomar-chair-verification/blob/048bb245b60abce79f1a2d0c82336ff8508ec752/src/SpectreGeometry/PhysicalHierarchyFromParent.lean#L52-L67) makes each factor translation-free. The parent-occurrence premise is supplied by `certifiedParentOccurrenceTheorem`, as explicitly assembled in [NativeFinalAssembly/AllDimensions.lean](https://github.com/jconorgrogan/palomar-chair-verification/blob/048bb245b60abce79f1a2d0c82336ff8508ec752/src/NativeFinalAssembly/AllDimensions.lean#L16-L23).

Fix an arbitrary admitted 4D tiling and its root chart. Apply the frame-replacement lemma with H equal to the labeled block product Isom+(R^2) x Isom+(R^2), embedded by the source's fixed product coordinates. Item 1 applies to every frame system, including the one with a single representative changed; the unchanged tile C aligns its labeled split with the original chart. Consequently every full physical symmetry is of the form (u,v) in that fixed chart. Factor swapping is excluded by the labeled splitting theorem, not silently ignored. If only an unlabeled split had been proved, an additional finite factor-swap extension would need to be handled instead.

The reverse inclusion needed in item 2, that each raw carrier is a product of its two factor tiles, is supplied by `ProductGlobalBlockSplitting.image_body` in [PolygonProductBlockCoordinates.lean, lines 33-41](https://github.com/jconorgrogan/palomar-chair-verification/blob/048bb245b60abce79f1a2d0c82336ff8508ec752/src/SpectreGeometry/PolygonProductBlockCoordinates.lean#L33-L41). The full equality is also recorded by `cartesian_family` in [PolygonProductCartesianConsistency.lean, lines 113-128](https://github.com/jconorgrogan/palomar-chair-verification/blob/048bb245b60abce79f1a2d0c82336ff8508ec752/src/SpectreGeometry/PolygonProductCartesianConsistency.lean#L113-L128).

Items 2 and 3 transport that symmetry to the full Cartesian family of the two fixed planar factor tilings. Item 4 then makes u and v genuine symmetries of their respective factor tilings. Each factor group is finite by item 5 and the planar lemma. Thus the map from the 4D symmetry group into their product is injective: the two coordinate maps determine the entire ambient isometry. The 4D group is therefore finite.

This proof covers every physical tiling, including symmetries fixing individual tiles; unrestricted reflections in the initial tiling definition have not been dropped. No numerical universal d=4 bound is claimed here.

## 7. Conclusion and formal work still required

Together, these arguments establish an ordinary mathematical finite-full-symmetry corollary for the existing witnesses in every integer dimension d>2, conditional only on the correctness of the already-stated source lemmas. They do not need a new geometric registration assumption. The missing formal developments are:

1. Generic one-frame symmetry lifting from arbitrary-frame relative registration.
2. Generic finite-point-group injection and cardinal bound.
3. The planar finite-symmetry lemma with its compact-polygon local-finiteness prerequisites.
4. Labeled-block symmetry lifting and Cartesian factor injection for d=4.
5. A stronger all-dimensional endpoint, followed by builds and appropriate verification.

The currently selected all-dimensional Lean endpoint does not state this strengthening. No claim is made that these new lemmas or the stronger endpoint have been implemented, compiled, independently kernel-checked, or registered.
