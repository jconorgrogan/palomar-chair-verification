module

public import SpectreGeometry.DeformationHomeomorphismTile
public import SpectreGeometry.DeformationHomeomorphismCover
public import SpectreGeometry.PhysicalDevelopmentPasting

@[expose] public section


/-! Construction from ordinary physical tiling data. All source triangle
coverage, common-face pasting, affine estimates, and global inversion are derived. -/
namespace SpectreGeometry.Deformation
noncomputable section
open Set

theorem affineEuclidean_realFormula (k j : Fin 12) (a b p : RealPoint) :
    affineEuclidean k j (euclideanCoordinates (a+rotate k (realVertex (triangle j).1)))
      (euclideanCoordinates (b+realDeformedVertex k (triangle j).1))
      (euclideanCoordinates (a+p)) = euclideanCoordinates (b+triangleAffine k j p) := by
  change coordinateLinearEquiv (b+realDeformedVertex k (triangle j).1) +
      coordinateLinearEquiv (matrixLinearMap k j (coordinateLinearEquiv.symm
        (coordinateLinearEquiv (a+p)-coordinateLinearEquiv (a+rotate k (realVertex (triangle j).1))))) = _
  rw [←map_sub,coordinateLinearEquiv.symm_apply_apply]
  have he : (a+p)-(a+rotate k (realVertex (triangle j).1)) = p-rotate k (realVertex (triangle j).1) := by abel
  rw [he,←map_add]
  change coordinateLinearEquiv _ = coordinateLinearEquiv _
  congr 1
  rw [triangleAffine_apply]
  abel

theorem sourceTriangle_subset_body (j : Fin 12) : sourceTriangle j ⊆ polygonBody := by
  rw [sourceTriangles_cover_polygonBody]
  exact subset_iUnion _ j

theorem sourceTriangle_compact (j : Fin 12) : IsCompact (sourceTriangle j) :=
  (Set.toFinite {realVertex (triangle j).1,realVertex (triangle j).2.1,
    realVertex (triangle j).2.2}).isCompact_convexHull ℝ

section Tiling
variable {ι : Type*} (f : ι → EPlane ≃ᵢ EPlane)
  (hdirect : ∀ i, DirectPlacement (f i))
  (hdisjoint : Pairwise fun i j =>
    Disjoint (interior (f i '' euclideanBody)) (interior (f j '' euclideanBody)))
  (hcover : ∀ x, ∃ i, x ∈ f i '' euclideanBody) (root : ι)

def tilingFrame (i : ι) : Fin 12 :=
  Classical.choose (homochiral_tiling_cyclic_frames f hdirect hdisjoint hcover root i)

theorem tilingFrame_spec (i : ι) : ∀ q : RealPoint,
    coordinateAction (f i) q = coordinateAction (f root) (rotate (tilingFrame f hdirect hdisjoint hcover root i) q) :=
  Classical.choose_spec (homochiral_tiling_cyclic_frames f hdirect hdisjoint hcover root i)

def tilingSourceOrigin (i : ι) : RealPoint := sourcePoint (f root) (f i 0)

def tilingTargetOrigin (i : ι) : RealPoint :=
  kiteCoordinateEmbedding (quadraticDevelopment ⟨sourcePoint (f root) (f i 0),
    homochiral_origin_mem_quadraticPlane f hdirect hdisjoint hcover root i⟩)

def physicalTilePL (i : ι) (x : EPlane) : RealPoint :=
  tilingTargetOrigin f hdirect hdisjoint hcover root i +
    tilePLMap (tilingFrame f hdirect hdisjoint hcover root i) (sourcePoint (f i) x)

theorem physicalTilePL_boundary (i : ι) (e : Fin 14) (t : ℝ) (ht : 0 ≤ t) (ht' : t ≤ 1) :
    physicalTilePL f hdirect hdisjoint hcover root i
      (f i (euclideanCoordinates (interpolate (realVertex e) (realVertex (next e)) t))) =
    interpolate (physicalVertexDevelopment (f root) (f i (euclideanVertex e)))
      (physicalVertexDevelopment (f root) (f i (euclideanVertex (next e)))) t := by
  have hi : sourcePoint (f i)
      (f i (euclideanCoordinates (interpolate (realVertex e) (realVertex (next e)) t))) =
      interpolate (realVertex e) (realVertex (next e)) t := by
    simp only [sourcePoint,(f i).symm_apply_apply,euclideanCoordinates.symm_apply_apply]
  rw [physicalTilePL,hi,tilePLMap_boundary _ _ _ ht ht',
    homochiral_vertex_development_formula f hdirect hdisjoint hcover root i _
      (tilingFrame_spec f hdirect hdisjoint hcover root i) e,
    homochiral_vertex_development_formula f hdirect hdisjoint hcover root i _
      (tilingFrame_spec f hdirect hdisjoint hcover root i) (next e)]
  change _ + interpolate _ _ t = interpolate (_+_) (_+_) t
  apply Prod.ext <;> simp only [tilingTargetOrigin,interpolate,Prod.fst_add,Prod.snd_add] <;> ring

def normalizedPLMap (x : EPlane) : EPlane :=
  euclideanCoordinates (physicalPastedMap f hcover
    (physicalTilePL f hdirect hdisjoint hcover root) (f root x))

def normalizedTriangle (ij : ι × Fin 12) : Set EPlane :=
  f root ⁻¹' (f ij.1 '' (euclideanCoordinates '' sourceTriangle ij.2))

theorem normalizedTriangle_closed (ij : ι × Fin 12) : IsClosed (normalizedTriangle f root ij) :=
  (((sourceTriangle_compact ij.2).image euclideanCoordinates.continuous).image (f ij.1).continuous).isClosed.preimage
    (f root).continuous

include hdisjoint in
theorem normalizedTriangle_local : LocallyFinite (normalizedTriangle f root) := by
  apply locallyFinite_finite_refinement (fun i => f root ⁻¹' (f i '' euclideanBody))
    (normalizedTriangle f root)
    ((CompactPacking.polygon_packing_locallyFinite f hdisjoint).preimage_continuous (f root).continuous)
  intro i j x hx
  exact (Set.image_mono (Set.image_mono (sourceTriangle_subset_body j))) hx

include hcover in
theorem normalizedTriangle_cover : ∀ x, ∃ ij, x ∈ normalizedTriangle f root ij := by
  intro x
  obtain ⟨i,p,hp,hpx⟩ := hcover (f root x)
  obtain ⟨q,hq,rfl⟩ := hp
  rw [sourceTriangles_cover_polygonBody] at hq
  obtain ⟨j,hj⟩ := mem_iUnion.mp hq
  exact ⟨(i,j),euclideanCoordinates q,⟨q,hj,rfl⟩,hpx⟩

theorem normalizedPLMap_on_triangle (i : ι) (j : Fin 12) (x : EPlane)
    (hx : x ∈ normalizedTriangle f root (i,j)) :
    normalizedPLMap f hdirect hdisjoint hcover root x =
      affineEuclidean (tilingFrame f hdirect hdisjoint hcover root i) j
        (euclideanCoordinates (tilingSourceOrigin f root i +
          rotate (tilingFrame f hdirect hdisjoint hcover root i) (realVertex (triangle j).1)))
        (euclideanCoordinates (tilingTargetOrigin f hdirect hdisjoint hcover root i +
          realDeformedVertex (tilingFrame f hdirect hdisjoint hcover root i) (triangle j).1)) x := by
  obtain ⟨y,⟨p,hp,rfl⟩,hpx⟩ := hx
  have himem : f root x ∈ f i '' euclideanBody :=
    ⟨euclideanCoordinates p,⟨p,sourceTriangle_subset_body j hp,rfl⟩,hpx⟩
  have hsource := relative_sourcePoint (f root) (f i)
    (tilingFrame f hdirect hdisjoint hcover root i) (tilingFrame_spec f hdirect hdisjoint hcover root i) p
  rw [hpx] at hsource
  simp only [sourcePoint,(f root).symm_apply_apply] at hsource
  have hx' : x = euclideanCoordinates (tilingSourceOrigin f root i +
      rotate (tilingFrame f hdirect hdisjoint hcover root i) p) := by
    exact (euclideanCoordinates.apply_symm_apply x).symm.trans (congrArg euclideanCoordinates hsource)
  rw [normalizedPLMap,physicalPastedMap_on_tile f hdirect hdisjoint hcover
    (physicalVertexDevelopment (f root)) (physicalTilePL f hdirect hdisjoint hcover root)
    (physicalTilePL_boundary f hdirect hdisjoint hcover root) i (f root x) himem]
  rw [physicalTilePL,←hpx]
  simp only [sourcePoint,(f i).symm_apply_apply,euclideanCoordinates.symm_apply_apply]
  rw [tilePLMap_on_triangle _ j p hp,sourceAffine_apply,hx',affineEuclidean_realFormula]

/-- A genuine normalized-plane homeomorphism, derived from arbitrary direct
isometric placements satisfying only coverage and interior packing. -/
def normalizedPhysicalHomeomorph : EPlane ≃ₜ EPlane :=
  homeomorphOfAffineCover (normalizedTriangle f root)
    (normalizedTriangle_local f hdisjoint root) (normalizedTriangle_closed f root)
    (normalizedTriangle_cover f hcover root)
    (fun ij => tilingFrame f hdirect hdisjoint hcover root ij.1) Prod.snd
    (fun ij => euclideanCoordinates (tilingSourceOrigin f root ij.1+
      rotate (tilingFrame f hdirect hdisjoint hcover root ij.1) (realVertex (triangle ij.2).1)))
    (fun ij => euclideanCoordinates (tilingTargetOrigin f hdirect hdisjoint hcover root ij.1+
      realDeformedVertex (tilingFrame f hdirect hdisjoint hcover root ij.1) (triangle ij.2).1))
    (normalizedPLMap f hdirect hdisjoint hcover root)
    (fun ij x hx => normalizedPLMap_on_triangle f hdirect hdisjoint hcover root ij.1 ij.2 x hx)

end Tiling
end
end SpectreGeometry.Deformation
