module

public import SpectreGeometry.GridPhysicalCoordinates
public import SpectreGeometry.GridFieldExtraction
public import SpectreGeometry.PhysicalDevelopedLattice
public import SpectreGeometry.DeformationHomeomorphismTransport

@[expose] public section


/-! Realization in the literal common kite grid, from an arbitrary genuine
homochiral physical tiling. No lattice, cell-coverage or recognition input occurs. -/
namespace SpectreGeometry
noncomputable section
open Set SpectreClusters SpectreClusters.DeformedLiteralBinding SpectreGeometry.Deformation

theorem gridKiteBody_moved (k : Turn) (t : SpectreClusters.Point) (c : Cell) :
    gridKiteBody (moveCell k t c) = gridMotion k (integerPoint (lattice t)) '' gridKiteBody c := by
  rw [gridKiteBody,cellVertices_moved,integerHull_image_motion]
  rfl

theorem placementKiteBody_image_literal (p : HTPlacement) :
    placementKiteBody p = gridMotion p.turn (integerPoint (lattice p.center)) '' literalKiteBody p.kind := by
  ext x
  simp only [placementKiteBody,placementCells,mem_iUnion,List.mem_map]
  constructor
  · rintro ⟨c,⟨d,hd,rfl⟩,hx⟩
    rw [gridKiteBody_moved] at hx
    obtain ⟨y,hy,rfl⟩ := hx
    exact ⟨y,mem_iUnion.mpr ⟨d,mem_iUnion.mpr ⟨hd,hy⟩⟩,rfl⟩
  · rintro ⟨y,hy,rfl⟩
    obtain ⟨d,hd⟩ := mem_iUnion.mp hy
    obtain ⟨hd,hy⟩ := mem_iUnion.mp hd
    refine ⟨moveCell p.turn p.center d,⟨d,hd,rfl⟩,?_⟩
    rw [gridKiteBody_moved]
    exact ⟨y,hy,rfl⟩

section Tiling
variable {ι : Type*} (f : ι → EPlane ≃ᵢ EPlane)
  (hdirect : ∀ i, DirectPlacement (f i))
  (hdisjoint : Pairwise fun i j =>
    Disjoint (interior (f i '' euclideanBody)) (interior (f j '' euclideanBody)))
  (hcover : ∀ x, ∃ i, x ∈ f i '' euclideanBody) (root : ι)

set_option backward.privateInPublic true in
theorem anchor_registered (i : ι) :
    physicalDevelopedAnchor f hdirect hdisjoint hcover root
      (tilingFrame f hdirect hdisjoint hcover root) i-
    physicalDevelopedAnchor f hdirect hdisjoint hcover root
      (tilingFrame f hdirect hdisjoint hcover root) root ∈ rationalKiteCenterLattice :=
  homochiral_developed_anchors_lattice f hdirect hdisjoint hcover root
    (tilingFrame f hdirect hdisjoint hcover root)
    (tilingFrame_spec f hdirect hdisjoint hcover root) i

set_option backward.privateInPublic true in
def tilingLatticeCoordinate (i : ι) : SpectreClusters.Point :=
  Classical.choose (anchor_registered f hdirect hdisjoint hcover root i)

theorem tilingLatticeCoordinate_spec (i : ι) :
    kiteCenterMap (tilingLatticeCoordinate f hdirect hdisjoint hcover root i) =
    physicalDevelopedAnchor f hdirect hdisjoint hcover root
      (tilingFrame f hdirect hdisjoint hcover root) i-
    physicalDevelopedAnchor f hdirect hdisjoint hcover root
      (tilingFrame f hdirect hdisjoint hcover root) root :=
  Classical.choose_spec (anchor_registered f hdirect hdisjoint hcover root i)

def tilingGridPlacement (i : ι) : HTPlacement :=
  ⟨literalKind (tilingFrame f hdirect hdisjoint hcover root i),
   literalTurn (tilingFrame f hdirect hdisjoint hcover root i),
   reflectCenter (tilingLatticeCoordinate f hdirect hdisjoint hcover root i)⟩

def tilingGridOrigin : RealPoint :=
  kiteCoordinateEmbedding (physicalDevelopedAnchor f hdirect hdisjoint hcover root
    (tilingFrame f hdirect hdisjoint hcover root) root)

theorem tilingGrid_anchor_real (i : ι) :
    tilingGridOrigin f hdirect hdisjoint hcover root + gridEmbeddingLinear
      (integerPoint (lattice (tilingLatticeCoordinate f hdirect hdisjoint hcover root i))) =
    tilingTargetOrigin f hdirect hdisjoint hcover root i + gridEmbeddingLinear
      (integerPoint (deformedOffset (tilingFrame f hdirect hdisjoint hcover root i))) := by
  rw [←gridEmbedding_centerMap,tilingGridOrigin,←kiteCoordinateEmbedding_add,
    tilingLatticeCoordinate_spec]
  have he (a b : ℚ × ℚ) : a+(b-a)=b := by abel
  rw [he,physicalDevelopedAnchor,kiteCoordinateEmbedding_add,gridEmbedding_integerPoint]
  rfl

theorem tilingGrid_point_formula (i : ι) (p : RealPoint) :
    gridPhysicalHomeomorph (tilingGridOrigin f hdirect hdisjoint hcover root)
      (gridMotion (tilingGridPlacement f hdirect hdisjoint hcover root i).turn
        (integerPoint (lattice (tilingGridPlacement f hdirect hdisjoint hcover root i).center)) p) =
    euclideanCoordinates (tilingTargetOrigin f hdirect hdisjoint hcover root i+
      literalTargetAffine (tilingFrame f hdirect hdisjoint hcover root i) p) := by
  rw [gridPhysicalHomeomorph_apply,gridMotion_apply]
  apply congrArg euclideanCoordinates
  simp only [tilingGridPlacement]
  rw [map_add gridReflectionLinear,map_add gridEmbeddingLinear,gridReflection_reflectCenter,
    ←_root_.add_assoc,tilingGrid_anchor_real]
  change (tilingTargetOrigin f hdirect hdisjoint hcover root i+
    gridEmbeddingLinear (integerPoint (deformedOffset (tilingFrame f hdirect hdisjoint hcover root i))))+
    gridEmbeddingLinear (gridReflectionLinear (gridRotation
      (literalTurn (tilingFrame f hdirect hdisjoint hcover root i)) p)) =
    tilingTargetOrigin f hdirect hdisjoint hcover root i+
    gridEmbeddingLinear (gridReflectionLinear (integerPoint
      (reflectPoint (deformedOffset (tilingFrame f hdirect hdisjoint hcover root i)))+
      gridRotation (literalTurn (tilingFrame f hdirect hdisjoint hcover root i)) p))
  rw [map_add gridReflectionLinear,map_add gridEmbeddingLinear,gridReflection_integerPoint,
    reflectPoint_involutive,_root_.add_assoc]

/-- The common coordinate homeomorphism maps actual literal kite unions onto
exactly the physical developed carriers. -/
theorem tilingGrid_image_body (i : ι) :
    gridPhysicalHomeomorph (tilingGridOrigin f hdirect hdisjoint hcover root) ''
      placementKiteBody (tilingGridPlacement f hdirect hdisjoint hcover root i) =
    developedPlacedBody f hdirect hdisjoint hcover root i := by
  rw [placementKiteBody_image_literal,developedPlacedBody,targetBody_eq_literalKiteBody,
    Set.image_image,Set.image_image]
  apply Set.image_congr
  intro p hp
  exact tilingGrid_point_formula f hdirect hdisjoint hcover root i p

/-- Both real coverage and disjoint interiors of literal registered kite unions
are consequences of only ordinary homochiral physical coverage and packing. -/
theorem homochiral_literal_kite_tiling :
    (∀ x : RealPoint, ∃ i, x ∈ placementKiteBody (tilingGridPlacement f hdirect hdisjoint hcover root i)) ∧
    Pairwise (fun i j => Disjoint
      (interior (placementKiteBody (tilingGridPlacement f hdirect hdisjoint hcover root i)))
      (interior (placementKiteBody (tilingGridPlacement f hdirect hdisjoint hcover root j)))) := by
  have ht := homochiral_developed_plane_tiling f hdirect hdisjoint hcover root
  let G := gridPhysicalHomeomorph (tilingGridOrigin f hdirect hdisjoint hcover root)
  have himage (i : ι) : G.symm '' developedPlacedBody f hdirect hdisjoint hcover root i =
      placementKiteBody (tilingGridPlacement f hdirect hdisjoint hcover root i) := by
    rw [←tilingGrid_image_body f hdirect hdisjoint hcover root i]
    exact G.symm_image_image _
  exact tiling_transport G.symm
    (developedPlacedBody f hdirect hdisjoint hcover root)
    (fun i => placementKiteBody (tilingGridPlacement f hdirect hdisjoint hcover root i))
    ht.1 ht.2 himage

def physicalGridField : Cell → HTPlacement :=
  fieldOfKiteTiling (tilingGridPlacement f hdirect hdisjoint hcover root)
    (homochiral_literal_kite_tiling f hdirect hdisjoint hcover root).1

theorem physicalGridField_valid :
    ValidGridField (physicalGridField f hdirect hdisjoint hcover root) :=
  fieldOfKiteTiling_valid _ _ (homochiral_literal_kite_tiling f hdirect hdisjoint hcover root).2

/-- Every original tile is genuinely represented as an owned placement in the
extracted field, preserving the physical-to-combinatorial correspondence. -/
theorem physicalGridField_owns (i : ι) :
    RootOwned (physicalGridField f hdirect hdisjoint hcover root)
      (tilingGridPlacement f hdirect hdisjoint hcover root i) := by
  intro c hc
  let p := tilingGridPlacement f hdirect hdisjoint hcover root
  let ht := homochiral_literal_kite_tiling f hdirect hdisjoint hcover root
  have he : probeOwner p ht.1 c = i := by
    by_contra hn
    exact Set.disjoint_left.mp (ht.2 hn)
      (gridProbe_interior_placement _ c (probeOwner_contains p ht.1 c))
      (gridProbe_interior_placement _ c hc)
  exact congrArg p he

include f hdirect hdisjoint hcover root in
/-- An actual valid grid field extracted from every homochiral physical tiling;
there is no remaining physical-to-grid registration or recognition hypothesis. -/
theorem homochiral_exists_validGridField : ∃ g : Cell → HTPlacement, ValidGridField g := by
  have ht := homochiral_literal_kite_tiling f hdirect hdisjoint hcover root
  exact exists_validGridField_of_kite_tiling
    (tilingGridPlacement f hdirect hdisjoint hcover root) ht.1 ht.2

end Tiling
end
end SpectreGeometry
