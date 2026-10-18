module

public import SpectreGeometry.ReverseMarkedInteriorAssembly
public import SpectreGeometry.ReverseMarkedAtlasOpenSides
public import SpectreGeometry.ReverseMarkedAtlasCorners
public import SpectreGeometry.ReverseMarkedNeighborIntersection
public import SpectreGeometry.ReverseSourceHexIncidence

@[expose] public section


namespace SpectreGeometry.ReverseExistence
noncomputable section
open Set SpectreClusters SpectreClusters.ReverseExistence SpectreFinite SpectreFinite.HexSearch
open ReverseClusterTriangulation ReverseLocalStarOccurrences ReverseFinitePL
open ReverseMeshEdgeIncidence ReverseClusterNeighborCells ReverseClusterNeighborBinding

/-- Precisely the finite inputs used by whole-plane marked-cluster assembly.
No global embedding or whole-plane coverage is assumed in these fields. -/
structure MarkedAtlasFiniteInputs : Prop where
  mesh : ∀ k : Fin 9, MarkedMeshCertificate k
  raw : ∀ big v, RawStarBinding big v
  rows : IncidentRowsCorrect
  interiorStar : ∀ big v, InteriorFastCertificate big v
  edgeIncidence : ∀ big i, EdgeIncidenceCertificate big i
  boundaryEdges : ∀ k i, BoundaryEdgeCertificate k i
  neighborChecked : ∀ i : Fin 35, configurationCheckedB (configuration i) = true
  neighborBinding : ∀ k r, MarkedConfigurationCertificate k r
  sideGeometry : ∀ i : Fin 217, SideGeometryCertificate i.val
  sideBinding : ∀ k d, SideGeometryBinding k d
  tripleGeometry : ∀ i : Fin 49, TripleGeometryCertificate i.val
  tripleBinding : ∀ k d, TripleGeometryBinding k d

namespace MarkedAtlasFiniteInputs
variable (C : MarkedAtlasFiniteInputs)

def localHomeomorphs (k : Fin 9) : sourceHexCarrier (0,0) ≃ₜ rawClusterBody (clusterOfMark k) :=
  (C.mesh k).markedClusterHomeomorph

theorem localBoundary (k : Fin 9) :
    MarkedBoundarySubintervalLaw k (fun x => (C.localHomeomorphs k x).val) :=
  (C.mesh k).markedClusterHomeomorph_boundary_law

def atlas (f : Position → State) (hf : GloballyLegal f) :
    LocallyFiniteCarrierAtlas RealPoint RealPoint Position :=
  markedCarrierAtlas C.localHomeomorphs f hf
    (marked_neighbor_agreement C.localHomeomorphs C.localBoundary f hf)

/-- Interior points remain ambient-interior points after both source and target
motions. This uses the proved finite mesh classification, not an assumption of
interior preservation for an arbitrary closed-carrier homeomorphism. -/
theorem placedChart_interior (f : Position → State) (hf : GloballyLegal f)
    (c : Position) (x : sourceHexCarrier c) (hx : x.val ∈ interior (sourceHexCarrier c)) :
    (markedPlacedChart C.localHomeomorphs f hf c x).val ∈
      interior (markedTargetCarrier f hf c) := by
  let S := axialMotionHomeomorph (f c).2 (integerPoint c)
  let H := sourceHexMotionHomeomorph (f c).2 c
  let x0 := H.symm x
  have hval : S x0.val = x.val := congrArg Subtype.val (H.apply_symm_apply x)
  have hx0 : x0.val ∈ interior (sourceHexCarrier (0,0)) := by
    have hi : S x0.val ∈ interior (S '' sourceHexCarrier (0,0)) := by
      rw [axialMotion_sourceHex_image,hval]
      exact hx
    rw [←S.image_interior] at hi
    obtain ⟨z,hz,he⟩ := hi
    have he' := S.injective he
    rwa [he'] at hz
  have hy := (C.mesh (f c).1).markedClusterHomeomorph_interior
    C.raw C.rows C.interiorStar C.edgeIncidence C.boundaryEdges x0 hx0
  let T := axialMotionHomeomorph (f c).2 (markedAnchor f hf c)
  change T ((C.mesh (f c).1).markedClusterHomeomorph x0).val ∈
    interior (T '' rawClusterBody (clusterOfMark (f c).1))
  rw [←T.image_interior]
  exact ⟨_,hy,rfl⟩

theorem interior_targetStar (f : Position → State) (hf : GloballyLegal f)
    (c : Position) (x : sourceHexCarrier c) (hx : x.val ∈ interior (sourceHexCarrier c)) :
    (C.atlas f hf).map x.val ∈ interior ((C.atlas f hf).targetStar x.val) := by
  have hs : markedTargetCarrier f hf c ⊆ (C.atlas f hf).targetStar x.val := by
    intro y hy
    exact mem_iUnion.mpr ⟨⟨c,x.property⟩,hy⟩
  rw [(C.atlas f hf).map_on c x.val x.property]
  exact interior_mono hs (C.placedChart_interior f hf c x hx)

/-- The finite source incidence trichotomy now yields every target-star
neighborhood required by the local-homeomorphism gluing theorem. -/
theorem all_targetStar_neighborhoods (f : Position → State) (hf : GloballyLegal f)
    (p : RealPoint) :
    (C.atlas f hf).map p ∈ interior ((C.atlas f hf).targetStar p) := by
  rcases sourceHex_incidence_classification p with ⟨c,hc,_⟩ | ⟨c,d,t,ht,hp,hi⟩ | ⟨c,d,hp,_⟩
  · exact C.interior_targetStar f hf c ⟨p,interior_subset hc⟩ hc
  · have hc : p ∈ sourceHexCarrier c := (hi c).mpr (Or.inl rfl)
    exact marked_open_side_targetStar_interior C.localHomeomorphs C.localBoundary f hf
      C.raw C.rows C.sideGeometry C.sideBinding C.neighborChecked C.neighborBinding
      c d t ht ⟨p,hc⟩ hp
  · rw [hp]
    exact marked_corner_targetStar_interior C.localHomeomorphs C.localBoundary f hf
      C.raw C.rows C.tripleGeometry C.tripleBinding c d

/-- All local finite inputs are sufficient for an actual whole-plane local
homeomorphism, with inverse compatibility checked on actual carrier overlaps. -/
theorem atlas_isLocalHomeomorph (f : Position → State) (hf : GloballyLegal f) :
    IsLocalHomeomorph (C.atlas f hf).map := by
  apply (C.atlas f hf).isLocalHomeomorph
  · exact marked_incident_inverse_agreement C.localHomeomorphs C.localBoundary f hf
      (marked_neighbor_intersection_of_certificates C.neighborChecked C.neighborBinding f hf)
  · exact C.all_targetStar_neighborhoods f hf

end MarkedAtlasFiniteInputs
end
end SpectreGeometry.ReverseExistence
