module

public import SpectreGeometry.ReverseMarkedAtlasLocalHomeomorphism
public import SpectreGeometry.ReverseGlobalHomeomorphism
public import SpectreGeometry.ReverseSourceHexInteriorDisjoint
public import SpectreGeometry.ReverseCarrierLocalFiniteRefinement

@[expose] public section


namespace SpectreGeometry.ReverseExistence.MarkedAtlasFiniteInputs
noncomputable section
open Set SpectreClusters SpectreFinite SpectreFinite.HexSearch ReverseClusterTriangulation

variable (C : MarkedAtlasFiniteInputs) (f : Position → State) (hf : GloballyLegal f)
include C

/-- The finite marked-cluster inputs produce a genuine plane homeomorphism.
The properness proof uses the independently constructed anchor homeomorphism
and the proved uniform distance bound, not a tiling premise. -/
def wholePlaneHomeomorph : RealPoint ≃ₜ RealPoint :=
  planeHomeomorphOfProperLocalHomeomorph (C.atlas f hf).map
    (markedCarrierAtlas_isProperMap C.localHomeomorphs f hf
      (marked_neighbor_agreement C.localHomeomorphs C.localBoundary f hf))
    (C.atlas_isLocalHomeomorph f hf)

@[simp] theorem wholePlaneHomeomorph_apply (p : RealPoint) :
    C.wholePlaneHomeomorph f hf p = (C.atlas f hf).map p := rfl

/-- The plane homeomorphism sends each whole source hexagon onto exactly its
literal placed marked target cluster. -/
theorem wholePlaneHomeomorph_image_source (c : Position) :
    C.wholePlaneHomeomorph f hf '' sourceHexCarrier c = markedTargetCarrier f hf c :=
  (C.atlas f hf).map_image_source c

/-- The actual target cluster cover is locally finite by the plane homeomorphism. -/
theorem marked_carriers_locallyFinite : LocallyFinite (markedTargetCarrier f hf) := by
  have h := homeomorph_images_locallyFinite (C.wholePlaneHomeomorph f hf)
    sourceHexCarrier sourceHex_locallyFinite
  simpa only [C.wholePlaneHomeomorph_image_source f hf] using h

/-- Coverage of the whole plane is a conclusion of global inversion. -/
theorem marked_carriers_cover (p : RealPoint) :
    ∃ c : Position, p ∈ markedTargetCarrier f hf c := by
  obtain ⟨x,rfl⟩ := (C.wholePlaneHomeomorph f hf).surjective p
  obtain ⟨c,hc⟩ := sourceHex_plane_cover x
  refine ⟨c,?_⟩
  rw [←C.wholePlaneHomeomorph_image_source f hf c]
  exact ⟨x,hc,rfl⟩

/-- Distinct literal marked carriers have disjoint ordinary ambient interiors. -/
theorem marked_carriers_interiors_disjoint :
    Pairwise (fun c d : Position => Disjoint (interior (markedTargetCarrier f hf c))
      (interior (markedTargetCarrier f hf d))) := by
  intro c d hcd
  rw [←C.wholePlaneHomeomorph_image_source f hf c,
    ←C.wholePlaneHomeomorph_image_source f hf d,
    ←(C.wholePlaneHomeomorph f hf).image_interior,
    ←(C.wholePlaneHomeomorph f hf).image_interior]
  exact Set.disjoint_image_of_injective (C.wholePlaneHomeomorph f hf).injective
    (sourceHex_interiors_disjoint c d hcd)

end
end SpectreGeometry.ReverseExistence.MarkedAtlasFiniteInputs
