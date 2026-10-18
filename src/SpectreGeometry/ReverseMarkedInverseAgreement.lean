module

public import SpectreGeometry.ReverseMarkedForwardAgreement

@[expose] public section


namespace SpectreGeometry.ReverseExistence
noncomputable section
open Set SpectreClusters SpectreClusters.ReverseExistence SpectreFinite SpectreFinite.HexSearch
open ReverseClusterTriangulation

variable (hlocal : ∀ k : Fin 9, sourceHexCarrier (0,0) ≃ₜ rawClusterBody (clusterOfMark k))
variable (hboundary : ∀ k, MarkedBoundarySubintervalLaw k (fun x => (hlocal k x).val))
variable (f : Position → State) (hf : GloballyLegal f)

/-- Exact neighbor carrier intersections, expressed in the parameter interface
needed to identify the two local inverse values. -/
def MarkedNeighborIntersection : Prop :=
  ∀ c d y, y ∈ markedTargetCarrier f hf c →
    y ∈ markedTargetCarrier f hf (sourceHexNeighbor c d) →
      ∃ t ∈ Icc (0:ℝ) 1, PathParameter (realDevelopedPath f hf c d) t y

/-- Only charts incident to a common source point need inverse compatibility. -/
theorem marked_incident_inverse_agreement (hinter : MarkedNeighborIntersection f hf) :
    (markedCarrierAtlas hlocal f hf
      (marked_neighbor_agreement hlocal hboundary f hf)).IncidentInverseAgree := by
  intro x c c' hxc hxc' y hy hy'
  by_cases he : c'=c
  · subst c'
    rfl
  obtain ⟨d,rfl⟩ := sourceHex_intersection_neighbor he ⟨x,hxc,hxc'⟩
  obtain ⟨t,ht,hyPath⟩ := hinter c d y hy hy'
  let p := AffineMap.lineMap (sourceHexCornerAt c d) (sourceHexCornerAt c (d+1)) t
  have hp : p ∈ sourceHexCarrier c ∩ sourceHexCarrier (sourceHexNeighbor c d) := by
    rw [sourceHex_neighbor_intersection_segment]
    exact lineMap_mem_segment ℝ _ _ ht
  have hparam := markedPlacedChart_pathParameter hlocal hboundary f hf c d t ht ⟨p,hp.1⟩ rfl
  have hF : (markedPlacedChart hlocal f hf c ⟨p,hp.1⟩).val = y := hparam.unique hyPath
  have hF' : (markedPlacedChart hlocal f hf (sourceHexNeighbor c d) ⟨p,hp.2⟩).val = y :=
    (marked_neighbor_agreement hlocal hboundary f hf c d p hp.1 hp.2).symm.trans hF
  have hleft : (markedPlacedChart hlocal f hf c).symm ⟨y,hy⟩ = ⟨p,hp.1⟩ := by
    apply (markedPlacedChart hlocal f hf c).injective
    rw [Homeomorph.apply_symm_apply]
    exact Subtype.ext hF.symm
  have hright : (markedPlacedChart hlocal f hf (sourceHexNeighbor c d)).symm ⟨y,hy'⟩ =
      ⟨p,hp.2⟩ := by
    apply (markedPlacedChart hlocal f hf (sourceHexNeighbor c d)).injective
    rw [Homeomorph.apply_symm_apply]
    exact Subtype.ext hF'.symm
  change ((markedPlacedChart hlocal f hf c).symm ⟨y,hy⟩).val =
    ((markedPlacedChart hlocal f hf (sourceHexNeighbor c d)).symm ⟨y,hy'⟩).val
  rw [hleft,hright]

end
end SpectreGeometry.ReverseExistence
