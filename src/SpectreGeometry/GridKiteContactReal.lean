module

public import SpectreGeometry.GridKiteContactLogic
public import SpectreGeometry.GridKiteContacts

@[expose] public section


/-! Exact finite vertex contacts coincide with actual closed carrier intersections. -/
namespace SpectreGeometry
noncomputable section
open Set SpectreClusters SpectreClusters.BodyBSP HalfplaneCertificate GridKiteContact

def closedKiteContactCertificate : ClosedKiteContactCertificate :=
  ⟨finite_contact_or_separated,finite_facets_nonnegative⟩

/-- Closed real grid kites meet exactly when their finite vertex lists meet. -/
theorem cellContact_iff_gridKiteBody_inter (a b : Cell) :
    CellContact a b ↔ (gridKiteBody a ∩ gridKiteBody b).Nonempty :=
  cellContact_iff_gridKiteBody_inter_of_certificate closedKiteContactCertificate a b

/-- This includes corner-only contacts and needs no packing assumption. -/
theorem shapeContact_iff_placementKiteBody_inter (p q : HTPlacement) :
    ShapeContact (placementCells p) (placementCells q) ↔
      (placementKiteBody p ∩ placementKiteBody q).Nonempty := by
  constructor
  · rintro ⟨a,ha,b,hb,hc⟩
    obtain ⟨x,hxa,hxb⟩ := (cellContact_iff_gridKiteBody_inter a b).mp hc
    exact ⟨x,mem_iUnion.mpr ⟨a,mem_iUnion.mpr ⟨ha,hxa⟩⟩,
      mem_iUnion.mpr ⟨b,mem_iUnion.mpr ⟨hb,hxb⟩⟩⟩
  · rintro ⟨x,hxp,hxq⟩
    obtain ⟨a,ha,hxa⟩ := (show ∃ a ∈ placementCells p, x ∈ gridKiteBody a by
      simpa only [placementKiteBody,mem_iUnion,exists_prop] using hxp)
    obtain ⟨b,hb,hxb⟩ := (show ∃ b ∈ placementCells q, x ∈ gridKiteBody b by
      simpa only [placementKiteBody,mem_iUnion,exists_prop] using hxq)
    exact ⟨a,ha,b,hb,(cellContact_iff_gridKiteBody_inter a b).mpr ⟨x,hxa,hxb⟩⟩

end
end SpectreGeometry
