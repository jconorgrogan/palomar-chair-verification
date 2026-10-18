module

public import SpectreGeometry.ReverseClusterTriangulationFacesAssemblyReal

@[expose] public section

namespace SpectreGeometry.ReverseClusterTriangulation
noncomputable section
open Set

/-- An existential row interface avoids expanding the entire quadratic code
    table while assembling the independently checked bounded finite rows. -/
theorem familyHasFaces_of_row_exists (ps : List PolygonPacket)
    (hc : ∀ i : Fin ps.length, ∃ codes,
      packetFaceRowB (ps.getD i.val default) (ps.take i.val) codes = true) :
    FamilyHasFaces ps := by
  intro i j hij
  have hn : i.val ≠ j.val := fun h => hij (Fin.ext h)
  rcases lt_or_gt_of_ne hn with h | h
  · obtain ⟨codes,hcodes⟩ := hc j
    obtain ⟨c,hc'⟩ := packetFaceRowB_at (ps.getD j.val default) (ps.take j.val)
      codes hcodes (ps.getD i.val default)
      (getD_mem_take_of_lt ps default i.val j.val i.isLt h)
    simpa only [inter_comm,disjoint_comm] using
      pairPacketsFaceB_sound (ps.getD j.val default) (ps.getD i.val default) c hc'
  · obtain ⟨codes,hcodes⟩ := hc i
    obtain ⟨c,hc'⟩ := packetFaceRowB_at (ps.getD i.val default) (ps.take i.val)
      codes hcodes (ps.getD j.val default)
      (getD_mem_take_of_lt ps default j.val i.val j.isLt h)
    exact pairPacketsFaceB_sound (ps.getD i.val default) (ps.getD j.val default) c hc'

end
end SpectreGeometry.ReverseClusterTriangulation
