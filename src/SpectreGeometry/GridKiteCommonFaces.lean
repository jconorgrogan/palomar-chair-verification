module

public import SpectreGeometry.GridKiteFaceData
public import SpectreGeometry.GridKiteContactReal
public import SpectreGeometry.ReverseClusterTriangulationFacesReal

@[expose] public section


/-! Exact common faces for all genuine grid kites. The finite stencil is
complete by the accepted contact classification, including corner contacts. -/
namespace SpectreGeometry
noncomputable section
open Set SpectreClusters SpectreClusters.BodyBSP ReverseClusterTriangulation GridKiteFace

theorem cellVertices_translateCell (t : SpectreClusters.Point) (c : Cell) :
    cellVertices (translateCell t c) = (cellVertices c).map (SpectreClusters.add (lattice t)) := by
  simp only [cellVertices,translateCell,lattice_add,List.map_map]
  apply List.map_congr_left
  intro p hp
  exact SpectreClusters.add_assoc _ _ _

theorem integerVertexSet_map_add (t : SpectreClusters.Point) (vs : List SpectreClusters.Point) :
    integerVertexSet (vs.map (SpectreClusters.add t)) =
      (fun x : RealPoint => integerPoint t+x) '' integerVertexSet vs := by
  ext x
  constructor
  · rintro ⟨v,hv,rfl⟩
    obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hv
    exact ⟨integerPoint u,⟨u,hu,rfl⟩,(integerPoint_add t u).symm⟩
  · rintro ⟨y,⟨u,hu,rfl⟩,rfl⟩
    exact ⟨SpectreClusters.add t u,List.mem_map.mpr ⟨u,hu,rfl⟩,integerPoint_add t u⟩

theorem integerVertexSet_translateCell (t : SpectreClusters.Point) (c : Cell) :
    integerVertexSet (cellVertices (translateCell t c)) =
      (Homeomorph.addLeft (integerPoint (lattice t))) '' integerVertexSet (cellVertices c) := by
  rw [cellVertices_translateCell,integerVertexSet_map_add]
  rfl

theorem gridKiteBody_translateCell (t : SpectreClusters.Point) (c : Cell) :
    gridKiteBody (translateCell t c) =
      (Homeomorph.addLeft (integerPoint (lattice t))) '' gridKiteBody c := by
  change convexHull ℝ (integerVertexSet (cellVertices (translateCell t c))) =
    (Homeomorph.addLeft (integerPoint (lattice t))) '' convexHull ℝ (integerVertexSet (cellVertices c))
  rw [integerVertexSet_translateCell]
  exact ((AffineEquiv.constVAdd ℝ RealPoint (integerPoint (lattice t))).toAffineMap.image_convexHull _).symm

private theorem gridKite_faces_translate (t : SpectreClusters.Point) (a b : Cell)
    (h : gridKiteBody a ∩ gridKiteBody b =
      convexHull ℝ (integerVertexSet (cellVertices a) ∩ integerVertexSet (cellVertices b)) ∧
      Disjoint (interior (gridKiteBody a)) (interior (gridKiteBody b))) :
    gridKiteBody (translateCell t a) ∩ gridKiteBody (translateCell t b) =
      convexHull ℝ (integerVertexSet (cellVertices (translateCell t a)) ∩
        integerVertexSet (cellVertices (translateCell t b))) ∧
      Disjoint (interior (gridKiteBody (translateCell t a)))
        (interior (gridKiteBody (translateCell t b))) := by
  let H := Homeomorph.addLeft (integerPoint (lattice t))
  have hHull (s : Set RealPoint) : H '' convexHull ℝ s = convexHull ℝ (H '' s) :=
    (AffineEquiv.constVAdd ℝ RealPoint (integerPoint (lattice t))).toAffineMap.image_convexHull s
  constructor
  · rw [gridKiteBody_translateCell,gridKiteBody_translateCell,
      integerVertexSet_translateCell,integerVertexSet_translateCell]
    change H '' gridKiteBody a ∩ H '' gridKiteBody b =
      convexHull ℝ (H '' integerVertexSet (cellVertices a) ∩ H '' integerVertexSet (cellVertices b))
    rw [←Set.image_inter H.injective,←Set.image_inter H.injective,h.1,hHull]
  · rw [gridKiteBody_translateCell,gridKiteBody_translateCell]
    change Disjoint (interior (H '' gridKiteBody a)) (interior (H '' gridKiteBody b))
    rw [←H.image_interior,←H.image_interior]
    exact (Set.disjoint_image_iff H.injective).mpr h.2

private theorem gridKite_contact_faces (a b : Cell) (hne : a ≠ b) (hc : CellContact a b) :
    gridKiteBody a ∩ gridKiteBody b =
      convexHull ℝ (integerVertexSet (cellVertices a) ∩ integerVertexSet (cellVertices b)) ∧
      Disjoint (interior (gridKiteBody a)) (interior (gridKiteBody b)) := by
  let a0 : Cell := ⟨(0,0),a.sector⟩
  let b0 : Cell := relativeCell a b
  have ha0 : translateCell a.center a0 = a := by
    cases a
    simp [a0,translateCell,SpectreClusters.add]
  have hb0 : translateCell a.center b0 = b := translate_relative a b
  have hne0 : a0 ≠ b0 := by
    intro heq
    apply hne
    calc
      a = translateCell a.center a0 := ha0.symm
      _ = translateCell a.center b0 := congrArg (translateCell a.center) heq
      _ = b := hb0
  have hc0 : CellContact a0 b0 := (contact_relative_iff a b).mp hc
  have hm : b0 ∈ localContacts a.sector := (mem_localContacts_iff a.sector b0).mpr hc0
  have hcert := local_contact_faces a.sector b0 hm hne0
  have hfaces := supportsPacketFaceB_sound (kitePacket a0) (kitePacket b0)
    (summedPacketSeparator (kitePacket a0) (kitePacket b0)) hcert
  change gridKiteBody a0 ∩ gridKiteBody b0 =
      convexHull ℝ (integerVertexSet (cellVertices a0) ∩ integerVertexSet (cellVertices b0)) ∧
      Disjoint (interior (gridKiteBody a0)) (interior (gridKiteBody b0)) at hfaces
  have htrans := gridKite_faces_translate a.center a0 b0 hfaces
  simpa only [ha0,hb0] using htrans

/-- Exact intersection, including equality, edge contact, corner contact and disjointness. -/
theorem gridKiteBody_inter_commonFace (a b : Cell) :
    gridKiteBody a ∩ gridKiteBody b =
      convexHull ℝ (integerVertexSet (cellVertices a) ∩ integerVertexSet (cellVertices b)) := by
  by_cases hne : a = b
  · subst b
    rw [inter_self,inter_self]
    rfl
  by_cases hc : CellContact a b
  · exact (gridKite_contact_faces a b hne hc).1
  · apply Subset.antisymm
    · rintro x ⟨hxa,hxb⟩
      exact (hc ((cellContact_iff_gridKiteBody_inter a b).mpr ⟨x,hxa,hxb⟩)).elim
    · intro x hx
      exact ⟨convexHull_mono inter_subset_left hx,convexHull_mono inter_subset_right hx⟩

/-- Distinct genuine grid kites have disjoint ordinary real-plane interiors. -/
theorem gridKiteBody_interior_disjoint (a b : Cell) (hne : a ≠ b) :
    Disjoint (interior (gridKiteBody a)) (interior (gridKiteBody b)) := by
  by_cases hc : CellContact a b
  · exact (gridKite_contact_faces a b hne hc).2
  · apply Set.disjoint_left.mpr
    intro x hxa hxb
    exact hc ((cellContact_iff_gridKiteBody_inter a b).mpr
      ⟨x,interior_subset hxa,interior_subset hxb⟩)

end
end SpectreGeometry
