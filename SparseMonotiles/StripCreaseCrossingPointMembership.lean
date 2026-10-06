module

public import SparseMonotiles.StripCreaseCrossingLiteralExclusion
public import SparseMonotiles.StripCreaseCrossingStrict

@[expose] public section

/-! # Actual incident membership at the new strip-crossing point -/
namespace SparseMonotiles
open Set Canonical

theorem T5_literal_pruned_crease_mem
    {k : KeyData 5} (hk : k ∈ keys5) (q : Contact.Pose 5)
    (hq : keySolid k = q.euclidean '' referenceSolid5) (i : Fin 4) (si : Bool)
    (a : PyramidSideBoundaryIndex i) {p : Point 5}
    (hi : posedHalfspaceSlack5 q (.inr (i,si)) p = 0)
    (ha : posedHalfspaceSlack5 q (pyramidFacetHalfspaceIndex (pyramidSideBoundaryFacet i a)) p = 0)
    (ho : ∀ l : PyramidHalfspaceIndex 4, l ≠ .inr (i,si) →
      l ≠ pyramidFacetHalfspaceIndex (pyramidSideBoundaryFacet i a) → 0 < posedHalfspaceSlack5 q l p) :
    p ∈ T5 := by
  cases a with
  | none =>
      have hl := T5_literal_base_side_crease_germ hk q hq i si ha hi (fun l hlb hls => ho l hls hlb)
      apply hl.mem_iff.mpr
      cases k.bump <;> simp [closedBaseSideWedge,hi,ha,pyramidFacetHalfspaceIndex,pyramidSideBoundaryFacet] at *
  | some a =>
      rcases a with ⟨j,sj⟩
      have hl := T5_literal_side_side_crease_germ hk q hq i j.val si sj hi ha ho
      apply hl.mem_iff.mpr
      cases k.bump <;> simp [closedSideSideWedge,hi,ha,pyramidFacetHalfspaceIndex,pyramidSideBoundaryFacet] at *

theorem T5_carrierFacetEdgeStrip_mem (f : Contact.Facet 5)
    (howner : Contact.IsChairCell f.cell) (hexposed : ¬ Contact.IsChairCell f.neighbor)
    (j : Fin 5) (hj : j ≠ f.axis) (upper : Bool) {p : Point 5}
    (hp : p ∈ carrierFacetEdgeStrip f j upper) : p ∈ T5 := by
  apply (T5_carrierFacetEdgeStrip_halfspace f howner hexposed j hj upper hp).mem_iff.mpr
  cases h : f.positive <;> simp [Contact.Facet.inwardHalfspace,h,hp.1.1]

#print axioms T5_literal_pruned_crease_mem
#print axioms T5_carrierFacetEdgeStrip_mem

theorem T7_literal_pruned_crease_mem
    {k : KeyData 7} (hk : k ∈ keys7) (q : Contact.Pose 7)
    (hq : keySolid k = q.euclidean '' referenceSolid7) (i : Fin 6) (si : Bool)
    (a : PyramidSideBoundaryIndex i) {p : Point 7}
    (hi : posedHalfspaceSlack7 q (.inr (i,si)) p = 0)
    (ha : posedHalfspaceSlack7 q (pyramidFacetHalfspaceIndex (pyramidSideBoundaryFacet i a)) p = 0)
    (ho : ∀ l : PyramidHalfspaceIndex 6, l ≠ .inr (i,si) →
      l ≠ pyramidFacetHalfspaceIndex (pyramidSideBoundaryFacet i a) → 0 < posedHalfspaceSlack7 q l p) :
    p ∈ T7 := by
  cases a with
  | none =>
      have hl := T7_literal_base_side_crease_germ hk q hq i si ha hi (fun l hlb hls => ho l hls hlb)
      apply hl.mem_iff.mpr
      cases k.bump <;> simp [closedBaseSideWedge,hi,ha,pyramidFacetHalfspaceIndex,pyramidSideBoundaryFacet] at *
  | some a =>
      rcases a with ⟨j,sj⟩
      have hl := T7_literal_side_side_crease_germ hk q hq i j.val si sj hi ha ho
      apply hl.mem_iff.mpr
      cases k.bump <;> simp [closedSideSideWedge,hi,ha,pyramidFacetHalfspaceIndex,pyramidSideBoundaryFacet] at *

theorem T7_carrierFacetEdgeStrip_mem (f : Contact.Facet 7)
    (howner : Contact.IsChairCell f.cell) (hexposed : ¬ Contact.IsChairCell f.neighbor)
    (j : Fin 7) (hj : j ≠ f.axis) (upper : Bool) {p : Point 7}
    (hp : p ∈ carrierFacetEdgeStrip f j upper) : p ∈ T7 := by
  apply (T7_carrierFacetEdgeStrip_halfspace f howner hexposed j hj upper hp).mem_iff.mpr
  cases h : f.positive <;> simp [Contact.Facet.inwardHalfspace,h,hp.1.1]

#print axioms T7_literal_pruned_crease_mem
#print axioms T7_carrierFacetEdgeStrip_mem

end SparseMonotiles
