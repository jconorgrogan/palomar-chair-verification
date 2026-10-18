module

public import SpectreGeometry.RealPolygonFacets
public import SpectreClusters.BodyBSPComplete

@[expose] public section


/-! Exact equality of the twelve canonical developed triangle carriers and
literal raw eight/ten closed-kite carriers, by checked rational BSP coverage. -/
namespace SpectreGeometry
noncomputable section
open Set HalfplaneCertificate
open SpectreClusters SpectreClusters.BodyBSP

def gridKiteBody (c : Cell) : Set RealPoint := integerHull (cellVertices c)
def literalKiteBody (kind : HTKind) : Set RealPoint := ⋃ c ∈ htCells kind, gridKiteBody c
def canonicalTargetBody (kind : HTKind) : Set RealPoint :=
  ⋃ i : Fin 12, integerHull ((targetVertexLists kind).getD i.val [])

theorem satisfies_unit_append (fs : List Constraint) (x : RealPoint) (hx : Satisfies fs x) :
    Satisfies (fs++[unitFacet]) x := by
  exact satisfies_append_facet fs unitFacet x hx (by norm_num [unitFacet,evalConstraint])

theorem canonical_triangle_covered (kind : HTKind) (i : Fin 12) (x : RealPoint)
    (hx : x ∈ integerHull ((targetVertexLists kind).getD i.val [])) :
    ∃ j : Fin (htCells kind).length,
      x ∈ integerHull ((kiteVertexLists kind).getD j.val []) := by
  obtain ⟨j,hj,hxj⟩ := checkTree_sound _ _ _ (forward_checked kind i) x
    (satisfies_unit_append _ _ ((canonicalTriangle_mem_iff kind i x).mp hx))
  have hj' : j<(htCells kind).length := by simpa only [kite_facets_length] using hj
  exact ⟨⟨j,hj'⟩,(canonicalKite_mem_iff kind ⟨j,hj'⟩ x).mpr hxj⟩

theorem canonical_kite_covered (kind : HTKind) (i : Fin (htCells kind).length) (x : RealPoint)
    (hx : x ∈ integerHull ((kiteVertexLists kind).getD i.val [])) :
    ∃ j : Fin 12, x ∈ integerHull ((targetVertexLists kind).getD j.val []) := by
  obtain ⟨j,hj,hxj⟩ := checkTree_sound _ _ _ (reverse_checked kind i) x
    (satisfies_unit_append _ _ ((canonicalKite_mem_iff kind i x).mp hx))
  have hj' : j<12 := by simpa only [target_facets_length] using hj
  exact ⟨⟨j,hj'⟩,(canonicalTriangle_mem_iff kind ⟨j,hj'⟩ x).mpr hxj⟩

theorem kiteVertexLists_get (kind : HTKind) (i : Fin (htCells kind).length) :
    (kiteVertexLists kind).getD i.val [] = cellVertices ((htCells kind).get i) := by
  cases kind <;> revert i <;> decide

theorem literalKiteBody_mem_iff (kind : HTKind) (x : RealPoint) :
    x ∈ literalKiteBody kind ↔ ∃ i : Fin (htCells kind).length,
      x ∈ integerHull ((kiteVertexLists kind).getD i.val []) := by
  simp only [literalKiteBody,mem_iUnion,gridKiteBody,kiteVertexLists_get]
  constructor
  · rintro ⟨c,hc,hx⟩
    obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hc
    exact ⟨i,hx⟩
  · rintro ⟨i,hx⟩
    exact ⟨_,List.get_mem _ _,hx⟩

/-- A real-set equality, rather than a boundary or area certificate. -/
theorem canonicalTargetBody_eq_literalKiteBody (kind : HTKind) :
    canonicalTargetBody kind = literalKiteBody kind := by
  ext x
  simp only [canonicalTargetBody,mem_iUnion,literalKiteBody_mem_iff]
  exact ⟨fun ⟨i,hi⟩ => canonical_triangle_covered kind i x hi,
    fun ⟨i,hi⟩ => canonical_kite_covered kind i x hi⟩

end
end SpectreGeometry
