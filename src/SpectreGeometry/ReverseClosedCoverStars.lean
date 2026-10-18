module

public import Mathlib.Topology.LocallyFinite

@[expose] public section


/-! The incident star of a locally finite closed cover is an ambient
neighborhood. This removes any need for a finite source-star cover certificate. -/
namespace SpectreGeometry.ReverseExistence
noncomputable section
open Set Topology
variable {X ι : Type*} [TopologicalSpace X]

def incidentStar (C : ι → Set X) (x : X) : Set X :=
  ⋃ i : {i // x ∈ C i}, C i.val

/-- Excluding the closed union of all nonincident carriers gives the required
neighborhood, using only local finiteness, closedness, and full coverage. -/
theorem incidentStar_mem_nhds
    (C : ι → Set X) (hloc : LocallyFinite C) (hclosed : ∀ i, IsClosed (C i))
    (hcover : ∀ y, ∃ i, y ∈ C i) (x : X) : incidentStar C x ∈ 𝓝 x := by
  apply Filter.mem_of_superset (hloc.iInter_compl_mem_nhds hclosed x)
  intro y hy
  obtain ⟨i,hi⟩ := hcover y
  have hxi : x ∈ C i := by
    by_contra hn
    exact (mem_iInter₂.mp hy i hn) hi
  exact mem_iUnion.mpr ⟨⟨i,hxi⟩,hi⟩

/-- Local finiteness gives the finite index set used to assemble the star. -/
theorem finite_incident_indices (C : ι → Set X) (hloc : LocallyFinite C) (x : X) :
    {i | x ∈ C i}.Finite := hloc.point_finite x

/-- The explicit source-interior hypothesis needed by carrier-chart assembly. -/
theorem mem_interior_incidentStar
    (C : ι → Set X) (hloc : LocallyFinite C) (hclosed : ∀ i, IsClosed (C i))
    (hcover : ∀ y, ∃ i, y ∈ C i) (x : X) : x ∈ interior (incidentStar C x) :=
  mem_interior_iff_mem_nhds.mpr (incidentStar_mem_nhds C hloc hclosed hcover x)

end
end SpectreGeometry.ReverseExistence
