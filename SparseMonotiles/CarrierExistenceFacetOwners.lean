module

public import SparseMonotiles.CarrierExistenceGluing

@[expose] public section

/-! Actual carrier germs at an integer facet are derived from its two cell
owners in the constructed registered world. No halfspace or empty-third-tile
germ is assumed here. -/
namespace SparseMonotiles.CarrierHierarchy.Existence
open Contact Set

def outwardHalfspace {d : ℕ} (f : Facet d) : Set (Point d) :=
  {x | if f.positive then (f.gridFacet.anchor f.axis : ℝ) ≤ x f.axis
    else x f.axis ≤ (f.gridFacet.anchor f.axis : ℝ)}

theorem coordinate_regions_opposed {d : ℕ} (j : Fin d) (a : ℝ) :
    OpposedClosedRegions {x : Point d | x j ≤ a} {x : Point d | a ≤ x j} := by
  have hc : Continuous (fun x : Point d => x j) := by fun_prop
  have ho : IsOpenMap (fun x : Point d => x j) :=
    (isOpenMap_eval j).comp
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).toHomeomorph.isOpenMap
  refine ⟨isClosed_le hc continuous_const, isClosed_le continuous_const hc, ?_, ?_, ?_⟩
  · apply Set.eq_univ_of_forall
    intro x
    exact le_total (x j) a
  · apply Set.disjoint_left.mpr
    intro x hx hj
    have hh := ho.interior_preimage_subset_preimage_interior (s := Set.Iic a) hx
    have hh' : x j < a := by simpa only [interior_Iic, Set.mem_preimage, Set.mem_Iio] using hh
    exact not_lt_of_ge hj hh'
  · apply Set.disjoint_left.mpr
    intro x hx hj
    have hh := ho.interior_preimage_subset_preimage_interior (s := Set.Ici a) hj
    have hh' : a < x j := by simpa only [interior_Ici, Set.mem_preimage, Set.mem_Ioi] using hh
    exact not_lt_of_ge hx hh'

theorem facet_regions_opposed {d : ℕ} (f : Facet d) :
    OpposedClosedRegions f.inwardHalfspace (outwardHalfspace f) := by
  cases hp : f.positive
  · simpa only [Facet.inwardHalfspace, outwardHalfspace, hp, Bool.false_eq_true, if_false]
      using (coordinate_regions_opposed f.axis (f.gridFacet.anchor f.axis : ℝ)).symm
  · simpa only [Facet.inwardHalfspace, outwardHalfspace, hp, if_true]
      using coordinate_regions_opposed f.axis (f.gridFacet.anchor f.axis : ℝ)

theorem mem_neighbor_iff_outwardHalfspace {d : ℕ} (f : Facet d) {x : Point d}
    (hx : x ∈ f.openCellNeighborhood) :
    x ∈ closedIntegerCell f.neighbor ↔ x ∈ outwardHalfspace f := by
  constructor
  · intro hc
    have hn := hc f.axis
    cases hp : f.positive
    · simpa [outwardHalfspace, Facet.gridFacet_anchor_axis, Facet.neighbor, Facet.normal, hp]
        using hn.2
    · simpa [outwardHalfspace, Facet.gridFacet_anchor_axis, Facet.neighbor, Facet.normal, hp]
        using hn.1
  · intro hh i
    by_cases hi : i = f.axis
    · subst i
      rcases abs_lt.mp hx.1 with ⟨hl, hu⟩
      cases hp : f.positive <;>
        simp [outwardHalfspace, Facet.gridFacet_anchor_axis, Facet.neighbor, Facet.normal, hp]
          at hh hl hu ⊢ <;> constructor <;> linarith
    · simpa [Facet.neighbor, hi] using
        And.intro (hx.2 i hi).1.le (hx.2 i hi).2.le

theorem owner_carrier_germ {d : ℕ} (W : RegisteredWorld d) (f : Facet d)
    {p q : Pose d} (hp : p ∈ W.tiles) (hq : q ∈ W.tiles) (hne : p ≠ q)
    (hpc : Occupies p f.cell) (hqn : Occupies q f.neighbor)
    {x : Point d} (hx : x ∈ f.openCellNeighborhood) :
    LocalSetEq x (p.euclidean '' carrier d) f.inwardHalfspace := by
  apply LocalSetEq.of_open f.openCellNeighborhood_isOpen hx
  intro y hy
  rw [mem_posed_carrier_iff]
  constructor
  · rintro ⟨c, hpc', hyc⟩
    rcases f.cell_eq_owner_or_neighbor hy hyc with rfl | rfl
    · exact (f.mem_owner_iff_inwardHalfspace hy).mp hyc
    · exact False.elim (hne (W.disjoint p hp q hq _ hpc' hqn))
  · intro hyH
    exact ⟨f.cell, hpc, (f.mem_owner_iff_inwardHalfspace hy).mpr hyH⟩

theorem neighbor_carrier_germ {d : ℕ} (W : RegisteredWorld d) (f : Facet d)
    {p q : Pose d} (hp : p ∈ W.tiles) (hq : q ∈ W.tiles) (hne : p ≠ q)
    (hpc : Occupies p f.cell) (hqn : Occupies q f.neighbor)
    {x : Point d} (hx : x ∈ f.openCellNeighborhood) :
    LocalSetEq x (q.euclidean '' carrier d) (outwardHalfspace f) := by
  apply LocalSetEq.of_open f.openCellNeighborhood_isOpen hx
  intro y hy
  rw [mem_posed_carrier_iff]
  constructor
  · rintro ⟨c, hqc, hyc⟩
    rcases f.cell_eq_owner_or_neighbor hy hyc with rfl | rfl
    · exact False.elim (hne (W.disjoint p hp q hq _ hpc hqc))
    · exact (mem_neighbor_iff_outwardHalfspace f hy).mp hyc
  · intro hyH
    exact ⟨f.neighbor, hqn, (mem_neighbor_iff_outwardHalfspace f hy).mpr hyH⟩

theorem third_carrier_germ_empty {d : ℕ} (W : RegisteredWorld d) (f : Facet d)
    {p q r : Pose d} (hp : p ∈ W.tiles) (hq : q ∈ W.tiles) (hr : r ∈ W.tiles)
    (hrp : r ≠ p) (hrq : r ≠ q)
    (hpc : Occupies p f.cell) (hqn : Occupies q f.neighbor)
    {x : Point d} (hx : x ∈ f.openCellNeighborhood) :
    LocalSetEq x (r.euclidean '' carrier d) ∅ := by
  apply LocalSetEq.of_open f.openCellNeighborhood_isOpen hx
  intro y hy
  constructor
  · intro hyr
    obtain ⟨c, hrc, hyc⟩ := (mem_posed_carrier_iff r y).mp hyr
    rcases f.cell_eq_owner_or_neighbor hy hyc with rfl | rfl
    · exact False.elim (hrp (W.disjoint r hr p hp _ hrc hpc))
    · exact False.elim (hrq (W.disjoint r hr q hq _ hrc hqn))
  · exact False.elim

#print axioms facet_regions_opposed
#print axioms owner_carrier_germ
#print axioms neighbor_carrier_germ
#print axioms third_carrier_germ_empty
end SparseMonotiles.CarrierHierarchy.Existence
