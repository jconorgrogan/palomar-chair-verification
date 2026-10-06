module

public import SparseMonotiles.PrescribedContactProfilesSymmetry
public import SparseMonotiles.CarrierHierarchyPartition

@[expose] public section

/-! Exact integer unit-cell adjacency supplies exposed opposed facets.
No facet search bound or physical registration assumption is hidden here. -/
namespace SparseMonotiles
open Contact CarrierHierarchy

/-- Converse of the exact shared-facet neighbor-cell identity. -/
theorem shared_of_cell_neighbor {d : ℕ} {p : Pose d} {a b : Facet d}
    (hc : p.cell b.cell = a.neighbor)
    (ha : p.perm a.axis = b.axis)
    (hn : p.sign a.axis * b.normal = -a.normal) : Shared p a b := by
  refine ⟨?_, ha, hn⟩
  funext i
  have hci := congrFun hc i
  by_cases hi : i = a.axis
  · subst i
    simp only [Facet.centre2, Pose.scaledPoint, if_pos rfl, if_pos ha]
    simp only [Pose.cell, Facet.neighbor, if_pos rfl] at hci
    cases hp : p.negative a.axis <;>
      simp [Pose.sign, hp] at hci hn ⊢ <;> omega
  · have hpi : p.perm i ≠ b.axis := by
      intro he
      exact hi (p.perm.injective (he.trans ha.symm))
    simp only [Facet.centre2, Pose.scaledPoint, if_neg hi, if_neg hpi, add_zero]
    simp only [Pose.cell, Facet.neighbor, if_neg hi, add_zero] at hci
    cases hp : p.negative i <;> simp [Pose.sign, hp] at hci ⊢ <;> omega

/-- The native source facet opposite a given root facet under a signed pose. -/
def oppositeSourceFacet {d : ℕ} (p : Pose d) (a : Facet d) : Facet d where
  cell := p.inverseCell a.neighbor
  axis := p.perm a.axis
  positive := if p.negative a.axis then a.positive else !a.positive

theorem oppositeSourceFacet_shared {d : ℕ} (p : Pose d) (a : Facet d) :
    Shared p a (oppositeSourceFacet p a) := by
  apply shared_of_cell_neighbor (p.cell_inverseCell a.neighbor) rfl
  cases hp : p.negative a.axis <;> cases ha : a.positive <;>
    simp [oppositeSourceFacet, Facet.normal, Pose.sign, hp, ha]

theorem oppositeSourceFacet_neighbor {d : ℕ} (p : Pose d) (a : Facet d) :
    (oppositeSourceFacet p a).neighbor = p.inverseCell a.cell := by
  have h := shared_cell_neighbor (shared_inversePose (oppositeSourceFacet_shared p a))
  rw [inversePose_cell] at h
  exact h.symm

theorem adjacentCells_exists_facet {d : ℕ} {x y : Cell d}
    (h : AdjacentCells x y) : ∃ a : Facet d, a.cell = x ∧ a.neighbor = y := by
  obtain ⟨i, hi, hj⟩ := h
  rcases hi with hi | hi
  · refine ⟨⟨x, i, true⟩, rfl, ?_⟩
    funext j
    by_cases he : j = i
    · subst j
      simpa [Facet.neighbor, Facet.normal] using hi.symm
    · simpa [Facet.neighbor, he] using (hj j he).symm
  · refine ⟨⟨x, i, false⟩, rfl, ?_⟩
    funext j
    by_cases he : j = i
    · subst j
      simpa [Facet.neighbor, Facet.normal, sub_eq_add_neg] using hi.symm
    · simpa [Facet.neighbor, he] using (hj j he).symm

/-- Exhaustive geometric shared-facet witness for a disjoint registered contact. -/
theorem cellContact_root_exists_exposed_shared {d : ℕ} {p : Pose d}
    (hdis : Disjoint (chairCells d) ((chairCells d).image p.cell))
    (hc : CellContact (rootPose d) p) :
    ∃ a b : Facet d,
      IsChairCell a.cell ∧ ¬IsChairCell a.neighbor ∧
      IsChairCell b.cell ∧ ¬IsChairCell b.neighbor ∧ Shared p a b := by
  have hno (x : Cell d) (hx : IsChairCell x)
      (hy : IsChairCell (p.inverseCell x)) : False := by
    exact Finset.disjoint_left.mp hdis ((mem_chairCells x).mpr hx)
      ((mem_image_cell p (chairCells d) x).mpr ((mem_chairCells _).mpr hy))
  obtain ⟨x, y, hx, hy, hxy⟩ := hc
  have hrootInv : (rootPose d).inverseCell x = x := by
    funext i
    simp [Pose.inverseCell, rootPose, Pose.sign]
  have hx' : IsChairCell x := by
    change IsChairCell ((rootPose d).inverseCell x) at hx
    rwa [hrootInv] at hx
  change IsChairCell (p.inverseCell y) at hy
  obtain ⟨a, hax, hay⟩ := adjacentCells_exists_facet hxy
  let b := oppositeSourceFacet p a
  have hac : IsChairCell a.cell := hax ▸ hx'
  have hbc : IsChairCell b.cell := by
    change IsChairCell (p.inverseCell a.neighbor)
    simpa only [hay] using hy
  refine ⟨a, b, hac, ?_, hbc, ?_, oppositeSourceFacet_shared p a⟩
  · intro han
    exact hno a.neighbor han hbc
  · intro hbn
    rw [oppositeSourceFacet_neighbor] at hbn
    exact hno a.cell hac hbn

#print axioms cellContact_root_exists_exposed_shared
end SparseMonotiles
