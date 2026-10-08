module
public import SparseMonotiles.T7ExistenceProfileBridge
public import SparseMonotiles.ContactSharedGeometry
public import SparseMonotiles.FacetAtlasCompleteness7
public import SparseMonotiles.ProfileCertificates7
public import ContactInverseReuse
@[expose] public section

/-! Exact compact T7 legal-contact semantics supplies the full keyed profile
matches required by the existence-side interface. No physical tiling or
all-catalog acceptance assumption occurs in this implication. -/
namespace SparseMonotiles.CarrierHierarchy.Existence.ProfileBridge7
open Contact Set Canonical
set_option maxRecDepth 100000

/-- Every occupied neighbor of an indexed root facet has an indexed, exposed
opposed source facet. Completeness is used only after deriving its exposure
from carrier disjointness. -/
theorem indexed_shared_of_legal_occupied {p : Pose 7}
    (legal : IndexedData7.geometry.LegalContact p) (i : Fin 896)
    (occupied : (IndexedData7.geometry.facet i).neighbor ∈
      IndexedData7.geometry.cells.image p.cell) :
    ∃ j : Fin 896, Shared p (IndexedData7.geometry.facet i)
      (IndexedData7.geometry.facet j) := by
  let a := IndexedData7.geometry.facet i
  let b := oppositeSourceFacet p a
  have hbc : IsChairCell b.cell := by
    change IsChairCell (p.inverseCell a.neighbor)
    rw [← mem_chairCells, ← IndexedData7.cells_eq]
    exact (mem_image_cell p IndexedData7.geometry.cells a.neighbor).mp occupied
  have hbn : ¬ IsChairCell b.neighbor := by
    intro h
    have hinv : IsChairCell (p.inverseCell a.cell) := by
      simpa only [b, oppositeSourceFacet_neighbor] using h
    have him : a.cell ∈ IndexedData7.geometry.cells.image p.cell := by
      apply (mem_image_cell p IndexedData7.geometry.cells a.cell).mpr
      rw [IndexedData7.cells_eq, mem_chairCells]
      exact hinv
    have hroot : a.cell ∈ IndexedData7.geometry.cells := by
      rw [IndexedData7.cells_eq, mem_chairCells]
      exact IndexedData7.owned_checked i
    exact Finset.disjoint_left.mp legal.1 hroot him
  obtain ⟨j, hj⟩ := T7_indexed_facets_complete b hbc hbn
  exact ⟨j, hj.symm ▸ oppositeSourceFacet_shared p a⟩

/-- Legal literal profile equality recovers actual full BoxKey mates, using
the checked OnFacet facts. This is stronger than just matching apex points. -/
theorem indexed_key_mates_of_legal_contacts (L : Set (Pose 7))
    (hlegal : ∀ p ∈ L, IndexedData7.geometry.LegalContact p) :
    IndexedKeyMateLaw L := by
  intro p hp i root hr occupied
  have legal := hlegal p hp
  obtain ⟨j, shared⟩ := indexed_shared_of_legal_occupied legal i occupied
  have hmem : root.literal ∈
      (IndexedData7.geometry.profile i).image BoxKey.literal :=
    Finset.mem_image.mpr ⟨root, hr, rfl⟩
  rw [legal.2.2 i j shared] at hmem
  obtain ⟨lit, hlit, heq⟩ := Finset.mem_image.mp hmem
  obtain ⟨source, hs, rfl⟩ := Finset.mem_image.mp hlit
  exact ⟨j, source, hs, BoxKey.eq_pose_of_literal_match
    ((profile7_checked i).2 root hr).1 ((profile7_checked j).2 source hs).1
    shared heq.symm⟩

/-- All actual key solids, closed coordinate supports, and opposite
coefficients follow for any set of exact registered legal contacts. -/
theorem complementaryProfiles_of_legal_contacts (L : Set (Pose 7))
    (hlegal : ∀ p ∈ L, IndexedData7.geometry.LegalContact p)
    (A : KeyFacetAssignment keys7) : ComplementaryProfiles A L :=
  complementaryProfiles_of_indexed_key_mates L
    (indexed_key_mates_of_legal_contacts L hlegal) A

theorem indexed_key_mates_singleton_of_legal {p : Pose 7}
    (legal : IndexedData7.geometry.LegalContact p) :
    IndexedKeyMateLaw ({p} : Set (Pose 7)) := by
  apply indexed_key_mates_of_legal_contacts
  intro q hq
  simpa only [Set.mem_singleton_iff.mp hq] using legal

theorem complementaryProfiles_singleton_of_legal {p : Pose 7}
    (legal : IndexedData7.geometry.LegalContact p) (A : KeyFacetAssignment keys7) :
    ComplementaryProfiles A ({p} : Set (Pose 7)) :=
  complementaryProfiles_of_indexed_key_mates _
    (indexed_key_mates_singleton_of_legal legal) A

/-- A proved legal contact also supplies the inverse profile law without any
new acceptance table or body-symmetry assumption. -/
theorem complementaryProfiles_inverse_singleton_of_legal {p : Pose 7}
    (legal : IndexedData7.geometry.LegalContact p) (A : KeyFacetAssignment keys7) :
    ComplementaryProfiles A ({inversePose p} : Set (Pose 7)) :=
  complementaryProfiles_singleton_of_legal
    (ContactInverseReuse.legalContact_inversePose legal) A

#print axioms indexed_shared_of_legal_occupied
#print axioms indexed_key_mates_of_legal_contacts
#print axioms complementaryProfiles_of_legal_contacts
#print axioms indexed_key_mates_singleton_of_legal
#print axioms complementaryProfiles_singleton_of_legal
#print axioms complementaryProfiles_inverse_singleton_of_legal
end SparseMonotiles.CarrierHierarchy.Existence.ProfileBridge7
