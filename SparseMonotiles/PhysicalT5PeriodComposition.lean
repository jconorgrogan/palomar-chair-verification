module

public import SparseMonotiles.GlobalPhysicalRegistration
public import SparseMonotiles.PhysicalContactWorldLaw
public import SparseMonotiles.CarrierHierarchyContactBinding5
public import SparseMonotiles.CoarseContactCertificates5
public import SparseMonotiles.TileGeometry

@[expose] public section

/-! All geometry-to-period steps for T5 are composed here. The remaining native
physical contact predicate is explicit until its whole-profile proof is supplied.
No contact or hierarchy axiom is introduced. -/
namespace SparseMonotiles
open Set Contact CarrierHierarchy

theorem T5_isAperiodic_of_native_contact_law
    (hnative : ∀ (tiles : Set (Set (Point 5))) (ht : IsTiling T5 tiles)
      (g : tiles → Point 5 ≃ᵢ Point 5)
      (hg : ∀ A : tiles, (A : Set (Point 5))=g A '' T5)
      (A B : tiles) (p : Pose 5), B≠A →
      (g B).trans (g A).symm=p.euclidean.toIsometryEquiv →
      CellContact (rootPose 5) p → IndexedData5.geometry.LegalContact p) :
    IsAperiodic T5 := by
  apply isAperiodic_of_registered_legal_frames T5 T5_isCompact T5_cellCentre_mem_iff
    (fun _ hc => T5_cellCentre_mem_interior hc) M5 ?_ t5_registered_period_zero
  intro tiles ht g hg
  obtain ⟨e,q,hreg⟩ := T5_global_registered_frames ht g hg
  refine ⟨e,q,hreg,?_⟩
  apply registered_range_law_of_native_physical_law g e q hreg M5
  intro A B p hBA hp hcontact
  exact (ContactBinding5.registered_contact_exact_catalog p).mp
    (hnative tiles ht g hg A B p hBA hp hcontact)

#print axioms T5_isAperiodic_of_native_contact_law
end SparseMonotiles
