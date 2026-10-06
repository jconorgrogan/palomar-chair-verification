module

public import SparseMonotiles.ContactPhysicalOverlap
public import SparseMonotiles.CoreCertificates

@[expose] public section

/-! The overlap rejection bridge instantiated for the exact frozen T5/T7 bodies.
No registration theorem for arbitrary Euclidean isometries is asserted here. -/
namespace SparseMonotiles.Contact

theorem T5_cellCentre_mem_interior {c : Cell 5} (hc : IsChairCell c) :
    cellCentre c ∈ interior T5 :=
  chairCellCentre_mem_interior_of_cores (1/100) (by norm_num)
    T5_carrierCellCore_subset_interior hc

theorem T7_cellCentre_mem_interior {c : Cell 7} (hc : IsChairCell c) :
    cellCentre c ∈ interior T7 :=
  chairCellCentre_mem_interior_of_cores (1/100) (by norm_num)
    T7_carrierCellCore_subset_interior hc

theorem T5_overlap_physical_witness {p : Pose 5} {c : Cell 5}
    (hc : IsChairCell c) (hm : IsChairCell (p.inverseCell c)) :
    cellCentre c ∈ interior T5 ∩ interior (p.euclidean '' T5) :=
  physical_overlap_of_chair_inverse (fun _ h => T5_cellCentre_mem_interior h) hc hm

theorem T7_overlap_physical_witness {p : Pose 7} {c : Cell 7}
    (hc : IsChairCell c) (hm : IsChairCell (p.inverseCell c)) :
    cellCentre c ∈ interior T7 ∩ interior (p.euclidean '' T7) :=
  physical_overlap_of_chair_inverse (fun _ h => T7_cellCentre_mem_interior h) hc hm

theorem T5_carrier_disjoint_of_physical_interiors {p : Pose 5}
    (h : Disjoint (interior T5) (interior (p.euclidean '' T5))) :
    Disjoint (chairCells 5) ((chairCells 5).image p.cell) :=
  carrier_disjoint_of_physical_interiors
    (fun c hc => T5_cellCentre_mem_interior ((mem_chairCells c).mp hc))
    (fun c hc => T5_cellCentre_mem_interior ((mem_chairCells c).mp hc)) h

theorem T7_carrier_disjoint_of_physical_interiors {p : Pose 7}
    (h : Disjoint (interior T7) (interior (p.euclidean '' T7))) :
    Disjoint (chairCells 7) ((chairCells 7).image p.cell) :=
  carrier_disjoint_of_physical_interiors
    (fun c hc => T7_cellCentre_mem_interior ((mem_chairCells c).mp hc))
    (fun c hc => T7_cellCentre_mem_interior ((mem_chairCells c).mp hc)) h

theorem T5_checked_overlap_not_disjoint {d : ℕ} {g : IndexedGeometry 5 d}
    {p : Pose 5} {c : Cell 5}
    (checked : (IndexedRejection.overlap c).FastValid g p) :
    ¬ Disjoint (interior T5) (interior (p.euclidean '' T5)) := by
  intro h
  have hw := T5_overlap_physical_witness checked.1 checked.2
  exact Set.disjoint_left.mp h hw.1 hw.2

theorem T7_checked_overlap_not_disjoint {d : ℕ} {g : IndexedGeometry 7 d}
    {p : Pose 7} {c : Cell 7}
    (checked : (IndexedRejection.overlap c).FastValid g p) :
    ¬ Disjoint (interior T7) (interior (p.euclidean '' T7)) := by
  intro h
  have hw := T7_overlap_physical_witness checked.1 checked.2
  exact Set.disjoint_left.mp h hw.1 hw.2

#print axioms T5_overlap_physical_witness
#print axioms T7_overlap_physical_witness
#print axioms T5_checked_overlap_not_disjoint
#print axioms T7_checked_overlap_not_disjoint
#print axioms T5_carrier_disjoint_of_physical_interiors
#print axioms T7_carrier_disjoint_of_physical_interiors
end SparseMonotiles.Contact
