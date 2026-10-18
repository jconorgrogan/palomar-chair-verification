module

public import ProductClosure.ProductWorldReindex
public import ProductClosure.ProductGraphCarrierDisjoint

@[expose] public section

/-! Relative physical carrier nonoverlap supplies the absolute footprint
separation required by complete-world decoding. -/
namespace ProductClosure.World
open Set RegisteredPrime
noncomputable section

/-- Disjointness in the first tile's native chart implies disjointness of
the two actual absolute placed footprints. -/
theorem placedCells_disjoint_of_relative {d : ℕ} (S : Finset (Lattice d))
    (q r : Pose d)
    (h : Disjoint (placedCells S (identityPose d)) (placedCells S (q.relative r))) :
    Disjoint (placedCells S q) (placedCells S r) := by
  apply Set.disjoint_left.mpr
  intro z hz hz'
  let x := poseCellIndex q.inv z
  have hx : x ∈ placedCells S (identityPose d) := by
    apply (placedCells_comp_cell_iff S q (identityPose d) x).mp
    simpa only [x, poseCellIndex_eq_cell, Pose.cell_inv_cell, Pose.comp_identity] using hz
  have hx' : x ∈ placedCells S (q.relative r) := by
    apply (placedCells_comp_cell_iff S q (q.relative r) x).mp
    simpa only [x, poseCellIndex_eq_cell, Pose.cell_inv_cell, Pose.comp_relative] using hz'
  exact Set.disjoint_left.mp h hx hx'

/-- The geometric F-language carrier-disjointness condition is sufficient;
raw full-profile equations alone are not assumed to force disjointness. -/
theorem placedCells_disjoint_of_relative_carrier {d : ℕ}
    (S : Finset (Lattice (d + 1))) (q r : Pose (d + 1))
    (h : ProductGraphCarrierDisjoint.CarrierDisjoint S
      (PhysicalRegistration.NativeChair.poseIsometry (q.relative r))) :
    Disjoint (placedCells S q) (placedCells S r) := by
  apply placedCells_disjoint_of_relative S q r
  apply placedCells_disjoint_of_interiors S (identityPose (d + 1)) (q.relative r)
  have hid : placedCarrier S (identityPose (d + 1)) = Polycube.carrier S := by
    unfold placedCarrier
    rw [PhysicalRegistration.NativeChair.poseIsometry_identity]
    change id '' Polycube.carrier S = Polycube.carrier S
    exact Set.image_id _
  rw [hid]
  exact h

/-- Any factor relative language with actual physical nonoverlap has the
exact separation property needed to rule out wrong-axis contacts. -/
theorem separates_of_relative_carrier {d : ℕ} (S : Finset (Lattice (d + 1)))
    {M : Pose (d + 1) → Prop}
    (hM : ∀ e, M e → ProductGraphCarrierDisjoint.CarrierDisjoint S
      (PhysicalRegistration.NativeChair.poseIsometry e)) :
    Separates (placedCells S) (fun q r => M (q.relative r)) := by
  intro q r hqr
  exact placedCells_disjoint_of_relative_carrier S q r (hM _ hqr)

#print axioms placedCells_disjoint_of_relative_carrier
#print axioms separates_of_relative_carrier

end
end ProductClosure.World
