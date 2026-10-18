module

public import ProductClosure.ProductWorldPeriods
public import ProductClosure.CarrierLocal
public import PhysicalRegistration.PoseRealization

@[expose] public section

/-!
# Concrete registered finite-polycube placed states

States are the existing `RegisteredPrime.Pose`, with the original signed-row
frame convention. Their actual Euclidean realizations are reused, rather
than replaced by an abstract label action. The lower-corner correction on a
negative row is explicit.
-/
namespace ProductClosure

open Set
noncomputable section

namespace Polycube

theorem latticeCenter_mem_latticeCell_iff {d : ℕ} (z w : LatticeIndex d) :
    latticeCenter z ∈ latticeCell w ↔ z = w := by
  constructor
  · intro h
    funext i
    have hi := h i
    have hz := latticeCenter_mem_open z i
    exact (integer_cell_unique (z i) (w i) (latticeCenter z i) hz hi).symm
  · rintro rfl
    exact openLatticeCell_subset z (latticeCenter_mem_open z)

theorem latticeCenter_mem_carrier_iff {d : ℕ} (S : Finset (LatticeIndex d))
    (z : LatticeIndex d) : latticeCenter z ∈ carrier S ↔ z ∈ S := by
  rw [mem_carrier_iff]
  constructor
  · rintro ⟨w, hw, hzw⟩
    exact (latticeCenter_mem_latticeCell_iff z w).mp hzw ▸ hw
  · intro hz
    exact ⟨z, hz, (latticeCenter_mem_latticeCell_iff z z).mpr rfl⟩

end Polycube

namespace World

/-- Exact occupied-cell action of the original signed row pose. -/
def poseCellIndex {d : ℕ} (q : RegisteredPrime.Pose d) (z : Lattice d) : Lattice d :=
  fun i => q.anchor i + if q.frame.negative i then -z (q.frame.perm i) - 1
    else z (q.frame.perm i)

/-- Concrete placed footprint, retaining the entire registered pose as its
state even when the unmarked carrier has a self-isometry. -/
def placedCells {d : ℕ} (S : Finset (Lattice d)) (q : RegisteredPrime.Pose d) :
    Set (Lattice d) := poseCellIndex q '' (S : Set (Lattice d))

/-- An actual congruent placed finite-polycube body. -/
def placedCarrier {m : ℕ} (S : Finset (Lattice (m + 1)))
    (q : RegisteredPrime.Pose (m + 1)) : Set (Polycube.Space (m + 1)) :=
  PhysicalRegistration.NativeChair.poseIsometry q '' Polycube.carrier S

/-- The pose realization sends exactly the native cell to the cell indexed
by the reflected-corner-corrected integer action. -/
theorem pose_mem_latticeCell_iff {m : ℕ} (q : RegisteredPrime.Pose (m + 1))
    (z : Lattice (m + 1)) (x : Polycube.Space (m + 1)) :
    PhysicalRegistration.NativeChair.poseIsometry q x ∈
      Polycube.latticeCell (poseCellIndex q z) ↔ x ∈ Polycube.latticeCell z := by
  constructor
  · intro h i
    have hi := h (q.frame.inverse i)
    rw [PhysicalRegistration.NativeChair.poseIsometry_apply] at hi
    simp only [poseCellIndex, q.frame.right_inverse] at hi
    cases hneg : q.frame.negative (q.frame.inverse i) <;>
      simp [RegisteredPrime.RegisteredFrame.sign, hneg] at hi <;>
      constructor <;> linarith
  · intro h i
    have hi := h (q.frame.perm i)
    rw [PhysicalRegistration.NativeChair.poseIsometry_apply]
    cases hneg : q.frame.negative i <;>
      simp [poseCellIndex, RegisteredPrime.RegisteredFrame.sign, hneg] <;>
      constructor <;> linarith

theorem pose_image_latticeCell {m : ℕ} (q : RegisteredPrime.Pose (m + 1))
    (z : Lattice (m + 1)) :
    PhysicalRegistration.NativeChair.poseIsometry q '' Polycube.latticeCell z =
      Polycube.latticeCell (poseCellIndex q z) := by
  let e := PhysicalRegistration.NativeChair.poseIsometry q
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (pose_mem_latticeCell_iff q z y).mpr hy
  · intro hx
    refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    apply (pose_mem_latticeCell_iff q z (e.symm x)).mp
    change e (e.symm x) ∈ Polycube.latticeCell (poseCellIndex q z)
    simpa only [e.apply_symm_apply] using hx

/-- The actual posed body is exactly its explicitly computed finite union of
integer cells. -/
theorem placedCarrier_eq_carrier_image {m : ℕ} (S : Finset (Lattice (m + 1)))
    (q : RegisteredPrime.Pose (m + 1)) :
    placedCarrier S q = Polycube.carrier (S.image (poseCellIndex q)) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨z, hz, hyz⟩ := (Polycube.mem_carrier_iff S y).mp hy
    exact (Polycube.mem_carrier_iff _ _).mpr ⟨poseCellIndex q z,
      Finset.mem_image.mpr ⟨z, hz, rfl⟩, (pose_mem_latticeCell_iff q z y).mpr hyz⟩
  · intro hx
    obtain ⟨w, hw, hxw⟩ := (Polycube.mem_carrier_iff _ _).mp hx
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hw
    rw [← pose_image_latticeCell q z] at hxw
    obtain ⟨y, hy, rfl⟩ := hxw
    exact ⟨y, (Polycube.mem_carrier_iff _ _).mpr ⟨z, hz, hy⟩, rfl⟩

/-- Testing actual geometric coverage at the center of a cell recovers its
literal placed-cell footprint, with no generic-position assumption. -/
theorem center_mem_placedCarrier_iff {m : ℕ} (S : Finset (Lattice (m + 1)))
    (q : RegisteredPrime.Pose (m + 1)) (z : Lattice (m + 1)) :
    Polycube.latticeCenter z ∈ placedCarrier S q ↔ z ∈ placedCells S q := by
  rw [placedCarrier_eq_carrier_image, Polycube.latticeCenter_mem_carrier_iff]
  simp [placedCells]

theorem latticeCell_subset_placedCarrier {m : ℕ} (S : Finset (Lattice (m + 1)))
    (q : RegisteredPrime.Pose (m + 1)) {z : Lattice (m + 1)}
    (hz : z ∈ placedCells S q) : Polycube.latticeCell z ⊆ placedCarrier S q := by
  obtain ⟨w, hw, rfl⟩ := hz
  intro x hx
  rw [placedCarrier_eq_carrier_image]
  exact (Polycube.mem_carrier_iff _ _).mpr
    ⟨poseCellIndex q w, Finset.mem_image.mpr ⟨w, hw, rfl⟩, hx⟩

/-- Every occupied lattice center is in the genuine topological interior of
the actual placed carrier. -/
theorem center_mem_interior_placedCarrier {m : ℕ} (S : Finset (Lattice (m + 1)))
    (q : RegisteredPrime.Pose (m + 1)) {z : Lattice (m + 1)}
    (hz : z ∈ placedCells S q) :
    Polycube.latticeCenter z ∈ interior (placedCarrier S q) := by
  apply interior_mono (latticeCell_subset_placedCarrier S q hz)
  rw [Polycube.interior_latticeCell]
  exact Polycube.latticeCenter_mem_open z

/-- Actual disjointness of carrier interiors implies the separation property
used by the complete-world theorem. -/
theorem placedCells_disjoint_of_interiors {m : ℕ} (S : Finset (Lattice (m + 1)))
    (q r : RegisteredPrime.Pose (m + 1))
    (h : Disjoint (interior (placedCarrier S q)) (interior (placedCarrier S r))) :
    Disjoint (placedCells S q) (placedCells S r) := by
  apply Set.disjoint_left.mpr
  intro z hz hz'
  exact Set.disjoint_left.mp h (center_mem_interior_placedCarrier S q hz)
    (center_mem_interior_placedCarrier S r hz')

/-- A nonempty finite carrier has a nonempty cell footprint at every actual
registered pose. -/
theorem placedCells_nonempty {d : ℕ} {S : Finset (Lattice d)} (hS : S.Nonempty)
    (q : RegisteredPrime.Pose d) : (placedCells S q).Nonempty := by
  obtain ⟨z, hz⟩ := hS
  exact ⟨poseCellIndex q z, z, hz, rfl⟩

#print axioms pose_image_latticeCell
#print axioms placedCarrier_eq_carrier_image
#print axioms center_mem_placedCarrier_iff
#print axioms placedCells_disjoint_of_interiors

end World
end
end ProductClosure
