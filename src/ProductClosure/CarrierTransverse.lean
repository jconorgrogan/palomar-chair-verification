module

public import ProductClosure.NativeBoundaryPlanes
public import PhysicalRegistration.CarrierTransverse

@[expose] public section

/-! Regular closure and orthogonal active-coordinate control for arbitrary finite polycubes. -/
namespace ProductClosure.NativeCompiler
open scoped InnerProductSpace
open Set
noncomputable section
variable {m : ℕ} {S : Finset (Polycube.LatticeIndex (m + 1))}

theorem coordinate_three_linearIndependent (i j k : Fin (m + 1))
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    LinearIndependent ℝ ![EuclideanSpace.single i (1 : ℝ), EuclideanSpace.single j (1 : ℝ),
      EuclideanSpace.single k (1 : ℝ)] := by
  exact PhysicalRegistration.NativeChair.coordinate_three_linearIndependent i j k hij hik hjk

/-- A two-normal span cannot contain three distinct coordinate normals. -/
theorem activeCarrierAxes_card_le_two (S : Finset (Polycube.LatticeIndex (m + 1)))
    (x p q : Space m)
    (hspan : ∀ i ∈ activeCarrierAxes S x,
      EuclideanSpace.single i (1 : ℝ) ∈ Submodule.span ℝ ({p, q} : Set (Space m))) :
    (activeCarrierAxes S x).card ≤ 2 := by
  classical
  by_contra hcard
  obtain ⟨i, hi, j, hj, k, hk, hij, hik, hjk⟩ :=
    Finset.two_lt_card.mp (by omega : 2 < (activeCarrierAxes S x).card)
  exact PhysicalRegistration.NativeChair.three_independent_not_mem_span_pair _ _ _ p q
    (coordinate_three_linearIndependent i j k hij hik hjk)
    ⟨hspan i hi, hspan j hj, hspan k hk⟩

/-- Strictly inside any occupied cell is strictly inside the carrier. -/
theorem strict_cell_mem_interior_carrier (c : Polycube.Cell S) (x : Space m)
    (hx : ∀ i, (c.val i : ℝ) < x i ∧ x i < (c.val i : ℝ) + 1) :
    x ∈ interior (Polycube.carrier S) := by
  apply interior_mono (show Polycube.latticeCell c.val ⊆ Polycube.carrier S from
    fun y hy => (Polycube.mem_carrier_iff S y).mpr ⟨c.val, c.property, hy⟩)
  rwa [Polycube.interior_latticeCell]

/-- Interpolation toward the center of a chosen containing cell enters that
cell's interior. No global star-center is assumed or needed. -/
theorem carrier_combination_cellCenter_mem_interior (c : Polycube.Cell S)
    (x : Space m) (hx : x ∈ Polycube.latticeCell c.val)
    (t : ℝ) (ht : 0 < t) (htone : t ≤ 1) :
    (1 - t) • x + t • Polycube.latticeCenter c.val ∈ interior (Polycube.carrier S) := by
  apply strict_cell_mem_interior_carrier c
  intro i
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, Polycube.latticeCenter]
  have hlo := mul_nonneg (sub_nonneg.mpr htone) (sub_nonneg.mpr (hx i).1)
  have hup := mul_nonneg (sub_nonneg.mpr htone) (sub_nonneg.mpr (hx i).2)
  constructor <;> nlinarith

/-- A finite union of full closed cells is regular closed, even when it has
holes, disconnected components, or reentrant corners. -/
theorem closure_interior_carrier (S : Finset (Polycube.LatticeIndex (m + 1))) :
    closure (interior (Polycube.carrier S)) = Polycube.carrier S := by
  apply subset_antisymm
  · exact closure_minimal interior_subset (carrier_isClosed S)
  · intro x hx
    obtain ⟨z, hz, hxz⟩ := (Polycube.mem_carrier_iff S x).mp hx
    exact PhysicalRegistration.NativeChair.mem_closure_of_positive_interpolation
      x (Polycube.latticeCenter z)
      (carrier_combination_cellCenter_mem_interior ⟨z, hz⟩ x hxz)

#print axioms activeCarrierAxes_card_le_two
#print axioms carrier_combination_cellCenter_mem_interior
#print axioms closure_interior_carrier
end
end ProductClosure.NativeCompiler
