module

public import PhysicalRegistration.ConicalFanRegularity
public import PhysicalRegistration.CarrierInteriorRay

@[expose] public section

/-! A concrete strict transverse inward vector for every actual untouched
ordinary cone. The witness comes from native active coordinates, not an
assumed positive sector or angular mass. -/
namespace PhysicalRegistration.NativeChair
open scoped InnerProductSpace Topology
open Set
noncomputable section

def placedActiveCarrierDirection {m : ℕ} (f : Space m ≃ᵢ Space m)
    (x : Space m) : Space m := placedNormal f (activeCarrierDirection (f.symm x))

theorem placedCoordinateNormal_inner_placedDirection {m : ℕ}
    (f : Space m ≃ᵢ Space m) (x : Space m) (i : Fin (m + 1)) :
    ⟪placedCoordinateNormal f i, placedActiveCarrierDirection f x⟫_ℝ =
      activeCarrierDirection (f.symm x) i := by
  change ⟪f.toRealAffineIsometryEquiv.linearIsometryEquiv _,
    f.toRealAffineIsometryEquiv.linearIsometryEquiv _⟫_ℝ = _
  rw [f.toRealAffineIsometryEquiv.linearIsometryEquiv.inner_map_map]
  simp [EuclideanSpace.inner_single_left]

theorem placedActiveCarrierDirection_mem_span {m : ℕ}
    (f : Space m ≃ᵢ Space m) (x p q : Space m)
    (hspan : ∀ n ∈ placedActiveCarrierNormals f x,
      n ∈ Submodule.span ℝ ({p, q} : Set (Space m))) :
    placedActiveCarrierDirection f x ∈ Submodule.span ℝ ({p, q} : Set (Space m)) := by
  unfold placedActiveCarrierDirection activeCarrierDirection placedNormal
  rw [map_sum]
  apply Submodule.sum_mem
  intro i hi
  rw [map_smul]
  apply Submodule.smul_mem
  exact hspan (placedCoordinateNormal f i) (Finset.mem_image.mpr ⟨i, hi, rfl⟩)

theorem placedActiveCarrierDirection_off_normals {m : ℕ}
    (f : Space m ≃ᵢ Space m) (x : Space m) :
    ∀ n ∈ placedActiveCarrierNormals f x,
      ⟪n, placedActiveCarrierDirection f x⟫_ℝ ≠ 0 := by
  intro n hn
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hn
  rw [placedCoordinateNormal_inner_placedDirection]
  exact activeCarrierDirection_strict (f.symm x) i hi

/-- Direct verification in the literal homogeneous Boolean formula. -/
theorem placedActiveCarrierDirection_mem_cone {m : ℕ}
    (f : Space m ≃ᵢ Space m) (x : Space m) (hx : f.symm x ∈ carrier m) :
    placedActiveCarrierDirection f x ∈ placedCarrierCone f x := by
  constructor
  · intro i
    rw [placedCoordinateNormal_inner_placedDirection, activeCarrierDirection_coordinate]
    constructor
    · intro hi
      have ha : i ∈ activeCarrierAxes (f.symm x) := by simp [activeCarrierAxes, hi]
      rw [ite_eq_left ha, hi]
      norm_num
    · intro hi
      have ha : i ∈ activeCarrierAxes (f.symm x) := by simp [activeCarrierAxes, hi]
      rw [ite_eq_left ha, hi]
      norm_num
  · obtain ⟨i, hi⟩ := ((mem_carrier_iff (f.symm x)).mp hx).2
    refine ⟨i, ?_⟩
    rcases lt_or_eq_of_le hi with hi | hi
    · exact Or.inl hi
    · refine Or.inr ⟨hi, ?_⟩
      rw [placedCoordinateNormal_inner_placedDirection, activeCarrierDirection_coordinate]
      have ha : i ∈ activeCarrierAxes (f.symm x) := by simp [activeCarrierAxes, hi]
      rw [ite_eq_left ha, hi]
      norm_num

/-- Every actual ordinary boundary cone has a nonzero vector in the proved
transverse span that belongs to the cone and avoids all its active normal
hyperplanes. This supplies positivity without a positive-angle hypothesis. -/
theorem placedCarrierCone_strict_inward_direction
    {m J : ℕ} [NeZero m] (hm : 2 ≤ m) (a : Coefficients m J)
    (f : Space m ≃ᵢ Space m) (x p q : Space m)
    (hx : f.symm x ∈ frontier (body a))
    (hkey : ∀ u, f.symm x ∉ keyGraph a u)
    (hspan : ∀ n ∈ placedActiveCarrierNormals f x,
      n ∈ Submodule.span ℝ ({p, q} : Set (Space m))) :
    ∃ v ∈ Submodule.span ℝ ({p, q} : Set (Space m)), v ≠ 0 ∧
      v ∈ placedCarrierCone f x ∧
      ∀ n ∈ placedActiveCarrierNormals f x, ⟪n, v⟫_ℝ ≠ 0 := by
  have houtside := (frontier_body_outside_keyGraphs hm a (f.symm x) hx hkey).1
  have hfront :=
    (frontier_body_iff_frontier_carrier_of_not_mem_closedTube a (f.symm x) houtside).mp hx
  refine ⟨placedActiveCarrierDirection f x, placedActiveCarrierDirection_mem_span f x p q hspan,
    placedNormal_ne_zero f _ (activeCarrierDirection_ne_zero _ hfront),
    placedActiveCarrierDirection_mem_cone f x ((carrier_isClosed m).frontier_subset hfront),
    placedActiveCarrierDirection_off_normals f x⟩

#print axioms placedCarrierCone_strict_inward_direction
end
end PhysicalRegistration.NativeChair
