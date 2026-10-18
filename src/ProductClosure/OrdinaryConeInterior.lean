module

public import ProductClosure.CarrierConeRegularity
public import ProductClosure.CarrierInteriorRay

@[expose] public section

/-! A strict transverse inward vector for each literal finite-cell ordinary cone. -/
namespace ProductClosure.NativeCompiler
open scoped InnerProductSpace Topology
open Set
noncomputable section
variable {m : ℕ} {polyCells : Finset (Polycube.LatticeIndex (m + 1))}

def placedActiveCarrierDirection (c : Polycube.Cell polyCells)
    (f : Space m ≃ᵢ Space m) (x : Space m) : Space m :=
  placedNormal f (activeCarrierDirection c (f.symm x))

theorem placedCoordinateNormal_inner_placedDirection (c : Polycube.Cell polyCells)
    (f : Space m ≃ᵢ Space m) (x : Space m) (i : Fin (m + 1)) :
    ⟪placedCoordinateNormal f i, placedActiveCarrierDirection c f x⟫_ℝ =
      activeCarrierDirection c (f.symm x) i := by
  change ⟪f.toRealAffineIsometryEquiv.linearIsometryEquiv _,
    f.toRealAffineIsometryEquiv.linearIsometryEquiv _⟫_ℝ = _
  rw [f.toRealAffineIsometryEquiv.linearIsometryEquiv.inner_map_map]
  simp [EuclideanSpace.inner_single_left]

theorem placedActiveCarrierDirection_mem_span (c : Polycube.Cell polyCells)
    (f : Space m ≃ᵢ Space m) (x p q : Space m)
    (hspan : ∀ n ∈ placedActiveCarrierNormals polyCells f x,
      n ∈ Submodule.span ℝ ({p, q} : Set (Space m))) :
    placedActiveCarrierDirection c f x ∈ Submodule.span ℝ ({p, q} : Set (Space m)) := by
  unfold placedActiveCarrierDirection activeCarrierDirection placedNormal
  rw [map_sum]
  apply Submodule.sum_mem
  intro i hi
  rw [map_smul]
  apply Submodule.smul_mem
  exact hspan (placedCoordinateNormal f i) (Finset.mem_image.mpr ⟨i, hi, rfl⟩)

theorem placedActiveCarrierDirection_off_normals (c : Polycube.Cell polyCells)
    (f : Space m ≃ᵢ Space m) (x : Space m) :
    ∀ n ∈ placedActiveCarrierNormals polyCells f x,
      ⟪n, placedActiveCarrierDirection c f x⟫_ℝ ≠ 0 := by
  intro n hn
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hn
  rw [placedCoordinateNormal_inner_placedDirection]
  exact activeCarrierDirection_strict c (f.symm x) i hi

/-- The chosen containing cell certifies the vector's strict inward signs. -/
theorem placedActiveCarrierDirection_mem_cone (c : Polycube.Cell polyCells)
    (f : Space m ≃ᵢ Space m) (x : Space m)
    (hx : f.symm x ∈ Polycube.latticeCell c.val) :
    placedActiveCarrierDirection c f x ∈ placedCarrierCone polyCells f x := by
  refine ⟨c, hx, fun i => ?_⟩
  rw [placedCoordinateNormal_inner_placedDirection, activeCarrierDirection_coordinate]
  constructor
  · intro hi
    have ha : i ∈ activeCarrierAxes polyCells (f.symm x) :=
      (mem_activeCarrierAxes (f.symm x) i).mpr ⟨c, Or.inl hi⟩
    rw [ite_eq_left ha, hi]
    linarith
  · intro hi
    have ha : i ∈ activeCarrierAxes polyCells (f.symm x) :=
      (mem_activeCarrierAxes (f.symm x) i).mpr ⟨c, Or.inr hi⟩
    rw [ite_eq_left ha, hi]
    linarith

/-- A concrete nonzero strict-sign vector derives positive transverse mass
without assuming an angular sector or a measure certificate. -/
theorem placedCarrierCone_strict_inward_direction
    {J : ℕ} [NeZero m] [Nonempty (Polycube.Cell polyCells)]
    (hm : 2 ≤ m) (a : Coefficients polyCells J)
    (f : Space m ≃ᵢ Space m) (x p q : Space m)
    (hx : f.symm x ∈ frontier (body a))
    (hkey : ∀ u, f.symm x ∉ keyGraph a u)
    (hspan : ∀ n ∈ placedActiveCarrierNormals polyCells f x,
      n ∈ Submodule.span ℝ ({p, q} : Set (Space m))) :
    ∃ v ∈ Submodule.span ℝ ({p, q} : Set (Space m)), v ≠ 0 ∧
      v ∈ placedCarrierCone polyCells f x ∧
      ∀ n ∈ placedActiveCarrierNormals polyCells f x, ⟪n, v⟫_ℝ ≠ 0 := by
  have houtside := (frontier_body_outside_keyGraphs hm a (f.symm x) hx hkey).1
  have hfront :=
    (frontier_body_iff_frontier_carrier_of_not_mem_closedTube a (f.symm x) houtside).mp hx
  obtain ⟨z, hz, hxz⟩ := (Polycube.mem_carrier_iff polyCells (f.symm x)).mp
    ((carrier_isClosed polyCells).frontier_subset hfront)
  let c : Polycube.Cell polyCells := ⟨z, hz⟩
  exact ⟨placedActiveCarrierDirection c f x, placedActiveCarrierDirection_mem_span c f x p q hspan,
    placedNormal_ne_zero f _ (activeCarrierDirection_ne_zero c _ hfront),
    placedActiveCarrierDirection_mem_cone c f x hxz,
    placedActiveCarrierDirection_off_normals c f x⟩

#print axioms placedCarrierCone_strict_inward_direction
end
end ProductClosure.NativeCompiler
