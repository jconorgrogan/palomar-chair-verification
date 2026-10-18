module

public import ProductClosure.PlacedConicalGerms

@[expose] public section

/-! Closedness and nonzero normals of the actual native conical fan. -/
namespace ProductClosure.NativeCompiler
open scoped InnerProductSpace Topology
open Set
noncomputable section
variable {m : ℕ} {polyCells : Finset (Polycube.LatticeIndex (m + 1))}

/-- Orthogonal transport preserves the nonzero condition on a normal. -/
theorem placedNormal_ne_zero  (f : Space m ≃ᵢ Space m)
    (n : Space m) (hn : n ≠ 0) : placedNormal f n ≠ 0 := by
  simpa [placedNormal] using hn

theorem placed_outward_ne_zero  (f : Space m ≃ᵢ Space m)
    (u : Site polyCells) : placedNormal f (outward u.1) ≠ 0 := by
  apply placedNormal_ne_zero
  intro h
  have hh := outward_unit u.1
  rw [h, norm_zero] at hh
  norm_num at hh

theorem placed_sideNormal_ne_zero {J : ℕ} (a : Coefficients polyCells J)
    (f : Space m ≃ᵢ Space m) (u : Site polyCells) (s : Side m) :
    placedNormal f (sideNormal a u s) ≠ 0 :=
  placedNormal_ne_zero f _ (sideNormal_ne_zero a u s)

theorem placedCoordinateNormal_ne_zero  (f : Space m ≃ᵢ Space m)
    (i : Fin (m + 1)) : placedCoordinateNormal f i ≠ 0 := by
  intro h
  have hh := placedCoordinateNormal_unit f i
  rw [h, norm_zero] at hh
  norm_num at hh

theorem placedActiveCarrierNormals_ne_zero (polyCells : Finset (Polycube.LatticeIndex (m + 1))) (f : Space m ≃ᵢ Space m)
    (x : Space m) : ∀ n ∈ placedActiveCarrierNormals polyCells f x, n ≠ 0 := by
  intro n hn
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hn
  exact placedCoordinateNormal_ne_zero f i

/-- Every literal centered closed halfspace is closed. -/
theorem centeredHalfspace_isClosed  (n : Space m) :
    IsClosed {z : Space m | ⟪n, z⟫_ℝ ≤ 0} :=
  isClosed_le (continuous_const.inner continuous_id) continuous_const

theorem twoHalfspaceCone_isClosed  (p q : Space m) (b : Bool) :
    IsClosed (twoHalfspaceCone p q b) := by
  cases b
  · exact (centeredHalfspace_isClosed p).inter (centeredHalfspace_isClosed q)
  · exact (centeredHalfspace_isClosed p).union (centeredHalfspace_isClosed q)

/-- A finite union of closed endpoint halfspace intersections is closed. -/
theorem placedCarrierCone_isClosed (polyCells : Finset (Polycube.LatticeIndex (m + 1)))
    (f : Space m ≃ᵢ Space m) (x : Space m) : IsClosed (placedCarrierCone polyCells f x) := by
  have hu (i : Fin (m + 1)) := centeredHalfspace_isClosed (placedCoordinateNormal f i)
  have hl (i : Fin (m + 1)) :
      IsClosed {z : Space m | 0 ≤ ⟪placedCoordinateNormal f i, z⟫_ℝ} :=
    isClosed_le continuous_const (continuous_const.inner continuous_id)
  have hlo (c : Polycube.Cell polyCells) (i : Fin (m + 1)) : IsClosed
      {z : Space m | (f.symm x) i = (c.val i : ℝ) → 0 ≤ ⟪placedCoordinateNormal f i, z⟫_ℝ} := by
    by_cases h : (f.symm x) i = (c.val i : ℝ)
    · simpa only [h, true_implies] using hl i
    · simp [h]
  have hup (c : Polycube.Cell polyCells) (i : Fin (m + 1)) : IsClosed
      {z : Space m | (f.symm x) i = (c.val i : ℝ) + 1 → ⟪placedCoordinateNormal f i, z⟫_ℝ ≤ 0} := by
    by_cases h : (f.symm x) i = (c.val i : ℝ) + 1
    · simpa only [h, true_implies] using hu i
    · simp [h]
  unfold placedCarrierCone
  simp only [ofPred_exists]
  apply isClosed_iUnion_of_finite
  intro c
  by_cases hc : f.symm x ∈ Polycube.latticeCell c.val
  · simp only [hc, true_and, ofPred_forall, ofPred_and]
    apply isClosed_iInter
    intro i
    simpa only [ofPred_forall] using (hlo c i).inter (hup c i)
  · simp [hc]

#print axioms placedCarrierCone_isClosed
end
end ProductClosure.NativeCompiler
