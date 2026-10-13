module

public import PhysicalRegistration.GenericConicalFans

@[expose] public section

/-! Closedness and nonzero normals of the actual native conical fan. -/
namespace PhysicalRegistration.NativeChair
open scoped InnerProductSpace Topology
open Set
noncomputable section

/-- Orthogonal transport preserves the nonzero condition on a normal. -/
theorem placedNormal_ne_zero {m : ℕ} (f : Space m ≃ᵢ Space m)
    (n : Space m) (hn : n ≠ 0) : placedNormal f n ≠ 0 := by
  simpa [placedNormal] using hn

theorem placed_outward_ne_zero {m : ℕ} (f : Space m ≃ᵢ Space m)
    (u : Site m) : placedNormal f (outward u.1) ≠ 0 := by
  apply placedNormal_ne_zero
  intro h
  have hh := outward_unit u.1
  rw [h, norm_zero] at hh
  norm_num at hh

theorem placed_sideNormal_ne_zero {m J : ℕ} (a : Coefficients m J)
    (f : Space m ≃ᵢ Space m) (u : Site m) (s : Side m) :
    placedNormal f (sideNormal a u s) ≠ 0 :=
  placedNormal_ne_zero f _ (sideNormal_ne_zero a u s)

theorem placedCoordinateNormal_ne_zero {m : ℕ} (f : Space m ≃ᵢ Space m)
    (i : Fin (m + 1)) : placedCoordinateNormal f i ≠ 0 := by
  intro h
  have hh := placedCoordinateNormal_unit f i
  rw [h, norm_zero] at hh
  norm_num at hh

theorem placedActiveCarrierNormals_ne_zero {m : ℕ} (f : Space m ≃ᵢ Space m)
    (x : Space m) : ∀ n ∈ placedActiveCarrierNormals f x, n ≠ 0 := by
  intro n hn
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hn
  exact placedCoordinateNormal_ne_zero f i

/-- Every literal centered closed halfspace is closed. -/
theorem centeredHalfspace_isClosed {m : ℕ} (n : Space m) :
    IsClosed {z : Space m | ⟪n, z⟫_ℝ ≤ 0} :=
  isClosed_le (continuous_const.inner continuous_id) continuous_const

theorem twoHalfspaceCone_isClosed {m : ℕ} (p q : Space m) (b : Bool) :
    IsClosed (twoHalfspaceCone p q b) := by
  cases b
  · exact (centeredHalfspace_isClosed p).inter (centeredHalfspace_isClosed q)
  · exact (centeredHalfspace_isClosed p).union (centeredHalfspace_isClosed q)

/-- The explicit ordinary Boolean cone is closed, including the carrier's
reentrant cases. -/
theorem placedCarrierCone_isClosed {m : ℕ} (f : Space m ≃ᵢ Space m)
    (x : Space m) : IsClosed (placedCarrierCone f x) := by
  have hupper (i : Fin (m + 1)) := centeredHalfspace_isClosed (placedCoordinateNormal f i)
  have hlower (i : Fin (m + 1)) :
      IsClosed {z : Space m | 0 ≤ ⟪placedCoordinateNormal f i, z⟫_ℝ} :=
    isClosed_le continuous_const (continuous_const.inner continuous_id)
  have h0 (i : Fin (m + 1)) : IsClosed
      {z : Space m | (f.symm x) i = 0 → 0 ≤ ⟪placedCoordinateNormal f i, z⟫_ℝ} := by
    by_cases h : (f.symm x) i = 0
    · simpa only [h, true_implies] using hlower i
    · simp [h]
  have h2 (i : Fin (m + 1)) : IsClosed
      {z : Space m | (f.symm x) i = 2 → ⟪placedCoordinateNormal f i, z⟫_ℝ ≤ 0} := by
    by_cases h : (f.symm x) i = 2
    · simpa only [h, true_implies] using hupper i
    · simp [h]
  have h1 (i : Fin (m + 1)) : IsClosed
      {z : Space m | (f.symm x) i < 1 ∨
        ((f.symm x) i = 1 ∧ ⟪placedCoordinateNormal f i, z⟫_ℝ ≤ 0)} := by
    by_cases hlt : (f.symm x) i < 1
    · simp [hlt]
    · by_cases heq : (f.symm x) i = 1
      · simpa [heq] using hupper i
      · simp [hlt, heq]
  change IsClosed ({z | ∀ i, ((f.symm x) i = 0 → 0 ≤ ⟪placedCoordinateNormal f i, z⟫_ℝ) ∧
    ((f.symm x) i = 2 → ⟪placedCoordinateNormal f i, z⟫_ℝ ≤ 0)} ∩
    {z | ∃ i, (f.symm x) i < 1 ∨
      ((f.symm x) i = 1 ∧ ⟪placedCoordinateNormal f i, z⟫_ℝ ≤ 0)})
  apply IsClosed.inter
  · simp only [ofPred_forall, ofPred_and]
    apply isClosed_iInter
    intro i
    simpa only [ofPred_forall] using (h0 i).inter (h2 i)
  · simp only [ofPred_exists]
    exact isClosed_iUnion_of_finite h1

/-- Every cone in the derived native shape classification is closed. -/
theorem ActualNativeCone.isClosed {m J : ℕ} [NeZero m] {a : Coefficients m J}
    {f : Space m ≃ᵢ Space m} {x : Space m} {C : Set (Space m)}
    (h : ActualNativeCone a f x C) : IsClosed C := by
  cases h with
  | strictSide u s hx hs => exact centeredHalfspace_isClosed _
  | base u s hx => exact twoHalfspaceCone_isClosed _ _ _
  | side u s t hst hx => exact twoHalfspaceCone_isClosed _ _ _
  | ordinary hx hkey => exact placedCarrierCone_isClosed _ _

theorem ActualTwoNormalGerm.cone_isClosed {m J : ℕ} [NeZero m]
    {a : Coefficients m J} {f : Space m ≃ᵢ Space m} {x p q : Space m}
    (G : ActualTwoNormalGerm a f x p q) : IsClosed G.cone :=
  G.native_shape.isClosed

#print axioms ActualNativeCone.isClosed
#print axioms placedActiveCarrierNormals_ne_zero

end
end PhysicalRegistration.NativeChair
