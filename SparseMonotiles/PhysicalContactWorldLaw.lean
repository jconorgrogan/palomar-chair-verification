module

public import SparseMonotiles.RegisteredIsometryGroup
public import SparseMonotiles.PhysicalRegisteredPeriodEndpoint
public import SparseMonotiles.CarrierHierarchyRefinementLaw

@[expose] public section

/-! Transport a native physical contact law into the common registered carrier
world. All changes of frame are proved equal as actual Euclidean isometries. -/
namespace SparseMonotiles
open Set Contact CarrierHierarchy

theorem relative_pose_of_registered_frames {d : ℕ}
    {tiles : Set (Set (Point d))} (g : tiles → Point d ≃ᵢ Point d)
    (e : Point d ≃ᵃⁱ[ℝ] Point d) (q : tiles → Pose d)
    (hreg : ∀ A x, e (g A x) = (q A).euclidean x) (A B : tiles) :
    (g B).trans (g A).symm = (normalize (q A) (q B)).euclidean.toIsometryEquiv := by
  have he : ∀ A, (g A).trans e.toIsometryEquiv = (q A).euclidean.toIsometryEquiv := by
    intro A
    ext x
    exact congrArg (fun y : Point d => y _) (hreg A x)
  calc
    (g B).trans (g A).symm =
        ((g B).trans e.toIsometryEquiv).trans ((g A).trans e.toIsometryEquiv).symm := by
      ext x
      simp
    _ = (q B).euclidean.toIsometryEquiv.trans (q A).euclidean.toIsometryEquiv.symm := by
      rw [he A,he B]
    _ = (normalize (q A) (q B)).euclidean.toIsometryEquiv := by
      rw [CarrierHierarchy.normalize,compose_euclidean,inversePose_euclidean]
      rfl

theorem normalized_cellContact {d : ℕ} {p q : Pose d} (h : CellContact p q) :
    CellContact (rootPose d) (normalize p q) := by
  apply CellContact.remove_common_left p
  simpa only [compose_root_right,compose_normalize] using h

/-- The local law is applied to actual physical tiles, not independent abstract
copies of a corona or an assumed globally legal registered world. -/
theorem registered_range_law_of_native_physical_law {d : ℕ}
    {tiles : Set (Set (Point d))} (g : tiles → Point d ≃ᵢ Point d)
    (e : Point d ≃ᵃⁱ[ℝ] Point d) (q : tiles → Pose d)
    (hreg : ∀ A x, e (g A x) = (q A).euclidean x) (L : Set (Pose d))
    (hnative : ∀ (A B : tiles) (p : Pose d), B≠A →
      (g B).trans (g A).symm=p.euclidean.toIsometryEquiv →
      CellContact (rootPose d) p → p ∈ L) :
    ∀ p ∈ Set.range q, ∀ r ∈ Set.range q,
      p≠r → CellContact p r → normalize p r ∈ L := by
  rintro p ⟨A,rfl⟩ r ⟨B,rfl⟩ hne hcontact
  have hBA : B≠A := by
    intro he
    subst B
    exact hne rfl
  exact hnative A B (normalize (q A) (q B)) hBA
    (relative_pose_of_registered_frames g e q hreg A B) (normalized_cellContact hcontact)

#print axioms relative_pose_of_registered_frames
#print axioms normalized_cellContact
#print axioms registered_range_law_of_native_physical_law
end SparseMonotiles
