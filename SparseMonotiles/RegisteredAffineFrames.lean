module

public import SparseMonotiles.RegisteredGridExtension
public import SparseMonotiles.PhysicalPeriodLift

@[expose] public section

/-! Package registration relative to any actual root frame as the single
ambient affine chart used by physical period transport. -/
namespace SparseMonotiles
open Contact

theorem exists_affine_registered_frames_of_relative_registration {d : ℕ}
    {tiles : Set (Set (Point d))} (g : tiles → Point d ≃ᵢ Point d) (A0 : tiles)
    (hreg : ∀ A : tiles, IsRegisteredIsometry ((g A).trans (g A0).symm)) :
    ∃ e : Point d ≃ᵃⁱ[ℝ] Point d, ∃ q : tiles → Pose d,
      ∀ A x, e (g A x) = (q A).euclidean x := by
  classical
  choose q hq using hreg
  refine ⟨(g A0).symm.toRealAffineIsometryEquiv,q,?_⟩
  intro A x
  exact congrArg (fun f : Point d ≃ᵢ Point d => f x) (hq A)

theorem T5_affine_registered_frames_of_exposed_extension
    {tiles : Set (Set (Point 5))} (ht : IsTiling T5 tiles)
    (g : tiles → Point 5 ≃ᵢ Point 5)
    (hg : ∀ A : tiles, (A : Set (Point 5))=g A '' T5)
    (hext : RegisteredExposedExtension g) :
    ∃ e : Point 5 ≃ᵃⁱ[ℝ] Point 5, ∃ q : tiles → Pose 5,
      ∀ A x, e (g A x) = (q A).euclidean x := by
  obtain ⟨A,hA,_⟩ := ht.2.1 (0 : Point 5)
  exact exists_affine_registered_frames_of_relative_registration g ⟨A,hA⟩
    (T5_all_frames_registered_of_exposed_extension ht g (fun B => (hg B).symm) ⟨A,hA⟩ hext)

theorem T7_affine_registered_frames_of_exposed_extension
    {tiles : Set (Set (Point 7))} (ht : IsTiling T7 tiles)
    (g : tiles → Point 7 ≃ᵢ Point 7)
    (hg : ∀ A : tiles, (A : Set (Point 7))=g A '' T7)
    (hext : RegisteredExposedExtension g) :
    ∃ e : Point 7 ≃ᵃⁱ[ℝ] Point 7, ∃ q : tiles → Pose 7,
      ∀ A x, e (g A x) = (q A).euclidean x := by
  obtain ⟨A,hA,_⟩ := ht.2.1 (0 : Point 7)
  exact exists_affine_registered_frames_of_relative_registration g ⟨A,hA⟩
    (T7_all_frames_registered_of_exposed_extension ht g (fun B => (hg B).symm) ⟨A,hA⟩ hext)

#print axioms exists_affine_registered_frames_of_relative_registration
#print axioms T5_affine_registered_frames_of_exposed_extension
#print axioms T7_affine_registered_frames_of_exposed_extension
end SparseMonotiles
