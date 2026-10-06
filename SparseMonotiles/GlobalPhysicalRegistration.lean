module

public import SparseMonotiles.RegisteredAffineFrames
public import SparseMonotiles.ExposedCellExtensionRegistered
public import SparseMonotiles.PhysicalRegisteredPeriodEndpoint

@[expose] public section

/-! Global registration for arbitrary physical tilings of the exact T5/T7
bodies. All local companion, exposed-facet, integer-grid and core-clamp premises
are discharged. No registered-placement assumption is introduced. -/
namespace SparseMonotiles
open Set Contact CarrierHierarchy

theorem T5_global_registered_frames
    {tiles : Set (Set (Point 5))} (ht : IsTiling T5 tiles)
    (g : tiles → Point 5 ≃ᵢ Point 5)
    (hg : ∀ A : tiles, (A : Set (Point 5))=g A '' T5) :
    ∃ e : Point 5 ≃ᵃⁱ[ℝ] Point 5, ∃ q : tiles → Pose 5,
      ∀ A x, e (g A x) = (q A).euclidean x :=
  T5_affine_registered_frames_of_exposed_extension ht g hg
    (T5_registered_exposed_extension ht g (fun A => (hg A).symm))

theorem T7_global_registered_frames
    {tiles : Set (Set (Point 7))} (ht : IsTiling T7 tiles)
    (g : tiles → Point 7 ≃ᵢ Point 7)
    (hg : ∀ A : tiles, (A : Set (Point 7))=g A '' T7) :
    ∃ e : Point 7 ≃ᵃⁱ[ℝ] Point 7, ∃ q : tiles → Pose 7,
      ∀ A x, e (g A x) = (q A).euclidean x :=
  T7_affine_registered_frames_of_exposed_extension ht g hg
    (T7_registered_exposed_extension ht g (fun A => (hg A).symm))

/-- The normalized carrier world is constructed from the actual physical tiling. -/
theorem T5_global_registered_carrier_world
    {tiles : Set (Set (Point 5))} (ht : IsTiling T5 tiles)
    (g : tiles → Point 5 ≃ᵢ Point 5)
    (hg : ∀ A : tiles, (A : Set (Point 5))=g A '' T5) :
    ∃ e : Point 5 ≃ᵃⁱ[ℝ] Point 5, ∃ q : tiles → Pose 5,
      (∀ A x, e (g A x) = (q A).euclidean x) ∧
      ∃ W : RegisteredWorld 5, W.tiles=Set.range q := by
  obtain ⟨e,q,hq⟩ := T5_global_registered_frames ht g hg
  refine ⟨e,q,hq,?_⟩
  let W := T5_registeredWorld ht e.toIsometryEquiv q (registered_frame_images g hg e q hq)
  exact ⟨W,rfl⟩

theorem T7_global_registered_carrier_world
    {tiles : Set (Set (Point 7))} (ht : IsTiling T7 tiles)
    (g : tiles → Point 7 ≃ᵢ Point 7)
    (hg : ∀ A : tiles, (A : Set (Point 7))=g A '' T7) :
    ∃ e : Point 7 ≃ᵃⁱ[ℝ] Point 7, ∃ q : tiles → Pose 7,
      (∀ A x, e (g A x) = (q A).euclidean x) ∧
      ∃ W : RegisteredWorld 7, W.tiles=Set.range q := by
  obtain ⟨e,q,hq⟩ := T7_global_registered_frames ht g hg
  refine ⟨e,q,hq,?_⟩
  let W := T7_registeredWorld ht e.toIsometryEquiv q (registered_frame_images g hg e q hq)
  exact ⟨W,rfl⟩

#print axioms T5_global_registered_frames
#print axioms T7_global_registered_frames
#print axioms T5_global_registered_carrier_world
#print axioms T7_global_registered_carrier_world
end SparseMonotiles
