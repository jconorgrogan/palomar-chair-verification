module

public import SparseMonotiles.PhysicalPeriodLift
public import SparseMonotiles.RegisteredPhysicalWorld

@[expose] public section

/-!
# Compose registered physical frames with a registered-world period theorem

Carrier coverage, unique ownership, integer period transport, and the final
linear cancellation are proved here. Registration and the finite contact law
remain explicit hypotheses. This is not an unconditional T5/T7 theorem.
-/
namespace SparseMonotiles
open Set Contact CarrierHierarchy

theorem registered_frame_images {d : ℕ} {T : Set (Point d)}
    {tiles : Set (Set (Point d))} (g : tiles → Point d ≃ᵢ Point d)
    (hg : ∀ A : tiles, (A : Set (Point d)) = g A '' T)
    (e : Point d ≃ᵃⁱ[ℝ] Point d) (q : tiles → Pose d)
    (hreg : ∀ A x, e (g A x) = (q A).euclidean x) :
    ∀ A : tiles, e.toIsometryEquiv '' (A : Set (Point d)) = (q A).euclidean '' T := by
  intro A
  rw [hg A,Set.image_image]
  have hf : (e.toIsometryEquiv : Point d → Point d) ∘ (g A) = (q A).euclidean := by
    funext x
    exact hreg A x
  change ((e.toIsometryEquiv : Point d → Point d) ∘ (g A)) '' T = _
  rw [hf]

/-- The full physical-to-registered period composition, without an assumed
carrier-cell tiling or assumed integer translation vector. -/
theorem physical_period_zero_of_registered_legal_frames {d : ℕ}
    {T : Set (Point d)} {tiles : Set (Set (Point d))} (ht : IsTiling T tiles)
    (hc : ∀ c : Cell d, cellCentre c ∈ T ↔ IsChairCell c)
    (hi : ∀ c : Cell d, IsChairCell c → cellCentre c ∈ interior T)
    (L : Set (Pose d))
    (g : tiles → Point d ≃ᵢ Point d)
    (hg : ∀ A : tiles, (A : Set (Point d)) = g A '' T)
    (hequiv : ∀ v, ∀ hv : IsPeriod tiles v, ∀ A : tiles,
      g (periodTile hv A) = (g A).trans (translationIsometry v))
    (e : Point d ≃ᵃⁱ[ℝ] Point d) (q : tiles → Pose d)
    (hreg : ∀ A x, e (g A x) = (q A).euclidean x)
    (hlaw : ∀ p ∈ Set.range q, ∀ r ∈ Set.range q,
      p ≠ r → CellContact p r → normalize p r ∈ L)
    (hzero : ∀ W : RegisteredWorld d, W.Legal L → ∀ w, W.IsPeriod w → w=0)
    {v : Point d} (hv : IsPeriod tiles v) : v=0 := by
  let W := registeredWorldOfPhysicalFrames ht hc hi e.toIsometryEquiv q
    (registered_frame_images g hg e q hreg)
  have hlegal : W.Legal L := hlaw
  obtain ⟨A,hA,_⟩ := ht.2.1 (0 : Point d)
  exact physical_period_zero_of_registered_frame_world ⟨A,hA⟩ g hequiv e q hreg W rfl
    (hzero W hlegal) hv

/-- Compactness discharges all frame-choice and period-equivariance premises.
The remaining registration/contact hypothesis is explicitly quantified over
actual physical tilings and arbitrary supplied image-certified frames. -/
theorem isAperiodic_of_registered_legal_frames {d : ℕ}
    (T : Set (Point d)) (hcompact : IsCompact T)
    (hc : ∀ c : Cell d, cellCentre c ∈ T ↔ IsChairCell c)
    (hi : ∀ c : Cell d, IsChairCell c → cellCentre c ∈ interior T)
    (L : Set (Pose d))
    (hregister : ∀ tiles, IsTiling T tiles → ∀ g : tiles → Point d ≃ᵢ Point d,
      (∀ A : tiles, (A : Set (Point d)) = g A '' T) →
      ∃ e : Point d ≃ᵃⁱ[ℝ] Point d, ∃ q : tiles → Pose d,
        (∀ A x, e (g A x) = (q A).euclidean x) ∧
        (∀ p ∈ Set.range q, ∀ r ∈ Set.range q,
          p ≠ r → CellContact p r → normalize p r ∈ L))
    (hzero : ∀ W : RegisteredWorld d, W.Legal L → ∀ w, W.IsPeriod w → w=0) :
    IsAperiodic T := by
  intro tiles ht v hv
  obtain ⟨g,hg,hequiv⟩ := ht.exists_translation_equivariant_representatives hcompact
  obtain ⟨e,q,hreg,hlaw⟩ := hregister tiles ht g hg
  exact physical_period_zero_of_registered_legal_frames ht hc hi L g hg hequiv e q hreg hlaw hzero hv

#print axioms physical_period_zero_of_registered_legal_frames
#print axioms isAperiodic_of_registered_legal_frames
end SparseMonotiles
