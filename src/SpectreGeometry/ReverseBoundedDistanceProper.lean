module

public import Mathlib.Topology.Maps.Proper.CompactlyGenerated
public import Mathlib.Topology.MetricSpace.Bounded

@[expose] public section


/-! A bounded perturbation of a proper map into a proper metric space is proper.
The continuity and distance-bound premises are explicit; this module makes no
claim that any particular cluster-wise map has already supplied them. -/
namespace SpectreGeometry.ReverseExistence
noncomputable section
open Set Metric

/-- The compactness part of bounded-distance properness. -/
theorem isCompact_preimage_of_bounded_distance
    {X Y : Type*} [TopologicalSpace X] [MetricSpace Y] [ProperSpace Y]
    {F H : X → Y} (hF : Continuous F) (hH : IsProperMap H)
    (y₀ : Y) (C : ℝ) (hC : ∀ x, dist (F x) (H x) ≤ C)
    {K : Set Y} (hK : IsCompact K) : IsCompact (F ⁻¹' K) := by
  obtain ⟨r, hr⟩ := hK.isBounded.subset_closedBall y₀
  apply (hH.isCompact_preimage (isCompact_closedBall y₀ (C + r))).of_isClosed_subset
    (hK.isClosed.preimage hF)
  intro x hx
  change dist (H x) y₀ ≤ C + r
  calc
    dist (H x) y₀ ≤ dist (H x) (F x) + dist (F x) y₀ := dist_triangle _ _ _
    _ ≤ C + r := add_le_add (by simpa [dist_comm] using hC x) (hr hx)

/-- Continuous bounded perturbations of proper maps into proper metric spaces are proper. -/
theorem isProperMap_of_bounded_distance
    {X Y : Type*} [TopologicalSpace X] [MetricSpace Y] [ProperSpace Y]
    {F H : X → Y} (hF : Continuous F) (hH : IsProperMap H)
    (y₀ : Y) (C : ℝ) (hC : ∀ x, dist (F x) (H x) ≤ C) : IsProperMap F := by
  exact isProperMap_iff_isCompact_preimage.mpr
    ⟨hF, fun _ hK => isCompact_preimage_of_bounded_distance hF hH y₀ C hC hK⟩

/-- Application-ready properness for a map within bounded distance of an auxiliary homeomorphism. -/
theorem isProperMap_of_bounded_distance_homeomorph
    {X Y : Type*} [TopologicalSpace X] [MetricSpace Y] [ProperSpace Y]
    (H : X ≃ₜ Y) {F : X → Y} (hF : Continuous F)
    (y₀ : Y) (C : ℝ) (hC : ∀ x, dist (F x) (H x) ≤ C) : IsProperMap F :=
  isProperMap_of_bounded_distance hF H.isProperMap y₀ C hC

end
end SpectreGeometry.ReverseExistence
