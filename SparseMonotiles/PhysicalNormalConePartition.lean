module

public import SparseMonotiles.OrthogonalTransverseSection
public import SparseMonotiles.GlobalBodyAffine
public import SparseMonotiles.TileIncidentLocalization
public import SparseMonotiles.BoundedTilingRidgePoints

@[expose] public section

/-!
# Genuine normal cone partitions of arbitrary physical tilings

The cones below are built from the global affine equations of the actual
incident tiles, in their arbitrary physical frames. Their covering and
intrinsic-interior disjointness come from the ambient tiling, using the open
orthogonal projection theorem. No angle inventory or planar-partition
hypothesis is supplied. The active-plane hypothesis is precisely the output
of the bounded generic-ridge-point theorem.
-/

namespace SparseMonotiles

open Set Metric

/-- The closed normal cone of an actual incident T5 tile in its fixed frame. -/
noncomputable def T5IncidentNormalCone {tiles : Set (Set (Point 5))}
    (g : tiles → Point 5 ≃ᵢ Point 5) (R : AffineSubspace ℝ (Point 5)) (p : Point 5)
    (A : incidentTiles tiles p) : Set R.directionᗮ :=
  closure (frozenRidgeSection R p (T5WorldAffineFields (g ⟨A, A.property.1⟩))
    (globalBodyFormula keys5 (PyramidHalfspaceIndex 4)))

/-- An actual T5 tiling, at a generic codimension-two ridge point, gives a
finite partition of the entire genuine two-dimensional normal space by
closed homogeneous material cones. Interiors here are intrinsic to that space. -/
theorem T5_tiling_normal_cone_partition
    {tiles : Set (Set (Point 5))} (ht : IsTiling T5 tiles)
    (R : AffineSubspace ℝ (Point 5)) {p : Point 5} (hp : p ∈ R)
    (hcodim : Module.finrank ℝ R.direction + 2 = 5)
    (g : tiles → Point 5 ≃ᵢ Point 5)
    (hg : ∀ A : tiles, (A : Set (Point 5)) = g A '' T5)
    (hactive : ∀ A : incidentTiles tiles p, ∀ j,
      T5WorldAffineFields (g ⟨A, A.property.1⟩) j p = 0 →
        R ≤ affineFormPlane (T5WorldAffineFields (g ⟨A, A.property.1⟩) j) 0) :
    (incidentTiles tiles p).Finite ∧
    Module.finrank ℝ R.directionᗮ = 2 ∧
    (∀ A : incidentTiles tiles p,
      IsClosed (T5IncidentNormalCone g R p A) ∧
      IsPositiveCone (T5IncidentNormalCone g R p A) ∧
      LocalSetEq p (A : Set (Point 5))
        (ridgeNormalProjection R p ⁻¹' T5IncidentNormalCone g R p A)) ∧
    (∀ v : R.directionᗮ, ∃ A, v ∈ T5IncidentNormalCone g R p A) ∧
    ∀ A B : incidentTiles tiles p, A ≠ B →
      Disjoint (interior (T5IncidentNormalCone g R p A))
        (interior (T5IncidentNormalCone g R p B)) := by
  have hlocal (A : incidentTiles tiles p) :
      LocalSetEq p (A : Set (Point 5))
        (ridgeNormalProjection R p ⁻¹' T5IncidentNormalCone g R p A) := by
    have hrepr : (A : Set (Point 5)) =
        closure ((globalBodyFormula keys5 (PyramidHalfspaceIndex 4)).region
          (fun j => T5WorldAffineFields (g ⟨A, A.property.1⟩) j)) := by
      apply (hg ⟨A, A.property.1⟩).trans
      apply (T5_copy_global_halfspace_formula _).trans
      have hf : (fun j x => T5GlobalSlacks j ((g ⟨A, A.property.1⟩).symm x)) =
          (fun j => (T5WorldAffineFields (g ⟨A, A.property.1⟩) j : Point 5 → ℝ)) := by
        funext j x
        exact (T5WorldAffineFields_apply _ j x).symm
      exact congrArg (fun f => closure ((globalBodyFormula keys5
        (PyramidHalfspaceIndex 4)).region f)) hf
    have heq : LocalSetEq p (A : Set (Point 5))
        (closure ((globalBodyFormula keys5 (PyramidHalfspaceIndex 4)).region
          (fun j => T5WorldAffineFields (g ⟨A, A.property.1⟩) j))) :=
      Filter.Eventually.of_forall (Set.ext_iff.mp hrepr)
    exact heq.trans (localSetEq_closed_normal_section R hp _ _
      (fun j hj y hy => (mem_affineFormPlane _ _ _).mp (hactive A j hj hy)))
  have hcones (A : incidentTiles tiles p) :
      IsPositiveCone (T5IncidentNormalCone g R p A) :=
    closure_frozenRidgeSection_isPositiveCone R p _ _
  obtain ⟨ε, hε, hpart⟩ := T5_tiling_exists_ball_local_models_partition ht p
    (fun A => ridgeNormalProjection R p ⁻¹' T5IncidentNormalCone g R p A) hlocal
  have hnormal := ridgeNormalProjection_local_partition R p
    (T5IncidentNormalCone g R p) hpart
  have hglobal := positiveCones_global_partition_of_local
    (T5IncidentNormalCone g R p) hcones hε hnormal
  refine ⟨T5_tiling_finite_incident ht p, ?_,
    fun A => ⟨isClosed_closure, hcones A, hlocal A⟩, hglobal⟩
  apply ridge_orthogonal_finrank_two R
  simpa only [Point, finrank_euclideanSpace, Fintype.card_fin] using hcodim

#print axioms T5_tiling_normal_cone_partition

/-- The closed normal cone of an actual incident T7 tile in its fixed frame. -/
noncomputable def T7IncidentNormalCone {tiles : Set (Set (Point 7))}
    (g : tiles → Point 7 ≃ᵢ Point 7) (R : AffineSubspace ℝ (Point 7)) (p : Point 7)
    (A : incidentTiles tiles p) : Set R.directionᗮ :=
  closure (frozenRidgeSection R p (T7WorldAffineFields (g ⟨A, A.property.1⟩))
    (globalBodyFormula keys7 (PyramidHalfspaceIndex 6)))

/-- An actual T7 tiling, at a generic codimension-two ridge point, gives a
finite partition of the entire genuine two-dimensional normal space by
closed homogeneous material cones. Interiors here are intrinsic to that space. -/
theorem T7_tiling_normal_cone_partition
    {tiles : Set (Set (Point 7))} (ht : IsTiling T7 tiles)
    (R : AffineSubspace ℝ (Point 7)) {p : Point 7} (hp : p ∈ R)
    (hcodim : Module.finrank ℝ R.direction + 2 = 7)
    (g : tiles → Point 7 ≃ᵢ Point 7)
    (hg : ∀ A : tiles, (A : Set (Point 7)) = g A '' T7)
    (hactive : ∀ A : incidentTiles tiles p, ∀ j,
      T7WorldAffineFields (g ⟨A, A.property.1⟩) j p = 0 →
        R ≤ affineFormPlane (T7WorldAffineFields (g ⟨A, A.property.1⟩) j) 0) :
    (incidentTiles tiles p).Finite ∧
    Module.finrank ℝ R.directionᗮ = 2 ∧
    (∀ A : incidentTiles tiles p,
      IsClosed (T7IncidentNormalCone g R p A) ∧
      IsPositiveCone (T7IncidentNormalCone g R p A) ∧
      LocalSetEq p (A : Set (Point 7))
        (ridgeNormalProjection R p ⁻¹' T7IncidentNormalCone g R p A)) ∧
    (∀ v : R.directionᗮ, ∃ A, v ∈ T7IncidentNormalCone g R p A) ∧
    ∀ A B : incidentTiles tiles p, A ≠ B →
      Disjoint (interior (T7IncidentNormalCone g R p A))
        (interior (T7IncidentNormalCone g R p B)) := by
  have hlocal (A : incidentTiles tiles p) :
      LocalSetEq p (A : Set (Point 7))
        (ridgeNormalProjection R p ⁻¹' T7IncidentNormalCone g R p A) := by
    have hrepr : (A : Set (Point 7)) =
        closure ((globalBodyFormula keys7 (PyramidHalfspaceIndex 6)).region
          (fun j => T7WorldAffineFields (g ⟨A, A.property.1⟩) j)) := by
      apply (hg ⟨A, A.property.1⟩).trans
      apply (T7_copy_global_halfspace_formula _).trans
      have hf : (fun j x => T7GlobalSlacks j ((g ⟨A, A.property.1⟩).symm x)) =
          (fun j => (T7WorldAffineFields (g ⟨A, A.property.1⟩) j : Point 7 → ℝ)) := by
        funext j x
        exact (T7WorldAffineFields_apply _ j x).symm
      exact congrArg (fun f => closure ((globalBodyFormula keys7
        (PyramidHalfspaceIndex 6)).region f)) hf
    have heq : LocalSetEq p (A : Set (Point 7))
        (closure ((globalBodyFormula keys7 (PyramidHalfspaceIndex 6)).region
          (fun j => T7WorldAffineFields (g ⟨A, A.property.1⟩) j))) :=
      Filter.Eventually.of_forall (Set.ext_iff.mp hrepr)
    exact heq.trans (localSetEq_closed_normal_section R hp _ _
      (fun j hj y hy => (mem_affineFormPlane _ _ _).mp (hactive A j hj hy)))
  have hcones (A : incidentTiles tiles p) :
      IsPositiveCone (T7IncidentNormalCone g R p A) :=
    closure_frozenRidgeSection_isPositiveCone R p _ _
  obtain ⟨ε, hε, hpart⟩ := T7_tiling_exists_ball_local_models_partition ht p
    (fun A => ridgeNormalProjection R p ⁻¹' T7IncidentNormalCone g R p A) hlocal
  have hnormal := ridgeNormalProjection_local_partition R p
    (T7IncidentNormalCone g R p) hpart
  have hglobal := positiveCones_global_partition_of_local
    (T7IncidentNormalCone g R p) hcones hε hnormal
  refine ⟨T7_tiling_finite_incident ht p, ?_,
    fun A => ⟨isClosed_closure, hcones A, hlocal A⟩, hglobal⟩
  apply ridge_orthogonal_finrank_two R
  simpa only [Point, finrank_euclideanSpace, Fintype.card_fin] using hcodim

#print axioms T7_tiling_normal_cone_partition

/-- Every nonempty relatively open codimension-two ridge patch inside a fixed
bounded set contains a point carrying the genuine finite T5 normal-cone
partition. All physical frames are selected before the patch and point. -/
theorem T5_tiling_exists_normal_cone_partition_in_open
    {tiles : Set (Set (Point 5))} (ht : IsTiling T5 tiles)
    {K : Set (Point 5)} (hK : Bornology.IsBounded K)
    (R : AffineSubspace ℝ (Point 5)) (hR : (R : Set (Point 5)).Nonempty)
    (hcodim : Module.finrank ℝ R.direction + 2 = 5) :
    ∃ g : tiles → Point 5 ≃ᵢ Point 5,
      (∀ A : tiles, (A : Set (Point 5)) = g A '' T5) ∧
      ∀ O : Set R, IsOpen O → O.Nonempty →
        (∀ x ∈ O, (x : Point 5) ∈ K) →
        ∃ p ∈ O,
          (∀ A : incidentTiles tiles (p : Point 5), ∀ j,
            T5WorldAffineFields (g ⟨A, A.property.1⟩) j p = 0 →
              R ≤ affineFormPlane (T5WorldAffineFields (g ⟨A, A.property.1⟩) j) 0) ∧
          (incidentTiles tiles (p : Point 5)).Finite ∧
          Module.finrank ℝ R.directionᗮ = 2 ∧
          (∀ A : incidentTiles tiles (p : Point 5),
            IsClosed (T5IncidentNormalCone g R p A) ∧
            IsPositiveCone (T5IncidentNormalCone g R p A) ∧
            LocalSetEq (p : Point 5) (A : Set (Point 5))
              (ridgeNormalProjection R p ⁻¹' T5IncidentNormalCone g R p A)) ∧
          (∀ v : R.directionᗮ, ∃ A, v ∈ T5IncidentNormalCone g R p A) ∧
          ∀ A B : incidentTiles tiles (p : Point 5), A ≠ B →
            Disjoint (interior (T5IncidentNormalCone g R p A))
              (interior (T5IncidentNormalCone g R p B)) := by
  obtain ⟨g, hg, hgeneric⟩ :=
    T5_tiling_fixed_frames_generic_point_in_open ht hK R hR
  refine ⟨g, hg, ?_⟩
  intro O hO hne hOK
  obtain ⟨p, hpO, hpactive⟩ := hgeneric O hO hne hOK
  refine ⟨p, hpO, (fun A j hj => hpactive ⟨A, A.property.1⟩ A.property.2 j hj), ?_⟩
  exact T5_tiling_normal_cone_partition ht R p.property hcodim g hg
    (fun A j hj => hpactive ⟨A, A.property.1⟩ A.property.2 j hj)

#print axioms T5_tiling_exists_normal_cone_partition_in_open

/-- Every nonempty relatively open codimension-two ridge patch inside a fixed
bounded set contains a point carrying the genuine finite T7 normal-cone
partition. All physical frames are selected before the patch and point. -/
theorem T7_tiling_exists_normal_cone_partition_in_open
    {tiles : Set (Set (Point 7))} (ht : IsTiling T7 tiles)
    {K : Set (Point 7)} (hK : Bornology.IsBounded K)
    (R : AffineSubspace ℝ (Point 7)) (hR : (R : Set (Point 7)).Nonempty)
    (hcodim : Module.finrank ℝ R.direction + 2 = 7) :
    ∃ g : tiles → Point 7 ≃ᵢ Point 7,
      (∀ A : tiles, (A : Set (Point 7)) = g A '' T7) ∧
      ∀ O : Set R, IsOpen O → O.Nonempty →
        (∀ x ∈ O, (x : Point 7) ∈ K) →
        ∃ p ∈ O,
          (∀ A : incidentTiles tiles (p : Point 7), ∀ j,
            T7WorldAffineFields (g ⟨A, A.property.1⟩) j p = 0 →
              R ≤ affineFormPlane (T7WorldAffineFields (g ⟨A, A.property.1⟩) j) 0) ∧
          (incidentTiles tiles (p : Point 7)).Finite ∧
          Module.finrank ℝ R.directionᗮ = 2 ∧
          (∀ A : incidentTiles tiles (p : Point 7),
            IsClosed (T7IncidentNormalCone g R p A) ∧
            IsPositiveCone (T7IncidentNormalCone g R p A) ∧
            LocalSetEq (p : Point 7) (A : Set (Point 7))
              (ridgeNormalProjection R p ⁻¹' T7IncidentNormalCone g R p A)) ∧
          (∀ v : R.directionᗮ, ∃ A, v ∈ T7IncidentNormalCone g R p A) ∧
          ∀ A B : incidentTiles tiles (p : Point 7), A ≠ B →
            Disjoint (interior (T7IncidentNormalCone g R p A))
              (interior (T7IncidentNormalCone g R p B)) := by
  obtain ⟨g, hg, hgeneric⟩ :=
    T7_tiling_fixed_frames_generic_point_in_open ht hK R hR
  refine ⟨g, hg, ?_⟩
  intro O hO hne hOK
  obtain ⟨p, hpO, hpactive⟩ := hgeneric O hO hne hOK
  refine ⟨p, hpO, (fun A j hj => hpactive ⟨A, A.property.1⟩ A.property.2 j hj), ?_⟩
  exact T7_tiling_normal_cone_partition ht R p.property hcodim g hg
    (fun A j hj => hpactive ⟨A, A.property.1⟩ A.property.2 j hj)

#print axioms T7_tiling_exists_normal_cone_partition_in_open

end SparseMonotiles
