module

public import SparseMonotiles.IncidentTileLocalization
public import SparseMonotiles.TileTilingGeometry

@[expose] public section

/-!
# Incident-tile localization for the exact T5 and T7 bodies

The compactness and positive inball premises of the generic localization bridge
are discharged by the already checked exact tile geometry. The remaining input
is precisely `Model.IsTiling`, with arbitrary isometries and physical tile sets.
-/

namespace SparseMonotiles

open Set Metric

/-- Every point lies in only finitely many physical T5 tiles. -/
theorem T5_tiling_finite_incident {tiles : Set (Set (Point 5))}
    (ht : IsTiling T5 tiles) (p : Point 5) : (incidentTiles tiles p).Finite :=
  ht.finite_incident T5_isCompact (by norm_num) T5_centralBall_from_cellCores p

/-- Every point lies in only finitely many physical T7 tiles. -/
theorem T7_tiling_finite_incident {tiles : Set (Set (Point 7))}
    (ht : IsTiling T7 tiles) (p : Point 7) : (incidentTiles tiles p).Finite :=
  ht.finite_incident T7_isCompact (by norm_num) T7_centralBall_from_cellCores p

/-- A ball around any point meets exactly its incident T5 tiles. -/
theorem T5_tiling_exists_ball_meets_iff_incident {tiles : Set (Set (Point 5))}
    (ht : IsTiling T5 tiles) (p : Point 5) :
    ∃ ε > 0, ∀ A ∈ tiles, (A ∩ ball p ε).Nonempty ↔ p ∈ A :=
  ht.exists_ball_meets_iff_incident T5_isCompact (by norm_num)
    T5_centralBall_from_cellCores p

/-- A ball around any point meets exactly its incident T7 tiles. -/
theorem T7_tiling_exists_ball_meets_iff_incident {tiles : Set (Set (Point 7))}
    (ht : IsTiling T7 tiles) (p : Point 7) :
    ∃ ε > 0, ∀ A ∈ tiles, (A ∩ ball p ε).Nonempty ↔ p ∈ A :=
  ht.exists_ball_meets_iff_incident T7_isCompact (by norm_num)
    T7_centralBall_from_cellCores p

/-- Any proved incident-tile germs in a T5 tiling cover a common ball without
interior overlap. Geometric identification of those germs remains explicit. -/
theorem T5_tiling_exists_ball_local_models_partition {tiles : Set (Set (Point 5))}
    (ht : IsTiling T5 tiles) (p : Point 5)
    (M : incidentTiles tiles p → Set (Point 5))
    (hlocal : ∀ A : incidentTiles tiles p, LocalSetEq p (A : Set (Point 5)) (M A)) :
    ∃ ε > 0, ∀ y ∈ ball p ε,
      (∃ A, y ∈ M A) ∧
      ∀ A B, A ≠ B → ¬ (y ∈ interior (M A) ∧ y ∈ interior (M B)) :=
  ht.exists_ball_local_models_partition T5_isCompact (by norm_num)
    T5_centralBall_from_cellCores p M hlocal

/-- Any proved incident-tile germs in a T7 tiling cover a common ball without
interior overlap. Geometric identification of those germs remains explicit. -/
theorem T7_tiling_exists_ball_local_models_partition {tiles : Set (Set (Point 7))}
    (ht : IsTiling T7 tiles) (p : Point 7)
    (M : incidentTiles tiles p → Set (Point 7))
    (hlocal : ∀ A : incidentTiles tiles p, LocalSetEq p (A : Set (Point 7)) (M A)) :
    ∃ ε > 0, ∀ y ∈ ball p ε,
      (∃ A, y ∈ M A) ∧
      ∀ A B, A ≠ B → ¬ (y ∈ interior (M A) ∧ y ∈ interior (M B)) :=
  ht.exists_ball_local_models_partition T7_isCompact (by norm_num)
    T7_centralBall_from_cellCores p M hlocal

#print axioms T5_tiling_finite_incident
#print axioms T7_tiling_finite_incident
#print axioms T5_tiling_exists_ball_meets_iff_incident
#print axioms T7_tiling_exists_ball_meets_iff_incident
#print axioms T5_tiling_exists_ball_local_models_partition
#print axioms T7_tiling_exists_ball_local_models_partition

end SparseMonotiles
