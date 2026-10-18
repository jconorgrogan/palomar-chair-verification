module

public import SpectreGeometry.ReverseLocalStarPlacedNeighborhood
public import SpectreGeometry.ReverseLocalStarInteriorFastData
public import SpectreGeometry.ReverseLocalStarBoundaryIndexBinding

@[expose] public section


namespace SpectreGeometry.ReverseLocalStarOccurrences
noncomputable section
open Set SpectreClusters SpectreClusters.ReverseExistence SpectreFinite.HexSearch
open ReverseClusterTriangulation ReverseExistence

theorem origin_interior_rotated (ts : List (List Point)) (r : Fin 6)
    (h : (0:RealPoint) ∈ interior (starBody ts)) :
    (0:RealPoint) ∈ interior (starBody (rotatedStar ts r)) := by
  rw [starBody_rotate,←(gridTurnHomeomorph r).image_interior]
  exact ⟨0,h,(gridRotationLinear r).map_zero⟩

/-- Every nonboundary vertex in an actual rotated marked mesh carries the
checked complete interior star, using the finite kind reduction. -/
theorem interior_fast_origin
    (hcert : ∀ big v, InteriorFastCertificate big v)
    (k : Fin 9) (r : Fin 6) (v : Nat)
    (hv : v < (targetVertices k).length) (hnb : ¬IsBoundaryIndex k v) :
    (0:RealPoint) ∈ interior (starBody (fastLocalStar (k,r) v)) := by
  have hv133 : v < 133 := by
    have he := all_target_lengths k
    rw [he] at hv
    split_ifs at hv <;> omega
  have hv' : v < (targetVertices (kindMark (k.val != 0))).length := by
    rwa [targetVertices_kind_reduced]
  have hnb' : ¬IsBoundaryIndex (kindMark (k.val != 0)) v := by
    intro h
    exact hnb ((all_boundary_indices_kind_reduced k ⟨v,hv133⟩).mpr h)
  have hi := structural_occurrence_origin _ _ (hcert (k.val != 0) v hv' hnb')
  have he : fastLocalStar (kindMark (k.val != 0),0) v = fastLocalStar (k,0) v := by
    fin_cases k <;> rfl
  rw [he] at hi
  have hr := fastLocalStar_rotate r (k,0) v
  simp only [rotateState,rotateTurn_zero_right] at hr
  rw [hr]
  exact origin_interior_rotated _ r hi

/-- The certified interior vertex is interior to the literal placed cluster,
not merely to an abstract normalized star packet. -/
theorem placed_interior_vertex
    (hraw : ∀ big v, RawStarBinding big v) (hrows : IncidentRowsCorrect)
    (hcert : ∀ big v, InteriorFastCertificate big v)
    (k : Fin 9) (r : Fin 6) (v : Nat) (anchor : RealPoint)
    (hv : v < (targetVertices k).length) (hnb : ¬IsBoundaryIndex k v) :
    anchor + gridRotation r ((1/6:ℝ) • integerPoint (targetVertex k v)) ∈
      interior (placedClusterCarrier r anchor (clusterOfMark k)) := by
  apply translated_scaled_origin_interior _ (1/6) (by norm_num)
    (interior_fast_origin hcert k r v hv hnb)
  exact fastLocalStar_image_subset_placedClusterCarrier hraw hrows (k,r) v anchor _ hv rfl

end
end SpectreGeometry.ReverseLocalStarOccurrences
