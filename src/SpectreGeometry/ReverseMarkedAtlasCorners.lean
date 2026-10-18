module

public import SpectreGeometry.ReverseMarkedAtlasBoundaryVertices
public import SpectreGeometry.ReverseSourceHexIncidence

@[expose] public section


namespace SpectreGeometry.ReverseExistence
noncomputable section
open Set SpectreClusters SpectreClusters.ReverseExistence SpectreFinite SpectreFinite.HexSearch
open ReverseClusterTriangulation ReverseLocalStarOccurrences ReverseFinitePL

private theorem turn_one_eq_add : ∀ d : Fin 6, rotateTurn 1 d = d+1 := by decide

private theorem next_neighbor_from_neighbor (c : Position) (d : Fin 6) :
    sourceHexNeighbor (sourceHexNeighbor c d) (rotateTurn 2 d) = sourceHexNeighbor c (d+1) := by
  fin_cases d <;> apply Prod.ext <;>
    norm_num [sourceHexNeighbor,SpectreFinite.direction,rotateTurn] <;> omega

private theorem source_corner_neighbor_start (c : Position) (d : Fin 6) :
    sourceHexCornerAt (sourceHexNeighbor c d) (opposite d) = sourceHexCornerAt c (d+1) := by
  have h := sourceHexNeighbor_side_reverse c d 1
  simpa only [sub_self,AffineMap.lineMap_apply_zero,AffineMap.lineMap_apply_one] using h

private theorem source_corner_next_neighbor_start (c : Position) (d : Fin 6) :
    sourceHexCornerAt (sourceHexNeighbor c (d+1)) (rotateTurn 4 (rotateTurn 1 d)) =
      sourceHexCornerAt c (d+1) := by
  have he : opposite (d+1)+1 = rotateTurn 4 (rotateTurn 1 d) := by
    have h : ∀ e : Fin 6, opposite (e+1)+1 = rotateTurn 4 (rotateTurn 1 e) := by decide
    exact h d
  have h := sourceHexNeighbor_side_reverse c (d+1) 0
  simpa only [sub_zero,AffineMap.lineMap_apply_zero,AffineMap.lineMap_apply_one,he] using h

private theorem getLastD_eq_getD_last {α : Type*} (ps : List α) (a : α) :
    ps.getLastD a = ps.getD (ps.length-1) a := by
  simp only [List.getLastD_eq_getLast?,List.getLast?_eq_getElem?,List.getD_eq_getElem?_getD]

variable (hlocal : ∀ k : Fin 9, sourceHexCarrier (0,0) ≃ₜ rawClusterBody (clusterOfMark k))
variable (hboundary : ∀ k, MarkedBoundarySubintervalLaw k (fun x => (hlocal k x).val))
variable (f : Position → State) (hf : GloballyLegal f)

include hboundary in
/-- The chart value at the starting corner is its literal first boundary vertex. -/
theorem markedPlacedChart_boundary_start (c : Position) (d : Fin 6) (x : sourceHexCarrier c)
    (hx : x.val = sourceHexCornerAt c d) :
    (markedPlacedChart hlocal f hf c x).val =
      markedAnchor f hf c+gridRotation (f c).2 ((1/6:ℝ) • integerPoint
        (targetVertex (f c).1 ((stateBoundaryIds (f c) d).headD 0))) := by
  have hn : 0 < (stateBoundaryIds (f c) d).length := by
    have h : 1 < (stateBoundaryIds (f c) d).length :=
      (all_boundary_linear_checks (f c).1 (sideTurn (f c).2 d)).1
    omega
  rw [List.headD_eq_getD]
  apply markedPlacedChart_boundary_vertex hlocal hboundary f hf c d 0 hn x
  simpa only [Nat.cast_zero,zero_div,AffineMap.lineMap_apply_zero] using hx

include hboundary in
/-- The chart value at the terminal corner is its literal last boundary vertex. -/
theorem markedPlacedChart_boundary_end (c : Position) (d : Fin 6) (x : sourceHexCarrier c)
    (hx : x.val = sourceHexCornerAt c (d+1)) :
    (markedPlacedChart hlocal f hf c x).val =
      markedAnchor f hf c+gridRotation (f c).2 ((1/6:ℝ) • integerPoint
        (targetVertex (f c).1 ((stateBoundaryIds (f c) d).getLastD 0))) := by
  have hn : 1 < (stateBoundaryIds (f c) d).length :=
    (all_boundary_linear_checks (f c).1 (sideTurn (f c).2 d)).1
  have hne : (((stateBoundaryIds (f c) d).length-1:Nat):ℝ) ≠ 0 := by
    exact_mod_cast (show (stateBoundaryIds (f c) d).length-1 ≠ 0 by omega)
  rw [getLastD_eq_getD_last]
  apply markedPlacedChart_boundary_vertex hlocal hboundary f hf c d _ (by omega) x
  simpa only [div_self hne,AffineMap.lineMap_apply_one] using hx

/-- At every actual source triple corner, the three complete target carriers
contain an ambient neighborhood of the atlas image. -/
theorem marked_corner_targetStar_interior
    (hraw : ∀ big v, RawStarBinding big v) (hrows : IncidentRowsCorrect)
    (hcert : ∀ i : Fin 49, TripleGeometryCertificate i.val)
    (hbind : ∀ k d, TripleGeometryBinding k d)
    (c : Position) (d : Fin 6) :
    (markedCarrierAtlas hlocal f hf (marked_neighbor_agreement hlocal hboundary f hf)).map
      (sourceHexCornerAt c (d+1)) ∈
      interior ((markedCarrierAtlas hlocal f hf
        (marked_neighbor_agreement hlocal hboundary f hf)).targetStar
          (sourceHexCornerAt c (d+1))) := by
  let A := markedCarrierAtlas hlocal f hf (marked_neighbor_agreement hlocal hboundary f hf)
  let p := sourceHexCornerAt c (d+1)
  let b := sourceHexNeighbor c d
  let e := sourceHexNeighbor c (d+1)
  have hp : p ∈ sourceHexCarrier c := sourceHexCornerAt_mem_center c (d+1)
  have hpb : p ∈ sourceHexCarrier b :=
    (sourceHexCornerAt_incident_iff c b d).mpr (Or.inr (Or.inl rfl))
  have hpe : p ∈ sourceHexCarrier e :=
    (sourceHexCornerAt_incident_iff c e d).mpr (Or.inr (Or.inr rfl))
  have hA := markedPlacedChart_boundary_end hlocal hboundary f hf c d ⟨p,hp⟩ rfl
  have hB := markedPlacedChart_boundary_start hlocal hboundary f hf b (opposite d) ⟨p,hpb⟩
    (source_corner_neighbor_start c d).symm
  have hC := markedPlacedChart_boundary_start hlocal hboundary f hf e
    (rotateTurn 4 (rotateTurn 1 d)) ⟨p,hpe⟩ (source_corner_next_neighbor_start c d).symm
  have hmA := A.map_on c p hp
  have hmB := A.map_on b p hpb
  have hmC := A.map_on e p hpe
  have hAB := field_sideMatch f hf c d
  have hAC : sideMatch (f c) (f e) (rotateTurn 1 d) := by
    rw [turn_one_eq_add]
    exact field_sideMatch f hf c (d+1)
  have hBC : sideMatch (f b) (f e) (rotateTurn 2 d) := by
    have h := field_sideMatch f hf b (rotateTurn 2 d)
    change sideMatch (f b) (f (sourceHexNeighbor b (rotateTurn 2 d))) (rotateTurn 2 d) at h
    rw [show sourceHexNeighbor b (rotateTurn 2 d)=e from next_neighbor_from_neighbor c d] at h
    exact h
  have hbound (z : Position) (q : Fin 6) :
      (stateBoundaryIds (f z) q).headD 0 < (targetVertices (f z).1).length ∧
      (stateBoundaryIds (f z) q).getLastD 0 < (targetVertices (f z).1).length := by
    have hn : 1 < (stateBoundaryIds (f z) q).length :=
      (all_boundary_linear_checks (f z).1 (sideTurn (f z).2 q)).1
    have hlength : (stateBoundaryIds (f z) q).length =
        (boundaryIndices (f z).1 (sideTurn (f z).2 q)).length := rfl
    rw [List.headD_eq_getD,getLastD_eq_getD_last]
    exact ⟨(boundary_vertex_index_bound (f z).1 (sideTurn (f z).2 q) 0 (by omega)).2,
      (boundary_vertex_index_bound (f z).1 (sideTurn (f z).2 q) _ (by omega)).2⟩
  have hi := triple_placed_origin_interior hraw hrows hcert hbind (f c) (f b) (f e) d
    hAB hAC hBC (markedAnchor f hf c) (markedAnchor f hf b) (markedAnchor f hf e) (A.map p)
    (hbound c d).2 (hbound b (opposite d)).1 (hbound e (rotateTurn 4 (rotateTurn 1 d))).1
    (hA.symm.trans hmA.symm) (hB.symm.trans hmB.symm) (hC.symm.trans hmC.symm)
  apply interior_mono (s := markedTargetCarrier f hf c ∪ markedTargetCarrier f hf b ∪
    markedTargetCarrier f hf e) (t := A.targetStar p) ?_ hi
  rintro y ((hy | hy) | hy)
  · exact mem_iUnion.mpr ⟨⟨c,hp⟩,hy⟩
  · exact mem_iUnion.mpr ⟨⟨b,hpb⟩,hy⟩
  · exact mem_iUnion.mpr ⟨⟨e,hpe⟩,hy⟩

end
end SpectreGeometry.ReverseExistence
