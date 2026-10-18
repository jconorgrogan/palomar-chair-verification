module

public import SpectreGeometry.ReverseLocalStarActualGeometry
public import SpectreGeometry.ReverseLocalStarNeighborhood
public import SpectreGeometry.ReverseLocalStarIncidentSoundness

@[expose] public section


/-! The checked cached stars give actual ambient neighborhoods after their
common target vertex is identified. All index and center bindings are explicit. -/
namespace SpectreGeometry.ReverseLocalStarOccurrences
noncomputable section
open Set SpectreClusters SpectreClusters.ReverseExistence SpectreFinite SpectreFinite.HexSearch
open ReverseClusterTriangulation ReverseExistence

/-- The raw target mesh depends only on the two literal cluster kinds. -/
theorem localStar_kind_reduced (k : Fin 9) (r : Fin 6) (v : Nat) :
    localStar (kindMark (k.val != 0),r) v = localStar (k,r) v := by
  fin_cases k <;> rfl

/-- Bind the fast finite lookup to the full actual rotated incident star. -/
theorem fastLocalStar_eq_localStar
    (hraw : ∀ big v, RawStarBinding big v)
    (k : Fin 9) (r : Fin 6) (v : Nat)
    (hv : v < (targetVertices k).length) :
    fastLocalStar (k,r) v = localStar (k,r) v := by
  have hv' : v < (targetVertices (kindMark (k.val != 0))).length := by
    rwa [targetVertices_kind_reduced]
  have h0 : rawStarValue (k.val != 0) v = localStar (k,0) v :=
    (hraw (k.val != 0) v hv').trans (localStar_kind_reduced k 0 v)
  have hr := localStar_rotate r (k,0) v
  simp only [rotateState,rotateTurn_zero_right] at hr
  rw [hr]
  exact congrArg (fun ts : List (List Point) =>
    ts.map (fun t => t.map (SpectreClusters.rotate r))) h0

/-- A finite cached star is included in its actual placed closed carrier. -/
theorem fastLocalStar_image_subset_placedClusterCarrier
    (hraw : ∀ big v, RawStarBinding big v) (hrows : IncidentRowsCorrect)
    (a : State) (v : Nat) (anchor center : RealPoint)
    (hv : v < (targetVertices a.1).length)
    (hc : anchor + gridRotation a.2 ((1/6:ℝ) • integerPoint (targetVertex a.1 v)) = center) :
    (fun q : RealPoint => center + (1/6:ℝ) • q) '' starBody (fastLocalStar a v) ⊆
      placedClusterCarrier a.2 anchor (clusterOfMark a.1) := by
  rcases a with ⟨k,r⟩
  rw [fastLocalStar_eq_localStar hraw k r v hv]
  have h := localStar_image_subset_placedClusterCarrier k r v anchor
    (incidentIds_bound hrows k v hv)
  rw [hc] at h
  exact h

theorem starBody_append (s t : List (List Point)) :
    starBody (s++t) = starBody s ∪ starBody t := by
  ext x
  simp only [starBody,mem_setOf_eq,List.mem_append,mem_union]
  constructor
  · rintro ⟨u,hu,hx⟩
    rcases hu with hs | ht
    · exact Or.inl ⟨u,hs,hx⟩
    · exact Or.inr ⟨u,ht,hx⟩
  · rintro (⟨u,hu,hx⟩ | ⟨u,hu,hx⟩)
    · exact ⟨u,Or.inl hu,hx⟩
    · exact ⟨u,Or.inr hu,hx⟩

/-- Any family of verified stars, recentered at the same actual target point,
transfers its origin neighborhood into the union of the genuine carriers. -/
theorem placed_stars_origin_interior {ι : Type*}
    (hraw : ∀ big v, RawStarBinding big v) (hrows : IncidentRowsCorrect)
    (a : ι → State) (v : ι → Nat) (anchor : ι → RealPoint) (center : RealPoint)
    (hv : ∀ i, v i < (targetVertices (a i).1).length)
    (hc : ∀ i, anchor i + gridRotation (a i).2
      ((1/6:ℝ) • integerPoint (targetVertex (a i).1 (v i))) = center)
    (hzero : (0:RealPoint) ∈ interior (⋃ i, starBody (fastLocalStar (a i) (v i)))) :
    center ∈ interior (⋃ i, placedClusterCarrier (a i).2 (anchor i) (clusterOfMark (a i).1)) := by
  apply translated_scaled_origin_interior center (1/6) (by norm_num) hzero
  rintro y ⟨q,hq,rfl⟩
  obtain ⟨i,hi⟩ := mem_iUnion.mp hq
  exact mem_iUnion.mpr ⟨i,fastLocalStar_image_subset_placedClusterCarrier
    hraw hrows (a i) (v i) (anchor i) center (hv i) (hc i) ⟨q,hi,rfl⟩⟩

/-- A legal two-cluster subdivision-vertex star gives an actual neighborhood
once both literal target vertices have been identified with its center. -/
theorem side_placed_origin_interior
    (hraw : ∀ big v, RawStarBinding big v) (hrows : IncidentRowsCorrect)
    (hcert : ∀ i : Fin 217, SideGeometryCertificate i.val)
    (hbind : ∀ k d, SideGeometryBinding k d)
    (a b : State) (d : Fin 6) (j : Fin 12)
    (hm : sideMatch a b d) (hj : 0<j.val)
    (hj' : j.val+1<(stateBoundaryIds a d).length)
    (A B center : RealPoint)
    (ha : (stateBoundaryIds a d).getD j.val 0 < (targetVertices a.1).length)
    (hb : (stateBoundaryIds b (opposite d)).getD
      ((stateBoundaryIds b (opposite d)).length-1-j.val) 0 < (targetVertices b.1).length)
    (hA : A+gridRotation a.2 ((1/6:ℝ) • integerPoint
      (targetVertex a.1 ((stateBoundaryIds a d).getD j.val 0))) = center)
    (hB : B+gridRotation b.2 ((1/6:ℝ) • integerPoint
      (targetVertex b.1 ((stateBoundaryIds b (opposite d)).getD
        ((stateBoundaryIds b (opposite d)).length-1-j.val) 0))) = center) :
    center ∈ interior (placedClusterCarrier a.2 A (clusterOfMark a.1) ∪
      placedClusterCarrier b.2 B (clusterOfMark b.1)) := by
  have hzero := side_origin hcert hbind a b d j hm hj hj'
  apply translated_scaled_origin_interior center (1/6) (by norm_num) hzero
  rintro y ⟨q,hq,rfl⟩
  change q ∈ starBody (_ ++ _) at hq
  rw [starBody_append] at hq
  rcases hq with hq | hq
  · exact Or.inl (fastLocalStar_image_subset_placedClusterCarrier
      hraw hrows a _ A center ha hA ⟨q,hq,rfl⟩)
  · exact Or.inr (fastLocalStar_image_subset_placedClusterCarrier
      hraw hrows b _ B center hb hB ⟨q,hq,rfl⟩)

/-- The same actual-carrier transfer for each legal ordered triple corner. -/
theorem triple_placed_origin_interior
    (hraw : ∀ big v, RawStarBinding big v) (hrows : IncidentRowsCorrect)
    (hcert : ∀ i : Fin 49, TripleGeometryCertificate i.val)
    (hbind : ∀ k d, TripleGeometryBinding k d)
    (a b c : State) (d : Fin 6)
    (hab : sideMatch a b d)
    (hac : sideMatch a c (rotateTurn 1 d))
    (hbc : sideMatch b c (rotateTurn 2 d))
    (A B C center : RealPoint)
    (ha : (stateBoundaryIds a d).getLastD 0 < (targetVertices a.1).length)
    (hb : (stateBoundaryIds b (opposite d)).headD 0 < (targetVertices b.1).length)
    (hc : (stateBoundaryIds c (rotateTurn 4 (rotateTurn 1 d))).headD 0 <
      (targetVertices c.1).length)
    (hA : A+gridRotation a.2 ((1/6:ℝ) • integerPoint
      (targetVertex a.1 ((stateBoundaryIds a d).getLastD 0))) = center)
    (hB : B+gridRotation b.2 ((1/6:ℝ) • integerPoint
      (targetVertex b.1 ((stateBoundaryIds b (opposite d)).headD 0))) = center)
    (hC : C+gridRotation c.2 ((1/6:ℝ) • integerPoint
      (targetVertex c.1 ((stateBoundaryIds c (rotateTurn 4 (rotateTurn 1 d))).headD 0))) = center) :
    center ∈ interior (placedClusterCarrier a.2 A (clusterOfMark a.1) ∪
      placedClusterCarrier b.2 B (clusterOfMark b.1) ∪
      placedClusterCarrier c.2 C (clusterOfMark c.1)) := by
  have hzero := triple_origin hcert hbind a b c d hab hac hbc
  apply translated_scaled_origin_interior center (1/6) (by norm_num) hzero
  rintro y ⟨q,hq,rfl⟩
  change q ∈ starBody ((_ ++ _) ++ _) at hq
  rw [starBody_append,starBody_append] at hq
  rcases hq with (hq | hq) | hq
  · exact Or.inl (Or.inl (fastLocalStar_image_subset_placedClusterCarrier
      hraw hrows a _ A center ha hA ⟨q,hq,rfl⟩))
  · exact Or.inl (Or.inr (fastLocalStar_image_subset_placedClusterCarrier
      hraw hrows b _ B center hb hB ⟨q,hq,rfl⟩))
  · exact Or.inr (fastLocalStar_image_subset_placedClusterCarrier
      hraw hrows c _ C center hc hC ⟨q,hq,rfl⟩)

end
end SpectreGeometry.ReverseLocalStarOccurrences
