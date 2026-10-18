module

public import SpectreGeometry.PolygonLocalConeGerms

@[expose] public section


/-! Cancellation of the auxiliary radial separator. The local cone depends
only on the two actual incident edge halfplanes. -/
namespace SpectreGeometry
noncomputable section
open Set

private theorem det_four_identity (p n r v : RealPoint) :
    RealPoint.det p n * RealPoint.det r v =
      RealPoint.det r n * RealPoint.det p v + RealPoint.det p r * RealPoint.det n v := by
  simp only [RealPoint.det]
  ring

private theorem radial_edge_signs (i : Fin 14) :
    0 < RealPoint.det (RealPoint.sub (realVertex i) realFanCenter) (realEdge i) ∧
      RealPoint.det (realEdge (previous i)) (RealPoint.sub (realVertex i) realFanCenter) < 0 := by
  have hn := fan_real_positive i
  have hp := fan_real_positive (previous i)
  rw [next_previous] at hp
  have hn' : RealPoint.det (RealPoint.sub (realVertex i) realFanCenter) (realEdge i) =
      side (realVertex i) (realVertex (next i)) realFanCenter := by
    simp only [realEdge,side,RealPoint.det,RealPoint.sub]
    ring
  have hp' : RealPoint.det (realEdge (previous i)) (RealPoint.sub (realVertex i) realFanCenter) =
      -side (realVertex (previous i)) (realVertex i) realFanCenter := by
    simp only [realEdge,next_previous,side,RealPoint.det,RealPoint.sub]
    ring
  rw [hn',hp']
  exact ⟨hn,neg_neg_of_pos hp⟩

private theorem wedge_inter_iff (A B R D a b : ℝ)
    (hD : 0 < D) (ha : 0 < a) (hb : b < 0) (he : D*R = a*A+b*B) :
    ((0 ≤ A ∧ R ≤ 0) ∨ (0 ≤ R ∧ 0 ≤ B)) ↔ (0 ≤ A ∧ 0 ≤ B) := by
  constructor
  · rintro (⟨hA,hR⟩ | ⟨hR,hB⟩)
    · refine ⟨hA,?_⟩
      by_contra hB
      have hB' : B < 0 := lt_of_not_ge hB
      have h1 := mul_pos_of_neg_of_neg hb hB'
      have h2 := mul_nonneg ha.le hA
      have h3 := mul_nonpos_of_nonneg_of_nonpos hD.le hR
      linarith
    · refine ⟨?_,hB⟩
      by_contra hA
      have hA' : A < 0 := lt_of_not_ge hA
      have h1 := mul_neg_of_pos_of_neg ha hA'
      have h2 := mul_nonpos_of_nonpos_of_nonneg hb.le hB
      have h3 := mul_nonneg hD.le hR
      linarith
  · rintro ⟨hA,hB⟩
    rcases le_total R 0 with hR | hR
    · exact Or.inl ⟨hA,hR⟩
    · exact Or.inr ⟨hR,hB⟩

private theorem wedge_union_iff (A B R D a b : ℝ)
    (hD : D < 0) (ha : 0 < a) (hb : b < 0) (he : D*R = a*A+b*B) :
    ((0 ≤ A ∧ R ≤ 0) ∨ (0 ≤ R ∧ 0 ≤ B)) ↔ (0 ≤ A ∨ 0 ≤ B) := by
  constructor
  · rintro (⟨hA,_⟩ | ⟨_,hB⟩)
    · exact Or.inl hA
    · exact Or.inr hB
  · rintro (hA | hB)
    · by_cases hR : R ≤ 0
      · exact Or.inl ⟨hA,hR⟩
      · have hR' : 0 < R := lt_of_not_ge hR
        refine Or.inr ⟨hR'.le,?_⟩
        by_contra hB
        have hB' : B < 0 := lt_of_not_ge hB
        have h1 := mul_neg_of_neg_of_pos hD hR'
        have h2 := mul_nonneg ha.le hA
        have h3 := mul_pos_of_neg_of_neg hb hB'
        linarith
    · by_cases hR : 0 ≤ R
      · exact Or.inr ⟨hR,hB⟩
      · have hR' : R < 0 := lt_of_not_ge hR
        refine Or.inl ⟨?_,hR'.le⟩
        by_contra hA
        have hA' : A < 0 := lt_of_not_ge hA
        have h1 := mul_pos_of_neg_of_neg hD hR'
        have h2 := mul_neg_of_pos_of_neg ha hA'
        have h3 := mul_nonpos_of_nonpos_of_nonneg hb.le hB
        linarith

theorem polygonVertexCone_eq_inter_of_pos (i : Fin 14)
    (hi : 0 < RealPoint.det (realEdge (previous i)) (realEdge i)) :
    polygonVertexCone i = {v | 0 ≤ RealPoint.det (realEdge (previous i)) v} ∩
      {v | 0 ≤ RealPoint.det (realEdge i) v} := by
  ext v
  obtain ⟨ha,hb⟩ := radial_edge_signs i
  exact wedge_inter_iff _ _ _ _ _ _ hi ha hb
    (det_four_identity (realEdge (previous i)) (realEdge i)
      (RealPoint.sub (realVertex i) realFanCenter) v)

theorem polygonVertexCone_eq_union_of_neg (i : Fin 14)
    (hi : RealPoint.det (realEdge (previous i)) (realEdge i) < 0) :
    polygonVertexCone i = {v | 0 ≤ RealPoint.det (realEdge (previous i)) v} ∪
      {v | 0 ≤ RealPoint.det (realEdge i) v} := by
  ext v
  obtain ⟨ha,hb⟩ := radial_edge_signs i
  exact wedge_union_iff _ _ _ _ _ _ hi ha hb
    (det_four_identity (realEdge (previous i)) (realEdge i)
      (RealPoint.sub (realVertex i) realFanCenter) v)

theorem polygonVertexCone_eq_halfplane_of_edges_eq (i : Fin 14)
    (hi : realEdge (previous i) = realEdge i) :
    polygonVertexCone i = {v | 0 ≤ RealPoint.det (realEdge i) v} := by
  ext v
  simp only [polygonVertexCone,Set.mem_setOf_eq,hi]
  constructor
  · rintro (⟨h,_⟩ | ⟨_,h⟩) <;> exact h
  · intro h
    rcases le_total (RealPoint.det (RealPoint.sub (realVertex i) realFanCenter) v) 0 with hr | hr
    · exact Or.inl ⟨h,hr⟩
    · exact Or.inr ⟨hr,h⟩

end
end SpectreGeometry
