module

public import SpectreGeometry.PolygonBoundary

@[expose] public section


/-! Actual local half-plane geometry at each strict outer-edge point. -/
namespace SpectreGeometry
noncomputable section
open Set

theorem outer_open_edge_local_halfplane (i : Fin 14) (t : ℝ) (ht : 0 < t) (ht' : t < 1) :
    ∃ U : Set RealPoint, IsOpen U ∧
      interpolate (realVertex i) (realVertex (next i)) t ∈ U ∧
      (∀ y ∈ U, (y ∈ polygonBody ↔ 0 ≤ side (realVertex i) (realVertex (next i)) y) ∧
        (y ∈ interior polygonBody ↔ 0 < side (realVertex i) (realVertex (next i)) y) ∧
        (y ∈ frontier polygonBody ↔ side (realVertex i) (realVertex (next i)) y = 0)) := by
  let x := interpolate (realVertex i) (realVertex (next i)) t
  let O : Set RealPoint := ⋃ j : {j : Fin 14 // j ≠ i}, triangleBody j.val
  let U : Set RealPoint := Oᶜ ∩ {y | 0 < radialSide i y ∧ radialSide (next i) y < 0}
  have hc : IsClosed O := isClosed_iUnion_of_finite fun j => (triangleBody_compact j.val).isClosed
  have hopen : IsOpen U := hc.isOpen_compl.inter
    ((isOpen_lt continuous_const (side_continuous _ _)).inter
    (isOpen_lt (side_continuous _ _) continuous_const))
  have hnot : x ∉ O := by
    intro hh
    obtain ⟨j,hj⟩ := mem_iUnion.1 hh
    exact outer_open_edge_not_other_triangle i j.val (Ne.symm j.property) t ht ht' hj
  have hp := fan_real_positive i
  have h1 : radialSide i x = t * side (realVertex i) (realVertex (next i)) realFanCenter := by
    simp only [x,radialSide,interpolate,side,RealPoint.det,RealPoint.sub]; ring
  have h2 : radialSide (next i) x = -(1-t) *
      side (realVertex i) (realVertex (next i)) realFanCenter := by
    simp only [x,radialSide,interpolate,side,RealPoint.det,RealPoint.sub]; ring
  have hx : x ∈ U := by
    refine ⟨hnot,?_,?_⟩
    · rw [h1]; exact mul_pos ht hp
    · rw [h2]; exact mul_neg_of_neg_of_pos (by linarith) hp
  have hsub : polygonBody ∩ Oᶜ ⊆ triangleBody i := by
    rintro y ⟨hy,ho⟩
    obtain ⟨j,hj⟩ := mem_iUnion.1 hy
    by_cases he : j = i
    · simpa [he] using hj
    · exact False.elim (ho (mem_iUnion.2 ⟨⟨j,he⟩,hj⟩))
  refine ⟨U,hopen,hx,?_⟩
  intro y hy
  have hm : y ∈ polygonBody ↔ 0 ≤ side (realVertex i) (realVertex (next i)) y := by
    constructor
    · intro hh
      exact ((triangleBody_mem_iff i y).1 (hsub ⟨hh,hy.1⟩)).2.1
    · intro hh
      exact mem_iUnion.2 ⟨i,(triangleBody_mem_iff i y).2 ⟨hy.2.1.le,hh,hy.2.2.le⟩⟩
  have hi : y ∈ interior polygonBody ↔ 0 < side (realVertex i) (realVertex (next i)) y := by
    constructor
    · intro hh
      have hi' : interior polygonBody ∩ Oᶜ ⊆ triangleBody i := by
        rintro z ⟨hz,ho⟩
        exact hsub ⟨interior_subset hz,ho⟩
      have ht' : y ∈ interior (triangleBody i) :=
        (interior_maximal hi' (isOpen_interior.inter hc.isOpen_compl)) ⟨hh,hy.1⟩
      exact ((triangleBody_interior_iff i y).1 ht').2.1
    · intro hh
      exact interior_mono (subset_iUnion triangleBody i)
        ((triangleBody_interior_iff i y).2 ⟨hy.2.1,hh,hy.2.2⟩)
  refine ⟨hm,hi,?_⟩
  rw [frontier,polygonBody_compact.isClosed.closure_eq]
  change (y ∈ polygonBody ∧ y ∉ interior polygonBody) ↔ _
  rw [hm,hi]
  constructor
  · rintro ⟨hge,hn⟩; linarith
  · intro he; simp [he]

theorem outer_open_edge_local_halfplane_sets (i : Fin 14) (t : ℝ) (ht : 0 < t) (ht' : t < 1) :
    ∃ U : Set RealPoint, IsOpen U ∧
      interpolate (realVertex i) (realVertex (next i)) t ∈ U ∧
      polygonBody ∩ U = {y | 0 ≤ side (realVertex i) (realVertex (next i)) y} ∩ U ∧
      interior polygonBody ∩ U = {y | 0 < side (realVertex i) (realVertex (next i)) y} ∩ U ∧
      frontier polygonBody ∩ U = {y | side (realVertex i) (realVertex (next i)) y = 0} ∩ U := by
  obtain ⟨U,ho,hx,hh⟩ := outer_open_edge_local_halfplane i t ht ht'
  refine ⟨U,ho,hx,?_,?_,?_⟩
  all_goals
    ext y
    constructor
    · rintro ⟨hy,hu⟩
      exact ⟨(by first | exact (hh y hu).1.1 hy | exact (hh y hu).2.1.1 hy | exact (hh y hu).2.2.1 hy),hu⟩
    · rintro ⟨hy,hu⟩
      exact ⟨(by first | exact (hh y hu).1.2 hy | exact (hh y hu).2.1.2 hy | exact (hh y hu).2.2.2 hy),hu⟩

end
end SpectreGeometry
