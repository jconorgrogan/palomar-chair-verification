module

public import SpectreGeometry.ReverseClusterNeighborCellsReal
public import SpectreGeometry.ReversePolygonalPathCarrier

@[expose] public section


namespace SpectreGeometry.ReverseClusterNeighborCells
noncomputable section
open Set SpectreClusters ReverseExistence

theorem mem_pathEdges_iff (ps : List Point) (edge : Point×Point) :
    edge ∈ pathEdges ps ↔ ∃ j : Nat, j < ps.length-1 ∧
      edge = (ps.getD j (0,0),ps.getD (j+1) (0,0)) := by
  induction ps with
  | nil => simp [pathEdges]
  | cons a ps ih =>
    cases ps with
    | nil => simp [pathEdges]
    | cons b ps =>
      have he : pathEdges (a::b::ps) = (a,b)::pathEdges (b::ps) := rfl
      rw [he,List.mem_cons]
      constructor
      · rintro (h|h)
        · exact ⟨0,by simp,by simpa using h⟩
        · obtain ⟨j,hj,hjEq⟩ := ih.mp h
          refine ⟨j+1,by simp only [List.length_cons] at hj ⊢; omega,?_⟩
          simpa only [List.getD_cons_succ,Nat.add_assoc] using hjEq
      · rintro ⟨j,hj,hjEq⟩
        cases j with
        | zero => left; simpa only [List.getD_cons_zero,List.getD_cons_succ] using hjEq
        | succ j =>
          right
          apply ih.mpr
          refine ⟨j,by simp only [List.length_cons] at hj ⊢; omega,?_⟩
          simpa only [Nat.succ_eq_add_one,List.getD_cons_succ,Nat.add_assoc] using hjEq

theorem pathCarrier_eq_polygonalPathCarrier (ps : List Point) :
    pathCarrier ps = polygonalPathCarrier (ps.map integerPoint) := by
  have hget (i : Nat) (hi : i < ps.length) :
      (ps.map integerPoint).getD i 0 = integerPoint (ps.getD i (0,0)) := by
    simp [List.getD_eq_getElem?_getD,hi]
  ext x
  constructor
  · intro hx
    obtain ⟨e,he,hx⟩ := mem_iUnion₂.mp hx
    obtain ⟨j,hj,rfl⟩ := (mem_pathEdges_iff ps e).mp he
    apply mem_iUnion.mpr
    refine ⟨⟨j,by simpa only [List.length_map] using hj⟩,?_⟩
    rw [hget j (by omega),hget (j+1) (by omega)]
    simpa only [edgeCarrier_eq_segment] using hx
  · intro hx
    obtain ⟨j,hx⟩ := mem_iUnion.mp hx
    have hj : j.val < ps.length-1 := by simpa only [List.length_map] using j.isLt
    apply mem_iUnion₂.mpr
    refine ⟨(ps.getD j.val (0,0),ps.getD (j.val+1) (0,0)),
      (mem_pathEdges_iff ps _).mpr ⟨j.val,hj,rfl⟩,?_⟩
    rw [edgeCarrier_eq_segment]
    rw [hget j.val (by omega),hget (j.val+1) (by omega)] at hx
    exact hx

end
end SpectreGeometry.ReverseClusterNeighborCells
