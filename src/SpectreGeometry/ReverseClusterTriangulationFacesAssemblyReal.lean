module

public import SpectreGeometry.ReverseClusterTriangulationFacesReal

@[expose] public section

namespace SpectreGeometry.ReverseClusterTriangulation
noncomputable section
open Set

def FamilyHasFaces (ps : List PolygonPacket) : Prop :=
  ∀ i j : Fin ps.length, i ≠ j →
    integerHull (ps.getD i.val default).vertices ∩ integerHull (ps.getD j.val default).vertices =
        convexHull ℝ (integerVertexSet (ps.getD i.val default).vertices ∩
          integerVertexSet (ps.getD j.val default).vertices) ∧
      Disjoint (interior (integerHull (ps.getD i.val default).vertices))
        (interior (integerHull (ps.getD j.val default).vertices))

theorem getD_mem_take_of_lt {α : Type} (ps : List α) (d : α) (i j : Nat)
    (hi : i < ps.length) (hij : i < j) : ps.getD i d ∈ ps.take j := by
  have hlt : i < (ps.take j).length := by
    rw [List.length_take]
    exact lt_min hij hi
  have hm := getD_mem_of_lt (ps.take j) i d hlt
  simpa only [List.getD_eq_getElem?_getD,List.getElem?_take_of_lt hij] using hm

theorem familyHasFaces_of_rows (ps : List PolygonPacket) (rows : Nat → List Nat)
    (hc : ∀ i : Fin ps.length,
      packetFaceRowB (ps.getD i.val default) (ps.take i.val) (rows i.val) = true) :
    FamilyHasFaces ps := by
  intro i j hij
  have hn : i.val ≠ j.val := fun h => hij (Fin.ext h)
  rcases lt_or_gt_of_ne hn with h | h
  · obtain ⟨c,hc'⟩ := packetFaceRowB_at (ps.getD j.val default) (ps.take j.val)
      (rows j.val) (hc j) (ps.getD i.val default)
      (getD_mem_take_of_lt ps default i.val j.val i.isLt h)
    simpa only [inter_comm,disjoint_comm] using
      pairPacketsFaceB_sound (ps.getD j.val default) (ps.getD i.val default) c hc'
  · obtain ⟨c,hc'⟩ := packetFaceRowB_at (ps.getD i.val default) (ps.take i.val)
      (rows i.val) (hc i) (ps.getD j.val default)
      (getD_mem_take_of_lt ps default j.val i.val j.isLt h)
    exact pairPacketsFaceB_sound (ps.getD i.val default) (ps.getD j.val default) c hc'

end
end SpectreGeometry.ReverseClusterTriangulation
