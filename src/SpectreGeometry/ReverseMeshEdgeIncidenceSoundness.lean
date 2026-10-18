module

public import SpectreGeometry.ReverseMeshEdgeIncidenceData
public import SpectreGeometry.ReverseFinitePLInteger

@[expose] public section


namespace SpectreGeometry.ReverseMeshEdgeIncidence
noncomputable section
open Set SpectreClusters ReverseClusterTriangulation ReverseFinitePL

theorem edgeVertex_eq_codeIndex (big : Bool) (i : Nat) (e : Fin 3) :
    edgeVertex big i e.val = codeIndex ((meshTriangles (kindMark big)).getD i (0,0,0)) e := by
  fin_cases e <;> rfl

theorem edgeVertex_next_eq_codeIndex (big : Bool) (i : Nat) (e : Fin 3) :
    edgeVertex big i (e.val+1) =
      codeIndex ((meshTriangles (kindMark big)).getD i (0,0,0)) (e+1) := by
  fin_cases e <;> rfl

theorem meshTriangles_kind_reduced (k : Fin 9) :
    meshTriangles (kindMark (k.val != 0)) = meshTriangles k := by
  fin_cases k <;> rfl

/-- Every actual cyclic mesh edge has either a distinct second incident
triangle or two consecutive literal boundary indices. -/
theorem actual_edge_incidence
    (hcert : ∀ big i, EdgeIncidenceCertificate big i)
    (k : Fin 9) (i : Fin (meshTriangles k).length) (e : Fin 3) :
    (∃ j : Fin (meshTriangles k).length, j ≠ i ∧
      codeIndex ((meshTriangles k).get i) e ∈ triangleIndices ((meshTriangles k).get j) ∧
      codeIndex ((meshTriangles k).get i) (e+1) ∈ triangleIndices ((meshTriangles k).get j)) ∨
    (codeIndex ((meshTriangles k).get i) e < boundarySize (k.val != 0) ∧
      codeIndex ((meshTriangles k).get i) (e+1) < boundarySize (k.val != 0) ∧
      ((codeIndex ((meshTriangles k).get i) e+1)%boundarySize (k.val != 0) =
        codeIndex ((meshTriangles k).get i) (e+1) ∨
       (codeIndex ((meshTriangles k).get i) (e+1)+1)%boundarySize (k.val != 0) =
        codeIndex ((meshTriangles k).get i) e)) := by
  have hi : i.val < (meshTriangles (kindMark (k.val != 0))).length := by
    rw [meshTriangles_kind_reduced]
    exact i.isLt
  have h := hcert (k.val != 0) i.val hi e
  dsimp only at h
  have hget : (meshTriangles (kindMark (k.val != 0))).getD i.val (0,0,0) =
      (meshTriangles k).get i := by
    rw [meshTriangles_kind_reduced]
    simp only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem i.isLt,
      Option.getD_some,List.get_eq_getElem]
  rw [edgeVertex_eq_codeIndex,edgeVertex_next_eq_codeIndex,hget,meshTriangles_kind_reduced] at h
  rcases h with ⟨hj,hji,hn,hm⟩ | hb
  · left
    refine ⟨⟨otherTriangle (k.val != 0) i.val e.val,hj⟩,?_,?_,?_⟩
    · intro he
      exact hji (congrArg Fin.val he)
    · simpa only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hj,
        Option.getD_some,List.get_eq_getElem] using hn
    · simpa only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hj,
        Option.getD_some,List.get_eq_getElem] using hm
  · exact Or.inr hb

/-- The three cyclic edges represent every ordered pair of distinct vertices,
possibly with its order reversed. -/
theorem distinct_vertices_cyclic_edge (a b : Fin 3) (hab : a ≠ b) :
    ∃ e : Fin 3, (a=e ∧ b=e+1) ∨ (b=e ∧ a=e+1) := by
  have h : ∀ a b : Fin 3, a ≠ b → ∃ e : Fin 3,
      (a=e ∧ b=e+1) ∨ (b=e ∧ a=e+1) := by decide
  exact h a b hab

end
end SpectreGeometry.ReverseMeshEdgeIncidence
