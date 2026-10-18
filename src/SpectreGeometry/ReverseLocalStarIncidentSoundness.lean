module

public import SpectreGeometry.ReverseLocalStarIncidentData
public import SpectreGeometry.ReverseClusterTriangulationInjective

@[expose] public section


namespace SpectreGeometry.ReverseLocalStarOccurrences
open SpectreClusters SpectreFinite.HexSearch ReverseClusterTriangulation

/-- Exact completeness of the cached incident-index rows. -/
def IncidentRowsCorrect : Prop := ∀ (big : Bool) (v : Nat),
  v < (targetVertices (kindMark big)).length →
  calculatedIncidentRow big v = (if big then incidentRows1 else incidentRows0).getD v []

theorem meshTriangles_kind_reduced (k : Fin 9) :
    meshTriangles (kindMark (k.val != 0)) = meshTriangles k := by
  revert k
  exact (Fin.cases (by intros; rfl) (Fin.cases (by intros; rfl) (Fin.cases (by intros; rfl) (Fin.cases (by intros; rfl) (Fin.cases (by intros; rfl) (Fin.cases (by intros; rfl) (Fin.cases (by intros; rfl) (Fin.cases (by intros; rfl) (Fin.cases (by intros; rfl) (fun i => Fin.elim0 i))))))))))

theorem targetVertices_kind_reduced (k : Fin 9) :
    targetVertices (kindMark (k.val != 0)) = targetVertices k := by
  revert k
  exact (Fin.cases (by intros; rfl) (Fin.cases (by intros; rfl) (Fin.cases (by intros; rfl) (Fin.cases (by intros; rfl) (Fin.cases (by intros; rfl) (Fin.cases (by intros; rfl) (Fin.cases (by intros; rfl) (Fin.cases (by intros; rfl) (Fin.cases (by intros; rfl) (fun i => Fin.elim0 i))))))))))

theorem incidentIds_eq_calculated (hrows : IncidentRowsCorrect) (k : Fin 9) (v : Nat)
    (hv : v < (targetVertices k).length) :
    incidentIds k v = calculatedIncidentRow (k.val != 0) v := by
  have h := hrows (k.val != 0) v (by rwa [targetVertices_kind_reduced])
  rw [h]
  unfold incidentIds
  revert k
  exact (Fin.cases (by intros; rfl) (Fin.cases (by intros; rfl) (Fin.cases (by intros; rfl) (Fin.cases (by intros; rfl) (Fin.cases (by intros; rfl) (Fin.cases (by intros; rfl) (Fin.cases (by intros; rfl) (Fin.cases (by intros; rfl) (Fin.cases (by intros; rfl) (fun i => Fin.elim0 i))))))))))

theorem incidentIds_mem_iff (hrows : IncidentRowsCorrect) (k : Fin 9) (v i : Nat)
    (hv : v < (targetVertices k).length) :
    i ∈ incidentIds k v ↔ i < (meshTriangles k).length ∧
      v ∈ triangleIndices ((meshTriangles k).getD i (0,0,0)) := by
  rw [incidentIds_eq_calculated hrows k v hv]
  simp only [calculatedIncidentRow,meshTriangles_kind_reduced,List.mem_filter,List.mem_range,
    decide_eq_true_eq]

theorem incidentIds_bound (hrows : IncidentRowsCorrect) (k : Fin 9) (v : Nat)
    (hv : v < (targetVertices k).length) :
    ∀ i ∈ incidentIds k v, i < (meshTriangles k).length := by
  intro i hi
  exact ((incidentIds_mem_iff hrows k v i hv).mp hi).1

end SpectreGeometry.ReverseLocalStarOccurrences
