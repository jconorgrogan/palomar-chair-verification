module

public import SpectreGeometry.ReverseLocalStarIncidentData

@[expose] public section


namespace SpectreGeometry.ReverseLocalStarOccurrences
open ReverseClusterTriangulation
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- A deduplicated finite union avoids enumerating arbitrary vertex indices. -/
def boundaryIndexList (k : Fin 9) : List Nat :=
  ((List.finRange 6).flatMap (fun d => boundaryIndices k d)).eraseDups

theorem boundary_index_mem_list_iff (k : Fin 9) (v : Nat) :
    IsBoundaryIndex k v ↔ v ∈ boundaryIndexList k := by
  simp [IsBoundaryIndex, boundaryIndexList, List.mem_eraseDups, List.mem_finRange]

theorem boundary_index_list_reduced_2 : List.Perm (boundaryIndexList 2) (boundaryIndexList 1) := by decide

theorem boundary_index_list_reduced_3 : List.Perm (boundaryIndexList 3) (boundaryIndexList 1) := by decide

theorem boundary_index_list_reduced_4 : List.Perm (boundaryIndexList 4) (boundaryIndexList 1) := by decide

theorem boundary_index_list_reduced_5 : List.Perm (boundaryIndexList 5) (boundaryIndexList 1) := by decide

theorem boundary_index_list_reduced_6 : List.Perm (boundaryIndexList 6) (boundaryIndexList 1) := by decide

theorem boundary_index_list_reduced_7 : List.Perm (boundaryIndexList 7) (boundaryIndexList 1) := by decide

theorem boundary_index_list_reduced_8 : List.Perm (boundaryIndexList 8) (boundaryIndexList 1) := by decide

theorem all_boundary_index_lists_reduced : ∀ k : Fin 9,
    List.Perm (boundaryIndexList k) (boundaryIndexList (kindMark (k.val != 0))) := by
  exact Fin.cases (List.Perm.refl _) (Fin.cases (List.Perm.refl _) (Fin.cases (boundary_index_list_reduced_2) (Fin.cases (boundary_index_list_reduced_3) (Fin.cases (boundary_index_list_reduced_4) (Fin.cases (boundary_index_list_reduced_5) (Fin.cases (boundary_index_list_reduced_6) (Fin.cases (boundary_index_list_reduced_7) (Fin.cases (boundary_index_list_reduced_8) ((fun i => Fin.elim0 i))))))))))

theorem all_boundary_indices_kind_reduced : ∀ (k : Fin 9) (v : Fin 133),
    IsBoundaryIndex k v.val ↔ IsBoundaryIndex (kindMark (k.val != 0)) v.val := by
  intro k v
  exact (boundary_index_mem_list_iff k v.val).trans
    ((all_boundary_index_lists_reduced k).mem_iff.trans
      (boundary_index_mem_list_iff (kindMark (k.val != 0)) v.val).symm)

theorem all_boundary_indices_length_le_twelve : ∀ (k : Fin 9) (d : Fin 6),
    (boundaryIndices k d).length ≤ 12 := by
  exact Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) ((fun i => Fin.elim0 i)))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) ((fun i => Fin.elim0 i)))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) ((fun i => Fin.elim0 i)))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) ((fun i => Fin.elim0 i)))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) ((fun i => Fin.elim0 i)))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) ((fun i => Fin.elim0 i)))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) ((fun i => Fin.elim0 i)))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) ((fun i => Fin.elim0 i)))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) ((fun i => Fin.elim0 i)))))))) ((fun i => Fin.elim0 i))))))))))

end SpectreGeometry.ReverseLocalStarOccurrences
