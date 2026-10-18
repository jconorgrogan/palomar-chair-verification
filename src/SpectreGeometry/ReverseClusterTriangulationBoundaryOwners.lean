module

public import SpectreGeometry.ReverseClusterTriangulationData

@[expose] public section

namespace SpectreGeometry.ReverseClusterTriangulation
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def boundaryOwnerTable : List (List (List Nat)) := [[[92, 49, 50, 109, 119, 124, 0], [1, 6, 55, 60, 65, 9, 10], [15, 135, 146, 68, 69, 157, 162, 167, 18, 19], [24, 172, 27, 28, 187, 188, 31, 32, 37, 74], [79, 84, 40, 41, 46], [205, 112, 87, 88, 91]], [[92, 45, 46, 109, 119, 124, 0, 1, 6, 51], [56, 61, 9, 10, 15], [135, 146, 64, 65, 157, 162, 167, 18], [19, 24, 70, 75, 80, 27, 28], [33, 189, 194, 83, 84, 211, 214, 215, 36, 37], [42, 176, 112, 87, 88, 91]], [[92, 45, 46, 109, 119, 124, 0, 1, 6, 51], [56, 61, 9, 10, 15], [135, 146, 64, 65, 157, 162, 167, 18, 19, 24, 70], [75, 80, 27, 28, 33], [189, 194, 83, 84, 211, 214, 215, 36, 37, 42], [176, 112, 87, 88, 91]], [[92, 45, 46, 109, 119, 124, 0, 1, 6, 51], [56, 61, 9, 10, 15], [135, 146, 64, 65, 157, 162, 167, 18], [19, 24, 70, 75, 80, 27, 28], [33, 189, 194, 83, 84, 211, 214, 215, 36, 37, 42], [176, 112, 87, 88, 91]], [[92, 45, 46, 109, 119, 124, 0], [1, 6, 51, 56, 61, 9, 10, 15], [135, 146, 64, 65, 157, 162, 167, 18, 19, 24, 70], [75, 80, 27, 28, 33], [189, 194, 83, 84, 211, 214, 215, 36, 37, 42], [176, 112, 87, 88, 91]], [[92, 45, 46, 109, 119, 124, 0], [1, 6, 51, 56, 61, 9, 10, 15], [135, 146, 64, 65, 157, 162, 167, 18], [19, 24, 70, 75, 80, 27, 28], [33, 189, 194, 83, 84, 211, 214, 215, 36, 37, 42], [176, 112, 87, 88, 91]], [[119, 124, 0, 1, 6, 51], [56, 61, 9, 10, 15], [135, 146, 64, 65, 157, 162, 167, 18], [19, 24, 70, 75, 80, 27, 28], [33, 189, 194, 83, 84, 211, 214, 215, 36, 37], [42, 176, 112, 87, 88, 91, 92, 45, 46, 109]], [[92, 45, 46, 109, 119, 124, 0, 1, 6, 51], [56, 61, 9, 10, 15], [135, 146, 64, 65, 157, 162, 167, 18], [19, 24, 70, 75, 80, 27, 28, 33], [189, 194, 83, 84, 211, 214, 215, 36, 37, 42], [176, 112, 87, 88, 91]], [[92, 45, 46, 109, 119, 124, 0], [1, 6, 51, 56, 61, 9, 10, 15], [135, 146, 64, 65, 157, 162, 167, 18], [19, 24, 70, 75, 80, 27, 28, 33], [189, 194, 83, 84, 211, 214, 215, 36, 37, 42], [176, 112, 87, 88, 91]]]
def boundaryEdgeOwner (k : Fin 9) (d : Fin 6) (j : Nat) : Nat :=
  ((boundaryOwnerTable.getD k.val []).getD d.val []).getD j 0

def boundaryOwnershipCheck (k : Fin 9) (d : Fin 6) : Prop :=
  ∀ j ∈ List.range ((boundaryIndices k d).length-1),
    let t := boundaryEdgeOwner k d j
    t < (meshTriangles k).length ∧
      (boundaryIndices k d).getD j 0 ∈ triangleIndices ((meshTriangles k).getD t (0,0,0)) ∧
      (boundaryIndices k d).getD (j+1) 0 ∈ triangleIndices ((meshTriangles k).getD t (0,0,0))
instance (k : Fin 9) (d : Fin 6) : Decidable (boundaryOwnershipCheck k d) :=
  inferInstanceAs (Decidable (∀ j ∈ List.range _, _))

theorem all_boundary_edge_owners : ∀ k : Fin 9, ∀ d : Fin 6, boundaryOwnershipCheck k d := by
  exact Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i)))))))))

end SpectreGeometry.ReverseClusterTriangulation
