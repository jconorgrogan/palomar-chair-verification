module

public import SpectreFinite.ParentBoundary

@[expose] public section


/-! Kernel-checked exact finite geometry, independent of all radius-five rows. -/
namespace SpectreFinite.HexSearch.ParentBoundary
open ParentOwnership Boundary

def supportTable : List (List Position) := [
  [((-1),2),((-1),1),((-1),0),((-1),(-1)),(0,(-2)),(1,(-2)),(2,(-2)),(3,(-2)),(3,(-1)),(2,0),(2,1),(1,2),(0,2),(0,1),(0,0),(0,(-1)),(1,(-1)),(2,(-1)),(1,0),(1,1)],
  [(0,2),((-1),2),((-1),1),((-1),0),((-1),(-1)),(0,(-2)),(1,(-2)),(2,(-3)),(3,(-3)),(3,(-2)),(3,(-1)),(2,0),(2,1),(1,2),(1,1),(0,1),(0,0),(0,(-1)),(1,(-1)),(2,(-2)),(2,(-1)),(1,0)],
  [(0,2),((-1),2),((-1),1),((-1),0),((-1),(-1)),(0,(-2)),(1,(-2)),(2,(-3)),(3,(-3)),(3,(-2)),(3,(-1)),(2,0),(2,1),(1,2),(1,1),(0,1),(0,0),(0,(-1)),(1,(-1)),(2,(-2)),(2,(-1)),(1,0)],
  [(0,2),((-1),2),((-1),1),((-1),0),((-1),(-1)),(0,(-2)),(1,(-2)),(2,(-3)),(3,(-3)),(3,(-2)),(3,(-1)),(2,0),(2,1),(1,2),(1,1),(0,1),(0,0),(0,(-1)),(1,(-1)),(2,(-2)),(2,(-1)),(1,0)],
  [((-1),2),((-1),1),((-1),0),((-1),(-1)),(0,(-2)),(1,(-2)),(2,(-3)),(3,(-3)),(3,(-2)),(3,(-1)),(2,0),(2,1),(1,2),(0,2),(0,1),(0,0),(0,(-1)),(1,(-1)),(2,(-2)),(2,(-1)),(1,0),(1,1)],
  [((-1),2),((-1),1),((-1),0),((-1),(-1)),(0,(-2)),(1,(-2)),(2,(-3)),(3,(-3)),(3,(-2)),(3,(-1)),(2,0),(2,1),(1,2),(0,2),(0,1),(0,0),(0,(-1)),(1,(-1)),(2,(-2)),(2,(-1)),(1,0),(1,1)],
  [(0,2),((-1),2),((-1),1),((-1),0),((-1),(-1)),(0,(-2)),(1,(-2)),(2,(-3)),(3,(-3)),(3,(-2)),(3,(-1)),(2,0),(2,1),(1,2),(1,1),(0,1),(0,0),(0,(-1)),(1,(-1)),(2,(-2)),(2,(-1)),(1,0)],
  [(0,2),((-1),2),((-1),1),((-1),0),((-1),(-1)),(0,(-2)),(1,(-2)),(2,(-3)),(3,(-3)),(3,(-2)),(3,(-1)),(2,0),(2,1),(1,2),(1,1),(0,1),(0,0),(0,(-1)),(1,(-1)),(2,(-2)),(2,(-1)),(1,0)],
  [((-1),2),((-1),1),((-1),0),((-1),(-1)),(0,(-2)),(1,(-2)),(2,(-3)),(3,(-3)),(3,(-2)),(3,(-1)),(2,0),(2,1),(1,2),(0,2),(0,1),(0,0),(0,(-1)),(1,(-1)),(2,(-2)),(2,(-1)),(1,0),(1,1)]
]

private theorem support_0 : support 0 = supportTable.getD 0 [] := by decide
private theorem support_1 : support 1 = supportTable.getD 1 [] := by decide
private theorem support_2 : support 2 = supportTable.getD 2 [] := by decide
private theorem support_3 : support 3 = supportTable.getD 3 [] := by decide
private theorem support_4 : support 4 = supportTable.getD 4 [] := by decide
private theorem support_5 : support 5 = supportTable.getD 5 [] := by decide
private theorem support_6 : support 6 = supportTable.getD 6 [] := by decide
private theorem support_7 : support 7 = supportTable.getD 7 [] := by decide
private theorem support_8 : support 8 = supportTable.getD 8 [] := by decide

theorem support_exact : ∀ k : TileKind, support k = supportTable.getD k.val [] := by
  exact Fin.cases support_0 (Fin.cases support_1 (Fin.cases support_2 (Fin.cases support_3 (Fin.cases support_4 (Fin.cases support_5 (Fin.cases support_6 (Fin.cases support_7 (Fin.cases support_8 ((fun i => Fin.elim0 i))))))))))

theorem support_radiusThree (k : TileKind) : ∀ x ∈ support k, x ∈ hexRegion 3 := by
  rw [support_exact]
  have h : ∀ j : TileKind, ∀ x ∈ supportTable.getD j.val [], x ∈ hexRegion 3 := by
    exact Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) ((fun i => Fin.elim0 i))))))))))
  exact h k

def QuerySupport (k : TileKind) : Prop :=
  (∀ s : Fin 6, ∀ e ∈ segment k s, outsideCell k e ∈ support k) ∧
  (∀ s : Fin 6, ∀ x ∈ incidentCells (vertexAt k s), x ∈ support k) ∧
  (∀ e ∈ trace k, ∀ x ∈ incidentCells (start (children k) e), x ∈ support k) ∧
  (∀ i : Fin (trace k).length, outsideCell k (edgeAt k i.val) ∈ support k ∧
    outsideCell k (previousEdge k i.val) ∈ support k)
instance (k : TileKind) : Decidable (QuerySupport k) :=
  inferInstanceAs (Decidable (_ ∧ _))

private theorem query_0 : QuerySupport 0 := by
  unfold QuerySupport
  simp only [support_exact]
  decide
private theorem query_1 : QuerySupport 1 := by
  unfold QuerySupport
  simp only [support_exact]
  decide
private theorem query_2 : QuerySupport 2 := by
  unfold QuerySupport
  simp only [support_exact]
  decide
private theorem query_3 : QuerySupport 3 := by
  unfold QuerySupport
  simp only [support_exact]
  decide
private theorem query_4 : QuerySupport 4 := by
  unfold QuerySupport
  simp only [support_exact]
  decide
private theorem query_5 : QuerySupport 5 := by
  unfold QuerySupport
  simp only [support_exact]
  decide
private theorem query_6 : QuerySupport 6 := by
  unfold QuerySupport
  simp only [support_exact]
  decide
private theorem query_7 : QuerySupport 7 := by
  unfold QuerySupport
  simp only [support_exact]
  decide
private theorem query_8 : QuerySupport 8 := by
  unfold QuerySupport
  simp only [support_exact]
  decide

theorem query_support : ∀ k : TileKind, QuerySupport k := by
  exact Fin.cases query_0 (Fin.cases query_1 (Fin.cases query_2 (Fin.cases query_3 (Fin.cases query_4 (Fin.cases query_5 (Fin.cases query_6 (Fin.cases query_7 (Fin.cases query_8 ((fun i => Fin.elim0 i))))))))))

theorem native_boundary_vertices_three : ∀ k : TileKind,
    ∀ e ∈ trace k, (incidentCells (start (children k) e)).length = 3 := by
  exact Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) ((fun i => Fin.elim0 i))))))))))

#print axioms support_exact
#print axioms support_radiusThree
#print axioms query_support
#print axioms native_boundary_vertices_three
end SpectreFinite.HexSearch.ParentBoundary
