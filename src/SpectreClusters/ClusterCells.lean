module

public import SpectreClusters.ClusterExteriorT6H
public import SpectreClusters.ClusterExteriorT7H
public import SpectreClusters.ClusterExteriorT8H

@[expose] public section


/-! Literal finite clusters. Uniqueness of their occurrence in arbitrary
hat/turtle tilings is deliberately not part of these finite checks. -/
namespace SpectreClusters

set_option maxRecDepth 100000 in
theorem t6h_cells_distinct : (clusterCells .t6h).Nodup := by decide
set_option maxRecDepth 100000 in
theorem t7h_cells_distinct : (clusterCells .t7h).Nodup := by decide
set_option maxRecDepth 100000 in
theorem t8h_cells_distinct : (clusterCells .t8h).Nodup := by decide

theorem t6h_cell_count : (clusterCells .t6h).length = 58 := by decide
theorem t7h_cell_count : (clusterCells .t7h).length = 66 := by decide
theorem t8h_cell_count : (clusterCells .t8h).length = 74 := by decide

theorem cluster_piece_counts : ∀ k : ClusterKind,
    (clusterPieces k).length = match k with | .t6h => 7 | .t7h => 8 | .t8h => 9 := by
  intro k; cases k <;> rfl

theorem clusters_one_turtle : ∀ k : ClusterKind,
    ((clusterPieces k).filter (fun p => p.kind == .turtle)).length = 1 := by
  intro k; cases k <;> decide

set_option maxRecDepth 100000 in
theorem t6h_boundary_agreement : BoundaryAgreement (clusterCells .t6h) (clusterPolygon .t6h) := by
  unfold BoundaryAgreement
  rw [t6h_exterior_eq]
  decide
set_option maxRecDepth 100000 in
theorem t7h_boundary_agreement : BoundaryAgreement (clusterCells .t7h) (clusterPolygon .t7h) := by
  unfold BoundaryAgreement
  rw [t7h_exterior_eq]
  decide
set_option maxRecDepth 100000 in
theorem t8h_boundary_agreement : BoundaryAgreement (clusterCells .t8h) (clusterPolygon .t8h) := by
  unfold BoundaryAgreement
  rw [t8h_exterior_eq]
  decide

end SpectreClusters
