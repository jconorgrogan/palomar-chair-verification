module

public import SpectreGeometry.ReverseClusterTriangulationScaleReal
public import SpectreGeometry.GridFieldExtraction
public import SpectreGeometry.GridKiteCommonFaces
public import SpectreGeometry.FiniteClosedCarrierInteriors
public import SpectreClusters.ClusterCells
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Data.List.Nodup

@[expose] public section


namespace SpectreGeometry.ReverseExistence
noncomputable section
open Set SpectreClusters ReverseClusterTriangulation

theorem placementKiteBody_interiors_disjoint_of_cells (p q : HTPlacement)
    (h : List.Disjoint (placementCells p) (placementCells q)) :
    Disjoint (interior (placementKiteBody p)) (interior (placementKiteBody q)) := by
  classical
  letI : Fintype {c // c ∈ placementCells p} := (List.finite_toSet (placementCells p)).fintype
  letI : Fintype {c // c ∈ placementCells q} := (List.finite_toSet (placementCells q)).fintype
  have hp : placementKiteBody p = ⋃ c : {c // c ∈ placementCells p}, gridKiteBody c.val := by
    ext x
    simp [placementKiteBody]
  have hq : placementKiteBody q = ⋃ c : {c // c ∈ placementCells q}, gridKiteBody c.val := by
    ext x
    simp [placementKiteBody]
  have hclosed (c : Cell) : IsClosed (gridKiteBody c) :=
    (((List.finite_toSet (cellVertices c)).image integerPoint).isCompact_convexHull ℝ).isClosed
  rw [hp,hq]
  apply finite_closed_iUnion_interiors_disjoint
    (fun c : {c // c ∈ placementCells p} => gridKiteBody c.val)
    (fun c : {c // c ∈ placementCells q} => gridKiteBody c.val)
    (fun c => hclosed c.val) (fun c => hclosed c.val)
  intro c d
  apply gridKiteBody_interior_disjoint
  intro he
  exact List.disjoint_left.mp h c.property (he.symm ▸ d.property)

theorem rawClusterBody_eq_pieces (k : ClusterKind) :
    rawClusterBody k = ⋃ p ∈ clusterPieces k, placementKiteBody p := by
  ext x
  simp only [rawClusterBody,placementKiteBody,clusterCells,mem_iUnion,List.mem_flatMap]
  constructor
  · rintro ⟨c,⟨p,hp,hc⟩,hx⟩
    exact ⟨p,hp,c,hc,hx⟩
  · rintro ⟨p,hp,c,hc,hx⟩
    exact ⟨c,⟨p,hp,hc⟩,hx⟩

theorem clusterPieces_cells_pairwise_disjoint (k : ClusterKind) :
    (clusterPieces k).Pairwise (fun p q => List.Disjoint (placementCells p) (placementCells q)) := by
  have hn : (clusterCells k).Nodup := by
    cases k
    · exact t6h_cells_distinct
    · exact t7h_cells_distinct
    · exact t8h_cells_distinct
  exact (List.nodup_flatMap.mp hn).2

theorem clusterPieces_interiors_pairwise_disjoint (k : ClusterKind) :
    (clusterPieces k).Pairwise (fun p q =>
      Disjoint (interior (placementKiteBody p)) (interior (placementKiteBody q))) :=
  (clusterPieces_cells_pairwise_disjoint k).imp
    (fun h => placementKiteBody_interiors_disjoint_of_cells _ _ h)

theorem clusterPieces_indexed_interiors_disjoint (k : ClusterKind) :
    Pairwise (fun i j : Fin (clusterPieces k).length =>
      Disjoint (interior (placementKiteBody ((clusterPieces k).get i)))
        (interior (placementKiteBody ((clusterPieces k).get j)))) := by
  intro i j hne
  have h := clusterPieces_interiors_pairwise_disjoint k
  rcases lt_or_gt_of_ne hne with hij | hji
  · exact List.Pairwise.rel_getElem_of_lt i.isLt j.isLt h hij
  · exact (List.Pairwise.rel_getElem_of_lt j.isLt i.isLt h hji).symm

end
end SpectreGeometry.ReverseExistence
