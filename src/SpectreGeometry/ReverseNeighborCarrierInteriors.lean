module

public import SpectreGeometry.ReverseClusterNeighborCellsReal
public import SpectreGeometry.FiniteClosedCarrierInteriors
public import Mathlib.Analysis.Convex.Topology

@[expose] public section


namespace SpectreGeometry.ReverseClusterNeighborCells
noncomputable section
open Set SpectreClusters ReverseExistence

theorem configurationCheckedB_carrier_interiors_disjoint (c : Configuration)
    (hc : configurationCheckedB c = true) :
    Disjoint (interior (rootCarrier c)) (interior (neighborCarrier c)) := by
  classical
  letI : Fintype {a // a ∈ rootCells c} := (List.finite_toSet (rootCells c)).fintype
  letI : Fintype {b // b ∈ neighborCells c} := (List.finite_toSet (neighborCells c)).fintype
  have hroot : rootCarrier c = ⋃ i : {a // a ∈ rootCells c}, gridKiteBody i.val := by
    ext x
    simp [rootCarrier]
  have hneighbor : neighborCarrier c = ⋃ i : {b // b ∈ neighborCells c}, gridKiteBody i.val := by
    ext x
    simp [neighborCarrier]
  have hclosed (a : Cell) : IsClosed (gridKiteBody a) :=
    (((List.finite_toSet (cellVertices a)).image integerPoint).isCompact_convexHull ℝ).isClosed
  rw [hroot,hneighbor]
  exact finite_closed_iUnion_interiors_disjoint
    (fun i : {a // a ∈ rootCells c} => gridKiteBody i.val)
    (fun j : {b // b ∈ neighborCells c} => gridKiteBody j.val)
    (fun i => hclosed i.val) (fun j => hclosed j.val)
    (fun i j => configurationCheckedB_cross_cells_disjoint c hc i.val i.property j.val j.property)

end
end SpectreGeometry.ReverseClusterNeighborCells
