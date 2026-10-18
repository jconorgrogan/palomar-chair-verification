module

public import SpectreGeometry.ReverseRawClusterPieces
public import SpectreGeometry.ReversePlacedClusterCharts
public import SpectreGeometry.ReverseCarrierRefinement

@[expose] public section


namespace SpectreGeometry.ReverseExistence
noncomputable section
open Set SpectreClusters ReverseClusterTriangulation

abbrev ClusterPieceIndex (k : ClusterKind) := Fin (clusterPieces k).length

def placedClusterPiece (k : ClusterKind) (r : Fin 6) (a : RealPoint)
    (i : ClusterPieceIndex k) : Set RealPoint :=
  axialMotionHomeomorph r a '' placementKiteBody ((clusterPieces k).get i)

theorem rawClusterBody_eq_indexed_pieces (k : ClusterKind) :
    rawClusterBody k = ⋃ i : ClusterPieceIndex k,
      placementKiteBody ((clusterPieces k).get i) := by
  rw [rawClusterBody_eq_pieces]
  ext x
  simp only [mem_iUnion]
  constructor
  · rintro ⟨p,hp,hx⟩
    obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp hp
    refine ⟨⟨i,hi⟩,?_⟩
    simpa only [List.get_eq_getElem,he] using hx
  · rintro ⟨i,hi⟩
    exact ⟨(clusterPieces k).get i,List.get_mem _ _,hi⟩

theorem placedClusterCarrier_eq_pieces (k : ClusterKind) (r : Fin 6) (a : RealPoint) :
    placedClusterCarrier r a k = ⋃ i : ClusterPieceIndex k, placedClusterPiece k r a i := by
  simp only [placedClusterCarrier,rawClusterBody_eq_indexed_pieces,image_iUnion,placedClusterPiece]

theorem placedClusterPiece_subset (k : ClusterKind) (r : Fin 6) (a : RealPoint)
    (i : ClusterPieceIndex k) : placedClusterPiece k r a i ⊆ placedClusterCarrier r a k := by
  rw [placedClusterCarrier_eq_pieces]
  exact subset_iUnion _ i

theorem placedClusterPiece_interiors_disjoint (k : ClusterKind) (r : Fin 6) (a : RealPoint) :
    Pairwise (fun i j : ClusterPieceIndex k =>
      Disjoint (interior (placedClusterPiece k r a i))
        (interior (placedClusterPiece k r a j))) :=
  homeomorph_images_interiors_disjoint (axialMotionHomeomorph r a)
    (fun i => placementKiteBody ((clusterPieces k).get i))
    (clusterPieces_indexed_interiors_disjoint k)

end
end SpectreGeometry.ReverseExistence
