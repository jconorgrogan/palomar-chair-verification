module

public import SpectreClusters.StageAActualSupport
public import SpectreClusters.GridFieldTranslations

@[expose] public section


namespace SpectreClusters.StageA

theorem clusterPiecesAt_canonical (k : ClusterKind) (kind : HTKind) :
    clusterPiecesAt k (canonicalRoot kind) = clusterPieces k := by
  change (clusterPieces k).map (movePlacement 0 (0,0)) = clusterPieces k
  rw [show movePlacement 0 (0,0) = id from funext movePlacement_zero,List.map_id]

theorem clusterPiecesAt_moved (k : ClusterKind) (turn : Turn) (t : Point) (root : HTPlacement) :
    clusterPiecesAt k (movePlacement turn t root) =
      (clusterPiecesAt k root).map (movePlacement turn t) := by
  simp only [clusterPiecesAt,List.map_map]
  apply List.map_congr_left
  intro p hp
  exact (movePlacement_compose turn root.turn t root.center p).symm

theorem clusterOwned_moved (k : ClusterKind) (turn : Turn) (t : Point)
    (f : Cell → HTPlacement) (root : HTPlacement) (h : ClusterOwned f k root) :
    ClusterOwned (moveField turn t f) k (movePlacement turn t root) := by
  refine ⟨h.1,?_⟩
  intro p hp
  rw [clusterPiecesAt_moved] at hp
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
  exact moveField_rootOwned turn t f q (h.2 q hq)

/-- Literal cluster occurrence recognition is translation covariant in the
same integer coordinates as the genuine tile-owner field. -/
theorem clusterOwned_translate_period (k : ClusterKind)
    (f : Cell → HTPlacement) (u : Point) (hperiod : GridFieldTranslationPeriod f u)
    (root : HTPlacement) (h : ClusterOwned f k root) :
    ClusterOwned f k (movePlacement 0 u root) := by
  refine ⟨h.1,?_⟩
  rw [clusterPiecesAt_moved]
  exact GridFieldTranslationPeriod.owned_family f u hperiod (clusterPiecesAt k root) h.2

end SpectreClusters.StageA
