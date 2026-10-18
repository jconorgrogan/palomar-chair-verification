module

public import SpectreClusters.ClusterGridMotions

@[expose] public section


/-! Fine-grid translation covariance of actual cluster ownership. This is
separate from marked-hexagon FieldPeriod, which needs a coarse coordinate chart. -/
namespace SpectreClusters

def ClusterGridFieldTranslationPeriod (g : Cell → ClusterPlacement) (u : Point) : Prop :=
  ∀ c, g (moveCell 0 u c) = moveClusterPlacement 0 u (g c)

theorem ClusterGridFieldTranslationPeriod.rootOwned (g : Cell → ClusterPlacement) (u : Point)
    (hperiod : ClusterGridFieldTranslationPeriod g u) (p : ClusterPlacement)
    (hp : ClusterRootOwned g p) : ClusterRootOwned g (moveClusterPlacement 0 u p) := by
  intro c hc
  rw [clusterPlacementCells_moved] at hc
  obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hc
  rw [hperiod,hp d hd]

end SpectreClusters
