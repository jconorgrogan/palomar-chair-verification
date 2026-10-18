module

public import SpectreClusters.GridCoverModel
public import SpectreClusters.GridReductionTransport

@[expose] public section


/-! Translation covariance of the literal kite ownership field, independent
of real geometry and independent of the later marked-state decoding. -/
namespace SpectreClusters

/-- Each translated cell is owned by the translated original placement. -/
def GridFieldTranslationPeriod (g : Cell → HTPlacement) (u : Point) : Prop :=
  ∀ c, g (moveCell 0 u c) = movePlacement 0 u (g c)

theorem GridFieldTranslationPeriod.rootOwned (g : Cell → HTPlacement) (u : Point)
    (hperiod : GridFieldTranslationPeriod g u) (p : HTPlacement) (hp : RootOwned g p) :
    RootOwned g (movePlacement 0 u p) := by
  intro c hc
  rw [placementCells_moved] at hc
  obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hc
  rw [hperiod,hp d hd]

theorem GridFieldTranslationPeriod.owned_family (g : Cell → HTPlacement) (u : Point)
    (hperiod : GridFieldTranslationPeriod g u) (ps : List HTPlacement)
    (hps : ∀ p ∈ ps, RootOwned g p) :
    ∀ p ∈ ps.map (movePlacement 0 u), RootOwned g p := by
  intro p hp
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
  exact GridFieldTranslationPeriod.rootOwned g u hperiod q (hps q hq)

end SpectreClusters
