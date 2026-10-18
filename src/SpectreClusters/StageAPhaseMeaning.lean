module

public import SpectreClusters.StageAPhaseMeaningData
public import SpectreClusters.GridNeighborInvariant

@[expose] public section


namespace SpectreClusters.StageA

theorem row_allOpposite_iff (f : Cell → HTPlacement) (hf : ValidGridField f)
    (kind : HTKind) (hr : RootOwned f (canonicalRoot kind)) (i : Nat)
    (hword : rawWordAt kind i = wordOf f kind) :
    AllOppositeNeighbors f (canonicalRoot kind) ↔ allOppositeRowB kind i = true := by
  constructor
  · intro h
    apply List.all_eq_true.mpr
    intro p hp
    have hn := h p ((row_neighbors_iff_fieldNeighbor f hf kind hr i hword p).mp hp)
    simpa [canonicalRoot] using hn
  · intro h p hp
    have hn := List.all_eq_true.mp h p
      ((row_neighbors_iff_fieldNeighbor f hf kind hr i hword p).mpr hp)
    simpa [canonicalRoot] using hn

theorem row_sparseTurtles_iff (f : Cell → HTPlacement) (hf : ValidGridField f)
    (kind : HTKind) (hr : RootOwned f (canonicalRoot kind)) (i : Nat)
    (hi : i ∈ keptIds 2 kind) (hword : rawWordAt kind i = wordOf f kind) :
    SparseTurtlesAt f (canonicalRoot kind) ↔ sparseTurtlesRow kind i = true := by
  unfold SparseTurtlesAt
  rw [row_allOpposite_iff f hf kind hr i hword,allOppositeRow_eq_special kind i hi]
  cases kind <;> simp [canonicalRoot,specialRowB,sparseTurtlesRow]

end SpectreClusters.StageA
