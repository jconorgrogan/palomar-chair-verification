module

public import SpectreFinite.BoundaryWords

@[expose] public section


/-! Every literal exposed child edge belongs to an actual marked macro-side.
This finite witness supports native-cell adjacency in the coarse graph. -/
namespace SpectreFinite.Boundary

def ExposedChildEdge (k : TileKind) (c : PlacedHex) (d : Fin 6) : Prop :=
  ∀ b ∈ children k, pos b ≠ addPos (pos c) (direction d)
instance (k : TileKind) (c : PlacedHex) (d : Fin 6) : Decidable (ExposedChildEdge k c d) :=
  inferInstanceAs (Decidable (∀ b ∈ children k, _ ≠ _))

theorem exposed_child_macro_side : ∀ (k : TileKind), ∀ c ∈ children k, ∀ d : Fin 6,
    ExposedChildEdge k c d →
      ∃ s : Fin 6, ∃ e ∈ segment k s, hexAt (children k) e = c ∧ e.side = d := by
  decide

end SpectreFinite.Boundary
