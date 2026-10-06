module

public import SparseMonotiles.T5Aperiodicity
public import SparseMonotiles.Tile5Existence

@[expose] public section

/-! The exact literal S54 five-dimensional body is an aperiodic monotile:
compactness, an actual tiling, and absence of nonzero translation periods in
every physical tiling under arbitrary Euclidean isometries. -/
namespace SparseMonotiles

theorem T5_isAperiodicMonotile : IsAperiodicMonotile T5 :=
  ⟨T5_isCompact,T5_hasTiling,T5_isAperiodic⟩

theorem T5Goal_proved : T5Goal := T5_isAperiodicMonotile

#print axioms T5_isAperiodicMonotile
#print axioms T5Goal_proved
end SparseMonotiles
