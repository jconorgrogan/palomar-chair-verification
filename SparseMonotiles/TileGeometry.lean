module

public import SparseMonotiles.Compactness
public import SparseMonotiles.Tile5Data
public import SparseMonotiles.Tile7Data

@[expose] public section

namespace SparseMonotiles

theorem T5_isCompact : IsCompact T5 := body_isCompact keys5
theorem T7_isCompact : IsCompact T7 := body_isCompact keys7

#print axioms body_isCompact
#print axioms T5_isCompact
#print axioms T7_isCompact
#print axioms keys5_length
#print axioms keys7_length

end SparseMonotiles
