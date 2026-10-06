module

public import SparseMonotiles.T5Monotile
public import SparseMonotiles.CompactKeys5

@[expose] public section
namespace PalomarMonotiles

theorem T5_isAperiodicMonotile : T5Claim :=
  SparseMonotiles.CompactBinding.Keys5.claim_iff.mpr
    SparseMonotiles.T5_isAperiodicMonotile

end PalomarMonotiles
