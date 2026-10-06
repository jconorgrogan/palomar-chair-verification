module

public import SparseMonotiles.Tile5Data
public import SparseMonotiles.Tile7Data

@[expose] public section

namespace SparseMonotiles

/-- This is the requested statement. A proposition definition is not a proof. -/
def T5Goal : Prop := IsAperiodicMonotile T5

/-- This is the requested statement. A proposition definition is not a proof. -/
def T7Goal : Prop := IsAperiodicMonotile T7

/- There are deliberately no declarations asserting T5Goal or T7Goal here. -/

end SparseMonotiles
