module

public import SpectreClusters.FiniteCoverWords
public import SpectreClusters.StageAData

@[expose] public section

namespace SpectreClusters.StageA

def idCompatible (kind : HTKind) (a b : Nat) : Bool :=
  ((compatibilityBits kind).getD a 0).testBit b

end SpectreClusters.StageA
