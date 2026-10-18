module

public import SpectreClusters.StageDRawData

@[expose] public section

namespace SpectreClusters.StageD.Raw
open FiniteCoverWords

def idCompatible (kind : ClusterKind) (a b : Nat) : Bool :=
  ((compatibilityBits kind).getD a 0).testBit b

theorem extend_append {α : Type} (compatible : α → α → Bool)
    (choices : List α) (a b : List (List α)) :
    extend compatible choices (a ++ b) =
      extend compatible choices a ++ extend compatible choices b := by
  simp [extend,List.flatMap_append]
end SpectreClusters.StageD.Raw
