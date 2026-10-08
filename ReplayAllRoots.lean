module
public import ReplayRangeTools
public import ReplayGroup00
public import ReplayGroup01
public import ReplayGroup02
public import ReplayGroup03
public import ReplayGroup04
public import ReplayGroup05
public import ReplayGroup06
public import ReplayGroup07
public import ReplayGroup08
public import ReplayGroup09
public import ReplayGroup10
public import ReplayGroup11
public import ReplayGroup12
public import ReplayGroup13
public import ReplayGroup14
public import ReplayGroup15
public import ReplayGroup16
public import ReplayGroup17
public import ReplayGroup18
public import ReplayGroup19
public import ReplayGroup20
public import ReplayGroup21
public import ReplayGroup22
public import ReplayGroup23
public import ReplayGroup24
public import ReplayGroup25
public import ReplayGroup26
public import ReplayGroup27
public import ReplayGroup28
public import ReplayGroup29
public import ReplayGroup30
public import ReplayGroup31
namespace SparseMonotiles.FullContactReplay.AllRoots
open Contact CarrierHierarchy Contact.DirectReplay T7DirectMatchedBlockCoverage
set_option maxRecDepth 100000
set_option maxHeartbeats 0
public theorem classified : ∀ a b : Fin 512, PairLaw a b :=
  range_all (range_merge (range_merge (range_merge (range_merge (range_merge Group00.classified Group01.classified) (range_merge Group02.classified Group03.classified)) (range_merge (range_merge Group04.classified Group05.classified) (range_merge Group06.classified Group07.classified))) (range_merge (range_merge (range_merge Group08.classified Group09.classified) (range_merge Group10.classified Group11.classified)) (range_merge (range_merge Group12.classified Group13.classified) (range_merge Group14.classified Group15.classified)))) (range_merge (range_merge (range_merge (range_merge Group16.classified Group17.classified) (range_merge Group18.classified Group19.classified)) (range_merge (range_merge Group20.classified Group21.classified) (range_merge Group22.classified Group23.classified))) (range_merge (range_merge (range_merge Group24.classified Group25.classified) (range_merge Group26.classified Group27.classified)) (range_merge (range_merge Group28.classified Group29.classified) (range_merge Group30.classified Group31.classified)))))
#print axioms classified
end SparseMonotiles.FullContactReplay.AllRoots
