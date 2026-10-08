module
public import ReplayRangeTools
public import ReplayRoot000
public import ReplayRoot001
public import ReplayRoot002
public import ReplayRoot003
public import ReplayRoot004
public import ReplayRoot005
public import ReplayRoot006
public import ReplayRoot007
public import ReplayRoot008
public import ReplayRoot009
public import ReplayRoot010
public import ReplayRoot011
public import ReplayRoot012
public import ReplayRoot013
public import ReplayRoot014
public import ReplayRoot015
namespace SparseMonotiles.FullContactReplay.Group00
open Contact CarrierHierarchy Contact.DirectReplay T7DirectMatchedBlockCoverage
set_option maxRecDepth 100000
set_option maxHeartbeats 0
public theorem classified : RootRange 0 16 :=
  (range_merge (range_merge (range_merge (range_merge (range_singleton 0 Root000.classified) (range_singleton 1 Root001.classified)) (range_merge (range_singleton 2 Root002.classified) (range_singleton 3 Root003.classified))) (range_merge (range_merge (range_singleton 4 Root004.classified) (range_singleton 5 Root005.classified)) (range_merge (range_singleton 6 Root006.classified) (range_singleton 7 Root007.classified)))) (range_merge (range_merge (range_merge (range_singleton 8 Root008.classified) (range_singleton 9 Root009.classified)) (range_merge (range_singleton 10 Root010.classified) (range_singleton 11 Root011.classified))) (range_merge (range_merge (range_singleton 12 Root012.classified) (range_singleton 13 Root013.classified)) (range_merge (range_singleton 14 Root014.classified) (range_singleton 15 Root015.classified)))))
#print axioms classified
end SparseMonotiles.FullContactReplay.Group00
