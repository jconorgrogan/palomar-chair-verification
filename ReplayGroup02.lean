module
public import ReplayRangeTools
public import ReplayRoot032
public import ReplayRoot033
public import ReplayRoot034
public import ReplayRoot035
public import ReplayRoot036
public import ReplayRoot037
public import ReplayRoot038
public import ReplayRoot039
public import ReplayRoot040
public import ReplayRoot041
public import ReplayRoot042
public import ReplayRoot043
public import ReplayRoot044
public import ReplayRoot045
public import ReplayRoot046
public import ReplayRoot047
namespace SparseMonotiles.FullContactReplay.Group02
open Contact CarrierHierarchy Contact.DirectReplay T7DirectMatchedBlockCoverage
set_option maxRecDepth 100000
set_option maxHeartbeats 0
public theorem classified : RootRange 32 48 :=
  (range_merge (range_merge (range_merge (range_merge (range_singleton 32 Root032.classified) (range_singleton 33 Root033.classified)) (range_merge (range_singleton 34 Root034.classified) (range_singleton 35 Root035.classified))) (range_merge (range_merge (range_singleton 36 Root036.classified) (range_singleton 37 Root037.classified)) (range_merge (range_singleton 38 Root038.classified) (range_singleton 39 Root039.classified)))) (range_merge (range_merge (range_merge (range_singleton 40 Root040.classified) (range_singleton 41 Root041.classified)) (range_merge (range_singleton 42 Root042.classified) (range_singleton 43 Root043.classified))) (range_merge (range_merge (range_singleton 44 Root044.classified) (range_singleton 45 Root045.classified)) (range_merge (range_singleton 46 Root046.classified) (range_singleton 47 Root047.classified)))))
#print axioms classified
end SparseMonotiles.FullContactReplay.Group02
