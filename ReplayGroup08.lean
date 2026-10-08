module
public import ReplayRangeTools
public import ReplayRoot128
public import ReplayRoot129
public import ReplayRoot130
public import ReplayRoot131
public import ReplayRoot132
public import ReplayRoot133
public import ReplayRoot134
public import ReplayRoot135
public import ReplayRoot136
public import ReplayRoot137
public import ReplayRoot138
public import ReplayRoot139
public import ReplayRoot140
public import ReplayRoot141
public import ReplayRoot142
public import ReplayRoot143
namespace SparseMonotiles.FullContactReplay.Group08
open Contact CarrierHierarchy Contact.DirectReplay T7DirectMatchedBlockCoverage
set_option maxRecDepth 100000
set_option maxHeartbeats 0
public theorem classified : RootRange 128 144 :=
  (range_merge (range_merge (range_merge (range_merge (range_singleton 128 Root128.classified) (range_singleton 129 Root129.classified)) (range_merge (range_singleton 130 Root130.classified) (range_singleton 131 Root131.classified))) (range_merge (range_merge (range_singleton 132 Root132.classified) (range_singleton 133 Root133.classified)) (range_merge (range_singleton 134 Root134.classified) (range_singleton 135 Root135.classified)))) (range_merge (range_merge (range_merge (range_singleton 136 Root136.classified) (range_singleton 137 Root137.classified)) (range_merge (range_singleton 138 Root138.classified) (range_singleton 139 Root139.classified))) (range_merge (range_merge (range_singleton 140 Root140.classified) (range_singleton 141 Root141.classified)) (range_merge (range_singleton 142 Root142.classified) (range_singleton 143 Root143.classified)))))
#print axioms classified
end SparseMonotiles.FullContactReplay.Group08
