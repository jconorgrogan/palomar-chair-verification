module
public import ReplayRangeTools
public import ReplayRoot160
public import ReplayRoot161
public import ReplayRoot162
public import ReplayRoot163
public import ReplayRoot164
public import ReplayRoot165
public import ReplayRoot166
public import ReplayRoot167
public import ReplayRoot168
public import ReplayRoot169
public import ReplayRoot170
public import ReplayRoot171
public import ReplayRoot172
public import ReplayRoot173
public import ReplayRoot174
public import ReplayRoot175
namespace SparseMonotiles.FullContactReplay.Group10
open Contact CarrierHierarchy Contact.DirectReplay T7DirectMatchedBlockCoverage
set_option maxRecDepth 100000
set_option maxHeartbeats 0
public theorem classified : RootRange 160 176 :=
  (range_merge (range_merge (range_merge (range_merge (range_singleton 160 Root160.classified) (range_singleton 161 Root161.classified)) (range_merge (range_singleton 162 Root162.classified) (range_singleton 163 Root163.classified))) (range_merge (range_merge (range_singleton 164 Root164.classified) (range_singleton 165 Root165.classified)) (range_merge (range_singleton 166 Root166.classified) (range_singleton 167 Root167.classified)))) (range_merge (range_merge (range_merge (range_singleton 168 Root168.classified) (range_singleton 169 Root169.classified)) (range_merge (range_singleton 170 Root170.classified) (range_singleton 171 Root171.classified))) (range_merge (range_merge (range_singleton 172 Root172.classified) (range_singleton 173 Root173.classified)) (range_merge (range_singleton 174 Root174.classified) (range_singleton 175 Root175.classified)))))
#print axioms classified
end SparseMonotiles.FullContactReplay.Group10
