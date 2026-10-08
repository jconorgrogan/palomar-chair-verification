module
public import ReplayRangeTools
public import ReplayRoot400
public import ReplayRoot401
public import ReplayRoot402
public import ReplayRoot403
public import ReplayRoot404
public import ReplayRoot405
public import ReplayRoot406
public import ReplayRoot407
public import ReplayRoot408
public import ReplayRoot409
public import ReplayRoot410
public import ReplayRoot411
public import ReplayRoot412
public import ReplayRoot413
public import ReplayRoot414
public import ReplayRoot415
namespace SparseMonotiles.FullContactReplay.Group25
open Contact CarrierHierarchy Contact.DirectReplay T7DirectMatchedBlockCoverage
set_option maxRecDepth 100000
set_option maxHeartbeats 0
public theorem classified : RootRange 400 416 :=
  (range_merge (range_merge (range_merge (range_merge (range_singleton 400 Root400.classified) (range_singleton 401 Root401.classified)) (range_merge (range_singleton 402 Root402.classified) (range_singleton 403 Root403.classified))) (range_merge (range_merge (range_singleton 404 Root404.classified) (range_singleton 405 Root405.classified)) (range_merge (range_singleton 406 Root406.classified) (range_singleton 407 Root407.classified)))) (range_merge (range_merge (range_merge (range_singleton 408 Root408.classified) (range_singleton 409 Root409.classified)) (range_merge (range_singleton 410 Root410.classified) (range_singleton 411 Root411.classified))) (range_merge (range_merge (range_singleton 412 Root412.classified) (range_singleton 413 Root413.classified)) (range_merge (range_singleton 414 Root414.classified) (range_singleton 415 Root415.classified)))))
#print axioms classified
end SparseMonotiles.FullContactReplay.Group25
