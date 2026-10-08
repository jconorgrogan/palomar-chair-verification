module
public import ReplayRangeTools
public import ReplayRoot384
public import ReplayRoot385
public import ReplayRoot386
public import ReplayRoot387
public import ReplayRoot388
public import ReplayRoot389
public import ReplayRoot390
public import ReplayRoot391
public import ReplayRoot392
public import ReplayRoot393
public import ReplayRoot394
public import ReplayRoot395
public import ReplayRoot396
public import ReplayRoot397
public import ReplayRoot398
public import ReplayRoot399
namespace SparseMonotiles.FullContactReplay.Group24
open Contact CarrierHierarchy Contact.DirectReplay T7DirectMatchedBlockCoverage
set_option maxRecDepth 100000
set_option maxHeartbeats 0
public theorem classified : RootRange 384 400 :=
  (range_merge (range_merge (range_merge (range_merge (range_singleton 384 Root384.classified) (range_singleton 385 Root385.classified)) (range_merge (range_singleton 386 Root386.classified) (range_singleton 387 Root387.classified))) (range_merge (range_merge (range_singleton 388 Root388.classified) (range_singleton 389 Root389.classified)) (range_merge (range_singleton 390 Root390.classified) (range_singleton 391 Root391.classified)))) (range_merge (range_merge (range_merge (range_singleton 392 Root392.classified) (range_singleton 393 Root393.classified)) (range_merge (range_singleton 394 Root394.classified) (range_singleton 395 Root395.classified))) (range_merge (range_merge (range_singleton 396 Root396.classified) (range_singleton 397 Root397.classified)) (range_merge (range_singleton 398 Root398.classified) (range_singleton 399 Root399.classified)))))
#print axioms classified
end SparseMonotiles.FullContactReplay.Group24
