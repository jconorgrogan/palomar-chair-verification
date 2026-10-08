module
public import ReplayRangeTools
public import ReplayRoot256
public import ReplayRoot257
public import ReplayRoot258
public import ReplayRoot259
public import ReplayRoot260
public import ReplayRoot261
public import ReplayRoot262
public import ReplayRoot263
public import ReplayRoot264
public import ReplayRoot265
public import ReplayRoot266
public import ReplayRoot267
public import ReplayRoot268
public import ReplayRoot269
public import ReplayRoot270
public import ReplayRoot271
namespace SparseMonotiles.FullContactReplay.Group16
open Contact CarrierHierarchy Contact.DirectReplay T7DirectMatchedBlockCoverage
set_option maxRecDepth 100000
set_option maxHeartbeats 0
public theorem classified : RootRange 256 272 :=
  (range_merge (range_merge (range_merge (range_merge (range_singleton 256 Root256.classified) (range_singleton 257 Root257.classified)) (range_merge (range_singleton 258 Root258.classified) (range_singleton 259 Root259.classified))) (range_merge (range_merge (range_singleton 260 Root260.classified) (range_singleton 261 Root261.classified)) (range_merge (range_singleton 262 Root262.classified) (range_singleton 263 Root263.classified)))) (range_merge (range_merge (range_merge (range_singleton 264 Root264.classified) (range_singleton 265 Root265.classified)) (range_merge (range_singleton 266 Root266.classified) (range_singleton 267 Root267.classified))) (range_merge (range_merge (range_singleton 268 Root268.classified) (range_singleton 269 Root269.classified)) (range_merge (range_singleton 270 Root270.classified) (range_singleton 271 Root271.classified)))))
#print axioms classified
end SparseMonotiles.FullContactReplay.Group16
