module
public import ReplayRangeTools
public import ReplayRoot016
public import ReplayRoot017
public import ReplayRoot018
public import ReplayRoot019
public import ReplayRoot020
public import ReplayRoot021
public import ReplayRoot022
public import ReplayRoot023
public import ReplayRoot024
public import ReplayRoot025
public import ReplayRoot026
public import ReplayRoot027
public import ReplayRoot028
public import ReplayRoot029
public import ReplayRoot030
public import ReplayRoot031
namespace SparseMonotiles.FullContactReplay.Group01
open Contact CarrierHierarchy Contact.DirectReplay T7DirectMatchedBlockCoverage
set_option maxRecDepth 100000
set_option maxHeartbeats 0
public theorem classified : RootRange 16 32 :=
  (range_merge (range_merge (range_merge (range_merge (range_singleton 16 Root016.classified) (range_singleton 17 Root017.classified)) (range_merge (range_singleton 18 Root018.classified) (range_singleton 19 Root019.classified))) (range_merge (range_merge (range_singleton 20 Root020.classified) (range_singleton 21 Root021.classified)) (range_merge (range_singleton 22 Root022.classified) (range_singleton 23 Root023.classified)))) (range_merge (range_merge (range_merge (range_singleton 24 Root024.classified) (range_singleton 25 Root025.classified)) (range_merge (range_singleton 26 Root026.classified) (range_singleton 27 Root027.classified))) (range_merge (range_merge (range_singleton 28 Root028.classified) (range_singleton 29 Root029.classified)) (range_merge (range_singleton 30 Root030.classified) (range_singleton 31 Root031.classified)))))
#print axioms classified
end SparseMonotiles.FullContactReplay.Group01
