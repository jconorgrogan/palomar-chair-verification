module

public import SparseMonotiles.TileGeometry
public import SparseMonotiles.CoreCertificates
public import SparseMonotiles.LocalFiniteness

@[expose] public section

namespace SparseMonotiles

theorem T5_tiling_finite_intersect {tiles : Set (Set (Point 5))}
    (ht : IsTiling T5 tiles) {K : Set (Point 5)} (hK : Bornology.IsBounded K) :
    {A | A ∈ tiles ∧ (A ∩ K).Nonempty}.Finite :=
  ht.finite_intersect_of_isBounded T5_isCompact (by norm_num) T5_centralBall_from_cellCores hK

theorem T7_tiling_finite_intersect {tiles : Set (Set (Point 7))}
    (ht : IsTiling T7 tiles) {K : Set (Point 7)} (hK : Bornology.IsBounded K) :
    {A | A ∈ tiles ∧ (A ∩ K).Nonempty}.Finite :=
  ht.finite_intersect_of_isBounded T7_isCompact (by norm_num) T7_centralBall_from_cellCores hK

theorem T5_tiling_locallyFinite {tiles : Set (Set (Point 5))}
    (ht : IsTiling T5 tiles) : LocallyFinite (fun A : tiles => (A : Set (Point 5))) :=
  ht.locallyFinite T5_isCompact (by norm_num) T5_centralBall_from_cellCores

theorem T7_tiling_locallyFinite {tiles : Set (Set (Point 7))}
    (ht : IsTiling T7 tiles) : LocallyFinite (fun A : tiles => (A : Set (Point 7))) :=
  ht.locallyFinite T7_isCompact (by norm_num) T7_centralBall_from_cellCores

#print axioms T5_tiling_finite_intersect
#print axioms T7_tiling_finite_intersect
#print axioms T5_tiling_locallyFinite
#print axioms T7_tiling_locallyFinite

end SparseMonotiles
