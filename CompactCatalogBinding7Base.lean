module
public import CompactPoseAdapter
public import SparseMonotiles.CarrierHierarchyCatalog7
@[expose] public section
namespace SparseMonotiles.CompactCatalogBinding7
open Contact CarrierHierarchy CompactPoseAdapter
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def nativeRow (i : Fin 408) : Contact.Pose 7 :=
  Catalog7.supplied.get ⟨i.val, by simpa only [Catalog7.supplied_count] using i.isLt⟩

def literalRow (i : Fin 408) : RegisteredPrime.Pose 7 :=
  CompactT7Preparation.literalCatalog.get ⟨i.val, by
    simpa only [CompactT7Preparation.literalCatalog_length] using i.isLt⟩

def RowSame (i : Fin 408) : Prop := (toRP (nativeRow i)).Same (literalRow i)

instance (i : Fin 408) : Decidable (RowSame i) := by
  unfold RowSame RegisteredPrime.Pose.Same
  infer_instance

end SparseMonotiles.CompactCatalogBinding7
