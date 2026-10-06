module

public import SparseMonotiles.CoreCertificateChunks.Tile5Chunk0
public import SparseMonotiles.CoreCertificateChunks.Tile5Chunk1
public import SparseMonotiles.CoreCertificateChunks.Tile5Chunk2
public import SparseMonotiles.CoreCertificateChunks.Tile5Chunk3
public import SparseMonotiles.CoreCertificateChunks.Tile5Chunk4
public import SparseMonotiles.CoreCertificateChunks.Tile5Chunk5
public import SparseMonotiles.CoreCertificateChunks.Tile5Chunk6
public import SparseMonotiles.CoreCertificateChunks.Tile5Chunk7
public import SparseMonotiles.CoreCertificateChunks.Tile7Chunk0
public import SparseMonotiles.CoreCertificateChunks.Tile7Chunk1
public import SparseMonotiles.CoreCertificateChunks.Tile7Chunk2
public import SparseMonotiles.CoreCertificateChunks.Tile7Chunk3
public import SparseMonotiles.CoreCertificateChunks.Tile7Chunk4
public import SparseMonotiles.CoreCertificateChunks.Tile7Chunk5
public import SparseMonotiles.CoreCertificateChunks.Tile7Chunk6
public import SparseMonotiles.CoreCertificateChunks.Tile7Chunk7
public import SparseMonotiles.CoreCertificateChunks.Tile7Chunk8
public import SparseMonotiles.CoreCertificateChunks.Tile7Chunk9
public import SparseMonotiles.CoreCertificateChunks.Tile7Chunk10
public import SparseMonotiles.CoreCertificateChunks.Tile7Chunk11
public import SparseMonotiles.CoreCertificateChunks.Tile7Chunk12
public import SparseMonotiles.CoreCertificateChunks.Tile7Chunk13
public import SparseMonotiles.CoreCertificateChunks.Tile7Chunk14
public import SparseMonotiles.CoreCertificateChunks.Tile7Chunk15
public import SparseMonotiles.CoreCertificateChunks.Tile7Chunk16
public import SparseMonotiles.CoreCertificateChunks.Tile7Chunk17
public import SparseMonotiles.CoreCertificateChunks.Tile7Chunk18
public import SparseMonotiles.CoreCertificateChunks.Tile7Chunk19
public import SparseMonotiles.CoreCertificateChunks.Tile7Chunk20
public import SparseMonotiles.CoreCertificateChunks.Tile7Chunk21
public import SparseMonotiles.CoreCertificateChunks.Tile7Chunk22
public import SparseMonotiles.CoreCertificateChunks.Tile7Chunk23
public import SparseMonotiles.CoreCertificateChunks.Tile7Chunk24
public import SparseMonotiles.CoreCertificateChunks.Tile7Chunk25
public import SparseMonotiles.CoreCertificateChunks.Tile7Chunk26
public import SparseMonotiles.CoreCertificateChunks.Tile7Chunk27
public import SparseMonotiles.CoreCertificateChunks.Tile7Chunk28
public import SparseMonotiles.CoreCertificateChunks.Tile7Chunk29
public import SparseMonotiles.CoreCertificateChunks.Tile7Chunk30
public import SparseMonotiles.CoreCertificateChunks.Tile7Chunk31

@[expose] public section

namespace SparseMonotiles

theorem keys5_normalBand : ∀ k ∈ keys5, HasNormalIntegerBand (1/100) k := by
  exact (List.forall_mem_append.mpr ⟨(List.forall_mem_append.mpr ⟨(List.forall_mem_append.mpr ⟨(List.forall_mem_append.mpr ⟨(List.forall_mem_append.mpr ⟨(List.forall_mem_append.mpr ⟨(List.forall_mem_append.mpr ⟨keys5Chunk0_normalBand, keys5Chunk1_normalBand⟩), keys5Chunk2_normalBand⟩), keys5Chunk3_normalBand⟩), keys5Chunk4_normalBand⟩), keys5Chunk5_normalBand⟩), keys5Chunk6_normalBand⟩), keys5Chunk7_normalBand⟩)

theorem T5_carrierCellCore_subset_interior (c : Fin 5 → Bool)
    (hc : ∃ i, c i = false) :
    carrierCellCore (1/100) c ⊆ interior T5 :=
  carrierCellCore_subset_interior_body (1/100) (by norm_num) keys5 keys5_normalBand c hc

theorem T5_centralBall_from_cellCores :
    Metric.ball (centralPoint 5) (1/4 : ℝ) ⊆ T5 :=
  centralBall_subset_body_of_normalIntegerBands (by norm_num) keys5 keys5_normalBand

theorem T5_interior_nonempty_from_cellCores : (interior T5).Nonempty :=
  body_interior_nonempty_of_normalIntegerBands (by norm_num) keys5 keys5_normalBand

#print axioms keys5_normalBand
#print axioms T5_carrierCellCore_subset_interior
#print axioms T5_centralBall_from_cellCores
#print axioms T5_interior_nonempty_from_cellCores

theorem keys7_normalBand : ∀ k ∈ keys7, HasNormalIntegerBand (1/100) k := by
  exact (List.forall_mem_append.mpr ⟨(List.forall_mem_append.mpr ⟨(List.forall_mem_append.mpr ⟨(List.forall_mem_append.mpr ⟨(List.forall_mem_append.mpr ⟨(List.forall_mem_append.mpr ⟨(List.forall_mem_append.mpr ⟨(List.forall_mem_append.mpr ⟨(List.forall_mem_append.mpr ⟨(List.forall_mem_append.mpr ⟨(List.forall_mem_append.mpr ⟨(List.forall_mem_append.mpr ⟨(List.forall_mem_append.mpr ⟨(List.forall_mem_append.mpr ⟨(List.forall_mem_append.mpr ⟨(List.forall_mem_append.mpr ⟨(List.forall_mem_append.mpr ⟨(List.forall_mem_append.mpr ⟨(List.forall_mem_append.mpr ⟨(List.forall_mem_append.mpr ⟨(List.forall_mem_append.mpr ⟨(List.forall_mem_append.mpr ⟨(List.forall_mem_append.mpr ⟨(List.forall_mem_append.mpr ⟨(List.forall_mem_append.mpr ⟨(List.forall_mem_append.mpr ⟨(List.forall_mem_append.mpr ⟨(List.forall_mem_append.mpr ⟨(List.forall_mem_append.mpr ⟨(List.forall_mem_append.mpr ⟨(List.forall_mem_append.mpr ⟨keys7Chunk0_normalBand, keys7Chunk1_normalBand⟩), keys7Chunk2_normalBand⟩), keys7Chunk3_normalBand⟩), keys7Chunk4_normalBand⟩), keys7Chunk5_normalBand⟩), keys7Chunk6_normalBand⟩), keys7Chunk7_normalBand⟩), keys7Chunk8_normalBand⟩), keys7Chunk9_normalBand⟩), keys7Chunk10_normalBand⟩), keys7Chunk11_normalBand⟩), keys7Chunk12_normalBand⟩), keys7Chunk13_normalBand⟩), keys7Chunk14_normalBand⟩), keys7Chunk15_normalBand⟩), keys7Chunk16_normalBand⟩), keys7Chunk17_normalBand⟩), keys7Chunk18_normalBand⟩), keys7Chunk19_normalBand⟩), keys7Chunk20_normalBand⟩), keys7Chunk21_normalBand⟩), keys7Chunk22_normalBand⟩), keys7Chunk23_normalBand⟩), keys7Chunk24_normalBand⟩), keys7Chunk25_normalBand⟩), keys7Chunk26_normalBand⟩), keys7Chunk27_normalBand⟩), keys7Chunk28_normalBand⟩), keys7Chunk29_normalBand⟩), keys7Chunk30_normalBand⟩), keys7Chunk31_normalBand⟩)

theorem T7_carrierCellCore_subset_interior (c : Fin 7 → Bool)
    (hc : ∃ i, c i = false) :
    carrierCellCore (1/100) c ⊆ interior T7 :=
  carrierCellCore_subset_interior_body (1/100) (by norm_num) keys7 keys7_normalBand c hc

theorem T7_centralBall_from_cellCores :
    Metric.ball (centralPoint 7) (1/4 : ℝ) ⊆ T7 :=
  centralBall_subset_body_of_normalIntegerBands (by norm_num) keys7 keys7_normalBand

theorem T7_interior_nonempty_from_cellCores : (interior T7).Nonempty :=
  body_interior_nonempty_of_normalIntegerBands (by norm_num) keys7 keys7_normalBand

#print axioms keys7_normalBand
#print axioms T7_carrierCellCore_subset_interior
#print axioms T7_centralBall_from_cellCores
#print axioms T7_interior_nonempty_from_cellCores

end SparseMonotiles
