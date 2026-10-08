module

public import SparseMonotiles.AlignedBindingChunks.Tile7Chunk0
public import SparseMonotiles.AlignedBindingChunks.Tile7Chunk1
public import SparseMonotiles.AlignedBindingChunks.Tile7Chunk2
public import SparseMonotiles.AlignedBindingChunks.Tile7Chunk3
public import SparseMonotiles.AlignedBindingChunks.Tile7Chunk4
public import SparseMonotiles.AlignedBindingChunks.Tile7Chunk5
public import SparseMonotiles.AlignedBindingChunks.Tile7Chunk6
public import SparseMonotiles.AlignedBindingChunks.Tile7Chunk7
public import SparseMonotiles.AlignedBindingChunks.Tile7Chunk8
public import SparseMonotiles.AlignedBindingChunks.Tile7Chunk9
public import SparseMonotiles.AlignedBindingChunks.Tile7Chunk10
public import SparseMonotiles.AlignedBindingChunks.Tile7Chunk11
public import SparseMonotiles.AlignedBindingChunks.Tile7Chunk12
public import SparseMonotiles.AlignedBindingChunks.Tile7Chunk13
public import SparseMonotiles.AlignedBindingChunks.Tile7Chunk14
public import SparseMonotiles.AlignedBindingChunks.Tile7Chunk15
public import SparseMonotiles.AlignedBindingChunks.Tile7Chunk16
public import SparseMonotiles.AlignedBindingChunks.Tile7Chunk17
public import SparseMonotiles.AlignedBindingChunks.Tile7Chunk18
public import SparseMonotiles.AlignedBindingChunks.Tile7Chunk19
public import SparseMonotiles.AlignedBindingChunks.Tile7Chunk20
public import SparseMonotiles.AlignedBindingChunks.Tile7Chunk21
public import SparseMonotiles.AlignedBindingChunks.Tile7Chunk22
public import SparseMonotiles.AlignedBindingChunks.Tile7Chunk23
public import SparseMonotiles.AlignedBindingChunks.Tile7Chunk24
public import SparseMonotiles.AlignedBindingChunks.Tile7Chunk25
public import SparseMonotiles.AlignedBindingChunks.Tile7Chunk26
public import SparseMonotiles.AlignedBindingChunks.Tile7Chunk27
public import SparseMonotiles.AlignedBindingChunks.Tile7Chunk28
public import SparseMonotiles.AlignedBindingChunks.Tile7Chunk29
public import SparseMonotiles.AlignedBindingChunks.Tile7Chunk30
public import SparseMonotiles.AlignedBindingChunks.Tile7Chunk31

@[expose] public section

namespace SparseMonotiles.Canonical

open SparseMonotiles.Contact

theorem everyKey7_has_aligned_atlas_pose : ∀ k ∈ keys7,
    ∃ i : Fin 896, ∃ b ∈ IndexedData7.geometry.profile i, ∃ p : Pose 7,
      p.boxKey 188160 (referenceBox7 (!b.bump)) = b ∧ b.toKeyData 188160 = k :=
  (List.forall_mem_append.mpr ⟨(List.forall_mem_append.mpr ⟨(List.forall_mem_append.mpr ⟨(List.forall_mem_append.mpr ⟨(List.forall_mem_append.mpr ⟨(List.forall_mem_append.mpr ⟨(List.forall_mem_append.mpr ⟨(List.forall_mem_append.mpr ⟨(List.forall_mem_append.mpr ⟨(List.forall_mem_append.mpr ⟨(List.forall_mem_append.mpr ⟨(List.forall_mem_append.mpr ⟨(List.forall_mem_append.mpr ⟨(List.forall_mem_append.mpr ⟨(List.forall_mem_append.mpr ⟨(List.forall_mem_append.mpr ⟨(List.forall_mem_append.mpr ⟨(List.forall_mem_append.mpr ⟨(List.forall_mem_append.mpr ⟨(List.forall_mem_append.mpr ⟨(List.forall_mem_append.mpr ⟨(List.forall_mem_append.mpr ⟨(List.forall_mem_append.mpr ⟨(List.forall_mem_append.mpr ⟨(List.forall_mem_append.mpr ⟨(List.forall_mem_append.mpr ⟨(List.forall_mem_append.mpr ⟨(List.forall_mem_append.mpr ⟨(List.forall_mem_append.mpr ⟨(List.forall_mem_append.mpr ⟨(List.forall_mem_append.mpr ⟨keys7Chunk0_aligned, keys7Chunk1_aligned⟩), keys7Chunk2_aligned⟩), keys7Chunk3_aligned⟩), keys7Chunk4_aligned⟩), keys7Chunk5_aligned⟩), keys7Chunk6_aligned⟩), keys7Chunk7_aligned⟩), keys7Chunk8_aligned⟩), keys7Chunk9_aligned⟩), keys7Chunk10_aligned⟩), keys7Chunk11_aligned⟩), keys7Chunk12_aligned⟩), keys7Chunk13_aligned⟩), keys7Chunk14_aligned⟩), keys7Chunk15_aligned⟩), keys7Chunk16_aligned⟩), keys7Chunk17_aligned⟩), keys7Chunk18_aligned⟩), keys7Chunk19_aligned⟩), keys7Chunk20_aligned⟩), keys7Chunk21_aligned⟩), keys7Chunk22_aligned⟩), keys7Chunk23_aligned⟩), keys7Chunk24_aligned⟩), keys7Chunk25_aligned⟩), keys7Chunk26_aligned⟩), keys7Chunk27_aligned⟩), keys7Chunk28_aligned⟩), keys7Chunk29_aligned⟩), keys7Chunk30_aligned⟩), keys7Chunk31_aligned⟩)

#print axioms everyKey7_has_aligned_atlas_pose

end SparseMonotiles.Canonical
