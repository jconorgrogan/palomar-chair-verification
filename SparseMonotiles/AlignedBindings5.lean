module

public import SparseMonotiles.AlignedBindingChunks.Tile5Chunk0
public import SparseMonotiles.AlignedBindingChunks.Tile5Chunk1
public import SparseMonotiles.AlignedBindingChunks.Tile5Chunk2
public import SparseMonotiles.AlignedBindingChunks.Tile5Chunk3
public import SparseMonotiles.AlignedBindingChunks.Tile5Chunk4
public import SparseMonotiles.AlignedBindingChunks.Tile5Chunk5
public import SparseMonotiles.AlignedBindingChunks.Tile5Chunk6
public import SparseMonotiles.AlignedBindingChunks.Tile5Chunk7

@[expose] public section

namespace SparseMonotiles.Canonical

open SparseMonotiles.Contact

theorem everyKey5_has_aligned_atlas_pose : ∀ k ∈ keys5,
    ∃ i : Fin 160, ∃ b ∈ IndexedData5.geometry.profile i, ∃ p : Pose 5,
      p.boxKey 19200 (referenceBox5 (!b.bump)) = b ∧ b.toKeyData 19200 = k :=
  (List.forall_mem_append.mpr ⟨(List.forall_mem_append.mpr ⟨(List.forall_mem_append.mpr ⟨(List.forall_mem_append.mpr ⟨(List.forall_mem_append.mpr ⟨(List.forall_mem_append.mpr ⟨(List.forall_mem_append.mpr ⟨keys5Chunk0_aligned, keys5Chunk1_aligned⟩), keys5Chunk2_aligned⟩), keys5Chunk3_aligned⟩), keys5Chunk4_aligned⟩), keys5Chunk5_aligned⟩), keys5Chunk6_aligned⟩), keys5Chunk7_aligned⟩)

#print axioms everyKey5_has_aligned_atlas_pose

end SparseMonotiles.Canonical
