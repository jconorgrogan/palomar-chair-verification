module

public import SparseMonotiles.AtlasBindingChunks.Tile5Chunk0
public import SparseMonotiles.AtlasBindingChunks.Tile5Chunk1
public import SparseMonotiles.AtlasBindingChunks.Tile5Chunk2
public import SparseMonotiles.AtlasBindingChunks.Tile5Chunk3
public import SparseMonotiles.AtlasBindingChunks.Tile5Chunk4
public import SparseMonotiles.AtlasBindingChunks.Tile5Chunk5
public import SparseMonotiles.AtlasBindingChunks.Tile5Chunk6
public import SparseMonotiles.AtlasBindingChunks.Tile5Chunk7

@[expose] public section

namespace SparseMonotiles.Canonical

open SparseMonotiles.Contact

theorem everyKey5_in_atlas : ∀ k ∈ keys5,
    ∃ i : Fin 160, ∃ b ∈ IndexedData5.geometry.profile i,
      b.toKeyData 19200 = k :=
  (List.forall_mem_append.mpr ⟨(List.forall_mem_append.mpr ⟨(List.forall_mem_append.mpr ⟨(List.forall_mem_append.mpr ⟨(List.forall_mem_append.mpr ⟨(List.forall_mem_append.mpr ⟨(List.forall_mem_append.mpr ⟨keys5Chunk0_in_atlas, keys5Chunk1_in_atlas⟩), keys5Chunk2_in_atlas⟩), keys5Chunk3_in_atlas⟩), keys5Chunk4_in_atlas⟩), keys5Chunk5_in_atlas⟩), keys5Chunk6_in_atlas⟩), keys5Chunk7_in_atlas⟩)

#print axioms everyKey5_in_atlas

end SparseMonotiles.Canonical
