module

public import SparseMonotiles.AtlasBindingChunks.Tile7Chunk0
public import SparseMonotiles.AtlasBindingChunks.Tile7Chunk1
public import SparseMonotiles.AtlasBindingChunks.Tile7Chunk2
public import SparseMonotiles.AtlasBindingChunks.Tile7Chunk3
public import SparseMonotiles.AtlasBindingChunks.Tile7Chunk4
public import SparseMonotiles.AtlasBindingChunks.Tile7Chunk5
public import SparseMonotiles.AtlasBindingChunks.Tile7Chunk6
public import SparseMonotiles.AtlasBindingChunks.Tile7Chunk7
public import SparseMonotiles.AtlasBindingChunks.Tile7Chunk8
public import SparseMonotiles.AtlasBindingChunks.Tile7Chunk9
public import SparseMonotiles.AtlasBindingChunks.Tile7Chunk10
public import SparseMonotiles.AtlasBindingChunks.Tile7Chunk11
public import SparseMonotiles.AtlasBindingChunks.Tile7Chunk12
public import SparseMonotiles.AtlasBindingChunks.Tile7Chunk13
public import SparseMonotiles.AtlasBindingChunks.Tile7Chunk14
public import SparseMonotiles.AtlasBindingChunks.Tile7Chunk15
public import SparseMonotiles.AtlasBindingChunks.Tile7Chunk16
public import SparseMonotiles.AtlasBindingChunks.Tile7Chunk17
public import SparseMonotiles.AtlasBindingChunks.Tile7Chunk18
public import SparseMonotiles.AtlasBindingChunks.Tile7Chunk19
public import SparseMonotiles.AtlasBindingChunks.Tile7Chunk20
public import SparseMonotiles.AtlasBindingChunks.Tile7Chunk21
public import SparseMonotiles.AtlasBindingChunks.Tile7Chunk22
public import SparseMonotiles.AtlasBindingChunks.Tile7Chunk23
public import SparseMonotiles.AtlasBindingChunks.Tile7Chunk24
public import SparseMonotiles.AtlasBindingChunks.Tile7Chunk25
public import SparseMonotiles.AtlasBindingChunks.Tile7Chunk26
public import SparseMonotiles.AtlasBindingChunks.Tile7Chunk27
public import SparseMonotiles.AtlasBindingChunks.Tile7Chunk28
public import SparseMonotiles.AtlasBindingChunks.Tile7Chunk29
public import SparseMonotiles.AtlasBindingChunks.Tile7Chunk30
public import SparseMonotiles.AtlasBindingChunks.Tile7Chunk31

@[expose] public section

namespace SparseMonotiles.Canonical

open SparseMonotiles.Contact

theorem everyKey7_in_atlas : ∀ k ∈ keys7,
    ∃ i : Fin 896, ∃ b ∈ IndexedData7.geometry.profile i,
      b.toKeyData 188160 = k :=
  (List.forall_mem_append.mpr ⟨(List.forall_mem_append.mpr ⟨(List.forall_mem_append.mpr ⟨(List.forall_mem_append.mpr ⟨(List.forall_mem_append.mpr ⟨(List.forall_mem_append.mpr ⟨(List.forall_mem_append.mpr ⟨(List.forall_mem_append.mpr ⟨(List.forall_mem_append.mpr ⟨(List.forall_mem_append.mpr ⟨(List.forall_mem_append.mpr ⟨(List.forall_mem_append.mpr ⟨(List.forall_mem_append.mpr ⟨(List.forall_mem_append.mpr ⟨(List.forall_mem_append.mpr ⟨(List.forall_mem_append.mpr ⟨(List.forall_mem_append.mpr ⟨(List.forall_mem_append.mpr ⟨(List.forall_mem_append.mpr ⟨(List.forall_mem_append.mpr ⟨(List.forall_mem_append.mpr ⟨(List.forall_mem_append.mpr ⟨(List.forall_mem_append.mpr ⟨(List.forall_mem_append.mpr ⟨(List.forall_mem_append.mpr ⟨(List.forall_mem_append.mpr ⟨(List.forall_mem_append.mpr ⟨(List.forall_mem_append.mpr ⟨(List.forall_mem_append.mpr ⟨(List.forall_mem_append.mpr ⟨(List.forall_mem_append.mpr ⟨keys7Chunk0_in_atlas, keys7Chunk1_in_atlas⟩), keys7Chunk2_in_atlas⟩), keys7Chunk3_in_atlas⟩), keys7Chunk4_in_atlas⟩), keys7Chunk5_in_atlas⟩), keys7Chunk6_in_atlas⟩), keys7Chunk7_in_atlas⟩), keys7Chunk8_in_atlas⟩), keys7Chunk9_in_atlas⟩), keys7Chunk10_in_atlas⟩), keys7Chunk11_in_atlas⟩), keys7Chunk12_in_atlas⟩), keys7Chunk13_in_atlas⟩), keys7Chunk14_in_atlas⟩), keys7Chunk15_in_atlas⟩), keys7Chunk16_in_atlas⟩), keys7Chunk17_in_atlas⟩), keys7Chunk18_in_atlas⟩), keys7Chunk19_in_atlas⟩), keys7Chunk20_in_atlas⟩), keys7Chunk21_in_atlas⟩), keys7Chunk22_in_atlas⟩), keys7Chunk23_in_atlas⟩), keys7Chunk24_in_atlas⟩), keys7Chunk25_in_atlas⟩), keys7Chunk26_in_atlas⟩), keys7Chunk27_in_atlas⟩), keys7Chunk28_in_atlas⟩), keys7Chunk29_in_atlas⟩), keys7Chunk30_in_atlas⟩), keys7Chunk31_in_atlas⟩)

#print axioms everyKey7_in_atlas

end SparseMonotiles.Canonical
