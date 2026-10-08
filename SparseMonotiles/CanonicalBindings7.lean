module

public import SparseMonotiles.CanonicalBindingChunks.Tile7Chunk0
public import SparseMonotiles.CanonicalBindingChunks.Tile7Chunk1
public import SparseMonotiles.CanonicalBindingChunks.Tile7Chunk2
public import SparseMonotiles.CanonicalBindingChunks.Tile7Chunk3
public import SparseMonotiles.CanonicalBindingChunks.Tile7Chunk4
public import SparseMonotiles.CanonicalBindingChunks.Tile7Chunk5
public import SparseMonotiles.CanonicalBindingChunks.Tile7Chunk6
public import SparseMonotiles.CanonicalBindingChunks.Tile7Chunk7
public import SparseMonotiles.CanonicalBindingChunks.Tile7Chunk8
public import SparseMonotiles.CanonicalBindingChunks.Tile7Chunk9
public import SparseMonotiles.CanonicalBindingChunks.Tile7Chunk10
public import SparseMonotiles.CanonicalBindingChunks.Tile7Chunk11
public import SparseMonotiles.CanonicalBindingChunks.Tile7Chunk12
public import SparseMonotiles.CanonicalBindingChunks.Tile7Chunk13
public import SparseMonotiles.CanonicalBindingChunks.Tile7Chunk14
public import SparseMonotiles.CanonicalBindingChunks.Tile7Chunk15
public import SparseMonotiles.CanonicalBindingChunks.Tile7Chunk16
public import SparseMonotiles.CanonicalBindingChunks.Tile7Chunk17
public import SparseMonotiles.CanonicalBindingChunks.Tile7Chunk18
public import SparseMonotiles.CanonicalBindingChunks.Tile7Chunk19
public import SparseMonotiles.CanonicalBindingChunks.Tile7Chunk20
public import SparseMonotiles.CanonicalBindingChunks.Tile7Chunk21
public import SparseMonotiles.CanonicalBindingChunks.Tile7Chunk22
public import SparseMonotiles.CanonicalBindingChunks.Tile7Chunk23
public import SparseMonotiles.CanonicalBindingChunks.Tile7Chunk24
public import SparseMonotiles.CanonicalBindingChunks.Tile7Chunk25
public import SparseMonotiles.CanonicalBindingChunks.Tile7Chunk26
public import SparseMonotiles.CanonicalBindingChunks.Tile7Chunk27
public import SparseMonotiles.CanonicalBindingChunks.Tile7Chunk28
public import SparseMonotiles.CanonicalBindingChunks.Tile7Chunk29
public import SparseMonotiles.CanonicalBindingChunks.Tile7Chunk30
public import SparseMonotiles.CanonicalBindingChunks.Tile7Chunk31

@[expose] public section

namespace SparseMonotiles.Canonical

open SparseMonotiles.Contact

theorem everyKey7_isCanonical : ∀ k ∈ keys7,
    ∃ p : Pose 7, keySolid k = p.euclidean '' referenceSolid7 := by
  exact (List.forall_mem_append.mpr ⟨(List.forall_mem_append.mpr ⟨(List.forall_mem_append.mpr ⟨(List.forall_mem_append.mpr ⟨(List.forall_mem_append.mpr ⟨(List.forall_mem_append.mpr ⟨(List.forall_mem_append.mpr ⟨(List.forall_mem_append.mpr ⟨(List.forall_mem_append.mpr ⟨(List.forall_mem_append.mpr ⟨(List.forall_mem_append.mpr ⟨(List.forall_mem_append.mpr ⟨(List.forall_mem_append.mpr ⟨(List.forall_mem_append.mpr ⟨(List.forall_mem_append.mpr ⟨(List.forall_mem_append.mpr ⟨(List.forall_mem_append.mpr ⟨(List.forall_mem_append.mpr ⟨(List.forall_mem_append.mpr ⟨(List.forall_mem_append.mpr ⟨(List.forall_mem_append.mpr ⟨(List.forall_mem_append.mpr ⟨(List.forall_mem_append.mpr ⟨(List.forall_mem_append.mpr ⟨(List.forall_mem_append.mpr ⟨(List.forall_mem_append.mpr ⟨(List.forall_mem_append.mpr ⟨(List.forall_mem_append.mpr ⟨(List.forall_mem_append.mpr ⟨(List.forall_mem_append.mpr ⟨(List.forall_mem_append.mpr ⟨keys7Chunk0_canonical, keys7Chunk1_canonical⟩), keys7Chunk2_canonical⟩), keys7Chunk3_canonical⟩), keys7Chunk4_canonical⟩), keys7Chunk5_canonical⟩), keys7Chunk6_canonical⟩), keys7Chunk7_canonical⟩), keys7Chunk8_canonical⟩), keys7Chunk9_canonical⟩), keys7Chunk10_canonical⟩), keys7Chunk11_canonical⟩), keys7Chunk12_canonical⟩), keys7Chunk13_canonical⟩), keys7Chunk14_canonical⟩), keys7Chunk15_canonical⟩), keys7Chunk16_canonical⟩), keys7Chunk17_canonical⟩), keys7Chunk18_canonical⟩), keys7Chunk19_canonical⟩), keys7Chunk20_canonical⟩), keys7Chunk21_canonical⟩), keys7Chunk22_canonical⟩), keys7Chunk23_canonical⟩), keys7Chunk24_canonical⟩), keys7Chunk25_canonical⟩), keys7Chunk26_canonical⟩), keys7Chunk27_canonical⟩), keys7Chunk28_canonical⟩), keys7Chunk29_canonical⟩), keys7Chunk30_canonical⟩), keys7Chunk31_canonical⟩)

#print axioms everyKey7_isCanonical

end SparseMonotiles.Canonical
