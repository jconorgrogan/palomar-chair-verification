module

public import SparseMonotiles.CanonicalBindingChunks.Tile5Chunk0
public import SparseMonotiles.CanonicalBindingChunks.Tile5Chunk1
public import SparseMonotiles.CanonicalBindingChunks.Tile5Chunk2
public import SparseMonotiles.CanonicalBindingChunks.Tile5Chunk3
public import SparseMonotiles.CanonicalBindingChunks.Tile5Chunk4
public import SparseMonotiles.CanonicalBindingChunks.Tile5Chunk5
public import SparseMonotiles.CanonicalBindingChunks.Tile5Chunk6
public import SparseMonotiles.CanonicalBindingChunks.Tile5Chunk7

@[expose] public section

namespace SparseMonotiles.Canonical

open SparseMonotiles.Contact

theorem everyKey5_isCanonical : ∀ k ∈ keys5,
    ∃ p : Pose 5, keySolid k = p.euclidean '' referenceSolid5 := by
  exact (List.forall_mem_append.mpr ⟨(List.forall_mem_append.mpr ⟨(List.forall_mem_append.mpr ⟨(List.forall_mem_append.mpr ⟨(List.forall_mem_append.mpr ⟨(List.forall_mem_append.mpr ⟨(List.forall_mem_append.mpr ⟨keys5Chunk0_canonical, keys5Chunk1_canonical⟩), keys5Chunk2_canonical⟩), keys5Chunk3_canonical⟩), keys5Chunk4_canonical⟩), keys5Chunk5_canonical⟩), keys5Chunk6_canonical⟩), keys5Chunk7_canonical⟩)

#print axioms everyKey5_isCanonical

end SparseMonotiles.Canonical
