module

public import SparseMonotiles.AtlasReverseChunks.Tile5Facets0
public import SparseMonotiles.AtlasReverseChunks.Tile5Facets1
public import SparseMonotiles.AtlasReverseChunks.Tile5Facets2
public import SparseMonotiles.AtlasReverseChunks.Tile5Facets3
public import SparseMonotiles.AtlasReverseChunks.Tile5Facets4

@[expose] public section

namespace SparseMonotiles.Canonical
open Contact

/-- Every box signature in any indexed profile decodes to an actual literal key. -/
theorem everyAtlas5Key_isLiteral (i : Fin 160) (b : BoxKey 5)
    (hb : b ∈ IndexedData5.geometry.profile i) : b.toKeyData 19200 ∈ keys5 := by
  by_cases h0 : i.val < 32
  · have h := atlasReverse5Chunk0 ⟨i.val - 0, by omega⟩
    have he : (⟨0 + (i.val - 0), by omega⟩ : Fin 160) = i := by apply Fin.ext; dsimp; omega
    exact (he ▸ h) b hb
  by_cases h1 : i.val < 64
  · have h := atlasReverse5Chunk1 ⟨i.val - 32, by omega⟩
    have he : (⟨32 + (i.val - 32), by omega⟩ : Fin 160) = i := by apply Fin.ext; dsimp; omega
    exact (he ▸ h) b hb
  by_cases h2 : i.val < 96
  · have h := atlasReverse5Chunk2 ⟨i.val - 64, by omega⟩
    have he : (⟨64 + (i.val - 64), by omega⟩ : Fin 160) = i := by apply Fin.ext; dsimp; omega
    exact (he ▸ h) b hb
  by_cases h3 : i.val < 128
  · have h := atlasReverse5Chunk3 ⟨i.val - 96, by omega⟩
    have he : (⟨96 + (i.val - 96), by omega⟩ : Fin 160) = i := by apply Fin.ext; dsimp; omega
    exact (he ▸ h) b hb
  have h := atlasReverse5Chunk4 ⟨i.val - 128, by omega⟩
  have he : (⟨128 + (i.val - 128), by omega⟩ : Fin 160) = i := by apply Fin.ext; dsimp; omega
  exact (he ▸ h) b hb

#print axioms everyAtlas5Key_isLiteral
end SparseMonotiles.Canonical
