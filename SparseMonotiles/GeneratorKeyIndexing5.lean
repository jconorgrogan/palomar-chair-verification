module

public import SparseMonotiles.GeneratorKeyIndexingChunks.Tile5Chunk0
public import SparseMonotiles.GeneratorKeyIndexingChunks.Tile5Chunk1
public import SparseMonotiles.GeneratorKeyIndexingChunks.Tile5Chunk2
public import SparseMonotiles.GeneratorKeyIndexingChunks.Tile5Chunk3
public import SparseMonotiles.GeneratorKeyIndexingChunks.Tile5Chunk4

@[expose] public section

namespace SparseMonotiles.Contact.IndexedData5
theorem generatorIndexBinding_checked : ∀ i : Fin 160, generatorIndexBinding i := by
  intro i
  by_cases h0 : i.val < 32
  · have h := generatorIndexBindingChunk0 ⟨i.val - 0, by omega⟩
    have he : (⟨0 + (i.val - 0), by omega⟩ : Fin 160) = i := by apply Fin.ext; dsimp; omega
    exact he ▸ h
  by_cases h1 : i.val < 64
  · have h := generatorIndexBindingChunk1 ⟨i.val - 32, by omega⟩
    have he : (⟨32 + (i.val - 32), by omega⟩ : Fin 160) = i := by apply Fin.ext; dsimp; omega
    exact he ▸ h
  by_cases h2 : i.val < 96
  · have h := generatorIndexBindingChunk2 ⟨i.val - 64, by omega⟩
    have he : (⟨64 + (i.val - 64), by omega⟩ : Fin 160) = i := by apply Fin.ext; dsimp; omega
    exact he ▸ h
  by_cases h3 : i.val < 128
  · have h := generatorIndexBindingChunk3 ⟨i.val - 96, by omega⟩
    have he : (⟨96 + (i.val - 96), by omega⟩ : Fin 160) = i := by apply Fin.ext; dsimp; omega
    exact he ▸ h
  by_cases h4 : i.val < 160
  · have h := generatorIndexBindingChunk4 ⟨i.val - 128, by omega⟩
    have he : (⟨128 + (i.val - 128), by omega⟩ : Fin 160) = i := by apply Fin.ext; dsimp; omega
    exact he ▸ h
  omega
noncomputable def generatorIndexing : KeyIndexing geometry 256 :=
  KeyIndexing.ofLists generatorOwner generatorKey generatorProfileList
    (fun i => (generatorIndexBinding_checked i).1)
    (fun i => (generatorIndexBinding_checked i).2)
#print axioms generatorIndexBinding_checked
end SparseMonotiles.Contact.IndexedData5
