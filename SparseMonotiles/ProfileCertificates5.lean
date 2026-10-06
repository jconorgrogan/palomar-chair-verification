module

public import SparseMonotiles.ProfileCertificateChunks.Tile5Chunk0
public import SparseMonotiles.ProfileCertificateChunks.Tile5Chunk1
public import SparseMonotiles.ProfileCertificateChunks.Tile5Chunk2
public import SparseMonotiles.ProfileCertificateChunks.Tile5Chunk3
public import SparseMonotiles.ProfileCertificateChunks.Tile5Chunk4

@[expose] public section

namespace SparseMonotiles.Contact

theorem profile5_checked : ∀ i, IndexedData5.geometry.ProfileValidAt 80 i := by
  intro i
  by_cases h0 : i.val < 32
  · have h := profile5Chunk0_checked ⟨i.val - 0, by omega⟩
    have he : (⟨0 + (i.val - 0), by omega⟩ : Fin 160) = i := by apply Fin.ext; dsimp; omega
    exact he ▸ h
  by_cases h1 : i.val < 64
  · have h := profile5Chunk1_checked ⟨i.val - 32, by omega⟩
    have he : (⟨32 + (i.val - 32), by omega⟩ : Fin 160) = i := by apply Fin.ext; dsimp; omega
    exact he ▸ h
  by_cases h2 : i.val < 96
  · have h := profile5Chunk2_checked ⟨i.val - 64, by omega⟩
    have he : (⟨64 + (i.val - 64), by omega⟩ : Fin 160) = i := by apply Fin.ext; dsimp; omega
    exact he ▸ h
  by_cases h3 : i.val < 128
  · have h := profile5Chunk3_checked ⟨i.val - 96, by omega⟩
    have he : (⟨96 + (i.val - 96), by omega⟩ : Fin 160) = i := by apply Fin.ext; dsimp; omega
    exact he ▸ h
  have h := profile5Chunk4_checked ⟨i.val - 128, by omega⟩
  have he : (⟨128 + (i.val - 128), by omega⟩ : Fin 160) = i := by apply Fin.ext; dsimp; omega
  exact he ▸ h

#print axioms profile5_checked

end SparseMonotiles.Contact
