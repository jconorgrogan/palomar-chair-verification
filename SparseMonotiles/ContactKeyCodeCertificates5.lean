module

public import SparseMonotiles.ContactKeyCodeChunks.Tile5Chunk00
public import SparseMonotiles.ContactKeyCodeChunks.Tile5Chunk01
public import SparseMonotiles.ContactKeyCodeChunks.Tile5Chunk02
public import SparseMonotiles.ContactKeyCodeChunks.Tile5Chunk03
public import SparseMonotiles.ContactKeyCodeChunks.Tile5Chunk04

@[expose] public section

namespace SparseMonotiles.Contact
open IndexedData5

set_option maxHeartbeats 0

theorem keyCode5_checked : ∀ i, geometry.CodeValidAt coordinateCode i := by
  intro i
  by_cases h0 : i.val < 32
  ·
    have h := keyCode5Chunk00_checked ⟨i.val - 0, by omega⟩
    have he : (⟨0 + (i.val - 0), by omega⟩ : Fin 160) = i := by apply Fin.ext; dsimp; omega
    exact he ▸ h
  by_cases h1 : i.val < 64
  ·
    have h := keyCode5Chunk01_checked ⟨i.val - 32, by omega⟩
    have he : (⟨32 + (i.val - 32), by omega⟩ : Fin 160) = i := by apply Fin.ext; dsimp; omega
    exact he ▸ h
  by_cases h2 : i.val < 96
  ·
    have h := keyCode5Chunk02_checked ⟨i.val - 64, by omega⟩
    have he : (⟨64 + (i.val - 64), by omega⟩ : Fin 160) = i := by apply Fin.ext; dsimp; omega
    exact he ▸ h
  by_cases h3 : i.val < 128
  ·
    have h := keyCode5Chunk03_checked ⟨i.val - 96, by omega⟩
    have he : (⟨96 + (i.val - 96), by omega⟩ : Fin 160) = i := by apply Fin.ext; dsimp; omega
    exact he ▸ h
  have h := keyCode5Chunk04_checked ⟨i.val - 128, by omega⟩
  have he : (⟨128 + (i.val - 128), by omega⟩ : Fin 160) = i := by apply Fin.ext; dsimp; omega
  exact he ▸ h

theorem keyCode5_codedBy : geometry.CodedBy coordinateCode :=
  ⟨rfl, fun i k hk => (keyCode5_checked i k hk).1⟩

theorem keyCode5_regular : ∀ i k, k ∈ geometry.profile i →
    coordinateCode.RegularKey (geometry.facet i) k :=
  fun i k hk => (keyCode5_checked i k hk).2

#print axioms keyCode5_checked
#print axioms keyCode5_codedBy
#print axioms keyCode5_regular
end SparseMonotiles.Contact
