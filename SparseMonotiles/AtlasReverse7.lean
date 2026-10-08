module

public import SparseMonotiles.AtlasReverseChunks.Tile7Facets0
public import SparseMonotiles.AtlasReverseChunks.Tile7Facets1
public import SparseMonotiles.AtlasReverseChunks.Tile7Facets2
public import SparseMonotiles.AtlasReverseChunks.Tile7Facets3
public import SparseMonotiles.AtlasReverseChunks.Tile7Facets4
public import SparseMonotiles.AtlasReverseChunks.Tile7Facets5
public import SparseMonotiles.AtlasReverseChunks.Tile7Facets6
public import SparseMonotiles.AtlasReverseChunks.Tile7Facets7
public import SparseMonotiles.AtlasReverseChunks.Tile7Facets8
public import SparseMonotiles.AtlasReverseChunks.Tile7Facets9
public import SparseMonotiles.AtlasReverseChunks.Tile7Facets10
public import SparseMonotiles.AtlasReverseChunks.Tile7Facets11
public import SparseMonotiles.AtlasReverseChunks.Tile7Facets12
public import SparseMonotiles.AtlasReverseChunks.Tile7Facets13
public import SparseMonotiles.AtlasReverseChunks.Tile7Facets14
public import SparseMonotiles.AtlasReverseChunks.Tile7Facets15
public import SparseMonotiles.AtlasReverseChunks.Tile7Facets16
public import SparseMonotiles.AtlasReverseChunks.Tile7Facets17
public import SparseMonotiles.AtlasReverseChunks.Tile7Facets18
public import SparseMonotiles.AtlasReverseChunks.Tile7Facets19
public import SparseMonotiles.AtlasReverseChunks.Tile7Facets20
public import SparseMonotiles.AtlasReverseChunks.Tile7Facets21
public import SparseMonotiles.AtlasReverseChunks.Tile7Facets22
public import SparseMonotiles.AtlasReverseChunks.Tile7Facets23
public import SparseMonotiles.AtlasReverseChunks.Tile7Facets24
public import SparseMonotiles.AtlasReverseChunks.Tile7Facets25
public import SparseMonotiles.AtlasReverseChunks.Tile7Facets26
public import SparseMonotiles.AtlasReverseChunks.Tile7Facets27

@[expose] public section

namespace SparseMonotiles.Canonical
open Contact

/-- Every indexed T7 profile key decodes to an actual literal body key. -/
theorem everyAtlas7Key_isLiteral (i : Fin 896) (b : BoxKey 7)
    (hb : b ∈ IndexedData7.geometry.profile i) : b.toKeyData 188160 ∈ keys7 := by
  by_cases h0 : i.val < 32
  · have h := atlasReverse7Chunk0 ⟨i.val - 0, by omega⟩
    have he : (⟨0 + (i.val - 0), by omega⟩ : Fin 896) = i := by apply Fin.ext; dsimp; omega
    exact (he ▸ h) b hb
  by_cases h1 : i.val < 64
  · have h := atlasReverse7Chunk1 ⟨i.val - 32, by omega⟩
    have he : (⟨32 + (i.val - 32), by omega⟩ : Fin 896) = i := by apply Fin.ext; dsimp; omega
    exact (he ▸ h) b hb
  by_cases h2 : i.val < 96
  · have h := atlasReverse7Chunk2 ⟨i.val - 64, by omega⟩
    have he : (⟨64 + (i.val - 64), by omega⟩ : Fin 896) = i := by apply Fin.ext; dsimp; omega
    exact (he ▸ h) b hb
  by_cases h3 : i.val < 128
  · have h := atlasReverse7Chunk3 ⟨i.val - 96, by omega⟩
    have he : (⟨96 + (i.val - 96), by omega⟩ : Fin 896) = i := by apply Fin.ext; dsimp; omega
    exact (he ▸ h) b hb
  by_cases h4 : i.val < 160
  · have h := atlasReverse7Chunk4 ⟨i.val - 128, by omega⟩
    have he : (⟨128 + (i.val - 128), by omega⟩ : Fin 896) = i := by apply Fin.ext; dsimp; omega
    exact (he ▸ h) b hb
  by_cases h5 : i.val < 192
  · have h := atlasReverse7Chunk5 ⟨i.val - 160, by omega⟩
    have he : (⟨160 + (i.val - 160), by omega⟩ : Fin 896) = i := by apply Fin.ext; dsimp; omega
    exact (he ▸ h) b hb
  by_cases h6 : i.val < 224
  · have h := atlasReverse7Chunk6 ⟨i.val - 192, by omega⟩
    have he : (⟨192 + (i.val - 192), by omega⟩ : Fin 896) = i := by apply Fin.ext; dsimp; omega
    exact (he ▸ h) b hb
  by_cases h7 : i.val < 256
  · have h := atlasReverse7Chunk7 ⟨i.val - 224, by omega⟩
    have he : (⟨224 + (i.val - 224), by omega⟩ : Fin 896) = i := by apply Fin.ext; dsimp; omega
    exact (he ▸ h) b hb
  by_cases h8 : i.val < 288
  · have h := atlasReverse7Chunk8 ⟨i.val - 256, by omega⟩
    have he : (⟨256 + (i.val - 256), by omega⟩ : Fin 896) = i := by apply Fin.ext; dsimp; omega
    exact (he ▸ h) b hb
  by_cases h9 : i.val < 320
  · have h := atlasReverse7Chunk9 ⟨i.val - 288, by omega⟩
    have he : (⟨288 + (i.val - 288), by omega⟩ : Fin 896) = i := by apply Fin.ext; dsimp; omega
    exact (he ▸ h) b hb
  by_cases h10 : i.val < 352
  · have h := atlasReverse7Chunk10 ⟨i.val - 320, by omega⟩
    have he : (⟨320 + (i.val - 320), by omega⟩ : Fin 896) = i := by apply Fin.ext; dsimp; omega
    exact (he ▸ h) b hb
  by_cases h11 : i.val < 384
  · have h := atlasReverse7Chunk11 ⟨i.val - 352, by omega⟩
    have he : (⟨352 + (i.val - 352), by omega⟩ : Fin 896) = i := by apply Fin.ext; dsimp; omega
    exact (he ▸ h) b hb
  by_cases h12 : i.val < 416
  · have h := atlasReverse7Chunk12 ⟨i.val - 384, by omega⟩
    have he : (⟨384 + (i.val - 384), by omega⟩ : Fin 896) = i := by apply Fin.ext; dsimp; omega
    exact (he ▸ h) b hb
  by_cases h13 : i.val < 448
  · have h := atlasReverse7Chunk13 ⟨i.val - 416, by omega⟩
    have he : (⟨416 + (i.val - 416), by omega⟩ : Fin 896) = i := by apply Fin.ext; dsimp; omega
    exact (he ▸ h) b hb
  by_cases h14 : i.val < 480
  · have h := atlasReverse7Chunk14 ⟨i.val - 448, by omega⟩
    have he : (⟨448 + (i.val - 448), by omega⟩ : Fin 896) = i := by apply Fin.ext; dsimp; omega
    exact (he ▸ h) b hb
  by_cases h15 : i.val < 512
  · have h := atlasReverse7Chunk15 ⟨i.val - 480, by omega⟩
    have he : (⟨480 + (i.val - 480), by omega⟩ : Fin 896) = i := by apply Fin.ext; dsimp; omega
    exact (he ▸ h) b hb
  by_cases h16 : i.val < 544
  · have h := atlasReverse7Chunk16 ⟨i.val - 512, by omega⟩
    have he : (⟨512 + (i.val - 512), by omega⟩ : Fin 896) = i := by apply Fin.ext; dsimp; omega
    exact (he ▸ h) b hb
  by_cases h17 : i.val < 576
  · have h := atlasReverse7Chunk17 ⟨i.val - 544, by omega⟩
    have he : (⟨544 + (i.val - 544), by omega⟩ : Fin 896) = i := by apply Fin.ext; dsimp; omega
    exact (he ▸ h) b hb
  by_cases h18 : i.val < 608
  · have h := atlasReverse7Chunk18 ⟨i.val - 576, by omega⟩
    have he : (⟨576 + (i.val - 576), by omega⟩ : Fin 896) = i := by apply Fin.ext; dsimp; omega
    exact (he ▸ h) b hb
  by_cases h19 : i.val < 640
  · have h := atlasReverse7Chunk19 ⟨i.val - 608, by omega⟩
    have he : (⟨608 + (i.val - 608), by omega⟩ : Fin 896) = i := by apply Fin.ext; dsimp; omega
    exact (he ▸ h) b hb
  by_cases h20 : i.val < 672
  · have h := atlasReverse7Chunk20 ⟨i.val - 640, by omega⟩
    have he : (⟨640 + (i.val - 640), by omega⟩ : Fin 896) = i := by apply Fin.ext; dsimp; omega
    exact (he ▸ h) b hb
  by_cases h21 : i.val < 704
  · have h := atlasReverse7Chunk21 ⟨i.val - 672, by omega⟩
    have he : (⟨672 + (i.val - 672), by omega⟩ : Fin 896) = i := by apply Fin.ext; dsimp; omega
    exact (he ▸ h) b hb
  by_cases h22 : i.val < 736
  · have h := atlasReverse7Chunk22 ⟨i.val - 704, by omega⟩
    have he : (⟨704 + (i.val - 704), by omega⟩ : Fin 896) = i := by apply Fin.ext; dsimp; omega
    exact (he ▸ h) b hb
  by_cases h23 : i.val < 768
  · have h := atlasReverse7Chunk23 ⟨i.val - 736, by omega⟩
    have he : (⟨736 + (i.val - 736), by omega⟩ : Fin 896) = i := by apply Fin.ext; dsimp; omega
    exact (he ▸ h) b hb
  by_cases h24 : i.val < 800
  · have h := atlasReverse7Chunk24 ⟨i.val - 768, by omega⟩
    have he : (⟨768 + (i.val - 768), by omega⟩ : Fin 896) = i := by apply Fin.ext; dsimp; omega
    exact (he ▸ h) b hb
  by_cases h25 : i.val < 832
  · have h := atlasReverse7Chunk25 ⟨i.val - 800, by omega⟩
    have he : (⟨800 + (i.val - 800), by omega⟩ : Fin 896) = i := by apply Fin.ext; dsimp; omega
    exact (he ▸ h) b hb
  by_cases h26 : i.val < 864
  · have h := atlasReverse7Chunk26 ⟨i.val - 832, by omega⟩
    have he : (⟨832 + (i.val - 832), by omega⟩ : Fin 896) = i := by apply Fin.ext; dsimp; omega
    exact (he ▸ h) b hb
  have h := atlasReverse7Chunk27 ⟨i.val - 864, by omega⟩
  have he : (⟨864 + (i.val - 864), by omega⟩ : Fin 896) = i := by apply Fin.ext; dsimp; omega
  exact (he ▸ h) b hb

#print axioms everyAtlas7Key_isLiteral
end SparseMonotiles.Canonical
