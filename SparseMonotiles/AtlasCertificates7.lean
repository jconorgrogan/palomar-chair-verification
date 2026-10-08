module

public import SparseMonotiles.AtlasCertificateChunks.Tile7Chunk0
public import SparseMonotiles.AtlasCertificateChunks.Tile7Chunk1
public import SparseMonotiles.AtlasCertificateChunks.Tile7Chunk2
public import SparseMonotiles.AtlasCertificateChunks.Tile7Chunk3
public import SparseMonotiles.AtlasCertificateChunks.Tile7Chunk4
public import SparseMonotiles.AtlasCertificateChunks.Tile7Chunk5
public import SparseMonotiles.AtlasCertificateChunks.Tile7Chunk6
public import SparseMonotiles.AtlasCertificateChunks.Tile7Chunk7
public import SparseMonotiles.AtlasCertificateChunks.Tile7Chunk8
public import SparseMonotiles.AtlasCertificateChunks.Tile7Chunk9
public import SparseMonotiles.AtlasCertificateChunks.Tile7Chunk10
public import SparseMonotiles.AtlasCertificateChunks.Tile7Chunk11
public import SparseMonotiles.AtlasCertificateChunks.Tile7Chunk12
public import SparseMonotiles.AtlasCertificateChunks.Tile7Chunk13
public import SparseMonotiles.AtlasCertificateChunks.Tile7Chunk14
public import SparseMonotiles.AtlasCertificateChunks.Tile7Chunk15
public import SparseMonotiles.AtlasCertificateChunks.Tile7Chunk16
public import SparseMonotiles.AtlasCertificateChunks.Tile7Chunk17
public import SparseMonotiles.AtlasCertificateChunks.Tile7Chunk18
public import SparseMonotiles.AtlasCertificateChunks.Tile7Chunk19
public import SparseMonotiles.AtlasCertificateChunks.Tile7Chunk20
public import SparseMonotiles.AtlasCertificateChunks.Tile7Chunk21
public import SparseMonotiles.AtlasCertificateChunks.Tile7Chunk22
public import SparseMonotiles.AtlasCertificateChunks.Tile7Chunk23
public import SparseMonotiles.AtlasCertificateChunks.Tile7Chunk24
public import SparseMonotiles.AtlasCertificateChunks.Tile7Chunk25
public import SparseMonotiles.AtlasCertificateChunks.Tile7Chunk26
public import SparseMonotiles.AtlasCertificateChunks.Tile7Chunk27

@[expose] public section

namespace SparseMonotiles.Contact

theorem atlas7_checked : ∀ i, IndexedData7.geometry.AtlasValidAt i := by
  intro i
  by_cases h0 : i.val < 32
  · have h := atlas7Chunk0_checked ⟨i.val - 0, by omega⟩
    have he : (⟨0 + (i.val - 0), by omega⟩ : Fin 896) = i := by apply Fin.ext; dsimp; omega
    exact he ▸ h
  by_cases h1 : i.val < 64
  · have h := atlas7Chunk1_checked ⟨i.val - 32, by omega⟩
    have he : (⟨32 + (i.val - 32), by omega⟩ : Fin 896) = i := by apply Fin.ext; dsimp; omega
    exact he ▸ h
  by_cases h2 : i.val < 96
  · have h := atlas7Chunk2_checked ⟨i.val - 64, by omega⟩
    have he : (⟨64 + (i.val - 64), by omega⟩ : Fin 896) = i := by apply Fin.ext; dsimp; omega
    exact he ▸ h
  by_cases h3 : i.val < 128
  · have h := atlas7Chunk3_checked ⟨i.val - 96, by omega⟩
    have he : (⟨96 + (i.val - 96), by omega⟩ : Fin 896) = i := by apply Fin.ext; dsimp; omega
    exact he ▸ h
  by_cases h4 : i.val < 160
  · have h := atlas7Chunk4_checked ⟨i.val - 128, by omega⟩
    have he : (⟨128 + (i.val - 128), by omega⟩ : Fin 896) = i := by apply Fin.ext; dsimp; omega
    exact he ▸ h
  by_cases h5 : i.val < 192
  · have h := atlas7Chunk5_checked ⟨i.val - 160, by omega⟩
    have he : (⟨160 + (i.val - 160), by omega⟩ : Fin 896) = i := by apply Fin.ext; dsimp; omega
    exact he ▸ h
  by_cases h6 : i.val < 224
  · have h := atlas7Chunk6_checked ⟨i.val - 192, by omega⟩
    have he : (⟨192 + (i.val - 192), by omega⟩ : Fin 896) = i := by apply Fin.ext; dsimp; omega
    exact he ▸ h
  by_cases h7 : i.val < 256
  · have h := atlas7Chunk7_checked ⟨i.val - 224, by omega⟩
    have he : (⟨224 + (i.val - 224), by omega⟩ : Fin 896) = i := by apply Fin.ext; dsimp; omega
    exact he ▸ h
  by_cases h8 : i.val < 288
  · have h := atlas7Chunk8_checked ⟨i.val - 256, by omega⟩
    have he : (⟨256 + (i.val - 256), by omega⟩ : Fin 896) = i := by apply Fin.ext; dsimp; omega
    exact he ▸ h
  by_cases h9 : i.val < 320
  · have h := atlas7Chunk9_checked ⟨i.val - 288, by omega⟩
    have he : (⟨288 + (i.val - 288), by omega⟩ : Fin 896) = i := by apply Fin.ext; dsimp; omega
    exact he ▸ h
  by_cases h10 : i.val < 352
  · have h := atlas7Chunk10_checked ⟨i.val - 320, by omega⟩
    have he : (⟨320 + (i.val - 320), by omega⟩ : Fin 896) = i := by apply Fin.ext; dsimp; omega
    exact he ▸ h
  by_cases h11 : i.val < 384
  · have h := atlas7Chunk11_checked ⟨i.val - 352, by omega⟩
    have he : (⟨352 + (i.val - 352), by omega⟩ : Fin 896) = i := by apply Fin.ext; dsimp; omega
    exact he ▸ h
  by_cases h12 : i.val < 416
  · have h := atlas7Chunk12_checked ⟨i.val - 384, by omega⟩
    have he : (⟨384 + (i.val - 384), by omega⟩ : Fin 896) = i := by apply Fin.ext; dsimp; omega
    exact he ▸ h
  by_cases h13 : i.val < 448
  · have h := atlas7Chunk13_checked ⟨i.val - 416, by omega⟩
    have he : (⟨416 + (i.val - 416), by omega⟩ : Fin 896) = i := by apply Fin.ext; dsimp; omega
    exact he ▸ h
  by_cases h14 : i.val < 480
  · have h := atlas7Chunk14_checked ⟨i.val - 448, by omega⟩
    have he : (⟨448 + (i.val - 448), by omega⟩ : Fin 896) = i := by apply Fin.ext; dsimp; omega
    exact he ▸ h
  by_cases h15 : i.val < 512
  · have h := atlas7Chunk15_checked ⟨i.val - 480, by omega⟩
    have he : (⟨480 + (i.val - 480), by omega⟩ : Fin 896) = i := by apply Fin.ext; dsimp; omega
    exact he ▸ h
  by_cases h16 : i.val < 544
  · have h := atlas7Chunk16_checked ⟨i.val - 512, by omega⟩
    have he : (⟨512 + (i.val - 512), by omega⟩ : Fin 896) = i := by apply Fin.ext; dsimp; omega
    exact he ▸ h
  by_cases h17 : i.val < 576
  · have h := atlas7Chunk17_checked ⟨i.val - 544, by omega⟩
    have he : (⟨544 + (i.val - 544), by omega⟩ : Fin 896) = i := by apply Fin.ext; dsimp; omega
    exact he ▸ h
  by_cases h18 : i.val < 608
  · have h := atlas7Chunk18_checked ⟨i.val - 576, by omega⟩
    have he : (⟨576 + (i.val - 576), by omega⟩ : Fin 896) = i := by apply Fin.ext; dsimp; omega
    exact he ▸ h
  by_cases h19 : i.val < 640
  · have h := atlas7Chunk19_checked ⟨i.val - 608, by omega⟩
    have he : (⟨608 + (i.val - 608), by omega⟩ : Fin 896) = i := by apply Fin.ext; dsimp; omega
    exact he ▸ h
  by_cases h20 : i.val < 672
  · have h := atlas7Chunk20_checked ⟨i.val - 640, by omega⟩
    have he : (⟨640 + (i.val - 640), by omega⟩ : Fin 896) = i := by apply Fin.ext; dsimp; omega
    exact he ▸ h
  by_cases h21 : i.val < 704
  · have h := atlas7Chunk21_checked ⟨i.val - 672, by omega⟩
    have he : (⟨672 + (i.val - 672), by omega⟩ : Fin 896) = i := by apply Fin.ext; dsimp; omega
    exact he ▸ h
  by_cases h22 : i.val < 736
  · have h := atlas7Chunk22_checked ⟨i.val - 704, by omega⟩
    have he : (⟨704 + (i.val - 704), by omega⟩ : Fin 896) = i := by apply Fin.ext; dsimp; omega
    exact he ▸ h
  by_cases h23 : i.val < 768
  · have h := atlas7Chunk23_checked ⟨i.val - 736, by omega⟩
    have he : (⟨736 + (i.val - 736), by omega⟩ : Fin 896) = i := by apply Fin.ext; dsimp; omega
    exact he ▸ h
  by_cases h24 : i.val < 800
  · have h := atlas7Chunk24_checked ⟨i.val - 768, by omega⟩
    have he : (⟨768 + (i.val - 768), by omega⟩ : Fin 896) = i := by apply Fin.ext; dsimp; omega
    exact he ▸ h
  by_cases h25 : i.val < 832
  · have h := atlas7Chunk25_checked ⟨i.val - 800, by omega⟩
    have he : (⟨800 + (i.val - 800), by omega⟩ : Fin 896) = i := by apply Fin.ext; dsimp; omega
    exact he ▸ h
  by_cases h26 : i.val < 864
  · have h := atlas7Chunk26_checked ⟨i.val - 832, by omega⟩
    have he : (⟨832 + (i.val - 832), by omega⟩ : Fin 896) = i := by apply Fin.ext; dsimp; omega
    exact he ▸ h
  have h := atlas7Chunk27_checked ⟨i.val - 864, by omega⟩
  have he : (⟨864 + (i.val - 864), by omega⟩ : Fin 896) = i := by apply Fin.ext; dsimp; omega
  exact he ▸ h

#print axioms atlas7_checked

end SparseMonotiles.Contact
