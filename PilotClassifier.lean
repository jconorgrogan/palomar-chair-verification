module
public import PilotChunk00
public import PilotChunk01
public import PilotChunk02
public import PilotChunk03
public import PilotChunk04
public import PilotChunk05
public import PilotChunk06
public import PilotChunk07
public import PilotChunk08
public import PilotChunk09
public import PilotChunk10
public import PilotChunk11
public import PilotChunk12
public import PilotChunk13
public import PilotChunk14
public import PilotChunk15
public import PilotChunk16
public import PilotChunk17
public import PilotChunk18
public import PilotChunk19
public import PilotChunk20
public import PilotChunk21
public import PilotChunk22
public import PilotChunk23
public import PilotChunk24
public import PilotChunk25
public import PilotChunk26
public import PilotChunk27
public import PilotChunk28
public import PilotChunk29
public import PilotChunk30
public import PilotChunk31
@[expose] public section
namespace SparseMonotiles.Contact.RootZeroPilot7
open IndexedData7 CarrierHierarchy
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem all_classified (i : Fin 1024) : RowClassified i := by
  by_cases h0 : i.val < 32
  · have h := chunk00_classified ⟨i.val - 0, by omega⟩
    have he : (⟨0 + (i.val - 0), by omega⟩ : Fin 1024) = i := by apply Fin.ext; dsimp; omega
    exact he ▸ h
  by_cases h1 : i.val < 64
  · have h := chunk01_classified ⟨i.val - 32, by omega⟩
    have he : (⟨32 + (i.val - 32), by omega⟩ : Fin 1024) = i := by apply Fin.ext; dsimp; omega
    exact he ▸ h
  by_cases h2 : i.val < 96
  · have h := chunk02_classified ⟨i.val - 64, by omega⟩
    have he : (⟨64 + (i.val - 64), by omega⟩ : Fin 1024) = i := by apply Fin.ext; dsimp; omega
    exact he ▸ h
  by_cases h3 : i.val < 128
  · have h := chunk03_classified ⟨i.val - 96, by omega⟩
    have he : (⟨96 + (i.val - 96), by omega⟩ : Fin 1024) = i := by apply Fin.ext; dsimp; omega
    exact he ▸ h
  by_cases h4 : i.val < 160
  · have h := chunk04_classified ⟨i.val - 128, by omega⟩
    have he : (⟨128 + (i.val - 128), by omega⟩ : Fin 1024) = i := by apply Fin.ext; dsimp; omega
    exact he ▸ h
  by_cases h5 : i.val < 192
  · have h := chunk05_classified ⟨i.val - 160, by omega⟩
    have he : (⟨160 + (i.val - 160), by omega⟩ : Fin 1024) = i := by apply Fin.ext; dsimp; omega
    exact he ▸ h
  by_cases h6 : i.val < 224
  · have h := chunk06_classified ⟨i.val - 192, by omega⟩
    have he : (⟨192 + (i.val - 192), by omega⟩ : Fin 1024) = i := by apply Fin.ext; dsimp; omega
    exact he ▸ h
  by_cases h7 : i.val < 256
  · have h := chunk07_classified ⟨i.val - 224, by omega⟩
    have he : (⟨224 + (i.val - 224), by omega⟩ : Fin 1024) = i := by apply Fin.ext; dsimp; omega
    exact he ▸ h
  by_cases h8 : i.val < 288
  · have h := chunk08_classified ⟨i.val - 256, by omega⟩
    have he : (⟨256 + (i.val - 256), by omega⟩ : Fin 1024) = i := by apply Fin.ext; dsimp; omega
    exact he ▸ h
  by_cases h9 : i.val < 320
  · have h := chunk09_classified ⟨i.val - 288, by omega⟩
    have he : (⟨288 + (i.val - 288), by omega⟩ : Fin 1024) = i := by apply Fin.ext; dsimp; omega
    exact he ▸ h
  by_cases h10 : i.val < 352
  · have h := chunk10_classified ⟨i.val - 320, by omega⟩
    have he : (⟨320 + (i.val - 320), by omega⟩ : Fin 1024) = i := by apply Fin.ext; dsimp; omega
    exact he ▸ h
  by_cases h11 : i.val < 384
  · have h := chunk11_classified ⟨i.val - 352, by omega⟩
    have he : (⟨352 + (i.val - 352), by omega⟩ : Fin 1024) = i := by apply Fin.ext; dsimp; omega
    exact he ▸ h
  by_cases h12 : i.val < 416
  · have h := chunk12_classified ⟨i.val - 384, by omega⟩
    have he : (⟨384 + (i.val - 384), by omega⟩ : Fin 1024) = i := by apply Fin.ext; dsimp; omega
    exact he ▸ h
  by_cases h13 : i.val < 448
  · have h := chunk13_classified ⟨i.val - 416, by omega⟩
    have he : (⟨416 + (i.val - 416), by omega⟩ : Fin 1024) = i := by apply Fin.ext; dsimp; omega
    exact he ▸ h
  by_cases h14 : i.val < 480
  · have h := chunk14_classified ⟨i.val - 448, by omega⟩
    have he : (⟨448 + (i.val - 448), by omega⟩ : Fin 1024) = i := by apply Fin.ext; dsimp; omega
    exact he ▸ h
  by_cases h15 : i.val < 512
  · have h := chunk15_classified ⟨i.val - 480, by omega⟩
    have he : (⟨480 + (i.val - 480), by omega⟩ : Fin 1024) = i := by apply Fin.ext; dsimp; omega
    exact he ▸ h
  by_cases h16 : i.val < 544
  · have h := chunk16_classified ⟨i.val - 512, by omega⟩
    have he : (⟨512 + (i.val - 512), by omega⟩ : Fin 1024) = i := by apply Fin.ext; dsimp; omega
    exact he ▸ h
  by_cases h17 : i.val < 576
  · have h := chunk17_classified ⟨i.val - 544, by omega⟩
    have he : (⟨544 + (i.val - 544), by omega⟩ : Fin 1024) = i := by apply Fin.ext; dsimp; omega
    exact he ▸ h
  by_cases h18 : i.val < 608
  · have h := chunk18_classified ⟨i.val - 576, by omega⟩
    have he : (⟨576 + (i.val - 576), by omega⟩ : Fin 1024) = i := by apply Fin.ext; dsimp; omega
    exact he ▸ h
  by_cases h19 : i.val < 640
  · have h := chunk19_classified ⟨i.val - 608, by omega⟩
    have he : (⟨608 + (i.val - 608), by omega⟩ : Fin 1024) = i := by apply Fin.ext; dsimp; omega
    exact he ▸ h
  by_cases h20 : i.val < 672
  · have h := chunk20_classified ⟨i.val - 640, by omega⟩
    have he : (⟨640 + (i.val - 640), by omega⟩ : Fin 1024) = i := by apply Fin.ext; dsimp; omega
    exact he ▸ h
  by_cases h21 : i.val < 704
  · have h := chunk21_classified ⟨i.val - 672, by omega⟩
    have he : (⟨672 + (i.val - 672), by omega⟩ : Fin 1024) = i := by apply Fin.ext; dsimp; omega
    exact he ▸ h
  by_cases h22 : i.val < 736
  · have h := chunk22_classified ⟨i.val - 704, by omega⟩
    have he : (⟨704 + (i.val - 704), by omega⟩ : Fin 1024) = i := by apply Fin.ext; dsimp; omega
    exact he ▸ h
  by_cases h23 : i.val < 768
  · have h := chunk23_classified ⟨i.val - 736, by omega⟩
    have he : (⟨736 + (i.val - 736), by omega⟩ : Fin 1024) = i := by apply Fin.ext; dsimp; omega
    exact he ▸ h
  by_cases h24 : i.val < 800
  · have h := chunk24_classified ⟨i.val - 768, by omega⟩
    have he : (⟨768 + (i.val - 768), by omega⟩ : Fin 1024) = i := by apply Fin.ext; dsimp; omega
    exact he ▸ h
  by_cases h25 : i.val < 832
  · have h := chunk25_classified ⟨i.val - 800, by omega⟩
    have he : (⟨800 + (i.val - 800), by omega⟩ : Fin 1024) = i := by apply Fin.ext; dsimp; omega
    exact he ▸ h
  by_cases h26 : i.val < 864
  · have h := chunk26_classified ⟨i.val - 832, by omega⟩
    have he : (⟨832 + (i.val - 832), by omega⟩ : Fin 1024) = i := by apply Fin.ext; dsimp; omega
    exact he ▸ h
  by_cases h27 : i.val < 896
  · have h := chunk27_classified ⟨i.val - 864, by omega⟩
    have he : (⟨864 + (i.val - 864), by omega⟩ : Fin 1024) = i := by apply Fin.ext; dsimp; omega
    exact he ▸ h
  by_cases h28 : i.val < 928
  · have h := chunk28_classified ⟨i.val - 896, by omega⟩
    have he : (⟨896 + (i.val - 896), by omega⟩ : Fin 1024) = i := by apply Fin.ext; dsimp; omega
    exact he ▸ h
  by_cases h29 : i.val < 960
  · have h := chunk29_classified ⟨i.val - 928, by omega⟩
    have he : (⟨928 + (i.val - 928), by omega⟩ : Fin 1024) = i := by apply Fin.ext; dsimp; omega
    exact he ▸ h
  by_cases h30 : i.val < 992
  · have h := chunk30_classified ⟨i.val - 960, by omega⟩
    have he : (⟨960 + (i.val - 960), by omega⟩ : Fin 1024) = i := by apply Fin.ext; dsimp; omega
    exact he ▸ h
  by_cases h31 : i.val < 1024
  · have h := chunk31_classified ⟨i.val - 992, by omega⟩
    have he : (⟨992 + (i.val - 992), by omega⟩ : Fin 1024) = i := by apply Fin.ext; dsimp; omega
    exact he ▸ h
  omega

theorem all_source (i : Fin 1024) : sourceKey i ∈ geometry.profile (sourceOwner i) := by
  by_cases h0 : i.val < 32
  · have h := chunk00_source ⟨i.val - 0, by omega⟩
    have he : (⟨0 + (i.val - 0), by omega⟩ : Fin 1024) = i := by apply Fin.ext; dsimp; omega
    exact he ▸ h
  by_cases h1 : i.val < 64
  · have h := chunk01_source ⟨i.val - 32, by omega⟩
    have he : (⟨32 + (i.val - 32), by omega⟩ : Fin 1024) = i := by apply Fin.ext; dsimp; omega
    exact he ▸ h
  by_cases h2 : i.val < 96
  · have h := chunk02_source ⟨i.val - 64, by omega⟩
    have he : (⟨64 + (i.val - 64), by omega⟩ : Fin 1024) = i := by apply Fin.ext; dsimp; omega
    exact he ▸ h
  by_cases h3 : i.val < 128
  · have h := chunk03_source ⟨i.val - 96, by omega⟩
    have he : (⟨96 + (i.val - 96), by omega⟩ : Fin 1024) = i := by apply Fin.ext; dsimp; omega
    exact he ▸ h
  by_cases h4 : i.val < 160
  · have h := chunk04_source ⟨i.val - 128, by omega⟩
    have he : (⟨128 + (i.val - 128), by omega⟩ : Fin 1024) = i := by apply Fin.ext; dsimp; omega
    exact he ▸ h
  by_cases h5 : i.val < 192
  · have h := chunk05_source ⟨i.val - 160, by omega⟩
    have he : (⟨160 + (i.val - 160), by omega⟩ : Fin 1024) = i := by apply Fin.ext; dsimp; omega
    exact he ▸ h
  by_cases h6 : i.val < 224
  · have h := chunk06_source ⟨i.val - 192, by omega⟩
    have he : (⟨192 + (i.val - 192), by omega⟩ : Fin 1024) = i := by apply Fin.ext; dsimp; omega
    exact he ▸ h
  by_cases h7 : i.val < 256
  · have h := chunk07_source ⟨i.val - 224, by omega⟩
    have he : (⟨224 + (i.val - 224), by omega⟩ : Fin 1024) = i := by apply Fin.ext; dsimp; omega
    exact he ▸ h
  by_cases h8 : i.val < 288
  · have h := chunk08_source ⟨i.val - 256, by omega⟩
    have he : (⟨256 + (i.val - 256), by omega⟩ : Fin 1024) = i := by apply Fin.ext; dsimp; omega
    exact he ▸ h
  by_cases h9 : i.val < 320
  · have h := chunk09_source ⟨i.val - 288, by omega⟩
    have he : (⟨288 + (i.val - 288), by omega⟩ : Fin 1024) = i := by apply Fin.ext; dsimp; omega
    exact he ▸ h
  by_cases h10 : i.val < 352
  · have h := chunk10_source ⟨i.val - 320, by omega⟩
    have he : (⟨320 + (i.val - 320), by omega⟩ : Fin 1024) = i := by apply Fin.ext; dsimp; omega
    exact he ▸ h
  by_cases h11 : i.val < 384
  · have h := chunk11_source ⟨i.val - 352, by omega⟩
    have he : (⟨352 + (i.val - 352), by omega⟩ : Fin 1024) = i := by apply Fin.ext; dsimp; omega
    exact he ▸ h
  by_cases h12 : i.val < 416
  · have h := chunk12_source ⟨i.val - 384, by omega⟩
    have he : (⟨384 + (i.val - 384), by omega⟩ : Fin 1024) = i := by apply Fin.ext; dsimp; omega
    exact he ▸ h
  by_cases h13 : i.val < 448
  · have h := chunk13_source ⟨i.val - 416, by omega⟩
    have he : (⟨416 + (i.val - 416), by omega⟩ : Fin 1024) = i := by apply Fin.ext; dsimp; omega
    exact he ▸ h
  by_cases h14 : i.val < 480
  · have h := chunk14_source ⟨i.val - 448, by omega⟩
    have he : (⟨448 + (i.val - 448), by omega⟩ : Fin 1024) = i := by apply Fin.ext; dsimp; omega
    exact he ▸ h
  by_cases h15 : i.val < 512
  · have h := chunk15_source ⟨i.val - 480, by omega⟩
    have he : (⟨480 + (i.val - 480), by omega⟩ : Fin 1024) = i := by apply Fin.ext; dsimp; omega
    exact he ▸ h
  by_cases h16 : i.val < 544
  · have h := chunk16_source ⟨i.val - 512, by omega⟩
    have he : (⟨512 + (i.val - 512), by omega⟩ : Fin 1024) = i := by apply Fin.ext; dsimp; omega
    exact he ▸ h
  by_cases h17 : i.val < 576
  · have h := chunk17_source ⟨i.val - 544, by omega⟩
    have he : (⟨544 + (i.val - 544), by omega⟩ : Fin 1024) = i := by apply Fin.ext; dsimp; omega
    exact he ▸ h
  by_cases h18 : i.val < 608
  · have h := chunk18_source ⟨i.val - 576, by omega⟩
    have he : (⟨576 + (i.val - 576), by omega⟩ : Fin 1024) = i := by apply Fin.ext; dsimp; omega
    exact he ▸ h
  by_cases h19 : i.val < 640
  · have h := chunk19_source ⟨i.val - 608, by omega⟩
    have he : (⟨608 + (i.val - 608), by omega⟩ : Fin 1024) = i := by apply Fin.ext; dsimp; omega
    exact he ▸ h
  by_cases h20 : i.val < 672
  · have h := chunk20_source ⟨i.val - 640, by omega⟩
    have he : (⟨640 + (i.val - 640), by omega⟩ : Fin 1024) = i := by apply Fin.ext; dsimp; omega
    exact he ▸ h
  by_cases h21 : i.val < 704
  · have h := chunk21_source ⟨i.val - 672, by omega⟩
    have he : (⟨672 + (i.val - 672), by omega⟩ : Fin 1024) = i := by apply Fin.ext; dsimp; omega
    exact he ▸ h
  by_cases h22 : i.val < 736
  · have h := chunk22_source ⟨i.val - 704, by omega⟩
    have he : (⟨704 + (i.val - 704), by omega⟩ : Fin 1024) = i := by apply Fin.ext; dsimp; omega
    exact he ▸ h
  by_cases h23 : i.val < 768
  · have h := chunk23_source ⟨i.val - 736, by omega⟩
    have he : (⟨736 + (i.val - 736), by omega⟩ : Fin 1024) = i := by apply Fin.ext; dsimp; omega
    exact he ▸ h
  by_cases h24 : i.val < 800
  · have h := chunk24_source ⟨i.val - 768, by omega⟩
    have he : (⟨768 + (i.val - 768), by omega⟩ : Fin 1024) = i := by apply Fin.ext; dsimp; omega
    exact he ▸ h
  by_cases h25 : i.val < 832
  · have h := chunk25_source ⟨i.val - 800, by omega⟩
    have he : (⟨800 + (i.val - 800), by omega⟩ : Fin 1024) = i := by apply Fin.ext; dsimp; omega
    exact he ▸ h
  by_cases h26 : i.val < 864
  · have h := chunk26_source ⟨i.val - 832, by omega⟩
    have he : (⟨832 + (i.val - 832), by omega⟩ : Fin 1024) = i := by apply Fin.ext; dsimp; omega
    exact he ▸ h
  by_cases h27 : i.val < 896
  · have h := chunk27_source ⟨i.val - 864, by omega⟩
    have he : (⟨864 + (i.val - 864), by omega⟩ : Fin 1024) = i := by apply Fin.ext; dsimp; omega
    exact he ▸ h
  by_cases h28 : i.val < 928
  · have h := chunk28_source ⟨i.val - 896, by omega⟩
    have he : (⟨896 + (i.val - 896), by omega⟩ : Fin 1024) = i := by apply Fin.ext; dsimp; omega
    exact he ▸ h
  by_cases h29 : i.val < 960
  · have h := chunk29_source ⟨i.val - 928, by omega⟩
    have he : (⟨928 + (i.val - 928), by omega⟩ : Fin 1024) = i := by apply Fin.ext; dsimp; omega
    exact he ▸ h
  by_cases h30 : i.val < 992
  · have h := chunk30_source ⟨i.val - 960, by omega⟩
    have he : (⟨960 + (i.val - 960), by omega⟩ : Fin 1024) = i := by apply Fin.ext; dsimp; omega
    exact he ▸ h
  by_cases h31 : i.val < 1024
  · have h := chunk31_source ⟨i.val - 992, by omega⟩
    have he : (⟨992 + (i.val - 992), by omega⟩ : Fin 1024) = i := by apply Fin.ext; dsimp; omega
    exact he ▸ h
  omega

/-- Bounded root-key-zero classifier. This theorem covers the exact 1,024
source-key entries only. It makes no claim about the other 1,023 root keys,
accepted-row legality, a full contact equivalence, existence, or monotilings. -/
theorem legal_pair_mem_M7 (i : Fin 1024) (p : Pose 7)
    (generated : pairPose geometry.denominator (geometry.facet 0)
      (geometry.facet (sourceOwner i)) key0 (sourceKey i) = some p)
    (legal : geometry.LegalContact p) : p ∈ M7 :=
  all_classified i p generated legal

#print axioms all_classified
#print axioms all_source
#print axioms legal_pair_mem_M7
end SparseMonotiles.Contact.RootZeroPilot7
